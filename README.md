Lambda-JS
=========

Our own implementation of some features of Lambda-JS, based on the paper "The Essence of JavaScript".

Generally speaking, it is a functional-programming-language version of desugared Javascript.

JavaScript is a feature-rich language with many quirks, and these quirks are often exploited in security and privacy attacks. Due to its popularity and shortcomings, people have tried to solve such problems via program analyses and sub-languages. These works claim but do not demonstrate soundness, because the JavaScript standard is large and informal. Although some researchers proposed one formal semantics, it was still too large to apply conventional proof techniques. In The Essence of JavaScript [1], the authors model JavaScript’s essential features in a core language JS. They show that they can desugar JavaScript into JS and apply proof techniques to it.


[1] Guha, Arjun, Claudiu Saftoiu, and Shriram Krishnamurthi. "The essence of JavaScript." ECOOP 2010–Object-Oriented Programming. Springer Berlin Heidelberg, 2010. 126-150.
