-- Prove2me | Definitions.Def_FRouting_languageOf
-- name    : FRouting_languageOf
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:09:06.106196+00:00
-- url     : https://prove2.me/theorems/5736c65d-6032-4393-82bc-b4a22f21cd49
-- title:
--   Promise problems and the language $L_f$
-- statement:
--   A **promise problem** is a pair of sets of binary strings, the Yes and the No instances. For a family $f=\{f_n\}$ of Boolean functions on $\{0,1\}^n\times\{0,1\}^n$,
--   $$L_f=\{x\circ y\mid f_n(x,y)=1\},$$
--   as the promise problem whose No instances are all other strings, including those of odd length.
--
--   **Formalization Note** Definition 5.1 is for languages and Theorem 5.6 for a promise problem, so the class is on promise problems. Disjointness is not a field: membership in the class implies it, and for QSD it is proved in the verification file.
-- source:
--   Renard, Computational Bounds for f-Routing, arXiv:2609.40278 (held copy, sha256 4a327f29…), Definition 5.1, p.20; Definition 5.5, p.21

import Definitions.Def_QAlgorithms_ClassicalStringComputability

set_option autoImplicit false

namespace FRouting

open QAlgorithms.Complexity

/-- **A promise problem on binary strings**: the Yes and the No instances. Renard, *Computational
Bounds for f-Routing*, arXiv:2609.40278 (held copy, sha256 4a327f29…), Definitions 5.1 and 5.5:
Definition 5.1 is for languages and Theorem 5.6 for a promise problem, so the class is defined on
promise problems, a language `L` being `(L, Lᶜ)`.

**Formalization Note** Disjointness is not a field; the class `InQSZK` implies it through completeness
and soundness, and for `QSD` it is proved in the verification file. -/
structure PromiseProblem where
  /-- The Yes instances. -/
  Yes : Set Str
  /-- The No instances. -/
  No : Set Str

/-- **The language of `f`** (Definition 5.1, p.20): `L_f := {x ∘ y | f_n(x, y) = 1}`, with `x`, `y` of
equal length `n`, as a promise problem whose No instances are all other strings, odd lengths
included. -/
def languageOf (f : ∀ n, (Fin n → Bool) → (Fin n → Bool) → Bool) : PromiseProblem where
  Yes := { w | ∃ n x y, w = List.ofFn x ++ List.ofFn y ∧ f n x y = true }
  No := { w | ¬ ∃ n x y, w = List.ofFn x ++ List.ofFn y ∧ f n x y = true }

end FRouting


