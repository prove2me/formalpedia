-- Prove2me | Definitions.Def_NadlerCLS_pnPromiseSearch
-- name    : NadlerCLS_pnPromiseSearch
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:03:42.351308+00:00
-- url     : https://prove2.me/theorems/e9499c2d-6c3c-4d28-ad0b-8ec57ca0b77f
-- title:
--   The search problem $\beta$-Projected-Nadler with every promise
-- statement:
--   The search problem $\beta$-Projected-Nadler on $[0,1]^n$ restricted to instances that satisfy every promise of Definition 1: the input format with $0<\varepsilon_2<\varepsilon_1(1-k)$, and the promise that $([0,1]^n,d)$ is a complete metric space. The answers are the valid outputs (N1)–(N4), unchanged.
--
--   Its hardness is the hardness claim of Theorem 3.2: Remark 3.1 notes that "the instances built in our hardness reduction satisfy every promise".
--
--   **Formalization Note** The promise restricts the valid instances only. Since its answers coincide with those of the problem without the metric promise, hardness of this problem implies hardness of that one.
-- source:
--   Xiong–Vlatakis-Gkaragkounis, On the Complexity of Finding Fixed Points for Set-Valued Contractions, arXiv:2609.14101 (held version of 2026-11-03, sha256 1fcc5a027ffe65205e4ef9a9ef7730f6f07fe3f7006447cac39a7562e36dc485), Definition 1, p.9; Remark 3.1, p.9

import Mathlib
import Definitions.Def_NetworkEquilibriumCLS_LinearNash_Encoding
import Definitions.Def_NadlerCLS_PNInstance
import Definitions.Def_NadlerCLS_PNAnswer

set_option autoImplicit false

namespace NadlerCLS

open NetworkEquilibriumCLS.LinearNash

/-- The search problem **β-Projected-Nadler with every promise of Definition 1** on `[0, 1]ⁿ`
(Xiong–Vlatakis-Gkaragkounis, *On the Complexity of Finding Fixed Points for Set-Valued
Contractions*, arXiv:2609.14101, held version of 2026-11-03, sha256 1fcc5a02…6dc485, Definition 1,
p.9: "We promise that 0 < ε2 < ε1(1 − k) and (X, d) is a complete metric space"). A valid instance
is the code of a `PNInstance` that satisfies the input format and the metric and completeness
promise; answers are the valid outputs (N1)–(N4), unchanged.

**Formalization Note** The promise restricts the instances only; the answer relation is the one of
`pnSearch`. Hardness for this problem implies hardness for `pnSearch` (Remark 3.1: "the instances
built in our hardness reduction satisfy every promise"). -/
def pnPromiseSearch (n : ℕ) (β : ℚ) : SearchProblem where
  valid s := ∃ I : PNInstance n, I.Valid ∧ I.MetricPromise ∧ encPN I = s
  answer s t := ∃ I : PNInstance n, I.Valid ∧ encPN I = s ∧ PNAnswer I β t

end NadlerCLS


