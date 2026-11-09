-- Prove2me | Definitions.Def_NadlerCLS_pnSearch
-- name    : NadlerCLS_pnSearch
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:03:36.079189+00:00
-- url     : https://prove2.me/theorems/8bbe2960-1477-4c7b-98d0-04f5866877e2
-- title:
--   The search problem $\beta$-Projected-Nadler (numerical promise only)
-- statement:
--   For a dimension $n$ and a fixed rational exponent $\beta$, the search problem $\beta$-Projected-Nadler on $[0,1]^n$ has as valid instances the codes of instances in the input format (well-behaved circuits of the right arities, positive parameters, $k\in(0,1)$, $0<\varepsilon_2<\varepsilon_1(1-k)$), and as answers the valid outputs (N1)–(N4).
--
--   The metric and completeness promise is not imposed: Remark C.7 states that the membership reduction and the totality hold for arbitrary well-behaved circuits under the numerical condition and the enforced ranges.
--
--   **Formalization Note** The exponent $\beta$ is a parameter of the problem, not part of the input (p.31). Search problems are the public `TetrisHard.Rows.SearchProblem`.
-- source:
--   Xiong–Vlatakis-Gkaragkounis, On the Complexity of Finding Fixed Points for Set-Valued Contractions, arXiv:2609.14101 (held version of 2026-11-03, sha256 1fcc5a027ffe65205e4ef9a9ef7730f6f07fe3f7006447cac39a7562e36dc485), Definition 1, p.9; Remark 3.1, p.9; Remark C.7, p.38

import Mathlib
import Definitions.Def_NetworkEquilibriumCLS_LinearNash_Encoding
import Definitions.Def_NadlerCLS_PNInstance
import Definitions.Def_NadlerCLS_PNAnswer

set_option autoImplicit false

namespace NadlerCLS

open NetworkEquilibriumCLS.LinearNash

/-- The search problem **β-Projected-Nadler** on `[0, 1]ⁿ`, with only the numerical promise
(Xiong–Vlatakis-Gkaragkounis, *On the Complexity of Finding Fixed Points for Set-Valued
Contractions*, arXiv:2609.14101, held version of 2026-11-03, sha256 1fcc5a02…6dc485, Definition 1,
p.9, and Remark 3.1, p.9). A valid instance is the code of a `PNInstance` satisfying the input
format `PNInstance.Valid` (well-behaved circuits, positive parameters, `k ∈ (0, 1)`,
`0 < ε₂ < ε₁(1 − k)`); an answer is a valid output (N1)–(N4) (`PNAnswer`).

**Formalization Note** The metric and completeness promise is **not** part of this problem
(Remark C.7, p.38: "the membership reduction and the totality of β-PROJECTED-NADLER hold for
arbitrary well-behaved circuits"); `pnPromiseSearch` adds it. The exponent `β` is fixed, not part
of the input (p.31). The search problem is the public `TetrisHard.Rows.SearchProblem`. -/
def pnSearch (n : ℕ) (β : ℚ) : SearchProblem where
  valid s := ∃ I : PNInstance n, I.Valid ∧ encPN I = s
  answer s t := ∃ I : PNInstance n, I.Valid ∧ encPN I = s ∧ PNAnswer I β t

end NadlerCLS


