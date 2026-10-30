-- Prove2me | Definitions.Def_FlexMargin_IsPartwiseSymm
-- name    : FlexMargin_IsPartwiseSymm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:35:45.332031+00:00
-- url     : https://prove2.me/theorems/d79f05c4-bf03-430f-89f9-4dbe67371102
-- title:
--   Definition 2.1: part-wise independently symmetric uncertainty set
-- statement:
--   An uncertainty set $U\subset\mathbb R^n_+$ is **part-wise independently symmetric** if
--
--   1. $U=U_1\times\dots\times U_T$, where $U_t=\{d_{s_t}: d\in U\}$, and
--   2. for every $d\in U$ and every $t$, permuting the coordinates of $d$ inside $s_t$ by any $\sigma^t\in\Omega(s_t)$ gives again a vector of $U$.
--
--   Such sets model demand whose fluctuations are symmetric within each margin category and independent across categories; Theorem 3 compares long chain designs over all of them.
--
--   **Formalization Note** The condition $U\subset\mathbb R^n_+$ is the first conjunct.
-- source:
--   Wang, Wang and Zhang, Robust Optimization Approach to Process Flexibility Designs with Contribution Margin Differentials, SSRN 3233721 (version of 2020-05-22), §2.3, Definition 2.1, p. 14

import Mathlib
import Definitions.Def_FlexMargin_IsPartwiseSymmCore

namespace FlexMargin

/-- **Definition 2.1: part-wise independently symmetric uncertainty set.**
Wang, Wang and Zhang, *Robust Optimization Approach to Process Flexibility Designs with
Contribution Margin Differentials*, SSRN 3233721 (version of 2020-05-22), §2.3, Definition 2.1, p. 14: "An uncertainty set U ⊂ R^n_+ is part-wise independently
symmetric if (1) U = U1 × ··· × UT, and (2) for any dst,−st ∈ U, we have dσt(st),−st ∈ U for any
permutation σt ∈ Ω(st) for each 1 ≤ t ≤ T."

`IsPartwiseSymm cat U`: every demand vector in `U` is nonnegative (`U ⊂ ℝ^n_+`), and `U` satisfies
clauses (1) and (2) (`FlexMargin.IsPartwiseSymmCore`) for the categories `s_t = {i | cat i = t}`.

**Formalization Note.** The nonnegativity is the page's `U ⊂ ℝ^n_+` (also the paper's standing
assumption on every uncertainty set, p. 13). -/
def IsPartwiseSymm {n T : ℕ} (cat : Fin n → Fin T) (U : Set (Fin n → ℝ)) : Prop :=
  (∀ d ∈ U, ∀ i, 0 ≤ d i) ∧ IsPartwiseSymmCore cat U

end FlexMargin


