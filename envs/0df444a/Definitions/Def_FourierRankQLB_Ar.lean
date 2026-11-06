-- Prove2me | Definitions.Def_FourierRankQLB_Ar
-- name    : FourierRankQLB_Ar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:42:07.660197+00:00
-- url     : https://prove2.me/theorems/ec06f283-2d6b-4feb-a995-fb26b4c473d0
-- title:
--   The probability space $A_r^{(n)}$
-- statement:
--   For an integer $r\ge0$,
--   $$
--   A_r^{(n)}=\overline{\operatorname{span}}^{L^1}\{\chi_\Xi:\operatorname{rank}\Xi\le r\}\subseteq L^1(O(n),\mu_n).
--   $$
--   It is the space used for scalar outcome probabilities, for which $L^1$ convergence is sufficient.
-- source:
--   Augustino et al., Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank, arXiv:2609.09035, Definition 3.1, Eq. (18), p.17

import Mathlib
import Definitions.Def_FourierRankQLB_chi
import Definitions.Def_FourierRankQLB_haarO

open MeasureTheory

namespace FourierRankQLB

/-- The probability space `A_r^{(n)}`: the `L¹` closure of the span of `χ_Ξ`, `rank Ξ ≤ r`, Eq. (18).

Augustino et al., *Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank*, arXiv:2609.09035, Definition 3.1, Eq. (18), p. 17.

**Formalization Note.** The generators are the classes in `L¹(O(n), μ_n)` of the functions `χ_Ξ`. -/
noncomputable def Ar (n r : ℕ) : Submodule ℂ (Lp ℂ 1 (haarO n)) :=
  (Submodule.span ℂ {f : Lp ℂ 1 (haarO n) |
    ∃ Ξ : Matrix (Fin n) (Fin n) ℝ, Ξ.rank ≤ r ∧ f =ᵐ[haarO n] chi Ξ}).topologicalClosure

end FourierRankQLB


