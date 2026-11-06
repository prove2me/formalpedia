-- Prove2me | Definitions.Def_FourierRankQLB_Vr
-- name    : FourierRankQLB_Vr
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:42:06.739797+00:00
-- url     : https://prove2.me/theorems/c9cfb206-81f2-4fd1-bce2-032d381c500c
-- title:
--   The amplitude space $V_r^{(n)}$
-- statement:
--   For an integer $r\ge0$,
--   $$
--   V_r^{(n)}=\overline{\operatorname{span}}^{L^2}\{\chi_\Xi:\operatorname{rank}\Xi\le r\}\subseteq L^2(O(n),\mu_n).
--   $$
--   It is the space of scalar amplitudes of Fourier rank at most $r$.
-- source:
--   Augustino et al., Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank, arXiv:2609.09035, Definition 3.1, Eq. (17), p.17

import Mathlib
import Definitions.Def_FourierRankQLB_chi
import Definitions.Def_FourierRankQLB_haarO

open MeasureTheory

namespace FourierRankQLB

/-- The amplitude space `V_r^{(n)}`: the `L²` closure of the span of `χ_Ξ`, `rank Ξ ≤ r`, Eq. (17).

Augustino et al., *Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank*, arXiv:2609.09035, Definition 3.1, Eq. (17), p. 17.

**Formalization Note.** The generators are the classes in `L²(O(n), μ_n)` of the functions `χ_Ξ`. -/
noncomputable def Vr (n r : ℕ) : Submodule ℂ (Lp ℂ 2 (haarO n)) :=
  (Submodule.span ℂ {f : Lp ℂ 2 (haarO n) |
    ∃ Ξ : Matrix (Fin n) (Fin n) ℝ, Ξ.rank ≤ r ∧ f =ᵐ[haarO n] chi Ξ}).topologicalClosure

end FourierRankQLB


