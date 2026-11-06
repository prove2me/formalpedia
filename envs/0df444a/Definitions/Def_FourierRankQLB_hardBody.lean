-- Prove2me | Definitions.Def_FourierRankQLB_hardBody
-- name    : FourierRankQLB_hardBody
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:44:15.035291+00:00
-- url     : https://prove2.me/theorems/7e3c9290-3cdd-4fd7-a9d3-5a0d7f9fe4cc
-- title:
--   The hard ellipsoid $K_{s,Q}$
-- statement:
--   For a scale $s>0$ and $Q\in O(d_n)$, the ellipsoid
--   $$
--   K_{s,Q}=\{y\in\mathbb R^n: y^T\overline A_{n,Q}\,y\le s^2\}.
--   $$
--   These are the convex bodies of the lower bound. Membership of a point is a threshold on $q^TQq$, and the optimal value of a linear objective reveals $v^TA_Q^{-1}v$.
--
--   **Formalization Note** The inequality is non-strict, so boundary points are members. The module also records that $K_{s,Q}$ is a Borel set.
-- source:
--   Augustino et al., Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank, arXiv:2609.09035, Eq. (38), p.25

import Mathlib
import Definitions.Def_FourierRankQLB_Abar
import Definitions.Def_FourierRankQLB_Ambient

open Matrix

namespace FourierRankQLB

/-- The hard ellipsoid `K_{s,Q} = {y ∈ ℝⁿ : yᵀ Ā_{n,Q} y ≤ s²}` of Eq. (38).

Augustino et al., *Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank*, arXiv:2609.09035, Eq. (38), p. 25.

**Formalization Note.** The inequality is non-strict, so boundary points are members, as Definition
2.2 requires. -/
def hardBody {n : ℕ} (s : ℝ) (Q : Od (dn n)) : Set (Ambient n) :=
  {y | y.ofLp ⬝ᵥ (Abar Q *ᵥ y.ofLp) ≤ s ^ 2}

/-- `K_{s,Q}` is closed, hence Borel. -/
theorem measurableSet_hardBody {n : ℕ} (s : ℝ) (Q : Od (dn n)) :
    MeasurableSet (hardBody s Q) := by
  have hc : Continuous fun y : Ambient n => y.ofLp ⬝ᵥ (Abar Q *ᵥ y.ofLp) := by
    have h0 : Continuous fun y : Ambient n => y.ofLp := PiLp.continuous_ofLp 2 _
    exact h0.dotProduct (continuous_const.matrix_mulVec h0)
  exact (isClosed_le hc continuous_const).measurableSet

end FourierRankQLB


