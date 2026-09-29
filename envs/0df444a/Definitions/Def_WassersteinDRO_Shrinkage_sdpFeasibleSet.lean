-- Prove2me | Definitions.Def_WassersteinDRO_Shrinkage_sdpFeasibleSet
-- name    : WassersteinDRO_Shrinkage_sdpFeasibleSet
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T02:50:22.670132+00:00
-- url     : https://prove2.me/theorems/f690134a-aef7-40e3-8803-e32ea50763e6
-- title:
--   Feasible set of the nonlinear convex SDP (36)
-- statement:
--   The feasible set of SDP (36) is the set of symmetric block matrices $S=\begin{pmatrix}
--   S_{xx}&S_{xy}\\S_{yx}&S_{yy}\end{pmatrix}$ with $S\succeq 0$, $S_{xx}\succeq 0$,
--   $S_{yy}\succeq 0$ (the block relation $S_{xy}=S_{yx}^\top$ following automatically from $S$
--   symmetric), $\mathrm{Tr}[S+\hat\Sigma-2(\hat\Sigma^{1/2}S\hat\Sigma^{1/2})^{1/2}]\le
--   \varepsilon^2$, and $S \succeq \lambda_{\min}(\hat\Sigma)\cdot I$.
-- source:
--   Kuhn, Mohajerin Esfahani, Nguyen & Shafieezadeh-Abadeh, Wasserstein Distributionally Robust Optimization, INFORMS TutORials 2019, eq. (36), p. 29

import Mathlib
import Definitions.Def_WassersteinDRO_Shrinkage_psdSqrt

namespace WassersteinDRO.Shrinkage

/-- The feasible set of the nonlinear convex SDP (36), Kuhn et al. 2019, p. 29: `S ⪰ 0`,
`S_xx ⪰ 0`, `S_yy ⪰ 0` (`S_xx = S.toBlocks₁₁`, `S_yy = S.toBlocks₂₂`; `S_xy = S.toBlocks₁₂ =
S.toBlocks₂₁ᵀ` holds automatically once `S` is symmetric, so is not a separate hypothesis —
see `MODERATION_NOTES.md`), the trace/matrix-square-root constraint
`Tr[S+Σ̂-2(Σ̂^{1/2}SΣ̂^{1/2})^{1/2}] ≤ ε²`, and the Loewner lower bound `S ⪰ λmin(Σ̂)·I`. -/
def sdpFeasibleSet {mx my : ℕ} (ε : ℝ)
    (SigmaHat : Matrix (Fin mx ⊕ Fin my) (Fin mx ⊕ Fin my) ℝ) (lambdaMin : ℝ) :
    Set (Matrix (Fin mx ⊕ Fin my) (Fin mx ⊕ Fin my) ℝ) :=
  {S | S.PosSemidef ∧ S.toBlocks₁₁.PosSemidef ∧ S.toBlocks₂₂.PosSemidef ∧
    (S + SigmaHat - (2 : ℝ) • psdSqrt (psdSqrt SigmaHat * S * psdSqrt SigmaHat)).trace ≤ ε ^ 2 ∧
    (S - lambdaMin • (1 : Matrix (Fin mx ⊕ Fin my) (Fin mx ⊕ Fin my) ℝ)).PosSemidef}

end WassersteinDRO.Shrinkage


