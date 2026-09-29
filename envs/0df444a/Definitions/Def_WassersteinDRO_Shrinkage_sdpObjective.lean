-- Prove2me | Definitions.Def_WassersteinDRO_Shrinkage_sdpObjective
-- name    : WassersteinDRO_Shrinkage_sdpObjective
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T02:50:38.276651+00:00
-- url     : https://prove2.me/theorems/18db1926-403b-4fc4-855b-30cd058c88e3
-- title:
--   Objective of the nonlinear convex SDP (36)
-- statement:
--   The objective of SDP (36) is $f(S) = \mathrm{Tr}[S_{xx} - S_{xy}S_{yy}^{-1}S_{yx}]$, the trace
--   of the Schur complement.
-- source:
--   Kuhn, Mohajerin Esfahani, Nguyen & Shafieezadeh-Abadeh, Wasserstein Distributionally Robust Optimization, INFORMS TutORials 2019, eq. (36), p. 29

import Mathlib

namespace WassersteinDRO.Shrinkage

/-- The objective of the nonlinear convex SDP (36), Kuhn et al. 2019, p. 29:
`f(S) = Tr[S_xx - S_xy S_yy⁻¹ S_yx]`, the Schur complement's trace. Uses the ordinary matrix
inverse (`Matrix.inv`, junk `0` matrix when `S_yy` is singular), matching the paper's literal
notation; see `MODERATION_NOTES.md` for the convention. -/
noncomputable def sdpObjective {mx my : ℕ}
    (S : Matrix (Fin mx ⊕ Fin my) (Fin mx ⊕ Fin my) ℝ) : ℝ :=
  (S.toBlocks₁₁ - S.toBlocks₁₂ * S.toBlocks₂₂⁻¹ * S.toBlocks₂₁).trace

end WassersteinDRO.Shrinkage


