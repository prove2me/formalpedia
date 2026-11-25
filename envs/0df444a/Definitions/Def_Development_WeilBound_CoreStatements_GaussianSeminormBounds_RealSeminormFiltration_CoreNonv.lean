-- Prove2me | Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreNonv
-- name    : Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreNonv
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T12:38:16.809179+00:00
-- url     : https://prove2.me/theorems/551ef9b8-e38a-40b4-91ea-23d4eaee645e
-- title:
--   Core Nonv
-- statement:
--   Definitions and structural lemmas for Core Nonv, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/GaussianSeminormBounds/RealSeminormFiltration/CoreNonv.lean

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreGraph
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreDelta
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreProj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory.ThetaSummability.Real ReciprocityTheory.ChartRestriction.G.ThK.Real FockH1Action MvPolynomial Matrix
open scoped InnerProductSpace
namespace PositivityTheory.KReal
section Dual
variable {p q : ℕ}
def thetaM (p q : ℕ) : Mat p q →ₗ[ℂ] Mat p q where
  toFun Z := Matrix.of fun a b => epsB a b * Z b a
  map_add' Z W := by
    ext a b
    simp [mul_add]
  map_smul' t Z := by
    ext a b
    simp [mul_left_comm]
def dualAct {B : Type} [AddCommGroup B] [Module ℂ B] (ρ : Mat p q →ₗ[ℂ] Module.End ℂ B) (c : ℂ) :
    Mat p q →ₗ[ℂ] Module.End ℂ B :=
  (c • Matrix.traceLinearMap (Ix p q) ℂ ℂ).smulRight 1 - ρ ∘ₗ thetaM p q
end Dual
section Conj
variable {p q r s : ℕ}
def cjP (P : Pol p q r s) : Pol p q r s := MvPolynomial.map (starRingEnd ℂ) P
end Conj
end PositivityTheory.KReal
end


