-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_PolarConjTranspose
-- name    : Development_AbelianVarietyTheory_Proofs_HeightProofs_PolarConjTranspose
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T22:04:57.067089+00:00
-- url     : https://prove2.me/theorems/0ab405b9-d4e4-48c8-a703-c8d188fb0944
-- title:
--   Polar Conj Transpose
-- statement:
--   Definitions and structural lemmas for Polar Conj Transpose, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/PolarConjTranspose.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsLieDataCircle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_RightDerivativeAlongLieSmoothAndLinearStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_RightDerivativeAlongLieCommutatorEqBracketStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_CommutatorGlGeneratorTensorWordMapMatrixUnitsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_MemAdjoinGlActionOfCommuteTensorPermStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_BicommutantTensorFactorPermMemSpanStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_CommutantLiftModStableSelfAdjointStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_PermutationWordGelfandPolynomialModShorterStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_CommuteGelfandInvariantMatrixUnitsOfGlRelStatement
import Theorems.Thm_GlobalTheory_T_rightDerivativeAlongLie_smooth_and_linear

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped ContDiff Topology
open Matrix
namespace GlobalTheory.SmoothForms
section Centre
variable {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} {E : Fin n → Fin n → A}
end Centre
section Operators
variable {𝔸 L G : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [FiniteDimensional ℝ 𝔸] [NormedAddCommGroup L]
  [NormedSpace ℝ L] [Group G] {σ : 𝔸 →ₗ[ℝ] 𝔸} {j : L →ₗ[ℝ] 𝔸} {s : 𝔸 → G}
def smSub (e : L → G) : Submodule ℂ (G → ℂ) where
  carrier := {φ | Sm e φ}
  zero_mem' := fun _ => contDiff_const
  add_mem' := fun h h' g => (h g).add (h' g)
  smul_mem' := fun c _ h g => (h g).const_smul c
theorem Sm.differentiableAt {e : L → G} {φ : G → ℂ} (h : Sm e φ) (g : G) (X : L) :
    DifferentiableAt ℝ (fun t : ℝ => φ (g * e (t • X))) 0 :=
  (((h g).comp (contDiff_id.smul contDiff_const : ContDiff ℝ ∞ fun t : ℝ => t • X)).differentiable
    (by simp)).differentiableAt
def derOp (H : IsLieData σ j s) (hl : HasLog σ j) (X : L) : Module.End ℂ (smSub (expMap j s)) where
  toFun φ := ⟨Der (expMap j s) X φ.1, (GlobalTheory.T.rightDerivativeAlongLie_smooth_and_linear 𝔸 L G σ j s H hl φ.1 φ.2).1 X⟩
  map_add' φ ψ := Subtype.ext (funext fun g => deriv_add (Sm.differentiableAt φ.2 g X) (Sm.differentiableAt ψ.2 g X))
  map_smul' c φ := Subtype.ext (funext fun g => deriv_const_smul c (Sm.differentiableAt φ.2 g X))
end Operators
end GlobalTheory.SmoothForms
end


