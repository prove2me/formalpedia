-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WeilConditionProductSplitting
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WeilConditionProductSplitting
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:04:23.832028+00:00
-- url     : https://prove2.me/theorems/16d01255-c00e-4443-b502-21c0a9f52343
-- title:
--   Weil Condition Product Splitting
-- statement:
--   Definitions and structural lemmas for Weil Condition Product Splitting, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/WeilConditionProductSplitting.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsSplitting
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TensorRepApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedValuationParitySignCharacterKernelNormStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NonemptyMeasAndReps
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocallyConstantTestRepresentationTensorProductStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FourBProdIteratedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AbsKMulOfEtaleSplittingStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
namespace GlobalTheory.JR.WeilProd
def transRep {G H X Y : Type} (ρ : G → H) (e : X ≃ Y) (W : H → (Y → ℂ) → Y → ℂ) : G → (X → ℂ) → X → ℂ :=
  fun g f x => W (ρ g) (f ∘ e.symm) (e x)
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
section rel
variable [Unram F E] (A A₁ A₂ : Et F E) (eK : A.K ≃ₐ[F] A₁.K × A₂.K) (eL : A.L ≃ₐ[F] A₁.L × A₂.L)
  (hS : IsSplitting A A₁ A₂ eK eL) (ψ : AddChar F ℂ) (x : A.K)
  (W₁ : SpecialLinearGroup (Fin 2) A₁.K → (A₁.L → ℂ) → A₁.L → ℂ)
  (W₂ : SpecialLinearGroup (Fin 2) A₂.K → (A₂.L → ℂ) → A₂.L → ℂ) (γ₁ γ₂ : ℂ) (μ₁ : Measure A₁.L) (μ₂ : Measure A₂.L)
  (hW₁ : A₁.IsWeil ψ (eK x).1 A₁.etaK μ₁ γ₁ W₁) (hW₂ : A₂.IsWeil ψ (eK x).2 A₂.etaK μ₂ γ₂ W₂)
  (f : A₁.L × A₂.L → ℂ) (hf1 : ∀ u, IsTest (fun v => f (u, v)))
  (hf2 : ∀ h y, IsTest (fun u => W₂ h (fun v => f (u, v)) y))
include hS hW₁ hW₂ hf1 hf2
end rel
end GlobalTheory.JR.WeilProd


