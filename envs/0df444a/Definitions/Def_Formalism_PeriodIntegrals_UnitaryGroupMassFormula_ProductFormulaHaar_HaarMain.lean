-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_HaarMain
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_HaarMain
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:28:48.934031+00:00
-- url     : https://prove2.me/theorems/1c52ffc6-18ec-433b-8662-43d008435f7a
-- title:
--   Haar Main
-- statement:
--   Definitions and structural lemmas for Haar Main, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProductFormulaHaar/HaarMain.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_HaarBox
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_NormMod
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_ResCharIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Measure ValuativeRel Topology Module
open scoped NNReal ENNReal Pointwise
namespace PI.ProdFormulaE.HaarBox
variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {E : Type} [AddCommGroup E] [Module K E] [TopologicalSpace E] [IsModuleTopology K E]
variable {ι : Type} [Fintype ι] [DecidableEq ι]
def equivOfDet (b : Basis ι K E) (A : Matrix ι ι K) (hA : A.det ≠ 0) : E ≃ₗ[K] E :=
  LinearEquiv.ofIsUnitDet (f := Matrix.toLin b b A) (v := b) (v' := b)
    (by rw [LinearMap.toMatrix_toLin]; exact hA.isUnit)
variable [MeasurableSpace E] [BorelSpace E]
def ScaleBox (b : Basis ι K E) (μ : Measure E) : Prop :=
  ∀ (i : ι) (a : K) (ha : a ≠ 0),
    μ (Matrix.toLin b b (Matrix.diagonal (Function.update 1 i a)) '' box b 1) =
      (distribHaarChar K (Units.mk0 a ha) : ℝ≥0∞) * μ (box b 1)
def TransvBox (b : Basis ι K E) : Prop :=
  ∀ t : Matrix.TransvectionStruct ι K, ∃ γ : ι → ValueGroupWithZero K, (∀ i, γ i ≠ 0) ∧
    Matrix.toLin b b t.toMatrix '' box b γ = box b γ
end PI.ProdFormulaE.HaarBox
namespace PI.ProdFormulaE.HaarAlgP
open HaarBox
end PI.ProdFormulaE.HaarAlgP


