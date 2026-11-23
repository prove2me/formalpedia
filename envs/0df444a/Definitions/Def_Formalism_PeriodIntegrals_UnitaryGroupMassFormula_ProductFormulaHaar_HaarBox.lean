-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_HaarBox
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_HaarBox
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:20:04.408204+00:00
-- url     : https://prove2.me/theorems/55afafb0-faf9-4135-bffd-90d4cea69488
-- title:
--   Haar Box
-- statement:
--   Definitions and structural lemmas for Haar Box, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProductFormulaHaar/HaarBox.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
set_option linter.style.haveILetI false
open MeasureTheory Measure ValuativeRel Topology Filter Module
open scoped NNReal ENNReal Pointwise
namespace PI.ProdFormulaE.HaarBox
section Field
variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {K}
end Field
variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {E : Type} [AddCommGroup E] [Module K E] [TopologicalSpace E] [IsModuleTopology K E]
variable {ι : Type} [Fintype ι] [DecidableEq ι]
def box (b : Basis ι K E) (γ : ι → ValueGroupWithZero K) : Set E :=
  {x | ∀ i, valuation K (b.repr x i) ≤ γ i}
theorem continuous_equivFun_symm (b : Basis ι K E) : Continuous b.equivFun.symm := by
  haveI := IsModuleTopology.toContinuousAdd K E
  exact IsModuleTopology.continuous_of_linearMap (R := K) b.equivFun.symm.toLinearMap
def homeo (b : Basis ι K E) : E ≃ₜ (ι → K) where
  toEquiv := b.equivFun.toEquiv
  continuous_toFun := IsModuleTopology.continuous_of_linearMap (R := K) b.equivFun.toLinearMap
  continuous_invFun := continuous_equivFun_symm b
def toCLE (T : E ≃ₗ[K] E) : E ≃L[K] E :=
  haveI : ContinuousAdd E := IsModuleTopology.toContinuousAdd K E
  { T with
    continuous_toFun := IsModuleTopology.continuous_of_linearMap (R := K) T.toLinearMap
    continuous_invFun := IsModuleTopology.continuous_of_linearMap (R := K) T.symm.toLinearMap }
variable [MeasurableSpace E] [BorelSpace E]
end PI.ProdFormulaE.HaarBox


