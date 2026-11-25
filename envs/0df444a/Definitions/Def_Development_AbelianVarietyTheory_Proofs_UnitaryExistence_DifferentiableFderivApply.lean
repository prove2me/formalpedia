-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DifferentiableFderivApply
-- name    : Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DifferentiableFderivApply
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T00:37:41.400892+00:00
-- url     : https://prove2.me/theorems/de395092-b36f-45a9-be5c-175232b535de
-- title:
--   Differentiable Fderiv Apply
-- statement:
--   Definitions and structural lemmas for Differentiable Fderiv Apply, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/DifferentiableFderivApply.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsImEqLattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology Metric
open scoped ComplexOrder
namespace GlobalTheory.ThetaGauss
variable {g : ℕ}
noncomputable def transl {K : Type} [TopologicalSpace K] {f : (Fin g → ℂ) → ℂ}
    (hf : Differentiable ℂ f) (γ : C(K, Fin g → ℂ)) (z : Fin g → ℂ) : C(K, ℂ) :=
  ⟨fun k => f (z + γ k), hf.continuous.comp (continuous_const.add γ.continuous)⟩
end GlobalTheory.ThetaGauss


