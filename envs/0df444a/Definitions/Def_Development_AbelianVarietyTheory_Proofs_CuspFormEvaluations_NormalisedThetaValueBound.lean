-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_NormalisedThetaValueBound
-- name    : Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_NormalisedThetaValueBound
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T17:27:02.97131+00:00
-- url     : https://prove2.me/theorems/6640f904-5e96-54dd-9d2d-758b6e8bc388
-- title:
--   Normalised Theta Value Bound
-- statement:
--   Definitions and structural lemmas for Normalised Theta Value Bound, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/NormalisedThetaValueBound.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_L2NormFundamentalDomain
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_FlatMemLatIffStdLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_TraceHermNondegenerate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_SupLeL2PrincipalTorus
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_PointwiseNormSqPullbackTensorEqProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ContinuousThetaSectionPointwiseNormSq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsBasisSpanEqOfCommensurable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_LeMulNormFlatOfSelfDual
import Theorems.Thm_GlobalTheory_TensorLat_mem_tensorLat_stdLat
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_actE_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_dim
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.I2.actE_apply


set_option autoImplicit false
namespace GlobalTheory.TensorLat
open NumberField Complex ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.GeometryOfNumbersTheory (stdLat)
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
end GlobalTheory.TensorLat
namespace GlobalTheory
open NumberField Complex ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.FD TensorLat
example {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (T : PT E) :
    (∀ y ∈ ({0} : Finset (Fin n → Vsp T.dim)), y ∈ tensorLat T (ReciprocityTheory.GeometryOfNumbersTheory.stdLat E n)) ∧
      ∀ y ∈ tensorLat T (ReciprocityTheory.GeometryOfNumbersTheory.stdLat E n),
        ∃! r, r ∈ ({0} : Finset (Fin n → Vsp T.dim)) ∧ ∀ k, y k - r k ∈ T.L := by
  refine ⟨fun y hy => by rw [Finset.mem_singleton.1 hy]; exact Submodule.zero_mem _,
    fun y hy => ⟨0, ⟨Finset.mem_singleton_self _, fun k => ?_⟩,
      fun r hr => Finset.mem_singleton.1 hr.1⟩⟩
  simpa using mem_tensorLat_stdLat.1 hy k
end GlobalTheory


