-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteGaussianExtensionUnitsQuotUnits
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteGaussianExtensionUnitsQuotUnits
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T11:38:12.27239+00:00
-- url     : https://prove2.me/theorems/b634174a-5cf4-4d57-ba85-02f221b1cf57
-- title:
--   Finite Gaussian Extension Units Quot Units
-- statement:
--   Definitions and structural lemmas for Finite Gaussian Extension Units Quot Units, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiniteGaussianExtensionUnitsQuotUnits.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeEisensteinConstantTermPartDifferentiableOn
import Definitions.Def_ReciprocityTheory_Chebotarev_EulerSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IrreducibleXSqAddOne
import Theorems.Thm_GlobalTheory_GaussExt_ii_sq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex Polynomial
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
noncomputable section
namespace GlobalTheory.GaussExt.UnitIdx
variable (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F]
theorem aeval_neg_ii : aeval (-ii F) (X ^ 2 + 1 : F[X]) = 0 := by
  simp only [map_add, map_pow, aeval_X, map_one, neg_sq, ii_sq F]; ring
def conj : Ext F →ₐ[F] Ext F := AdjoinRoot.liftAlgHom (X ^ 2 + 1 : F[X]) (Algebra.ofId F (Ext F)) (-ii F)
  (by have := aeval_neg_ii F; rwa [aeval_def] at this)
end GlobalTheory.GaussExt.UnitIdx


