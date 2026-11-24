-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AlgebraNormRatGaussianExtensionOfPair
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_AlgebraNormRatGaussianExtensionOfPair
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T11:27:36.317009+00:00
-- url     : https://prove2.me/theorems/28ae2403-2a77-431b-b2d6-0b5e7c70b7b7
-- title:
--   Algebra Norm Rat Gaussian Extension Of Pair
-- statement:
--   Definitions and structural lemmas for Algebra Norm Rat Gaussian Extension Of Pair, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AlgebraNormRatGaussianExtensionOfPair.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeEisensteinConstantTermPartDifferentiableOn
import Definitions.Def_ReciprocityTheory_Chebotarev_EulerSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IrreducibleXSqAddOne
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
namespace GlobalTheory.GaussExt
variable (F : Type) [Field F] [NumberField F] [IsTotallyReal F]
theorem X_sq_add_one_ne_zero : (X ^ 2 + 1 : F[X]) ≠ 0 := Monic.ne_zero (by monicity!)
theorem natDegree_X_sq_add_one : (X ^ 2 + 1 : F[X]).natDegree = 2 := by compute_degree!
def basisOneI : Module.Basis (Fin 2) F (Ext F) :=
  (AdjoinRoot.powerBasis (X_sq_add_one_ne_zero F)).basis.reindex
    (finCongr (by rw [AdjoinRoot.powerBasis_dim, natDegree_X_sq_add_one]))
end GlobalTheory.GaussExt


