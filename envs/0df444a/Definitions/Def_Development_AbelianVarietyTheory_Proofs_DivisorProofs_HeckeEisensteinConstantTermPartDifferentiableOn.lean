-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeEisensteinConstantTermPartDifferentiableOn
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeEisensteinConstantTermPartDifferentiableOn
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:49:56.678949+00:00
-- url     : https://prove2.me/theorems/a02ff9e7-f974-44e1-a0a2-6ebb3d7e3f6c
-- title:
--   Hecke Eisenstein Constant Term Part Differentiable On
-- statement:
--   Definitions and structural lemmas for Hecke Eisenstein Constant Term Part Differentiable On, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckeEisensteinConstantTermPartDifferentiableOn.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_ReciprocityTheory_Chebotarev_EulerSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
noncomputable section
namespace GlobalTheory.HeckeTwo.APart
variable {F : Type} [Field F] [NumberField F]
variable [IsTotallyReal F]
end GlobalTheory.HeckeTwo.APart


