-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeEisensteinZeroFrequencyPartIsSmoothHolomorphic
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeEisensteinZeroFrequencyPartIsSmoothHolomorphic
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:18:20.02105+00:00
-- url     : https://prove2.me/theorems/a8335d7c-d6e6-4bb1-bb8c-2f30f4811851
-- title:
--   Hecke Eisenstein Zero Frequency Part Is Smooth Holomorphic
-- statement:
--   Definitions and structural lemmas for Hecke Eisenstein Zero Frequency Part Is Smooth Holomorphic, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckeEisensteinZeroFrequencyPartIsSmoothHolomorphic.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSmoothHolomorphicInSigmaFamilyMulLeft
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckePhiFourierConstantAtZeroDifferentiableOnStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckePhiFourierConstantAtZeroZeroStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UpperHalfPlaneProductProdImRpowContDiffOnStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ProdImIteratedWirtingerDerivWordDifferentiableOnStatement
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
namespace GlobalTheory.HeckeTwo
namespace BZeroGood
end BZeroGood
end GlobalTheory.HeckeTwo


