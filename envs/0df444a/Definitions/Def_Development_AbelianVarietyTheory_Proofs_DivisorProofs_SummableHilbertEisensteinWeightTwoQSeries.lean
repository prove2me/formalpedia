-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SummableHilbertEisensteinWeightTwoQSeries
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_SummableHilbertEisensteinWeightTwoQSeries
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:59:47.209902+00:00
-- url     : https://prove2.me/theorems/4843ba56-0b5a-4040-b109-60b83e829a97
-- title:
--   Summable Hilbert Eisenstein Weight Two QSeries
-- statement:
--   Definitions and structural lemmas for Summable Hilbert Eisenstein Weight Two QSeries, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SummableHilbertEisensteinWeightTwoQSeries.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AbsNormEqProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeEisensteinConstantTermPartDifferentiableOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DiscreteTopologyFractionalIdealRealLatticeImage
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex
open scoped nonZeroDivisors
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
noncomputable section
namespace GlobalTheory.HeckeTwoSum
variable {F : Type} [Field F] [NumberField F]
end GlobalTheory.HeckeTwoSum
namespace GlobalTheory.HeckeTwoSum
open GlobalTheory.LipschitzTR
variable {F : Type} [Field F] [NumberField F]
end GlobalTheory.HeckeTwoSum


