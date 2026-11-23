-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SummableHeckeBalancedLatticeDoubleSum
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_SummableHeckeBalancedLatticeDoubleSum
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:50:12.214933+00:00
-- url     : https://prove2.me/theorems/5910d177-9392-4bd3-96c5-533c8f5619d9
-- title:
--   Summable Hecke Balanced Lattice Double Sum
-- statement:
--   Definitions and structural lemmas for Summable Hecke Balanced Lattice Double Sum, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SummableHeckeBalancedLatticeDoubleSum.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
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
namespace GlobalTheory.HeckeTwo.LatSum
variable {F : Type} [Field F] [NumberField F]
def absSum (x : F) : ℝ := ∑ τ : Emb F, |τ x|
variable [IsTotallyReal F]
end GlobalTheory.HeckeTwo.LatSum


