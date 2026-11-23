-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsBasisAdaptedLatticeSubspace
-- name    : Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsBasisAdaptedLatticeSubspace
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:37:00.075811+00:00
-- url     : https://prove2.me/theorems/27c5bdd5-990a-47e3-b8b2-f599ed797cac
-- title:
--   Exists Basis Adapted Lattice Subspace
-- statement:
--   Definitions and structural lemmas for Exists Basis Adapted Lattice Subspace, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsBasisAdaptedLatticeSubspace.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory.TateSeq
variable {M : Type} [AddCommGroup M]
def tors (M : Type) [AddCommGroup M] (N : ℕ) : AddSubgroup M where
  carrier := {x | N • x = 0}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    rw [smul_add, ha, hb, add_zero]
  zero_mem' := by simp
  neg_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at *
    rw [smul_neg, ha, neg_zero]
end GlobalTheory.TateSeq
namespace GlobalTheory
open TateSeq
end GlobalTheory


