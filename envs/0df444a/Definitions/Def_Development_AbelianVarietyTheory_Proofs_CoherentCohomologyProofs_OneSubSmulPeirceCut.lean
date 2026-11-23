-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_OneSubSmulPeirceCut
-- name    : Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_OneSubSmulPeirceCut
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T08:24:23.140439+00:00
-- url     : https://prove2.me/theorems/c59b56f6-ae79-4cbe-8577-b43fb5c84482
-- title:
--   One Sub Smul Peirce Cut
-- statement:
--   Definitions and structural lemmas for One Sub Smul Peirce Cut, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/OneSubSmulPeirceCut.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory.PeirceDecompositionCut
variable {R : Type*} [CommRing R] (A : Type*) [Ring A] [Algebra R A]
def peirceCut (e : R) (he : IsIdempotentElem e) : A →* A where
  toFun x := e • x + (1 - e) • (1 : A)
  map_one' := by rw [← add_smul, add_sub_cancel, one_smul]
  map_mul' x y := by
    have h1 : e * e = e := he
    have h2 : e * (1 - e) = 0 := by rw [mul_sub, mul_one, h1, sub_self]
    have h3 : (1 - e) * e = 0 := by rw [mul_comm, h2]
    have h4 : (1 - e) * (1 - e) = 1 - e := he.one_sub
    simp only [add_mul, mul_add, smul_mul_smul_comm, h1, h2, h3, h4, zero_smul, add_zero,
      zero_add, mul_one]
variable {A}
end GlobalTheory.PeirceDecompositionCut


