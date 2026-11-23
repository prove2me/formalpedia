-- Prove2me | Definitions.Def_GroundTheory_PAdicHodge_UnramifiedClosure
-- name    : GroundTheory_PAdicHodge_UnramifiedClosure
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T18:24:44.296683+00:00
-- url     : https://prove2.me/theorems/0a04076f-2b2e-447a-a3b8-578900ad98cc
-- title:
--   Unramified Closure
-- statement:
--   Definitions and structural lemmas for Unramified Closure, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/UnramifiedClosure.lean

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_GaloisOnCp
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_UnramifiedClosureCountableNeighbourhoods
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.PAdicHodge
open Polynomial Filter Topology
variable (p : ℕ) [hp : Fact p.Prime]
def primeToPRoots : Set (PadicAlgCl p) := {x | ∃ m : ℕ, 0 < m ∧ m.Coprime p ∧ x ^ m = 1}
def unramifiedClosure : IntermediateField ℚ_[p] (PadicAlgCl p) :=
  IntermediateField.adjoin ℚ_[p] (primeToPRoots p)
def maxUnramified (K : IntermediateField ℚ_[p] (PadicAlgCl p)) :
    IntermediateField ℚ_[p] (PadicAlgCl p) :=
  K ⊓ unramifiedClosure p
variable {p}
section Approx
variable {F : Type*} [NormedField F] [IsUltrametricDist F]
end Approx
end GroundTheory.PAdicHodge


