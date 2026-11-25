-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_FiniteLengthSubquotient
-- name    : GroundTheory_AutomorphicForms_FiniteLengthSubquotient
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T11:47:38.166379+00:00
-- url     : https://prove2.me/theorems/47e27478-a229-4716-8ae0-0a6d95cdda7f
-- title:
--   Finite Length Subquotient
-- statement:
--   Definitions and structural lemmas for Finite Length Subquotient, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/FiniteLengthSubquotient.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteLengthLattice
import Definitions.Def_GroundTheory_AutomorphicForms_JacquetAdmissible
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
namespace GroundTheory.Automorphic
open Function Parabolic
universe u
section Subquotient
variable {G : Type*} [Group G] {V W U : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
  [Module ℂ W] [AddCommGroup U] [Module ℂ U]
def IsSubquotient (π : Representation ℂ G W) (ρ : Representation ℂ G V) : Prop :=
  ∃ C : Subrepresentation ρ, ∃ p : Representation.IntertwiningMap C.toRepresentation π,
    Surjective p
variable {π : Representation ℂ G W} {ρ : Representation ℂ G V} {θ : Representation ℂ G U}
def subrepInclusion (C : Subrepresentation ρ) :
    Representation.IntertwiningMap C.toRepresentation ρ where
  toLinearMap := C.toSubmodule.subtype
  isIntertwining' _ := rfl
end Subquotient
section Coinvariants
variable {G : Type*} [Group G] [TopologicalSpace G] {V W : Type*} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W] {ρ : Representation ℂ G V}
variable [IsTopologicalGroup G]
end Coinvariants
section Criterion
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
end Criterion
end GroundTheory.Automorphic


