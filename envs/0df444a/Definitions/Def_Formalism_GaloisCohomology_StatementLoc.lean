-- Prove2me | Definitions.Def_Formalism_GaloisCohomology_StatementLoc
-- name    : Formalism_GaloisCohomology_StatementLoc
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:05:24.860083+00:00
-- url     : https://prove2.me/theorems/1181e758-cffb-4aa3-902b-f859d5ef2b0b
-- title:
--   Statement Loc
-- statement:
--   Definitions and structural lemmas for Statement Loc, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaloisCohomology/StatementLoc.lean

import Definitions.Def_ReciprocityTheory_GaloisValuations_ContinuousConstSMulQuotient
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Representation ReciprocityTheory.Gal
namespace Formalism.GaloisCohomology
variable (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l))
abbrev GK : Type := PadicAlgCl l ≃ₐ[K] PadicAlgCl l
def inertiaSet : Set (GK l K) := {σ | ∀ x : PadicAlgCl l, ‖x‖ ≤ 1 → ‖σ x - x‖ < 1}
def inertiaK : Subgroup (GK l K) := Subgroup.closure (inertiaSet l K)
variable {l K}
def unrK {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M] [TopologicalSpace M]
    [IsTopologicalAddGroup M] [ContinuousConstSMul R M] (rho : Representation R (GK l K) M) :
    Submodule R (H1 rho) :=
  H1ur rho (inertiaK l K)
def InertiaIsSet : Prop := ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)),
  FiniteDimensional ℚ_[l] K →
    ((inertiaK l K : Set (GK l K)) = inertiaSet l K) ∧ (inertiaK l K).Normal ∧
      IsClosed (inertiaK l K : Set (GK l K))
def InertiaProper : Prop := ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)),
  FiniteDimensional ℚ_[l] K → inertiaK l K ≠ ⊤
end Formalism.GaloisCohomology


