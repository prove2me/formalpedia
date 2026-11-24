-- Prove2me | Definitions.Def_GroundTheory_ProfiniteCohomology_EulerCharDefs
-- name    : GroundTheory_ProfiniteCohomology_EulerCharDefs
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T16:04:15.574013+00:00
-- url     : https://prove2.me/theorems/dcb25911-d90e-4901-98db-1a40e429c1b3
-- title:
--   Euler Char Defs
-- statement:
--   Definitions and structural lemmas for Euler Char Defs, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/EulerCharDefs.lean

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_ContinuousCochains
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.ProfCoh
open CategoryTheory
universe u
variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G]
variable (k G) in

def finiteDiscreteRep (P : ℕ → Prop) : ObjectProperty (Rep.{u} k G) :=
  fun A => IsDiscreteRep A ∧ Finite A ∧ P (Nat.card A)
variable (k G) in

def grothendieckRelations (P : ℕ → Prop) :
    AddSubgroup (FreeAbelianGroup (finiteDiscreteRep k G P).FullSubcategory) :=
  AddSubgroup.closure {x | ∃ (S : ShortComplex (Rep.{u} k G)) (h₁ : finiteDiscreteRep k G P S.X₁)
    (h₂ : finiteDiscreteRep k G P S.X₂) (h₃ : finiteDiscreteRep k G P S.X₃), S.ShortExact ∧
      x = FreeAbelianGroup.of ⟨S.X₂, h₂⟩ - FreeAbelianGroup.of ⟨S.X₁, h₁⟩ -
        FreeAbelianGroup.of ⟨S.X₃, h₃⟩}
variable (k G) in

def GrothendieckGroup (P : ℕ → Prop) : Type (u + 1) :=
  FreeAbelianGroup (finiteDiscreteRep k G P).FullSubcategory ⧸ grothendieckRelations k G P
instance (P : ℕ → Prop) : AddCommGroup (GrothendieckGroup k G P) :=
  inferInstanceAs (AddCommGroup (_ ⧸ grothendieckRelations k G P))
def GrothendieckGroup.mk {P : ℕ → Prop} (A : Rep.{u} k G) (hA : finiteDiscreteRep k G P A) :
    GrothendieckGroup k G P :=
  QuotientAddGroup.mk (s := grothendieckRelations k G P) (FreeAbelianGroup.of ⟨A, hA⟩)
variable [IsTopologicalGroup G]
variable (k G) in

def HasFiniteCohomology (P : ℕ → Prop) : Prop :=
  ∀ (A : Rep.{u} k G) [IsDiscreteRep A], Finite A → P (Nat.card A) →
    (∀ q : ℕ, Finite (cohomology A q)) ∧ ∀ q : ℕ, 3 ≤ q → Subsingleton (cohomology A q)
noncomputable def eulerChar (A : Rep.{u} k G) [IsDiscreteRep A] : ℚ :=
  ∏ q ∈ Finset.range 3, (Nat.card (cohomology A q) : ℚ) ^ ((-1 : ℤ) ^ q)
end GroundTheory.ProfCoh


