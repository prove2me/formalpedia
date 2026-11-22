-- Prove2me | Definitions.Def_ReciprocityTheory_BasicDefinitions_ExistsUnique
-- name    : ReciprocityTheory_BasicDefinitions_ExistsUnique
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T16:46:14.695299+00:00
-- url     : https://prove2.me/theorems/d298095c-5851-4c7b-b494-c724ecaa5d1a
-- title:
--   Exists Unique
-- statement:
--   Definitions and structural lemmas for Exists Unique, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/BasicDefinitions/ExistsUnique.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.Def
open IsLocalRing Matrix
universe u v w w'
class IsCNL (O : Type u) (A : Type w) [CommRing O] [IsLocalRing O] [CommRing A] [IsLocalRing A]
    [Algebra O A] : Prop where
  noeth : IsNoetherianRing A
  complete : IsAdicComplete (maximalIdeal A) A
  localHom : IsLocalHom (algebraMap O A)
  resSurj : Function.Surjective fun x : O => residue A (algebraMap O A x)
attribute [instance] IsCNL.noeth IsCNL.complete IsCNL.localHom
abbrev PS (O : Type u) [CommRing O] (a : ℕ) : Type u := MvPowerSeries (Fin a) O
structure Pattern (n : ℕ) where
  rel : Fin n → Fin n → Prop
  refl : ∀ i, rel i i
  trans : ∀ i j l, rel i j → rel j l → rel i l
namespace Pattern
variable {n : ℕ}
def full (n : ℕ) : Pattern n := ⟨fun _ _ => True, fun _ => trivial, fun _ _ _ _ _ => trivial⟩
def upper (n : ℕ) : Pattern n := ⟨fun i j => i ≤ j, fun i => le_refl i, fun _ _ _ h h' => le_trans h h'⟩
def diag (n : ℕ) : Pattern n := ⟨fun i j => i = j, fun _ => rfl, fun _ _ _ h h' => h.trans h'⟩
def Mem (S : Pattern n) {A : Type*} [Zero A] (X : Matrix (Fin n) (Fin n) A) : Prop :=
  ∀ i j, ¬ S.rel i j → X i j = 0
def mat (S : Pattern n) (A : Type*) [CommRing A] : Submodule A (Matrix (Fin n) (Fin n) A) where
  carrier := {X | S.Mem X}
  add_mem' := fun {X Y} hX hY i j h => by simp [hX i j h, hY i j h]
  zero_mem' := fun _ _ _ => rfl
  smul_mem' := fun c X hX i j h => by simp [hX i j h]
end Pattern
section Lift
variable (O : Type u) [CommRing O] [IsLocalRing O]
variable {G : Type v} [Group G] [TopologicalSpace G] {n : ℕ}
structure IsResidual (S : Pattern n) (rbar : G →* GL (Fin n) (ResidueField O)) : Prop where
  cont : IsOpen {g : G | rbar g = 1}
  mem : ∀ g, S.Mem (rbar g).val
structure IsLift (S : Pattern n) (rbar : G →* GL (Fin n) (ResidueField O))
    {A : Type w} [CommRing A] [IsLocalRing A] [Algebra O A] [IsLocalHom (algebraMap O A)]
    (ρ : G →* GL (Fin n) A) : Prop where
  cont : ∀ N : ℕ, IsOpen {g : G | ∀ i j, (ρ g).val i j - (1 : Matrix (Fin n) (Fin n) A) i j ∈ maximalIdeal A ^ N}
  red : ∀ g, (ρ g).val.map (residue A) = (rbar g).val.map (ResidueField.map (algebraMap O A))
  mem : ∀ g, S.Mem (ρ g).val
def push {A : Type w} {B : Type w'} [CommRing A] [CommRing B] [Algebra O A] [Algebra O B] (f : A →ₐ[O] B)
    (ρ : G →* GL (Fin n) A) : G →* GL (Fin n) B :=
  (Matrix.GeneralLinearGroup.map f.toRingHom).comp ρ
structure IsUniversal (S : Pattern n) (rbar : G →* GL (Fin n) (ResidueField O))
    (R : Type u) [CommRing R] [IsLocalRing R] [Algebra O R] [IsCNL O R] (ρu : G →* GL (Fin n) R) : Prop where
  isLift : IsLift O S rbar ρu
  existsUnique : ∀ (A : Type u) [CommRing A] [IsLocalRing A] [Algebra O A] [IsCNL O A]
    (ρ : G →* GL (Fin n) A), IsLift O S rbar ρ → ∃! f : R →ₐ[O] A, push O f ρu = ρ
end Lift
def MazurFin (p : ℕ) (G : Type v) [Group G] [TopologicalSpace G] : Prop :=
  ∀ H : OpenSubgroup G, Finite (ContinuousMonoidHom H (Multiplicative (ZMod p)))
end ReciprocityTheory.Def


