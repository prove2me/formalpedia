-- Prove2me | Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_HerbrandA
-- name    : ReciprocityTheory_ClassFieldTheory_LocalClassField_HerbrandA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:03:34.786789+00:00
-- url     : https://prove2.me/theorems/83052a34-93d5-4423-a2d4-f2fdb2236f02
-- title:
--   Herbrand A
-- statement:
--   Definitions and structural lemmas for Herbrand A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/HerbrandA.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand
open Function
variable {M : Type*} [AddCommGroup M]
abbrev T (D N : M →+ M) : Type _ := D.ker ⧸ (N.range.addSubgroupOf D.ker)
def IsFin (D N : M →+ M) : Prop := Finite (T D N) ∧ Finite (T N D)
noncomputable def q (D N : M →+ M) : ℚ := (Nat.card (T D N) : ℚ) / (Nat.card (T N D) : ℚ)
structure SES {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    (DA NA : A →+ A) (DB NB : B →+ B) (DC NC : C →+ C) (f : A →+ B) (g : B →+ C) : Prop where
  inj : Injective f
  exact : Function.Exact f g
  surj : Surjective g
  fD : ∀ a, f (DA a) = DB (f a)
  fN : ∀ a, f (NA a) = NB (f a)
  gD : ∀ b, g (DB b) = DC (g b)
  gN : ∀ b, g (NB b) = NC (g b)
  DN : ∀ b, DB (NB b) = 0
  ND : ∀ b, NB (DB b) = 0
variable {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    {DA NA : A →+ A} {DB NB : B →+ B} {DC NC : C →+ C} {f : A →+ B} {g : B →+ C}
def kerMap (f : A →+ B) (fD : ∀ a, f (DA a) = DB (f a)) : DA.ker →+ DB.ker :=
  (f.comp DA.ker.subtype).codRestrict DB.ker (fun a => by
    have ha : DA (a : A) = 0 := a.2
    rw [AddMonoidHom.mem_ker]
    change DB (f a) = 0
    rw [← fD, ha, map_zero])
def Tmap (f : A →+ B) (fD : ∀ a, f (DA a) = DB (f a)) (fN : ∀ a, f (NA a) = NB (f a)) :
    T DA NA →+ T DB NB :=
  QuotientAddGroup.map _ _ (kerMap f fD) (by
    intro a ha
    rw [AddSubgroup.mem_addSubgroupOf] at ha
    obtain ⟨x, hx⟩ := ha
    rw [AddSubgroup.mem_comap, AddSubgroup.mem_addSubgroupOf]
    exact ⟨f x, by rw [← fN, hx]; rfl⟩)
def Rel (DB : B →+ B) (f : A →+ B) (g : B →+ C) (c : C) (a : A) : Prop := ∃ b, g b = c ∧ f a = DB b
section Count
variable {X Y Z : Type*} [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
end Count
end ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand


