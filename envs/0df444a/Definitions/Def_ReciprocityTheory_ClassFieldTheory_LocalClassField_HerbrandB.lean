-- Prove2me | Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_HerbrandB
-- name    : ReciprocityTheory_ClassFieldTheory_LocalClassField_HerbrandB
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:05:40.84928+00:00
-- url     : https://prove2.me/theorems/8e750f36-b83d-402f-b665-0c260ced5c44
-- title:
--   Herbrand B
-- statement:
--   Definitions and structural lemmas for Herbrand B, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/HerbrandB.lean

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_HerbrandA
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
section Abstract
variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    {DA NA : A →+ A} {DB NB : B →+ B} {f : A →+ B}
def cokerMap (f : A →+ B) (fD : ∀ a, f (DA a) = DB (f a)) : B ⧸ f.range →+ B ⧸ f.range :=
  QuotientAddGroup.map _ _ DB (by
    rintro _ ⟨a, rfl⟩
    exact ⟨DA a, fD a⟩)
end Abstract
section Cyclic
variable {k G M : Type*} [CommRing k] [Group G] [Fintype G] [AddCommGroup M] [Module k M]
def dHom (ρ : Representation k G M) (g : G) : M →+ M := (ρ g - 1 : Module.End k M).toAddMonoidHom
def nHom (ρ : Representation k G M) : M →+ M := (ρ.norm : Module.End k M).toAddMonoidHom
abbrev TateZerothCohomology (ρ : Representation k G M) (g : G) : Type _ := T (dHom ρ g) (nHom ρ)
abbrev H1 (ρ : Representation k G M) (g : G) : Type _ := T (nHom ρ) (dHom ρ g)
def HFin (ρ : Representation k G M) (g : G) : Prop := IsFin (dHom ρ g) (nHom ρ)
noncomputable def h (ρ : Representation k G M) (g : G) : ℚ := q (dHom ρ g) (nHom ρ)
variable {A B C : Type*} [AddCommGroup A] [Module k A] [AddCommGroup B] [Module k B]
  [AddCommGroup C] [Module k C]
end Cyclic
end ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand


