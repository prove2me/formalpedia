-- Prove2me | Definitions.Def_ProEtale_Algebra_Ind
-- name    : ProEtale_Algebra_Ind
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-26T11:09:18.032797+00:00
-- url     : https://prove2.me/theorems/21420287-e807-44de-9c43-024e8a96aab4
-- title:
--   From properties of ring homomorphisms to object properties of algebras
-- statement:
--   For a property $P$ of ring homomorphisms, the object property `RingHom.toObjectProperty P R` of commutative $R$-algebras whose structure map satisfies $P$, and the comparison between the ind-completion of $P$ as a morphism property and as an object property.
-- source:
--   Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Algebra/Ind.lean (declarations kept unchanged, unused ones removed).

/-
Copyright (c) 2025 Jiedong Jiang, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang, Christian Merten
-/
import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false
variable {R : Type*} [CommRing R]

universe u v w w'

open CategoryTheory Limits Algebra

section

variable {R : Type u} {S : Type u} [CommRing R] [CommRing S] [Algebra R S]

variable (R) in
/-- The induced object property in the category of commutative `R`-algebras by
a property of ring homomorphisms. -/
def RingHom.toObjectProperty
    (P : ∀ {R : Type u} {S : Type v} [CommRing R] [CommRing S], (R →+* S) → Prop)
    (R : Type u) [CommRing R] :
    ObjectProperty (CommAlgCat.{v} R) :=
  fun S ↦ P (algebraMap R S)

@[simp]
lemma RingHom.toObjectProperty_iff
    (P : ∀ {R : Type u} {S : Type v} [CommRing R] [CommRing S], (R →+* S) → Prop)
    (S : CommAlgCat.{v} R) :
    RingHom.toObjectProperty P R S ↔ P (algebraMap R S) :=
  .rfl

lemma RingHom.RespectsIso.isClosedUnderIsomorphisms_toObjectProperty
    {P : ∀ {R : Type u} {S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop}
    (hP : RingHom.RespectsIso P) (R : Type u) [CommRing R] :
    (RingHom.toObjectProperty P R).IsClosedUnderIsomorphisms := by
  refine ⟨fun {A B} e hA ↦ ?_⟩
  rw [toObjectProperty_iff, ← (CommAlgCat.algEquivOfIso e).toAlgHom.comp_algebraMap]
  exact hP.1 (algebraMap R A) (CommAlgCat.algEquivOfIso e).toRingEquiv hA

lemma RingHom.RespectsIso.ind_toMorphismProperty_iff_ind_toObjectProperty
    (P : ∀ {R : Type u} {S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop)
    (hP : RingHom.RespectsIso P) :
    MorphismProperty.ind.{w} (RingHom.toMorphismProperty P) (CommRingCat.ofHom <| algebraMap R S) ↔
      ObjectProperty.ind.{w} (RingHom.toObjectProperty P R) (CommAlgCat.of R S) := by
  have := hP.isClosedUnderIsomorphisms_toObjectProperty R
  rw [MorphismProperty.ind_iff_ind_underMk,
    ← ObjectProperty.ind_iff_of_equivalence (RingHom.toObjectProperty P R)
      (commAlgCatEquivUnder (.of R)).symm]
  rfl

end


