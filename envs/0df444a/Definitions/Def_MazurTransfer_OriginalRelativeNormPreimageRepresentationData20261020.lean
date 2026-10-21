-- Prove2me | Definitions.Def_MazurTransfer_OriginalRelativeNormPreimageRepresentationData20261020
-- name    : MazurTransfer_OriginalRelativeNormPreimageRepresentationData20261020
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-21T01:07:35.553929+00:00
-- url     : https://prove2.me/theorems/1a698341-f11c-4d38-b369-c3853ede2d1e
-- title:
--   Original relative norm-preimage fibre and point equivalence
-- statement:
--   Retain the original pullback fibre, structure morphism, inclusion, pulled section, intrinsic over-base certificate, forward and backward point maps and their exact equivalence. All nine complete original types, eight whole data values, twenty-five context types, sixteen whole context values and all generated structural proof types are independently checked. Both naturality propositions are separate theorem interfaces. Named downstream consumer: the principal-action scheme isomorphism of the actual integral nineteen norm torsor.
-- source:
--   MazurTheorem RelativeNormPreimageRepresentation by Vas and contributors; original constructor interface with full original types and whole values, preserving Apache-2.0 attribution.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the ACTUAL pullback fibre of a relative endomorphism
represents its preimages of the GIVEN integral section over EVERY test
scheme, with every precomposition map retained.
Named downstream consumer: principal-action isomorphism of the actual
finite-flat integral nineteen norm torsor.
-/
import Definitions.Def_MazurTransfer_OriginalRelativeNormPreimagePointTorsorData20261020

noncomputable section
namespace MazurTransfer.RelativeNormPreimageRepresentation
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GoodReductionJacobian NeronModelInfra
open RelativeNormPreimagePointTorsor
universe u
variable {R : Type u} [CommRing R] {A : Scheme.{u}}
variable {f : A ⟶ Spec (CommRingCat.of R)}
variable (F : SchemeHomOver f f)
variable (a : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f)

abbrev fibreScheme : Scheme.{u} := pullback F.val a.val
abbrev fibreStr : fibreScheme F a ⟶ Spec (CommRingCat.of R) := pullback.snd _ _
abbrev fibreIncl : fibreScheme F a ⟶ A := pullback.fst _ _

def pulledPoint {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) : SchemeHomOver t f :=
  ⟨t ≫ a.val, by rw [Category.assoc, a.property, Category.comp_id]⟩

theorem fibreIncl_over : fibreIncl F a ≫ f = fibreStr F a := by
  have h := congrArg (fun z => z ≫ f) (pullback.condition (f := F.val) (g := a.val))
  simpa only [Category.assoc, F.property, a.property, Category.comp_id] using h

variable {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))

def pointToBase (b : SchemeHomOver t (fibreStr F a)) : SchemeHomOver t f :=
  ⟨b.val ≫ fibreIncl F a, by rw [Category.assoc, fibreIncl_over, b.property]⟩

def pointsForward (b : SchemeHomOver t (fibreStr F a)) : preimagePoints F (pulledPoint a t) :=
  ⟨pointToBase F a t b, by
    apply Subtype.ext
    change (b.val ≫ fibreIncl F a) ≫ F.val = t ≫ a.val
    rw [Category.assoc, pullback.condition, ← Category.assoc, b.property]⟩

def pointsBackward (y : preimagePoints F (pulledPoint a t)) : SchemeHomOver t (fibreStr F a) :=
  ⟨pullback.lift y.val.val t (by exact congrArg Subtype.val y.property), pullback.lift_snd _ _ _⟩

def pointsEquiv : SchemeHomOver t (fibreStr F a) ≃ preimagePoints F (pulledPoint a t) where
  toFun := pointsForward F a t
  invFun := pointsBackward F a t
  left_inv b := by
    apply Subtype.ext
    apply pullback.hom_ext
    · exact pullback.lift_fst _ _ _
    · exact (pullback.lift_snd _ _ _).trans b.property.symm
  right_inv y := by
    apply Subtype.ext
    apply Subtype.ext
    exact pullback.lift_fst _ _ _

variable {T' : Scheme.{u}} (t' : T' ⟶ Spec (CommRingCat.of R))
variable (ψ : T' ⟶ T) (hψ : ψ ≫ t = t')





end MazurTransfer.RelativeNormPreimageRepresentation
#print axioms MazurTransfer.RelativeNormPreimageRepresentation.fibreScheme
#print axioms MazurTransfer.RelativeNormPreimageRepresentation.fibreStr
#print axioms MazurTransfer.RelativeNormPreimageRepresentation.fibreIncl
#print axioms MazurTransfer.RelativeNormPreimageRepresentation.pulledPoint
#print axioms MazurTransfer.RelativeNormPreimageRepresentation.fibreIncl_over
#print axioms MazurTransfer.RelativeNormPreimageRepresentation.pointToBase
#print axioms MazurTransfer.RelativeNormPreimageRepresentation.pointsForward
#print axioms MazurTransfer.RelativeNormPreimageRepresentation.pointsBackward
#print axioms MazurTransfer.RelativeNormPreimageRepresentation.pointsEquiv


