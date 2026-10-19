-- Prove2me | Definitions.Def_MazurTransfer_PicardCanonicalRepresentationGroupIsomorphism
-- name    : MazurTransfer_PicardCanonicalRepresentationGroupIsomorphism
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T08:33:01.86915+00:00
-- url     : https://prove2.me/theorems/135e16ab-c291-4ca9-822e-2350077b12af
-- title:
--   Canonical group-scheme comparison of two representations of the same Picard group functor
-- statement:
--   Let $D$ and $E$ be two designated representatives of the same rigidified relative Picard group subfunctor for a pointed scheme over a commutative ring $R$. Uniqueness of the representing object gives a specified isomorphism $$D\simeq E\quad\text{over }\operatorname{Spec}R.$$ This isomorphism preserves the canonical internal group structures, identifies the zero sections and induces multiplicative equivalences on points over every test object. The construction includes the classification identity for the universal bundles. It compares the actual rational Picard scheme and the rational fibre of its integral family for the extension of actual norm endomorphisms.
-- source:
--   Original complete PicardCanonicalRepresentationGroupIsomorphism.lean from MazurTheorem, Apache-2.0, Vas and contributors. All nine original declarations and bodies are unchanged; the original project import alone becomes the Proved public pointwise-to-internal monoid-morphism theorem. All nine complete original closed types and all three data construction values are kernel-compared in separate original and public environments. Reuses original official Anthropic FLT relative Picard representability and group APIs at exact pin 6e837e75355538c7f80bab5b956861e86c4eacc2 and Mathlib uniqueness of representing objects. Native, strict and full frontend checks pass with standard axioms only. Explicit design boundary: canonical pointed isomorphisms of actual Picard group schemes with their internal group structures. Named downstream consumer: Order13SameIntegralPicardRationalSchemeComparison, rational diamond and nineteen-norm morphisms and their local integral extension.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: two representations of the same relative Picard group
functor are canonically isomorphic as group schemes over the base.
Named downstream consumer: comparison of the actual rational order-13
Picard scheme with the rational fibre of its existing integral family.
-/
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Theorems.Thm_MazurTransfer_MonoidObjectMorphismFromPointwiseGroupLaw_isMonHom_of_all_points

noncomputable section
universe u
namespace MazurTransfer.PicardCanonicalRepresentationGroupIsomorphism
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open NeronModelInfra GoodReductionJacobian
open scoped CategoryTheory.MonObj

variable {R : Type u} [CommRing R] {C : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of R)}
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}
  {P : SubPicGroupCondition c ε} {D E : RelativePic0Designation R c}
  (hD : RepresentsRelSubPic c ε P.toSubPicCondition D)
  (hE : RepresentsRelSubPic c ε P.toSubPicCondition E)

def canonicalOverIso : Over.mk D.toBase ≅ Over.mk E.toBase :=
  hD.representableBy.uniqueUpToIso hE.representableBy

theorem canonicalOverIso_classification (T : Over (Spec (CommRingCat.of R)))
    (a : T ⟶ Over.mk D.toBase) :
    hE.representableBy.homEquiv (a ≫ (canonicalOverIso hD hE).hom) =
      hD.representableBy.homEquiv a := by
  change hE.representableBy.homEquiv
    (a ≫ hE.representableBy.homEquiv.symm
      (hD.representableBy.homEquiv (𝟙 (Over.mk D.toBase)))) = _
  rw [Functor.RepresentableBy.comp_homEquiv_symm, Equiv.apply_symm_apply,
    ← Functor.RepresentableBy.homEquiv_comp, Category.comp_id]


theorem canonicalOverIso_points_one (T : Over (Spec (CommRingCat.of R))) :
    letI := hD.grpObj
    letI := hE.grpObj
    (1 : T ⟶ Over.mk D.toBase) ≫ (canonicalOverIso hD hE).hom = 1 := by
  letI := hD.grpObj
  letI := hE.grpObj
  letI := P.commGroupObj (Opposite.op T)
  apply hE.representableBy.homEquiv.injective
  rw [canonicalOverIso_classification, hD.homEquiv_one, hE.homEquiv_one]

theorem canonicalOverIso_points_mul (T : Over (Spec (CommRingCat.of R)))
    (a b : T ⟶ Over.mk D.toBase) :
    letI := hD.grpObj
    letI := hE.grpObj
    (a * b) ≫ (canonicalOverIso hD hE).hom =
      (a ≫ (canonicalOverIso hD hE).hom) * (b ≫ (canonicalOverIso hD hE).hom) := by
  letI := hD.grpObj
  letI := hE.grpObj
  letI := P.commGroupObj (Opposite.op T)
  apply hE.representableBy.homEquiv.injective
  rw [canonicalOverIso_classification, hE.homEquiv_mul,
    canonicalOverIso_classification, canonicalOverIso_classification, hD.homEquiv_mul]

theorem canonicalOverIso_isMonHom :
    letI := hD.grpObj
    letI := hE.grpObj
    IsMonHom (canonicalOverIso hD hE).hom := by
  letI := hD.grpObj
  letI := hE.grpObj
  exact MonoidObjectMorphismFromPointwiseGroupLaw.isMonHom_of_all_points _
    (canonicalOverIso_points_one hD hE) (canonicalOverIso_points_mul hD hE)


def canonicalPointMulEquiv (T : Over (Spec (CommRingCat.of R))) :
    letI := hD.grpObj
    letI := hE.grpObj
    (T ⟶ Over.mk D.toBase) ≃* (T ⟶ Over.mk E.toBase) := by
  letI := hD.grpObj
  letI := hE.grpObj
  letI := canonicalOverIso_isMonHom hD hE
  exact CategoryTheory.Hom.mulEquivCongrRight (canonicalOverIso hD hE) T

def canonicalSchemeIso : D.P ≅ E.P :=
  (Over.forget (Spec (CommRingCat.of R))).mapIso (canonicalOverIso hD hE)

theorem canonicalSchemeIso_over : (canonicalSchemeIso hD hE).hom ≫ E.toBase = D.toBase :=
  Over.w (canonicalOverIso hD hE).hom

theorem canonicalSchemeIso_zero :
    D.zeroSection ≫ (canonicalSchemeIso hD hE).hom = E.zeroSection := by
  letI := hD.grpObj
  letI := hE.grpObj
  have hz := congrArg (fun f : Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶
    Over.mk E.toBase => f.left)
    (canonicalOverIso_points_one hD hE (Over.mk (𝟙 (Spec (CommRingCat.of R)))))
  change (hD.relativeGroupLaw.one (𝟙 _)).val ≫
    (canonicalSchemeIso hD hE).hom = (hE.relativeGroupLaw.one (𝟙 _)).val at hz
  rw [hD.relativeGroupLaw_one, hE.relativeGroupLaw_one] at hz
  exact hz

end MazurTransfer.PicardCanonicalRepresentationGroupIsomorphism
#print axioms MazurTransfer.PicardCanonicalRepresentationGroupIsomorphism.canonicalOverIso_classification
#print axioms MazurTransfer.PicardCanonicalRepresentationGroupIsomorphism.canonicalOverIso_isMonHom
#print axioms MazurTransfer.PicardCanonicalRepresentationGroupIsomorphism.canonicalPointMulEquiv
#print axioms MazurTransfer.PicardCanonicalRepresentationGroupIsomorphism.canonicalSchemeIso_over

#print axioms MazurTransfer.PicardCanonicalRepresentationGroupIsomorphism.canonicalSchemeIso_zero


