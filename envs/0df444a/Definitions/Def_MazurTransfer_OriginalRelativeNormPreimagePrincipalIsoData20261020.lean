-- Prove2me | Definitions.Def_MazurTransfer_OriginalRelativeNormPreimagePrincipalIsoData20261020
-- name    : MazurTransfer_OriginalRelativeNormPreimagePrincipalIsoData20261020
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-21T01:30:07.471616+00:00
-- url     : https://prove2.me/theorems/8da4e13e-6c7e-4562-ac2f-e730dfcc83e2
-- title:
--   Original norm-preimage principal-action isomorphism over the same base
-- statement:
--   Retain the original source and target structure maps, their exact point equivalences, original principal point action and original over-base principal-action isomorphism, with the intrinsic naturality certificates constructing it. All fourteen complete original types, six whole values, forty-five context types, thirty-two whole context values and all generated structural proof types are independently checked. The exact point-map and action-law propositions are separate theorem interfaces. Named downstream consumer: the actual finite-flat integral nineteen norm-preimage torsor and its selected mu19 pushforward.
-- source:
--   MazurTheorem RelativeNormPreimagePrincipalIso by Vas and contributors; complete original types and whole values, preserving Apache-2.0 attribution.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the GIVEN relative endomorphism's ACTUAL preimage fibre
has a principal-action isomorphism kernel × fibre ≅ fibre × fibre over
the SAME base; it realizes the natural point action on EVERY test scheme.
Named downstream consumer: actual finite-flat integral norm torsors and
selected mu19 pushforwards at nineteen.
-/
import Definitions.Def_MazurTransfer_OriginalRelativeNormPreimageRepresentationData20261020
import Definitions.Def_MazurTransfer_OriginalSchemePullbackProductPointsData20261020
import Definitions.Def_MazurTransfer_OriginalSchemePointNaturalEquivalenceIsoData20261020

noncomputable section
namespace MazurTransfer.RelativeNormPreimagePrincipalIso
open CategoryTheory AlgebraicGeometry GoodReductionJacobian NeronModelInfra
open RelativeGroupLawFiniteFlatKernelHopf RelativeNormPreimagePointTorsor
open RelativeNormPreimageRepresentation
universe u
variable {R : Type u} [CommRing R] {A : Scheme.{u}}
variable {f : A ⟶ Spec (CommRingCat.of R)}
variable (L : RelativeGroupLaw R f) (F : SchemeHomOver f f)
variable (hOne : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)),
  NeronModelInfra.schemeHomOverComp (L.one t) F = L.one t)
variable (hMul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
  NeronModelInfra.schemeHomOverComp (L.mul t x y) F =
    L.mul t (NeronModelInfra.schemeHomOverComp x F) (NeronModelInfra.schemeHomOverComp y F))
variable (a : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f)

abbrev sourceStr := SchemePullbackProductPoints.productStr (kernelStr L F) (fibreStr F a)
abbrev targetStr := SchemePullbackProductPoints.productStr (fibreStr F a) (fibreStr F a)

variable {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))

def sourcePointsEquiv : SchemeHomOver t (sourceStr L F a) ≃
    kernelPoints L F t × preimagePoints F (pulledPoint a t) :=
  (SchemePullbackProductPoints.pointsEquiv _ _ t).trans
    (Equiv.prodCongr (kernelPointsEquiv L F t) (RelativeNormPreimageRepresentation.pointsEquiv F a t))

def targetPointsEquiv : SchemeHomOver t (targetStr F a) ≃
    preimagePoints F (pulledPoint a t) × preimagePoints F (pulledPoint a t) :=
  (SchemePullbackProductPoints.pointsEquiv _ _ t).trans
    (Equiv.prodCongr (RelativeNormPreimageRepresentation.pointsEquiv F a t)
      (RelativeNormPreimageRepresentation.pointsEquiv F a t))

include hOne hMul in
def principalPointsEquiv : SchemeHomOver t (sourceStr L F a) ≃ SchemeHomOver t (targetStr F a) :=
  (sourcePointsEquiv L F a t).trans
    ((principalActionEquiv L F hOne hMul (pulledPoint a t)).trans (targetPointsEquiv F a t).symm)

include hOne hMul in
theorem principal_decode (b : SchemeHomOver t (sourceStr L F a)) :
    targetPointsEquiv F a t (principalPointsEquiv L F hOne hMul a t b) =
      principalActionEquiv L F hOne hMul (pulledPoint a t) (sourcePointsEquiv L F a t b) :=
  (targetPointsEquiv F a t).apply_symm_apply _

include hOne hMul in
theorem principal_first (b : SchemeHomOver t (sourceStr L F a)) :
    (targetPointsEquiv F a t (principalPointsEquiv L F hOne hMul a t b)).1.val =
      L.mul t (sourcePointsEquiv L F a t b).1.val (sourcePointsEquiv L F a t b).2.val :=
  congrArg (fun p => p.1.val) (principal_decode L F hOne hMul a t b)

include hOne hMul in
theorem principal_second (b : SchemeHomOver t (sourceStr L F a)) :
    (targetPointsEquiv F a t (principalPointsEquiv L F hOne hMul a t b)).2.val =
      (sourcePointsEquiv L F a t b).2.val :=
  congrArg (fun p => p.2.val) (principal_decode L F hOne hMul a t b)

variable {T' : Scheme.{u}} (t' : T' ⟶ Spec (CommRingCat.of R))
variable (ψ : T' ⟶ T) (hψ : ψ ≫ t = t')

theorem source_first_natural (b : SchemeHomOver t (sourceStr L F a)) :
    (sourcePointsEquiv L F a t' (GoodReductionJacobian.schemeHomOverComp ψ hψ b)).1.val =
      GoodReductionJacobian.schemeHomOverComp ψ hψ (sourcePointsEquiv L F a t b).1.val := by
  apply Subtype.ext
  simp only [sourcePointsEquiv, Equiv.trans_apply, Equiv.prodCongr_apply]
  change ((ψ ≫ b.val) ≫ _) ≫ _ = ψ ≫ ((b.val ≫ _) ≫ _)
  simp only [Category.assoc]

theorem source_second_natural (b : SchemeHomOver t (sourceStr L F a)) :
    (sourcePointsEquiv L F a t' (GoodReductionJacobian.schemeHomOverComp ψ hψ b)).2.val =
      GoodReductionJacobian.schemeHomOverComp ψ hψ (sourcePointsEquiv L F a t b).2.val := by
  apply Subtype.ext
  change ((ψ ≫ b.val) ≫ _) ≫ _ = ψ ≫ ((b.val ≫ _) ≫ _)
  simp only [Category.assoc]

theorem target_first_natural (b : SchemeHomOver t (targetStr F a)) :
    (targetPointsEquiv F a t' (GoodReductionJacobian.schemeHomOverComp ψ hψ b)).1.val =
      GoodReductionJacobian.schemeHomOverComp ψ hψ (targetPointsEquiv F a t b).1.val := by
  apply Subtype.ext
  change ((ψ ≫ b.val) ≫ _) ≫ _ = ψ ≫ ((b.val ≫ _) ≫ _)
  simp only [Category.assoc]

theorem target_second_natural (b : SchemeHomOver t (targetStr F a)) :
    (targetPointsEquiv F a t' (GoodReductionJacobian.schemeHomOverComp ψ hψ b)).2.val =
      GoodReductionJacobian.schemeHomOverComp ψ hψ (targetPointsEquiv F a t b).2.val := by
  apply Subtype.ext
  change ((ψ ≫ b.val) ≫ _) ≫ _ = ψ ≫ ((b.val ≫ _) ≫ _)
  simp only [Category.assoc]

include hOne hMul in
theorem principal_natural (b : SchemeHomOver t (sourceStr L F a)) :
    principalPointsEquiv L F hOne hMul a t' (GoodReductionJacobian.schemeHomOverComp ψ hψ b) =
      GoodReductionJacobian.schemeHomOverComp ψ hψ (principalPointsEquiv L F hOne hMul a t b) := by
  apply (targetPointsEquiv F a t').injective
  apply Prod.ext
  · apply Subtype.ext
    rw [principal_first, source_first_natural, source_second_natural, target_first_natural, principal_first]
    exact (L.mul_natural t t' ψ hψ _ _).symm
  · apply Subtype.ext
    rw [principal_second, source_second_natural, target_second_natural, principal_second]

include hOne hMul in
def principalOverIso : Over.mk (sourceStr L F a) ≅ Over.mk (targetStr F a) :=
  SchemePointNaturalEquivalenceIso.overIso (sourceStr L F a) (targetStr F a)
    (principalPointsEquiv L F hOne hMul a)
    (fun t t' ψ hψ b => principal_natural L F hOne hMul a t t' ψ hψ b)







end MazurTransfer.RelativeNormPreimagePrincipalIso

#print axioms MazurTransfer.RelativeNormPreimagePrincipalIso.sourceStr
#print axioms MazurTransfer.RelativeNormPreimagePrincipalIso.targetStr
#print axioms MazurTransfer.RelativeNormPreimagePrincipalIso.sourcePointsEquiv
#print axioms MazurTransfer.RelativeNormPreimagePrincipalIso.targetPointsEquiv
#print axioms MazurTransfer.RelativeNormPreimagePrincipalIso.principalPointsEquiv
#print axioms MazurTransfer.RelativeNormPreimagePrincipalIso.principal_decode
#print axioms MazurTransfer.RelativeNormPreimagePrincipalIso.principal_first
#print axioms MazurTransfer.RelativeNormPreimagePrincipalIso.principal_second
#print axioms MazurTransfer.RelativeNormPreimagePrincipalIso.source_first_natural
#print axioms MazurTransfer.RelativeNormPreimagePrincipalIso.source_second_natural
#print axioms MazurTransfer.RelativeNormPreimagePrincipalIso.target_first_natural
#print axioms MazurTransfer.RelativeNormPreimagePrincipalIso.target_second_natural
#print axioms MazurTransfer.RelativeNormPreimagePrincipalIso.principal_natural
#print axioms MazurTransfer.RelativeNormPreimagePrincipalIso.principalOverIso


