-- Prove2me | Definitions.Def_MazurTransfer_OriginalRelativeFiniteFlatNormPreimageTorsorData20261020
-- name    : MazurTransfer_OriginalRelativeFiniteFlatNormPreimageTorsorData20261020
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-21T01:39:22.879319+00:00
-- url     : https://prove2.me/theorems/b00639c7-7d28-4bd3-8413-4c6f179eeb1a
-- title:
--   Original actual finite-flat norm-preimage torsor predicate
-- statement:
--   Retain the original finite-flat preimage torsor predicate, including finiteness, flatness, local finite presentation and surjectivity of the same fibre, and a principal-action isomorphism realizing exactly the given point action over every test scheme. Its complete original type and whole predicate value, fifty-nine context types and thirty-eight whole context values are independently checked. Torsor existence is a separate theorem interface. Named downstream consumer: actual integral nineteen norm fibres and their selected mu19 quotient torsors.
-- source:
--   MazurTheorem RelativeFiniteFlatNormPreimageTorsor by Vas and contributors; complete original predicate type and whole value, preserving Apache-2.0 attribution.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the ACTUAL fibre of a finite-flat surjective endomorphism
is an fppf preimage torsor under its SAME represented kernel. Retain the
principal-action map on EVERY test scheme, not an arbitrary isomorphism.
Named downstream consumer: actual integral nineteen norm fibres and their
selected normalized mu19 quotient torsors.
-/
import Definitions.Def_MazurTransfer_OriginalRelativeNormPreimagePrincipalIsoData20261020

noncomputable section
namespace MazurTransfer.RelativeFiniteFlatNormPreimageTorsor
open CategoryTheory AlgebraicGeometry GoodReductionJacobian NeronModelInfra
open RelativeNormPreimageRepresentation RelativeNormPreimagePrincipalIso
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

def HasFiniteFlatPreimageTorsor : Prop :=
  IsFinite (fibreStr F a) ∧ Flat (fibreStr F a) ∧
    LocallyOfFinitePresentation (fibreStr F a) ∧ Surjective (fibreStr F a) ∧
  ∃ I : Over.mk (sourceStr L F a) ≅ Over.mk (targetStr F a),
    ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (b : SchemeHomOver t (sourceStr L F a)),
      (principalPointsEquiv L F hOne hMul a t b).val = b.val ≫ I.hom.left



end MazurTransfer.RelativeFiniteFlatNormPreimageTorsor
#print axioms MazurTransfer.RelativeFiniteFlatNormPreimageTorsor.HasFiniteFlatPreimageTorsor


