-- Prove2me | Definitions.Def_MazurTransfer_Order13LiteralFibrePicardRepresentation
-- name    : MazurTransfer_Order13LiteralFibrePicardRepresentation
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T07:59:12.518013+00:00
-- url     : https://prove2.me/theorems/b9bffc4d-ea19-45b7-ac27-87e2ba55c245
-- title:
--   The same integral Picard family represents each literal order-thirteen fibre
-- statement:
--   Let $R\to S$ be a homomorphism of commutative rings, and let $D$ be an actual designated representative of the algebraically trivial rigidified relative Picard subfunctor of the literal order-thirteen curve $C_R$, with its positive-infinity section. The base-changed designation, relabelled along the specified pointed curve isomorphism $C_S\simeq(C_R)_S$, represents the corresponding subfunctor of the literal curve: $$\operatorname{Pic}^{0}_{C_S/S}\simeq D_S.$$ This relabelling retains the exact base-changed representing scheme, structure morphism and zero section. The bridge identifies the literal rational and good-characteristic fibres of one integral Picard family.
-- source:
--   MazurTheorem Order13IntegralPicardLiteralFibreRepresentations.lean, Apache-2.0, Vas and contributors. The literalFibreDesignation constructor and its structural literal_fibre_representation proof retain their original bodies unchanged. Already public whole-curve fibre isomorphism, structural compatibility and positive-infinity section compatibility are imported rather than repeated. Reuses the original official Anthropic FLT Picard base-change theorem at exact pin 6e837e75355538c7f80bab5b956861e86c4eacc2 and the public pointed-curve representation transport. Both complete original closed types and the original designation value are kernel-compared; native, strict and full frontend checks pass. No extra domain, noetherian or invertibility assumptions are imposed on this bridge. Named downstream consumer: same-family rational, mod-3 and mod-5 arithmetic Picard groups and finite point counts.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: every algebra base change of an actual order-13 Picard
representation represents the Picard functor of the literal new-ring curve,
using the genuine whole-curve isomorphism and positive infinity section.
The representing scheme, structural map and zero section are retained.
Named downstream consumer: same-family finite-field Picard cardinalities
and rational arithmetic divisor-class identification.
-/
import Definitions.Def_MazurTransfer_PointedCurvePicardRepresentationTransport
import Theorems.Thm_MazurTransfer_Order13IntegralPicardLiteralFibreRepresentations_literalCurveFibreIso_section
import Definitions.Def_MazurTransfer_Order13LiteralCurveFibreIsomorphism
import Theorems.Thm_AlgebraicGeometry_RelPicard_exists_representsRelSubPic_baseChange

noncomputable section
universe u
namespace MazurTransfer.Order13IntegralPicardLiteralFibreRepresentations
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard
open AlgebraicGeometry.SmoothProperCurve GoodReductionJacobian NeronModelInfra
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13IntegralSections Order13ActualCurveBaseChange CurveIsoPicardRepresentationTransport
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]







def literalFibreDesignation (D : RelativePic0Designation R (curveToBase R)) :
    RelativePic0Designation S (curveToBase S) :=
  relabelDesignation (c' := curveToBase S) (D.baseChange S)

theorem literal_fibre_representation
    (D : RelativePic0Designation R (curveToBase R))
    (h : RepresentsRelSubPic (curveToBase R) (positiveInfinitySection R)
      (algEquivZeroCut (curveToBase R) (positiveInfinitySection R)) D) :
    Nonempty (RepresentsRelSubPic (curveToBase S) (positiveInfinitySection S)
      (algEquivZeroCut (curveToBase S) (positiveInfinitySection S))
      (literalFibreDesignation R S D)) := by
  obtain ⟨hS,_⟩ := exists_representsRelSubPic_baseChange R (curveToBase R)
    (positiveInfinitySection R) D h S
  exact ⟨transportRepresentation (literalCurveFibreIso R S)
    (literalCurveFibreIso_over R S) (literalCurveFibreIso_section R S) (D.baseChange S) hS⟩

end MazurTransfer.Order13IntegralPicardLiteralFibreRepresentations
#print axioms MazurTransfer.Order13IntegralPicardLiteralFibreRepresentations.literal_fibre_representation


