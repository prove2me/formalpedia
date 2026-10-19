-- Prove2me | Definitions.Def_MazurTransfer_Order13ActualRationalPicardDesignation
-- name    : MazurTransfer_Order13ActualRationalPicardDesignation
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T08:43:50.720395+00:00
-- url     : https://prove2.me/theorems/de68986e-a2e0-4ee5-bd97-9e9abfd875cc
-- title:
--   The original actual rational Picard designation and positive-infinity representation
-- statement:
--   The literal order-thirteen curve over $\mathbb Q$, with its specified positive-infinity section, has the designated Picard scheme $D_{\mathbb Q}$ selected by the original construction and a representation $$\operatorname{Pic}^{0}_{C/\mathbb Q}\simeq D_{\mathbb Q}.$$ The selected scheme, section and representing equivalence are retained as actual data. They are the inputs to the original rational diamond and norm endomorphisms and to comparison with the rational fibre of the integral Picard family.
-- source:
--   Three original constructors infinitySection, actualPicard and actualRepresentation from MazurTheorem Order13ActualPicardDiamondSchemeEndomorphism.lean, Apache-2.0, Vas and contributors. All bodies are unchanged; the previously Proved public actual integral Picard theorem is specialized to the rational field. All three complete original closed types and all three construction values are kernel-compared. Native, strict and full frontend checks pass with standard axioms only. Reuses the original official Anthropic FLT Picard interfaces at exact pin 6e837e75355538c7f80bab5b956861e86c4eacc2. Named downstream consumer: actual rational scheme comparison and the original diamond/nineteen-norm endomorphisms.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the actual diamond inverse acts by re-rigidified pullback
on every represented Picard scheme of the literal order-13 curve over Q.
The construction acts on all test schemes and respects multiplication and
identity. Named downstream consumer: comparison with the arithmetic Picard
diamond and a genuine scheme version of the nineteen norm relation.
-/
/- Public constructor boundary: the original designated rational Picard
scheme and representation, based at the literal positive-infinity section.
Named downstream consumer: comparison with the rational fibre of the
same actual integral family and its original nineteen-norm endomorphisms. -/
import Mathlib
import Theorems.Thm_MazurTransfer_Order13ActualIntegralPicardRepresentation_actual_integral_picard_representation
noncomputable section
namespace MazurTransfer.Order13ActualPicardDiamondSchemeEndomorphism
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open NeronModelInfra GoodReductionJacobian
open MazurTorsion.XOneThirteenProjectiveCurve
open MazurTransfer
abbrev infinitySection := Order13IntegralSections.positiveInfinitySection ℚ

def actualPicard : RelativePic0Designation ℚ (curveToBase ℚ) :=
  (Order13ActualIntegralPicardRepresentation.actual_integral_picard_representation ℚ
    (isUnit_iff_ne_zero.mpr (by norm_num : (104 : ℚ) ≠ 0))).choose

def actualRepresentation : RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroCut (curveToBase ℚ) infinitySection) actualPicard :=
  (Order13ActualIntegralPicardRepresentation.actual_integral_picard_representation ℚ
    (isUnit_iff_ne_zero.mpr (by norm_num : (104 : ℚ) ≠ 0))).choose_spec.1.some
end MazurTransfer.Order13ActualPicardDiamondSchemeEndomorphism
#print axioms MazurTransfer.Order13ActualPicardDiamondSchemeEndomorphism.actualRepresentation


