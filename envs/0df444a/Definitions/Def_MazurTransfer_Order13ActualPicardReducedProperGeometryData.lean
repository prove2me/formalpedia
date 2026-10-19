-- Prove2me | Definitions.Def_MazurTransfer_Order13ActualPicardReducedProperGeometryData
-- name    : MazurTransfer_Order13ActualPicardReducedProperGeometryData
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T19:48:34.434724+00:00
-- url     : https://prove2.me/theorems/7893b9de-6a0c-4906-9cbc-3710e11e40a1
-- title:
--   The same actual rational Picard scheme is smooth, proper, reduced and separated
-- statement:
--   For the existing rational Picard designation chosen from the original integral representation, retain the direct smoothness and properness projections of that same witness. Smoothness over Q gives reducedness of its underlying scheme, and properness gives separatedness of its structural morphism. All four complete original types are preserved; no new model or geometric hypothesis is substituted. The named downstream consumer is field-point extensionality for the actual diamond and nineteen-norm scheme endomorphisms.
-- source:
--   Complete original MazurTheorem Order13ActualPicardReducedProperGeometry, projecting the same actual_integral_picard_representation witness and applying the public smooth-over-field reducedness theorem. Official Anthropic FLT Picard representation inputs at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: smoothness and properness of the same existing rational
Picard designation imply reducedness and separatedness.
Named downstream consumer: field-point extensionality for its diamond
and nineteen-norm scheme endomorphisms.
-/
import Definitions.Def_MazurTransfer_Order13ActualPicardGenericFieldActionData
import Theorems.Thm_AlgebraicGeometry_isReduced_of_smooth_over_field

noncomputable section
namespace MazurTransfer.Order13ActualPicardReducedProperGeometry
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open Order13ActualPicardDiamondSchemeEndomorphism

theorem actualPicard_smooth : Smooth actualPicard.toBase :=
  (Order13ActualIntegralPicardRepresentation.actual_integral_picard_representation ℚ
    (isUnit_iff_ne_zero.mpr (by norm_num : (104 : ℚ) ≠ 0))).choose_spec.2.1

theorem actualPicard_proper : IsProper actualPicard.toBase :=
  (Order13ActualIntegralPicardRepresentation.actual_integral_picard_representation ℚ
    (isUnit_iff_ne_zero.mpr (by norm_num : (104 : ℚ) ≠ 0))).choose_spec.2.2.1

theorem actualPicard_reduced : IsReduced (Over.mk actualPicard.toBase).left :=
  AlgebraicGeometry.isReduced_of_smooth_over_field actualPicard_smooth

theorem actualPicard_separated : IsSeparated actualPicard.toBase := by
  letI := actualPicard_proper
  infer_instance

end MazurTransfer.Order13ActualPicardReducedProperGeometry
#print axioms MazurTransfer.Order13ActualPicardReducedProperGeometry.actualPicard_reduced
#print axioms MazurTransfer.Order13ActualPicardReducedProperGeometry.actualPicard_separated


