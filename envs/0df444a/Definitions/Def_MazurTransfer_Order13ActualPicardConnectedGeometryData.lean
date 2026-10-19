-- Prove2me | Definitions.Def_MazurTransfer_Order13ActualPicardConnectedGeometryData
-- name    : MazurTransfer_Order13ActualPicardConnectedGeometryData
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T20:38:24.238814+00:00
-- url     : https://prove2.me/theorems/712b164e-46c4-40dd-bbe3-3ea3055519c2
-- title:
--   The same actual rational Picard scheme is geometrically connected and connected
-- statement:
--   The same actual rational Picard designation chosen from the original integral representation is geometrically connected over Q, and its underlying scheme is connected. Both complete original declarations are preserved, using the same integral representation witness and no replacement model. The named downstream consumer is flatness and surjectivity of the actual Picard norm-nineteen factors.
-- source:
--   Complete original MazurTheorem Order13ActualPicardConnectedGeometry, retaining both original statements and proofs and the same actual integral Picard representation witness. Official Anthropic FLT Picard representation inputs at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: geometric connectedness of the SAME existing rational
represented Picard gives connectedness of its actual underlying scheme.
Named downstream consumer: flat norm endomorphisms and surjectivity of
finite etale norm isogenies.
-/
import Definitions.Def_MazurTransfer_Order13ActualPicardReducedProperGeometryData

noncomputable section
namespace MazurTransfer.Order13ActualPicardConnectedGeometry
open CategoryTheory AlgebraicGeometry
open Order13ActualPicardDiamondSchemeEndomorphism Order13ActualPicardReducedProperGeometry

theorem actualPicard_geometricallyConnected : GeometricallyConnected actualPicard.toBase :=
  (Order13ActualIntegralPicardRepresentation.actual_integral_picard_representation ℚ
    (isUnit_iff_ne_zero.mpr (by norm_num : (104 : ℚ) ≠ 0))).choose_spec.2.2.2

theorem actualPicard_connected : ConnectedSpace actualPicard.P := by
  letI : GeometricallyConnected actualPicard.toBase := actualPicard_geometricallyConnected
  exact GeometricallyConnected.connectedSpace_of_subsingleton (f := actualPicard.toBase)

end MazurTransfer.Order13ActualPicardConnectedGeometry
#print axioms MazurTransfer.Order13ActualPicardConnectedGeometry.actualPicard_connected


