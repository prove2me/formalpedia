-- Prove2me | Definitions.Def_MazurTransfer_Order13ActualPicardDiamondAcceptedIsomorphism
-- name    : MazurTransfer_Order13ActualPicardDiamondAcceptedIsomorphism
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T11:41:03.150979+00:00
-- url     : https://prove2.me/theorems/fcc7cccc-9d31-4df5-8442-9940a3bf114c
-- title:
--   The actual Picard diamond morphism is an isomorphism
-- statement:
--   The actual Picard diamond scheme endomorphism induced by inverse-curve re-rigidified pullback is an isomorphism: $$\Delta:J\simeq J.$$ This is the original direct specialization of the Proved general Picard pullback-isomorphism contract to the literal rational curve and its actual represented Picard scheme.
-- source:
--   Original complete one-declaration contract and proof from MazurTheorem Order13ActualPicardDiamondAcceptedIsomorphism.lean, Apache-2.0, Vas and contributors. The complete original closed type is kernel-compared; the original proof body is unchanged. Consumes the Proved original general Picard pullback isomorphism contract. Named downstream consumer: genuine Picard scheme norm descent.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: consume the exact Accepted public Picard pullback
isomorphism contract on the actual order-13 scheme group endomorphism.
Named downstream consumer: genuine scheme endomorphism norm descent.
-/
import Definitions.Def_MazurTransfer_Order13ActualPicardDiamondSchemeEndomorphism
import Theorems.Thm_MazurTransfer_picard_pullback_isIso_of_curve_iso

noncomputable section
namespace MazurTransfer.Order13ActualPicardDiamondAcceptedIsomorphism
open CategoryTheory AlgebraicGeometry
open Order13ActualDiamondCurveAutomorphism Order13ActualPicardDiamondSchemeEndomorphism

theorem actualDiamondHom_isIso_from_public_contract : IsIso actualDiamondHom.1 :=
  MazurTransfer.picard_pullback_isIso_of_curve_iso actualRepresentation
    diamondCurveIso diamondCurveIso_over diamondCurveIso_inv_over
    actualDiamondHom actualDiamondAction.classifies

end MazurTransfer.Order13ActualPicardDiamondAcceptedIsomorphism
#print axioms MazurTransfer.Order13ActualPicardDiamondAcceptedIsomorphism.actualDiamondHom_isIso_from_public_contract


