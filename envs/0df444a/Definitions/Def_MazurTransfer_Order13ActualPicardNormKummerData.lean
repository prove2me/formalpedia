-- Prove2me | Definitions.Def_MazurTransfer_Order13ActualPicardNormKummerData
-- name    : MazurTransfer_Order13ActualPicardNormKummerData
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T21:56:42.077888+00:00
-- url     : https://prove2.me/theorems/c78bb140-d2b9-45aa-81ab-75093f102baa
-- title:
--   Original rational points, field-automorphism action and norm Kummer difference on the actual Picard
-- statement:
--   For the same actual rational represented Picard group scheme P, retain its rational-point type, the field-automorphism action on P(K) for each characteristic-zero field K, scalar extension of rational points, the point homomorphism induced by any internal monoid endomorphism, and the preimage-difference function. All five original full constructor types and all five values are preserved, together with the original group-object provider. The named downstream consumers are the actual norm Kummer cocycle existence theorems, Galois kernel modules and local conditions.
-- source:
--   Original MazurTheorem Order13ActualPicardNormKummerCocycles five data constructors, Apache-2.0. Design boundary: actual Picard point action, scalar extension, norm point homomorphism and preimage difference; named downstream consumers: original actual norm Kummer cocycles and Galois kernel action.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: rational points on the SAME represented Picard give
kernel-valued algebraic Galois cocycles for each actual norm map; the
kernels are killed by nineteen. This does not assert continuity, Galois
descent of fixed points, or a Selmer bound.
Named downstream consumer: continuous norm Kummer classes and local conditions.
-/
import Definitions.Def_MazurTransfer_Order13ActualPicardGeometricFieldPointsData
import Definitions.Def_MazurTransfer_Order13ActualPicardSchemeNineteenNormData
import Definitions.Def_MazurTransfer_FieldPointActionsAndNormPreimageDifferenceData
import Theorems.Thm_MazurTransfer_Order13ActualPicardSchemeNormGroupHom_schemePi_isMonHom
import Theorems.Thm_MazurTransfer_Order13ActualPicardSchemeNormGroupHom_schemePiConjugate_isMonHom

noncomputable section
namespace MazurTransfer.Order13ActualPicardNormKummerCocycles
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open GoodReductionJacobian NeronModelInfra
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13ActualPicardDiamondSchemeEndomorphism
open Order13ActualPicardSchemeNineteenNorm Order13ActualPicardSchemeNormGroupHom
open Order13ActualPicardGeometricNormPreimages
open scoped CategoryTheory.MonObj
local instance actualPicardNormKummerDataProvider120261017 : GrpObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).grpObj
local instance actualPicardNormKummerDataProvider220261017 : IsCommMonObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).isCommMonObj
local instance actualPicardNormKummerDataProvider320261017 : IsMonHom schemePi := schemePi_isMonHom
local instance actualPicardNormKummerDataProvider420261017 : IsMonHom schemePiConjugate := schemePiConjugate_isMonHom

variable (K : Type) [Field K] [CharZero K]
abbrev RationalPoints := Over.mk (𝟙 (Spec (CommRingCat.of ℚ))) ⟶ Over.mk actualPicard.toBase

def actionHom (σ : K ≃ₐ[ℚ] K) : Points K →* Points K :=
  FieldAutomorphismOverPointAction.actHom actualPicard.toBase σ

def rationalPoint (a : RationalPoints) : Points K :=
  FieldAutomorphismOverPointAction.rationalPoint actualPicard.toBase a

def normHom (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ] :
    Points K →* Points K := IsMonHom.monoidHom φ _

def difference (b : Points K) (σ : K ≃ₐ[ℚ] K) : Points K :=
  EquivariantNormPreimageCocycle.difference (actionHom K) b σ

end MazurTransfer.Order13ActualPicardNormKummerCocycles
#print axioms MazurTransfer.Order13ActualPicardNormKummerCocycles.RationalPoints
#print axioms MazurTransfer.Order13ActualPicardNormKummerCocycles.actionHom
#print axioms MazurTransfer.Order13ActualPicardNormKummerCocycles.rationalPoint
#print axioms MazurTransfer.Order13ActualPicardNormKummerCocycles.normHom
#print axioms MazurTransfer.Order13ActualPicardNormKummerCocycles.difference


