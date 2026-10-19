-- Prove2me | Definitions.Def_MazurTransfer_Order13ActualPicardRationalFixedPointGroupData
-- name    : MazurTransfer_Order13ActualPicardRationalFixedPointGroupData
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T22:01:43.513094+00:00
-- url     : https://prove2.me/theorems/ac4c84cb-2c54-474e-b594-45f2a066386b
-- title:
--   Rational-to-fixed point homomorphism for the same actual rational Picard
-- statement:
--   Let P be the same actual rational represented Picard group scheme and K a characteristic-zero field. Retain scalar extension as a group homomorphism from P(Q) to P(K), the subgroup fixed by every Q-automorphism of K, and the induced homomorphism from rational points into that subgroup. All three complete original constructor types and values are preserved, with the original group-object provider. The named downstream consumers are the original rational-to-fixed bijectivity theorem, its multiplicative equivalence, and actual norm Kummer injectivity.
-- source:
--   Original MazurTheorem Order13ActualPicardGaloisFixedPointDescent rationalPointHom, fixedPointGroup and rationalToFixed constructors, Apache-2.0. Design boundary: actual rational/fixed point group maps. Named downstream consumers: rationalToFixed_bijective, rationalPointsFixedEquiv, and actual norm Kummer injectivity.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: rational points of the SAME represented Picard are
exactly its Galois-fixed geometric points, with their actual group law.
Named downstream consumer: algebraic norm Kummer injectivity.
-/
import Definitions.Def_MazurTransfer_Order13ActualPicardNormKummerData
noncomputable section
namespace MazurTransfer.Order13ActualPicardGaloisFixedPointDescent
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open GoodReductionJacobian NeronModelInfra
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13ActualPicardDiamondSchemeEndomorphism
open Order13ActualPicardSchemeNineteenNorm Order13ActualPicardSchemeNormGroupHom
open Order13ActualPicardGeometricNormPreimages
open Order13ActualPicardNormKummerCocycles
open scoped CategoryTheory.MonObj
local instance rationalFixedPointDataProvider120261017 : GrpObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).grpObj
local instance rationalFixedPointDataProvider220261017 : IsCommMonObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).isCommMonObj
local instance rationalFixedPointDataProvider320261017 : IsMonHom schemePi := schemePi_isMonHom
local instance rationalFixedPointDataProvider420261017 : IsMonHom schemePiConjugate := schemePiConjugate_isMonHom

variable (K : Type) [Field K] [CharZero K]
def rationalPointHom : RationalPoints →* Points K where
  toFun := rationalPoint K
  map_one' := MonObj.comp_one _
  map_mul' a b := MonObj.comp_mul _ a b

def fixedPointGroup : Subgroup (Points K) where
  carrier := {b | ∀ σ : K ≃ₐ[ℚ] K, actionHom K σ b = b}
  one_mem' σ := map_one (actionHom K σ)
  mul_mem' hx hy σ := by rw [map_mul, hx σ, hy σ]
  inv_mem' hx σ := by rw [map_inv, hx σ]

def rationalToFixed : RationalPoints →* fixedPointGroup K where
  toFun a := ⟨rationalPoint K a,
    fun σ => FieldAutomorphismOverPointAction.rationalPoint_fixed actualPicard.toBase σ a⟩
  map_one' := Subtype.ext (map_one (rationalPointHom K))
  map_mul' a b := Subtype.ext (map_mul (rationalPointHom K) a b)

end MazurTransfer.Order13ActualPicardGaloisFixedPointDescent
#print axioms MazurTransfer.Order13ActualPicardGaloisFixedPointDescent.rationalPointHom
#print axioms MazurTransfer.Order13ActualPicardGaloisFixedPointDescent.fixedPointGroup
#print axioms MazurTransfer.Order13ActualPicardGaloisFixedPointDescent.rationalToFixed


