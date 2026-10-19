-- Prove2me | Definitions.Def_MazurTransfer_PicardGeometricFieldPointDegreeZeroConditionData
-- name    : MazurTransfer_PicardGeometricFieldPointDegreeZeroConditionData
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T19:01:55.439515+00:00
-- url     : https://prove2.me/theorems/89aa3321-cfd7-4d2e-b849-1e0f8c6cd2de
-- title:
--   Geometric field-point line bundles of a represented degree-zero Picard remain degree zero on a fibre model
-- statement:
--   Let C over a commutative ring R have a represented relative degree-zero Picard, let K be a field, and let X over K map over the base to the actual fibre of C. The line bundle associated to every K-valued Picard point is invertible and geometrically algebraically equivalent to zero. If X is a smooth, proper, geometrically integral curve, then
--
--   $$\chi_K(L_a)=\chi_K(\mathcal O_X).$$
--
--   The full original types retain the representation, fibre-model map and its commuting condition. These structural facts about the geometric line-bundle constructor feed the degree-zero divisor presentation of points on the existing rational order-13 Picard family.
-- source:
--   Complete original MazurTheorem PicardGeometricFieldPointDegreeZeroCondition, using the original geometric line-bundle constructor and the separately accepted arbitrary-field Euler criterion. Official Anthropic FLT relative Picard inputs at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: geometric field points of a represented degree-zero Picard
remain geometrically algebraically equivalent to zero on any fibre model
mapping over the field. Named downstream consumer: degree-zero divisor
presentations for geometric points of the existing rational order-13 Picard.
-/
import Definitions.Def_MazurTransfer_PicardCurvePullbackGeometricFieldLineBundleData
import Definitions.Def_MazurTransfer_LineBundleGeometricDegreeZeroData
import Theorems.Thm_MazurTransfer_LineBundleFieldComparison_geometricallyAlgEquivZero_iff_curveEulerChar_eq

noncomputable section
universe u
namespace MazurTransfer.PicardGeometricFieldPointDegreeZeroCondition
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard
open NeronModelInfra GoodReductionJacobian
open PicardCurvePullbackGeometricFieldLineBundle LineBundleFieldComparison
variable {R : Type u} [CommRing R] {K : Type u} [Field K]
    {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (D : RelativePic0Designation R c)
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R))
    {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of K)) (j : X ⟶ pullback c t)
    (hj : j ≫ pullback.snd c t = x)
    (a : SchemeHomOver t D.toBase)

theorem geometricPointLineBundle_isInvertible :
    Scheme.Modules.IsInvertible (geometricPointLineBundle c ε D h t j a) :=
  (h.poincare.pullbackAlong a).isInvertible.pullback j

include hj in
theorem geometricPointLineBundle_geometricallyAlgEquivZero :
    GeometricallyAlgEquivZero x (geometricPointLineBundle c ε D h t j a) := by
  intro L _ _ _
  let s := Scheme.TwoAffineOpenCover.specMap K L
  let P := (h.poincare.pullbackAlong a).L
  let f : pullback x s ⟶ pullback (pullback.snd c t) s :=
    pullback.lift (pullback.fst x s ≫ j) (pullback.snd x s)
      (by rw [Category.assoc, hj, pullback.condition])
  have hf : f ≫ fibreAt c t s = pullback.snd x s := pullback.lift_snd _ _ _
  have hfac : f ≫ pullback.fst (pullback.snd c t) s = pullback.fst x s ≫ j :=
    pullback.lift_fst _ _ _
  have hzero := (algEquivZeroCut c ε).pullback_mem _ _ a _ h.poincare_mem
  exact ((hzero L s).pullback f hf).of_iso
    ((Scheme.Modules.pullbackComp f (pullback.fst (pullback.snd c t) s)).app P ≪≫
      (Scheme.Modules.pullbackCongr hfac).app P ≪≫
      ((Scheme.Modules.pullbackComp (pullback.fst x s) j).app P).symm)

include hj in
theorem geometricPointLineBundle_curveEulerChar_eq
    [IsProper x] [SmoothOfRelativeDimension 1 x] [GeometricallyIntegral x]
    (𝒱 : X.TwoAffineOpenCover) :
    curveEulerChar x 𝒱 (geometricPointLineBundle c ε D h t j a) =
      curveEulerChar x 𝒱 (𝟙_ X.Modules) :=
  (geometricallyAlgEquivZero_iff_curveEulerChar_eq K x _
    (geometricPointLineBundle_isInvertible c ε D h t j a) 𝒱).mp
    (geometricPointLineBundle_geometricallyAlgEquivZero c ε D h t x j hj a)

end MazurTransfer.PicardGeometricFieldPointDegreeZeroCondition
#print axioms MazurTransfer.PicardGeometricFieldPointDegreeZeroCondition.geometricPointLineBundle_geometricallyAlgEquivZero
#print axioms MazurTransfer.PicardGeometricFieldPointDegreeZeroCondition.geometricPointLineBundle_curveEulerChar_eq


