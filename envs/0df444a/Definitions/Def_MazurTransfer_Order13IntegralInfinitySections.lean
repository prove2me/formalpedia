-- Prove2me | Definitions.Def_MazurTransfer_Order13IntegralInfinitySections
-- name    : MazurTransfer_Order13IntegralInfinitySections
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T02:22:57.950814+00:00
-- url     : https://prove2.me/theorems/3d616b81-8d6e-4fba-8038-b53326d03a03
-- title:
--   Order-thirteen infinity sections from literal reciprocal-coordinate evaluation
-- statement:
--   For every commutative ring $R$, the reciprocal chart of the literal order-thirteen curve gives sections
--   $$s_+,s_-:\operatorname{Spec}R\longrightarrow C_R$$
--   by evaluating the reciprocal abscissa at $0$ and the ordinate at $1$ or $-1$. Both compose with $C_R\to\operatorname{Spec}R$ to the identity.
--
--   The interface reuses the already-published reciprocal evaluation and its coefficient compatibility, then provides only the scheme morphisms, their structural compatibility, and the two sections. The named downstream consumer is the actual integral Abel–Jacobi injection.
-- source:
--   Original literal constructors from MazurTheorem, Order13IntegralInfinitySections.lean. The reciprocal evaluation and its coefficient identity are reused from Definitions.Def_MazurTransfer_Order13InverseParameterChartComparison under InverseParameterChartComparisonLibrary. Exact original types and literal-lift value compatibility are independently checked. Apache-2.0.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: two actual infinity sections of the literal order-13 curve
for every commutative base ring, constructed from reciprocal coordinates.
Named downstream consumer: integral Picard representability with a section.
No rational-point classification or Picard representability is assumed.
-/
import Mathlib
import Definitions.Def_MazurTransfer_Order13ExplicitCurve
import Definitions.Def_MazurTransfer_Order13InverseParameterChartComparison
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier


noncomputable section
universe u
namespace MazurTransfer.Order13IntegralSections
open CategoryTheory AlgebraicGeometry Polynomial
open MazurTorsion.XOneThirteenProjectiveCurve
variable (R : Type u) [CommRing R]

noncomputable abbrev reciprocalInfinityEvaluation (a : R) (ha : a ^ 2 = 1) :
    ReciprocalRing R →+* R :=
  InverseParameterChartComparisonLibrary.MazurTransfer.Order13IntegralSections.reciprocalInfinityEvaluation R a ha

theorem reciprocalInfinityEvaluation_comp_algebraMap (a : R) (ha : a ^ 2 = 1) :
    (reciprocalInfinityEvaluation R a ha).comp
      (algebraMap R (ReciprocalRing R)) = RingHom.id R :=
  InverseParameterChartComparisonLibrary.MazurTransfer.Order13IntegralSections.reciprocalInfinityEvaluation_comp_algebraMap R a ha










noncomputable def infinityMorphism (a : R) (ha : a ^ 2 = 1) :
    Spec (.of R) ⟶ curveScheme R :=
  Spec.map (CommRingCat.ofHom (reciprocalInfinityEvaluation R a ha)) ≫ reciprocalChartMap R

theorem infinityMorphism_curveToBase (a : R) (ha : a ^ 2 = 1) :
    infinityMorphism R a ha ≫ curveToBase R = 𝟙 _ := by
  rw [infinityMorphism, Category.assoc, reciprocalChartMap_curveToBase]
  unfold reciprocalChartToBase
  rw [← Spec.map_comp]
  have h : CommRingCat.ofHom (algebraMap R (ReciprocalRing R)) ≫
      CommRingCat.ofHom (reciprocalInfinityEvaluation R a ha) = 𝟙 _ := by
    exact congrArg CommRingCat.ofHom
      (reciprocalInfinityEvaluation_comp_algebraMap R a ha)
  rw [h, Spec.map_id]

noncomputable def infinitySection (a : R) (ha : a ^ 2 = 1) :
    NeronModelInfra.SchemeHomOver (𝟙 (Spec (.of R))) (curveToBase R) :=
  ⟨infinityMorphism R a ha, infinityMorphism_curveToBase R a ha⟩

noncomputable def positiveInfinitySection :
    NeronModelInfra.SchemeHomOver (𝟙 (Spec (.of R))) (curveToBase R) :=
  infinitySection R 1 (by simp)

noncomputable def negativeInfinitySection :
    NeronModelInfra.SchemeHomOver (𝟙 (Spec (.of R))) (curveToBase R) :=
  infinitySection R (-1) (by simp)

end MazurTransfer.Order13IntegralSections
#print axioms MazurTransfer.Order13IntegralSections.infinityMorphism_curveToBase
#print axioms MazurTransfer.Order13IntegralSections.reciprocalInfinityEvaluation_comp_algebraMap
#print axioms MazurTransfer.Order13IntegralSections.positiveInfinitySection
#print axioms MazurTransfer.Order13IntegralSections.negativeInfinitySection


