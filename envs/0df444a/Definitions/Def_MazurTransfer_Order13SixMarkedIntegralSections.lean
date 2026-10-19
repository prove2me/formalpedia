-- Prove2me | Definitions.Def_MazurTransfer_Order13SixMarkedIntegralSections
-- name    : MazurTransfer_Order13SixMarkedIntegralSections
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T04:38:50.108519+00:00
-- url     : https://prove2.me/theorems/f067bd10-8d4f-47fc-b6d9-56184aac7807
-- title:
--   The six actual marked integral sections of the order-thirteen curve
-- statement:
--   Let $R$ be any commutative ring. On the actual projective order-thirteen curve $C_R$, the six marked sections are $$\infty^+,\quad\infty^-,\quad(0,1),\quad(0,-1),\quad(-1,1),\quad(-1,-1).$$ The four ordinary sections are defined by evaluation of the original coordinate algebra, and the two infinity sections are the previously specified actual sections. The sextic takes value one at both zero and minus one, so these evaluations satisfy the curve equation. Every section composes with the structure morphism to the identity on $\operatorname{Spec}R$. This interface supplies the actual section family for the integral Picard chart construction; distinctness and chart existence are separate theorems.
-- source:
--   The complete fifteen unchanged declarations of checked MazurTheorem Order13SixMarkedIntegralSections.lean, with only its broad import replaced by the public actual infinity-sections interface using the complete Lean frontend header range. Every complete original kernel type, including the private equation-evaluation helper, is checked by a closed witness. Constructor and structural proof bodies are byte-for-byte unchanged. Original per-file attribution and Apache-2.0 are retained. Vas and contributors.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: six explicitly constructed sections of the actual curve
family over every commutative base ring, at infinity and x=0,-1.
Named downstream consumer: a uniform chart-section construction for the
actual integral Picard family. Distinctness, chart coverage and rational
point exhaustion are separate assertions, not assumed here.
-/
import Definitions.Def_MazurTransfer_Order13IntegralInfinitySections


noncomputable section
universe u
namespace MazurTransfer.Order13IntegralSections
open CategoryTheory AlgebraicGeometry Polynomial
open MazurTorsion.XOneThirteenAffineCurve
open MazurTorsion.XOneThirteenProjectiveCurve
variable (R : Type u) [CommRing R]

private theorem ordinaryEquation_eval (t a : R)
    (ha : a ^ 2 = (sexticPolynomial R).eval t) :
    (affineEquation R).eval₂ (Polynomial.evalRingHom t) a = 0 := by
  simp [affineEquation, ha, eval₂_pow, eval₂_C]

noncomputable def ordinaryEvaluation (t a : R)
    (ha : a ^ 2 = (sexticPolynomial R).eval t) : CoordinateRing R →+* R :=
  AdjoinRoot.lift (Polynomial.evalRingHom t) a (ordinaryEquation_eval R t a ha)

theorem ordinaryEvaluation_x (t a : R) (ha : a ^ 2 = (sexticPolynomial R).eval t) :
    ordinaryEvaluation R t a ha (xCoordinate R) = t := by
  simp [ordinaryEvaluation, xCoordinate, AdjoinRoot.lift_of]

theorem ordinaryEvaluation_y (t a : R) (ha : a ^ 2 = (sexticPolynomial R).eval t) :
    ordinaryEvaluation R t a ha (yCoordinate R) = a := by
  simp [ordinaryEvaluation, yCoordinate, AdjoinRoot.lift_root]

theorem ordinaryEvaluation_comp_algebraMap (t a : R)
    (ha : a ^ 2 = (sexticPolynomial R).eval t) :
    (ordinaryEvaluation R t a ha).comp (algebraMap R (CoordinateRing R)) =
    RingHom.id R := by
  ext r
  simp [ordinaryEvaluation, AdjoinRoot.algebraMap_eq', AdjoinRoot.lift_of]

noncomputable def ordinaryMorphism (t a : R)
    (ha : a ^ 2 = (sexticPolynomial R).eval t) : Spec (.of R) ⟶ curveScheme R :=
  Spec.map (CommRingCat.ofHom (ordinaryEvaluation R t a ha)) ≫ ordinaryChartMap R

theorem ordinaryMorphism_curveToBase (t a : R)
    (ha : a ^ 2 = (sexticPolynomial R).eval t) :
    ordinaryMorphism R t a ha ≫ curveToBase R = 𝟙 _ := by
  rw [ordinaryMorphism, Category.assoc, ordinaryChartMap_curveToBase]
  unfold ordinaryChartToBase
  rw [← Spec.map_comp]
  have h : CommRingCat.ofHom (algebraMap R (CoordinateRing R)) ≫
      CommRingCat.ofHom (ordinaryEvaluation R t a ha) = 𝟙 _ := by
    exact congrArg CommRingCat.ofHom (ordinaryEvaluation_comp_algebraMap R t a ha)
  rw [h, Spec.map_id]

noncomputable def ordinarySection (t a : R)
    (ha : a ^ 2 = (sexticPolynomial R).eval t) :
    NeronModelInfra.SchemeHomOver (𝟙 (Spec (.of R))) (curveToBase R) :=
  ⟨ordinaryMorphism R t a ha, ordinaryMorphism_curveToBase R t a ha⟩

theorem sextic_eval_zero : (sexticPolynomial R).eval 0 = 1 := by
  simp [sexticPolynomial]

theorem sextic_eval_neg_one : (sexticPolynomial R).eval (-1) = 1 := by
  norm_num [sexticPolynomial, eval_add, eval_mul, eval_pow, eval_X]

noncomputable def zeroPositiveSection :
    NeronModelInfra.SchemeHomOver (𝟙 (Spec (.of R))) (curveToBase R) :=
  ordinarySection R 0 1 (by rw [sextic_eval_zero]; simp)

noncomputable def zeroNegativeSection :
    NeronModelInfra.SchemeHomOver (𝟙 (Spec (.of R))) (curveToBase R) :=
  ordinarySection R 0 (-1) (by rw [sextic_eval_zero]; simp)

noncomputable def negOnePositiveSection :
    NeronModelInfra.SchemeHomOver (𝟙 (Spec (.of R))) (curveToBase R) :=
  ordinarySection R (-1) 1 (by rw [sextic_eval_neg_one]; simp)

noncomputable def negOneNegativeSection :
    NeronModelInfra.SchemeHomOver (𝟙 (Spec (.of R))) (curveToBase R) :=
  ordinarySection R (-1) (-1) (by rw [sextic_eval_neg_one]; simp)

noncomputable def sixMarkedSections : Fin 6 →
    NeronModelInfra.SchemeHomOver (𝟙 (Spec (.of R))) (curveToBase R) :=
  ![positiveInfinitySection R, negativeInfinitySection R,
    zeroPositiveSection R, zeroNegativeSection R,
    negOnePositiveSection R, negOneNegativeSection R]

end MazurTransfer.Order13IntegralSections
#print axioms MazurTransfer.Order13IntegralSections.ordinaryMorphism_curveToBase
#print axioms MazurTransfer.Order13IntegralSections.sixMarkedSections


