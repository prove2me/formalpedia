-- Prove2me | Definitions.Def_MazurTransfer_Order13FiniteMapDataFromPublicCharts
-- name    : MazurTransfer_Order13FiniteMapDataFromPublicCharts
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T07:09:36.741034+00:00
-- url     : https://prove2.me/theorems/0d1e84bb-7a39-4b4e-8a7a-d9a96435a118
-- title:
--   Actual integral finite-map data of arbitrarily large degree for the order-thirteen curve
-- statement:
--   Let $R$ be a noetherian commutative integral domain with $104$ invertible. The literal order-thirteen curve, with its actual positive-infinity section, has the specified integral finite-map data of degree three. The two actual affine opens, structural parameter maps, exact overlap basic opens, reciprocal product and required finite free level sets are all retained. Raising both parameters to a positive power $n$ gives data of degree $3n$. In particular, for every $N\in\mathbb N$, $$\exists F:\operatorname{FiniteMapData}(C/R,\infty_+),\qquad N\leq\deg F.$$ This is the original arbitrary-degree input required by the integral Picard representability theorem.
-- source:
--   MazurTheorem, Apache-2.0, Vas and contributors. Complete actual integral FiniteMapData constructors from the two specified published affine-chart section comparisons and polynomial bases. All five chart cover, intersection, parameter basic-open and reciprocal-product inputs are Proved public theorems. Reuses the original official Anthropic FLT record and polynomial level-set equivalence at exact pin 6e837e75355538c7f80bab5b956861e86c4eacc2 through their public interfaces. The original degree-three constructor type, power-constructor type and complete arbitrary-degree existence contract are kernel-compared; both degree formulas and all five declarations are closed. No equality with an older selected first parameter or finite-map record is asserted. Native, strict and full frontend checks pass with standard axioms only. Named downstream consumer: the unchanged original actual integral Picard representation theorem.

/- Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Retains the original official Anthropic FLT FiniteMapData record and polynomial level-set construction at exact pin 6e837e75355538c7f80bab5b956861e86c4eacc2.
Design boundary: actual integral finite-map data of degree three and arbitrarily large degree for the literal order-thirteen curve and positive-infinity section, using the two specified public chart presentations and parameter sections.
Named downstream consumer: the unchanged original actual integral Picard representation theorem. The first chart uses its published selected presentation; no equality with an older selected parameter section or finite-map record is asserted. -/
import Mathlib
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData
import Definitions.Def_MazurTransfer_Order13FirstFiniteChartLevelSets
import Definitions.Def_MazurTransfer_Order13InverseFiniteChartPolynomialBasis
import Definitions.Def_MazurTransfer_PolynomialBasisPowerLevelSets
import Theorems.Thm_MazurTransfer_Order13SingleSectionTwoActualAffineCharts_actual_two_affine_open_cover
import Theorems.Thm_MazurTransfer_Order13InverseParameterFiniteAlgebra_actual_chart_intersection_opensRange
import Theorems.Thm_MazurTransfer_Order13FirstFiniteChartFromPublicTheorem_parameter_basicOpen
import Theorems.Thm_MazurTransfer_Order13InverseFiniteChartFromPublicTheorems_parameter_basicOpen
import Theorems.Thm_MazurTransfer_Order13PublicFiniteChartParameters_parameter_product
noncomputable section
universe u
open CategoryTheory AlgebraicGeometry Polynomial
open MazurTorsion.XOneThirteenProjectiveCurve
namespace MazurTransfer.Order13FiniteMapDataFromPublicCharts
open Order13InverseParameterFiniteAlgebra
variable (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]

def actualFiniteMapData (h104 : IsUnit (104 : R)) :
    SmoothProperCurve.FiniteMapData (curveToBase R)
      (Order13IntegralSections.positiveInfinitySection R) := by
  let U := Order13FirstFiniteChartFromPublicTheorem.chartOpen R
  let V := inverseChartOpen R
  have hInter : U ⊓ V = (ordinaryParameterCurveMap R).opensRange := by
    exact actual_chart_intersection_opensRange R h104
  exact {
    U := U
    V := V
    f := Order13FirstFiniteChartFromPublicTheorem.parameterSection R h104
    g := Order13InverseFiniteChartFromPublicTheorems.parameterSection R h104
    m := 3
    isAffineOpen_U := Order13FirstFiniteChartFromPublicTheorem.chartOpen_isAffine R h104
    isAffineOpen_V := inverseChartOpen_isAffineOpen R h104
    sup_eq_top := by exact Order13SingleSectionTwoActualAffineCharts.actual_two_affine_open_cover R h104
    mem_U_iff := Order13FirstFiniteChartFromPublicTheorem.mem_chartOpen_iff R h104
    inf_eq_basicOpen := hInter.trans
      (Order13FirstFiniteChartFromPublicTheorem.parameter_basicOpen R h104).symm
    inf_eq_basicOpen_g := hInter.trans
      (Order13InverseFiniteChartFromPublicTheorems.parameter_basicOpen R h104).symm
    res_f_mul_res_g := Order13PublicFiniteChartParameters.parameter_product R h104
    finite_f := Order13FirstFiniteChartFromPublicTheorem.parameter_finite R h104
    finite_g := Order13InverseFiniteChartFromPublicTheorems.parameter_finite R h104
    levelSet_free := fun S _ _ _ s =>
      Order13FirstFiniteChartFromPublicTheorem.levelSet_finite_free_finrank R S h104 s }

theorem actualFiniteMapData_degree (h104 : IsUnit (104 : R)) :
    (actualFiniteMapData R h104).m = 3 := rfl

def actualPowerFiniteMapData (h104 : IsUnit (104 : R)) (n : ℕ) (hn : n ≠ 0) :
    SmoothProperCurve.FiniteMapData (curveToBase R)
      (Order13IntegralSections.positiveInfinitySection R) := by
  let F := actualFiniteMapData R h104
  refine { F with
    f := F.f^n
    g := F.g^n
    m := n*3
    inf_eq_basicOpen := F.inf_eq_basicOpen.trans
      ((curveScheme R).basicOpen_pow F.f (Nat.pos_of_ne_zero hn)).symm
    inf_eq_basicOpen_g := F.inf_eq_basicOpen_g.trans
      ((curveScheme R).basicOpen_pow F.g (Nat.pos_of_ne_zero hn)).symm
    res_f_mul_res_g := ?_
    finite_f := ?_
    finite_g := ?_
    levelSet_free := ?_ }
  · rw [map_pow, map_pow, ← mul_pow, F.res_f_mul_res_g, one_pow]
  · letI := Scheme.TwoAffineOpenCover.algebraOfHom (curveToBase R)
      (Order13FirstFiniteChartFromPublicTheorem.chartOpen R)
    exact PolynomialBasisPowerLevelSets.parameter_power_finite R
      Γ(curveScheme R, Order13FirstFiniteChartFromPublicTheorem.chartOpen R) 3 n
      (Order13FirstFiniteChartFromPublicTheorem.parameterSection R h104)
      (Order13FirstFiniteChartFromPublicTheorem.polynomialBasis R h104) hn
  · letI := Scheme.TwoAffineOpenCover.algebraOfHom (curveToBase R) (inverseChartOpen R)
    exact PolynomialBasisPowerLevelSets.parameter_power_finite R
      Γ(curveScheme R, inverseChartOpen R) 3 n
      (Order13InverseFiniteChartFromPublicTheorems.parameterSection R h104)
      (Order13InverseFiniteChartFromPublicTheorems.polynomialBasis R h104) hn
  · intro S _ _ _ s
    letI := Scheme.TwoAffineOpenCover.algebraOfHom (curveToBase R)
      (Order13FirstFiniteChartFromPublicTheorem.chartOpen R)
    exact PolynomialBasisPowerLevelSets.powerLevelSet_finite_free_finrank R
      Γ(curveScheme R, Order13FirstFiniteChartFromPublicTheorem.chartOpen R) 3 n
      (Order13FirstFiniteChartFromPublicTheorem.parameterSection R h104)
      (Order13FirstFiniteChartFromPublicTheorem.polynomialBasis R h104) S hn s

theorem actualPowerFiniteMapData_degree (h104 : IsUnit (104 : R)) (n : ℕ) (hn : n ≠ 0) :
    (actualPowerFiniteMapData R h104 n hn).m = n*3 := rfl

end MazurTransfer.Order13FiniteMapDataFromPublicCharts

theorem MazurTransfer.Order13SingleSectionArbitrarilyLargeFiniteMapData.exists_actual_finiteMapData_degree_ge
    (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (h104 : IsUnit (104 : R)) (m₀ : ℕ) :
    ∃ F : SmoothProperCurve.FiniteMapData (curveToBase R)
      (MazurTransfer.Order13IntegralSections.positiveInfinitySection R), m₀ ≤ F.m := by
  refine ⟨MazurTransfer.Order13FiniteMapDataFromPublicCharts.actualPowerFiniteMapData R h104
    (m₀+1) (by omega), ?_⟩
  change m₀ ≤ (m₀+1)*3
  omega
#print axioms MazurTransfer.Order13FiniteMapDataFromPublicCharts.actualFiniteMapData
#print axioms MazurTransfer.Order13FiniteMapDataFromPublicCharts.actualPowerFiniteMapData
#print axioms MazurTransfer.Order13SingleSectionArbitrarilyLargeFiniteMapData.exists_actual_finiteMapData_degree_ge


