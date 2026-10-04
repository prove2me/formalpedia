-- Prove2me | Definitions.Def_ZetaNine_CoefficientMapAggregate
-- name    : ZetaNine_CoefficientMapAggregate
-- status  : Definition
-- author  : @Yuxuan Xu
-- created : 2026-10-03T21:52:30.418987+00:00
-- url     : https://prove2.me/theorems/0efd92c6-d434-4ba6-a512-c2371ad46b79
-- title:
--   Actual five rational outputs and quartic coordinate maps
-- statement:
--   For a natural number $n$ and a rational polynomial $W$, let $c^W_{n,j,s}$ be the actual weighted local coefficient, extracted at degree $9-s$ from the genuine cleared formal series. Use the existing exact rational definitions
--
--   $$\rho_{n,s}(W)=\sum_{j=0}^n c^W_{n,j,s},\qquad B_n(W)=-\sum_{j=0}^n\sum_{s=1}^9 c^W_{n,j,s}H_j^{(s)}.$$
--
--   Define the actual five-coordinate map, indexed by $\operatorname{Fin}(5)$ in the order displayed,
--
--   $$F_n(W)=(B_n(W),\rho_{n,3}(W),\rho_{n,5}(W),\rho_{n,7}(W),\rho_{n,9}(W)).$$
--
--   For $a\in\mathbb Q^5$, define $C(a)=\sum_{i=0}^4 a_iX^i$ and $\pi(W)_i=[X^i]W$. The other three definitions package $F_n$, $C$, and $F_n\circ C$ as rational linear maps, with their actual addition and scalar identities proved.
--
--   This is the genuine five-output aggregate, not the complete $(n+1)$-by-9 local coefficient array. Its definition assumes no properness, reflection, kernel triviality, rank or inverse. In particular $F_0(X^4)=0$ while $X^4\ne0$ and $\rho_{0,1}(X^4)=1$.
-- source:
--   Zeta(9) genuine five rational coefficient outputs and quartic coordinates: missions/zeta9/research/coefficient-map-aggregate-2026-10-04.md. Frozen missions/zeta9/formalization/CoefficientMapAggregate.lean SHA256 e538a7310f81ce9ab6c5e07d4b8bd64bb70be7a899e28f085a2c8506a4ff2299. The coefficients are extracted from the actual weighted local formal series; B is the actual finite negative harmonic constant.

import Definitions.Def_ZetaNine_CoefficientMapSummation
import Mathlib.Algebra.Polynomial.Eval.SMul
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset Polynomial

namespace ZetaNine.CoefficientMapAggregate

open scoped BigOperators
open Finset Polynomial
open CoefficientMapJet CoefficientMapInjectivity CoefficientMapReflection

def aggregate (n : ℕ) (W : ℚ[X]) (i : Fin 5) : ℚ :=
  match i.val with
  | 0 => CoefficientMapFiniteSum.constantTerm n W
  | 1 => CoefficientMapFiniteSum.rho n 3 W
  | 2 => CoefficientMapFiniteSum.rho n 5 W
  | 3 => CoefficientMapFiniteSum.rho n 7 W
  | _ => CoefficientMapFiniteSum.rho n 9 W

def coordinatePolynomial (a : Fin 5 → ℚ) : ℚ[X] :=
  ∑ i : Fin 5, C (a i) * X ^ i.val

def polynomialCoordinates (W : ℚ[X]) (i : Fin 5) : ℚ := W.coeff i.val

def aggregateLinearMap (n : ℕ) : ℚ[X] →ₗ[ℚ] (Fin 5 → ℚ) where
  toFun := aggregate n
  map_add' := ((by
    have actual_local_coefficient_add (n j s : ℕ) (W V : ℚ[X]) :
        weightedLocalCoefficient n j s (W + V) =
          weightedLocalCoefficient n j s W + weightedLocalCoefficient n j s V := by
      simp [weightedLocalCoefficient, weightedClearedSeries, add_comp, mul_add]
    have actual_rho_add (n s : ℕ) (W V : ℚ[X]) :
        CoefficientMapFiniteSum.rho n s (W + V) =
          CoefficientMapFiniteSum.rho n s W + CoefficientMapFiniteSum.rho n s V := by
      simp [CoefficientMapFiniteSum.rho, actual_local_coefficient_add, Finset.sum_add_distrib]
    have actual_constant_add (n : ℕ) (W V : ℚ[X]) :
        CoefficientMapFiniteSum.constantTerm n (W + V) =
          CoefficientMapFiniteSum.constantTerm n W + CoefficientMapFiniteSum.constantTerm n V := by
      simp only [CoefficientMapFiniteSum.constantTerm, actual_local_coefficient_add, add_mul,
        Finset.sum_add_distrib]
      ring
    have aggregate_add (n : ℕ) (W V : ℚ[X]) :
        aggregate n (W + V) = aggregate n W + aggregate n V := by
      funext i
      fin_cases i <;> simp [aggregate, actual_constant_add, actual_rho_add]
    exact aggregate_add) :
    (∀ (n : ℕ) (W V : ℚ[X]),
      ZetaNine.CoefficientMapAggregate.aggregate n (W + V) =
        ZetaNine.CoefficientMapAggregate.aggregate n W + ZetaNine.CoefficientMapAggregate.aggregate n V)) n
  map_smul' := ((by
    have actual_local_coefficient_smul (n j s : ℕ) (a : ℚ) (W : ℚ[X]) :
        weightedLocalCoefficient n j s (a • W) = a * weightedLocalCoefficient n j s W := by
      simp [weightedLocalCoefficient, weightedClearedSeries, smul_comp, smul_eq_mul]
    have actual_rho_smul (n s : ℕ) (a : ℚ) (W : ℚ[X]) :
        CoefficientMapFiniteSum.rho n s (a • W) = a * CoefficientMapFiniteSum.rho n s W := by
      simp [CoefficientMapFiniteSum.rho, actual_local_coefficient_smul, Finset.mul_sum]
    have actual_constant_smul (n : ℕ) (a : ℚ) (W : ℚ[X]) :
        CoefficientMapFiniteSum.constantTerm n (a • W) = a * CoefficientMapFiniteSum.constantTerm n W := by
      simp [CoefficientMapFiniteSum.constantTerm, actual_local_coefficient_smul, mul_assoc,
        Finset.mul_sum]
    have aggregate_smul (n : ℕ) (a : ℚ) (W : ℚ[X]) :
        aggregate n (a • W) = a • aggregate n W := by
      funext i
      fin_cases i <;> simp [aggregate, actual_constant_smul, actual_rho_smul, smul_eq_mul]
    exact aggregate_smul) :
    (∀ (n : ℕ) (a : ℚ) (W : ℚ[X]),
      ZetaNine.CoefficientMapAggregate.aggregate n (a • W) = a • ZetaNine.CoefficientMapAggregate.aggregate n W)) n

def coordinateLinearMap : (Fin 5 → ℚ) →ₗ[ℚ] ℚ[X] where
  toFun := coordinatePolynomial
  map_add' := ((by
    have coordinatePolynomial_add (a b : Fin 5 → ℚ) :
        coordinatePolynomial (a + b) = coordinatePolynomial a + coordinatePolynomial b := by
      simp [coordinatePolynomial, C_add, add_mul, Finset.sum_add_distrib]
    exact coordinatePolynomial_add) :
    (∀ (a b : Fin 5 → ℚ),
      ZetaNine.CoefficientMapAggregate.coordinatePolynomial (a + b) =
        ZetaNine.CoefficientMapAggregate.coordinatePolynomial a + ZetaNine.CoefficientMapAggregate.coordinatePolynomial b))
  map_smul' := ((by
    have coordinatePolynomial_smul (c : ℚ) (a : Fin 5 → ℚ) :
        coordinatePolynomial (c • a) = c • coordinatePolynomial a := by
      simp [coordinatePolynomial, smul_eq_mul, C_mul, mul_assoc, smul_eq_C_mul,
        Finset.mul_sum]
    exact coordinatePolynomial_smul) :
    (∀ (c : ℚ) (a : Fin 5 → ℚ),
      ZetaNine.CoefficientMapAggregate.coordinatePolynomial (c • a) =
        c • ZetaNine.CoefficientMapAggregate.coordinatePolynomial a))

def quarticAggregateLinearMap (n : ℕ) : (Fin 5 → ℚ) →ₗ[ℚ] (Fin 5 → ℚ) :=
  (aggregateLinearMap n).comp coordinateLinearMap

end ZetaNine.CoefficientMapAggregate


