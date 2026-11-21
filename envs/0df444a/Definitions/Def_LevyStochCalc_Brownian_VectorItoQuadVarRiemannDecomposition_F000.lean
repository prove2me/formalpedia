-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_VectorItoQuadVarRiemannDecomposition_F000
-- name    : LevyStochCalc_Brownian_VectorItoQuadVarRiemannDecomposition_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:40:56.490459+00:00
-- url     : https://prove2.me/theorems/5ca68730-a27f-4e9f-98fb-2c8a64364c57
-- title:
--   Source declarations: LevyStochCalc.Brownian.VectorItoQuadVarRiemannDecomposition
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.VectorItoQuadVarRiemannDecomposition. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_VectorItoProcessVersion_F000
import Definitions.Def_LevyStochCalc_Brownian_VectorItoQuadVarRiemannTermBounds_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Decomposition and convergence of the quadratic-variation Riemann sum

The product of the increments of two coordinates of a continuous vector Itô process splits into a
drift–drift term, two drift–martingale terms and the product of the increments of the martingale
parts, and the last splits further into the compensated products on the diagonal in the Brownian
index, their compensators, and the cross terms off that diagonal. Weighting the products by a
bounded continuous function of the process frozen at the left endpoint of each cell of a uniform
grid, the five error terms are `O(m^{-1/2})` in `L¹` and the sixth group is a frozen-weight
Riemann sum for `∫_0^T φ(X_s)·(∑ₖ H^{p,k}_s H^{q,k}_s) ds`, so the weighted Riemann sum converges
in `L¹` to that integral at rate `√(T/m)`.

## Main statements

* `LevyStochCalc.Brownian.Ito.IsVectorItoVersion.prod_sub_ae` — the product of the increments of
  two coordinates.
* `LevyStochCalc.Brownian.Ito.IsVectorItoVersion.quadVarRiemann_decomp_ae` — the decomposition of
  the weighted product sum into six groups.
* `LevyStochCalc.Brownian.Ito.IsVectorItoVersion.integral_abs_quadVarRiemann_sub_le` — the `L¹`
  rate of convergence of the weighted quadratic-variation Riemann sum.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

section VectorQuadVar

open LevyStochCalc.Brownian.Multidim

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} {W : Multidim.MultidimBrownianMotion P d}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ}
  {H : Fin n → Fin d → Ω → ℝ → ℝ}
  {hHm : ∀ m k, Measurable (Function.uncurry (H m k))}
  {hHp : ∀ m k, Probability.ProgressivelyMeasurable ℱ (H m k)}
  {hHs : ∀ (m : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H m k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
  {X₀ : Ω → Fin n → ℝ} {bdrift : Fin n → Ω → ℝ → ℝ} {X : ℝ → Ω → Fin n → ℝ}
  {C : ℝ} (hC0 : 0 ≤ C)
  (hCH : ∀ (m : Fin n) (k : Fin d) (ω : Ω) (s : ℝ), |H m k ω s| ≤ C)

/-- The product of the increments of two coordinates splits into a drift–drift term, two
drift–martingale terms and the product of the martingale parts. -/
theorem IsVectorItoVersion.prod_sub_ae
    (h : IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift X)
    (hbm : ∀ m, Measurable (Function.uncurry (bdrift m))) {B : ℝ}
    (hB : ∀ (m : Fin n) (ω : Ω) (s : ℝ), |bdrift m ω s| ≤ B) (p q : Fin n)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) :
    ∀ᵐ ω ∂P, (X v ω p - X u ω p) * (X v ω q - X u ω q)
      = (∫ s in Set.Ioc u v, bdrift p ω s ∂volume)
          * (∫ s in Set.Ioc u v, bdrift q ω s ∂volume)
        + (∫ s in Set.Ioc u v, bdrift p ω s ∂volume)
          * (vectorItoMartingale W ℱ hcoord H hHm hHp hHs q v ω
            - vectorItoMartingale W ℱ hcoord H hHm hHp hHs q u ω)
        + (∫ s in Set.Ioc u v, bdrift q ω s ∂volume)
          * (vectorItoMartingale W ℱ hcoord H hHm hHp hHs p v ω
            - vectorItoMartingale W ℱ hcoord H hHm hHp hHs p u ω)
        + (vectorItoMartingale W ℱ hcoord H hHm hHp hHs p v ω
            - vectorItoMartingale W ℱ hcoord H hHm hHp hHs p u ω)
          * (vectorItoMartingale W ℱ hcoord H hHm hHp hHs q v ω
            - vectorItoMartingale W ℱ hcoord H hHm hHp hHs q u ω) := by
  filter_upwards [h.sub_ae hbm hB hu huv p, h.sub_ae hbm hB hu huv q] with ω e1 e2
  rw [e1, e2]
  ring
end VectorQuadVar

end LevyStochCalc.Brownian.Ito


