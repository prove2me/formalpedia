-- Prove2me | Definitions.Def_SourceProof_1566953c59c85fa51b459ad0
-- name    : SourceProof_1566953c59c85fa51b459ad0
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:39:55.761284+00:00
-- url     : https://prove2.me/theorems/cd421b0c-c869-4f15-9e49-6f2ef5c416ef
-- title:
--   LevyStochCalc source module: SourceProof_1566953c59c85fa51b459ad0
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.vectorItoMartingale_prod_eq` comes from the `LevyStochCalc.Brownian.VectorItoQuadVarRiemannDecomposition` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_VectorItoProcess_F001
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

include hC0 hCH in

theorem _root_.Prove2MeSourceProof.h_1566953c59c85fa51b459ad0 (p q : Fin n) {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (ω : Ω) :
    (vectorItoMartingale W ℱ hcoord H hHm hHp hHs p v ω
        - vectorItoMartingale W ℱ hcoord H hHm hHp hHs p u ω)
      * (vectorItoMartingale W ℱ hcoord H hHm hHp hHs q v ω
        - vectorItoMartingale W ℱ hcoord H hHm hHp hHs q u ω)
      = (∑ k : Fin d, polarQuadVarIncrement (W.W k) ℱ (hcoord k) (H p k) (H q k) (hHm p k)
            (hHm q k) (hHp p k) (hHp q k) (hHs p k) (hHs q k) u v ω)
        + (∑ k : Fin d, ∫ s in Set.Ioc u v, H p k ω s * H q k ω s ∂volume)
        + ∑ k : Fin d, ∑ l ∈ Finset.univ.erase k,
            crossIncrement W hcoord (hHm p k) (hHp p k) (hHs p k) (hHm q l) (hHp q l)
              (hHs q l) k l u v ω := by
  have hcomp : ∀ k : Fin d,
      (∫ s in Set.Icc (0 : ℝ) v, H p k ω s * H q k ω s ∂volume)
        - ∫ s in Set.Icc (0 : ℝ) u, H p k ω s * H q k ω s ∂volume
      = ∫ s in Set.Ioc u v, H p k ω s * H q k ω s ∂volume := by
    intro k
    refine LevyStochCalc.setIntegral_Icc_sub_Icc (B := C ^ 2)
      ((Measurable.of_uncurry_left (hHm p k)).mul (Measurable.of_uncurry_left (hHm q k)))
      (fun s => ?_) hu huv
    change |H p k ω s * H q k ω s| ≤ C ^ 2
    rw [abs_mul, pow_two]
    exact mul_le_mul (hCH p k ω s) (hCH q k ω s) (abs_nonneg _) hC0
  have key : ∀ k : Fin d,
      (∑ l : Fin d, (LevyStochCalc.Brownian.Ito.coordItoIntegral W ℱ hcoord H hHm hHp hHs p k v ω
          - LevyStochCalc.Brownian.Ito.coordItoIntegral W ℱ hcoord H hHm hHp hHs p k u ω)
        * (LevyStochCalc.Brownian.Ito.coordItoIntegral W ℱ hcoord H hHm hHp hHs q l v ω
          - LevyStochCalc.Brownian.Ito.coordItoIntegral W ℱ hcoord H hHm hHp hHs q l u ω))
      = LevyStochCalc.Brownian.Ito.polarQuadVarIncrement (W.W k) ℱ (hcoord k) (H p k) (H q k) (hHm p k) (hHm q k)
          (hHp p k) (hHp q k) (hHs p k) (hHs q k) u v ω
        + (∫ s in Set.Ioc u v, H p k ω s * H q k ω s ∂volume)
        + ∑ l ∈ Finset.univ.erase k,
            LevyStochCalc.Brownian.Ito.crossIncrement W hcoord (hHm p k) (hHp p k) (hHs p k) (hHm q l) (hHp q l)
              (hHs q l) k l u v ω := by
    intro k
    have hcross : ∀ l : Fin d,
        (LevyStochCalc.Brownian.Ito.coordItoIntegral W ℱ hcoord H hHm hHp hHs p k v ω
            - LevyStochCalc.Brownian.Ito.coordItoIntegral W ℱ hcoord H hHm hHp hHs p k u ω)
          * (LevyStochCalc.Brownian.Ito.coordItoIntegral W ℱ hcoord H hHm hHp hHs q l v ω
            - LevyStochCalc.Brownian.Ito.coordItoIntegral W ℱ hcoord H hHm hHp hHs q l u ω)
        = LevyStochCalc.Brownian.Ito.crossIncrement W hcoord (hHm p k) (hHp p k) (hHs p k) (hHm q l) (hHp q l)
            (hHs q l) k l u v ω := fun l => rfl
    simp only [hcross]
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ k)]
    have hdiag : LevyStochCalc.Brownian.Ito.crossIncrement W hcoord (hHm p k) (hHp p k) (hHs p k) (hHm q k) (hHp q k)
          (hHs q k) k k u v ω
        = LevyStochCalc.Brownian.Ito.polarQuadVarIncrement (W.W k) ℱ (hcoord k) (H p k) (H q k) (hHm p k) (hHm q k)
            (hHp p k) (hHp q k) (hHs p k) (hHs q k) u v ω
          + ∫ s in Set.Ioc u v, H p k ω s * H q k ω s ∂volume := by
      simp only [LevyStochCalc.Brownian.Ito.crossIncrement, LevyStochCalc.Brownian.Ito.polarQuadVarIncrement]
      rw [← hcomp k]
      ring
    rw [hdiag]
  calc (LevyStochCalc.Brownian.Ito.vectorItoMartingale W ℱ hcoord H hHm hHp hHs p v ω
          - LevyStochCalc.Brownian.Ito.vectorItoMartingale W ℱ hcoord H hHm hHp hHs p u ω)
        * (LevyStochCalc.Brownian.Ito.vectorItoMartingale W ℱ hcoord H hHm hHp hHs q v ω
          - LevyStochCalc.Brownian.Ito.vectorItoMartingale W ℱ hcoord H hHm hHp hHs q u ω)
      = (∑ k : Fin d, (LevyStochCalc.Brownian.Ito.coordItoIntegral W ℱ hcoord H hHm hHp hHs p k v ω
            - LevyStochCalc.Brownian.Ito.coordItoIntegral W ℱ hcoord H hHm hHp hHs p k u ω))
          * ∑ l : Fin d, (LevyStochCalc.Brownian.Ito.coordItoIntegral W ℱ hcoord H hHm hHp hHs q l v ω
            - LevyStochCalc.Brownian.Ito.coordItoIntegral W ℱ hcoord H hHm hHp hHs q l u ω) := by
        rw [LevyStochCalc.Brownian.Ito.vectorItoMartingale_sub W ℱ hcoord H hHm hHp hHs p u v,
          LevyStochCalc.Brownian.Ito.vectorItoMartingale_sub W ℱ hcoord H hHm hHp hHs q u v]
    _ = ∑ k : Fin d, ∑ l : Fin d, (LevyStochCalc.Brownian.Ito.coordItoIntegral W ℱ hcoord H hHm hHp hHs p k v ω
          - LevyStochCalc.Brownian.Ito.coordItoIntegral W ℱ hcoord H hHm hHp hHs p k u ω)
        * (LevyStochCalc.Brownian.Ito.coordItoIntegral W ℱ hcoord H hHm hHp hHs q l v ω
          - LevyStochCalc.Brownian.Ito.coordItoIntegral W ℱ hcoord H hHm hHp hHs q l u ω) := Finset.sum_mul_sum _ _ _ _
    _ = ∑ k : Fin d, (LevyStochCalc.Brownian.Ito.polarQuadVarIncrement (W.W k) ℱ (hcoord k) (H p k) (H q k) (hHm p k)
            (hHm q k) (hHp p k) (hHp q k) (hHs p k) (hHs q k) u v ω
          + (∫ s in Set.Ioc u v, H p k ω s * H q k ω s ∂volume)
          + ∑ l ∈ Finset.univ.erase k,
              LevyStochCalc.Brownian.Ito.crossIncrement W hcoord (hHm p k) (hHp p k) (hHs p k) (hHm q l) (hHp q l)
                (hHs q l) k l u v ω) := Finset.sum_congr rfl fun k _ => key k
    _ = (∑ k : Fin d, LevyStochCalc.Brownian.Ito.polarQuadVarIncrement (W.W k) ℱ (hcoord k) (H p k) (H q k) (hHm p k)
            (hHm q k) (hHp p k) (hHp q k) (hHs p k) (hHs q k) u v ω)
          + (∑ k : Fin d, ∫ s in Set.Ioc u v, H p k ω s * H q k ω s ∂volume)
          + ∑ k : Fin d, ∑ l ∈ Finset.univ.erase k,
              LevyStochCalc.Brownian.Ito.crossIncrement W hcoord (hHm p k) (hHp p k) (hHs p k) (hHm q l) (hHp q l)
                (hHs q l) k l u v ω := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
end VectorQuadVar

end LevyStochCalc.Brownian.Ito


