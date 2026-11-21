-- Prove2me | Definitions.Def_SourceProof_347771d47d14cf2e5f4e8715
-- name    : SourceProof_347771d47d14cf2e5f4e8715
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:43:56.515332+00:00
-- url     : https://prove2.me/theorems/8eb232ca-bed8-4275-a802-bec23cfca0f6
-- title:
--   LevyStochCalc source module: SourceProof_347771d47d14cf2e5f4e8715
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.IsVectorItoVersion.quadVarRiemann_decomp_ae` comes from the `LevyStochCalc.Brownian.VectorItoQuadVarRiemannDecomposition` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_VectorItoQuadVarRiemannDecomposition_F000
import Definitions.Def_SourceProof_1566953c59c85fa51b459ad0

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

theorem _root_.Prove2MeSourceProof.h_347771d47d14cf2e5f4e8715
    (h : IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift X)
    (hbm : ∀ m, Measurable (Function.uncurry (bdrift m))) {B : ℝ}
    (hB : ∀ (m : Fin n) (ω : Ω) (s : ℝ), |bdrift m ω s| ≤ B) (p q : Fin n)
    (φ : (Fin n → ℝ) → ℝ) {T : ℝ} (hT : 0 < T) {m : ℕ} (hm0 : m ≠ 0) :
    ∀ᵐ ω ∂P, (∑ i ∈ Finset.range m, φ (X (unifGrid T m i) ω)
          * ((X (unifGrid T m (i + 1)) ω p - X (unifGrid T m i) ω p)
            * (X (unifGrid T m (i + 1)) ω q - X (unifGrid T m i) ω q)))
      = (∑ i ∈ Finset.range m, φ (X (unifGrid T m i) ω)
            * ((∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)), bdrift p ω s ∂volume)
              * ∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)), bdrift q ω s ∂volume))
        + (∑ i ∈ Finset.range m, φ (X (unifGrid T m i) ω)
            * ((∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)), bdrift p ω s ∂volume)
              * (vectorItoMartingale W ℱ hcoord H hHm hHp hHs q (unifGrid T m (i + 1)) ω
                - vectorItoMartingale W ℱ hcoord H hHm hHp hHs q (unifGrid T m i) ω)))
        + (∑ i ∈ Finset.range m, φ (X (unifGrid T m i) ω)
            * ((∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)), bdrift q ω s ∂volume)
              * (vectorItoMartingale W ℱ hcoord H hHm hHp hHs p (unifGrid T m (i + 1)) ω
                - vectorItoMartingale W ℱ hcoord H hHm hHp hHs p (unifGrid T m i) ω)))
        + (∑ k : Fin d, ∑ i ∈ Finset.range m, φ (X (unifGrid T m i) ω)
            * polarQuadVarIncrement (W.W k) ℱ (hcoord k) (H p k) (H q k) (hHm p k) (hHm q k)
                (hHp p k) (hHp q k) (hHs p k) (hHs q k)
                (unifGrid T m i) (unifGrid T m (i + 1)) ω)
        + (∑ k : Fin d, ∑ l ∈ Finset.univ.erase k, ∑ i ∈ Finset.range m,
            φ (X (unifGrid T m i) ω)
              * crossIncrement W hcoord (hHm p k) (hHp p k) (hHs p k) (hHm q l) (hHp q l)
                  (hHs q l) k l (unifGrid T m i) (unifGrid T m (i + 1)) ω)
        + ∑ i ∈ Finset.range m, φ (X (unifGrid T m i) ω)
            * ∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)),
                ∑ k : Fin d, H p k ω s * H q k ω s ∂volume := by
  filter_upwards [MeasureTheory.ae_all_iff.mpr fun i : ℕ =>
    h.prod_sub_ae hbm hB p q (LevyStochCalc.Brownian.Ito.unifGrid_nonneg hT.le m i)
      (LevyStochCalc.Brownian.Ito.unifGrid_lt_succ hT hm0 i).le] with ω hω
  have hswap : ∀ i : ℕ, (∑ k : Fin d, ∫ s in Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)),
        H p k ω s * H q k ω s ∂volume)
      = ∫ s in Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)),
          ∑ k : Fin d, H p k ω s * H q k ω s ∂volume := by
    intro i
    refine (MeasureTheory.integral_finsetSum _ fun k _ => ?_).symm
    refine LevyStochCalc.integrableOn_of_bounded_of_measurable (B := C ^ 2)
      ((Measurable.of_uncurry_left (hHm p k)).mul (Measurable.of_uncurry_left (hHm q k)))
      (fun s => ?_) (measure_Ioc_lt_top).ne
    change |H p k ω s * H q k ω s| ≤ C ^ 2
    rw [abs_mul, pow_two]
    exact mul_le_mul (hCH p k ω s) (hCH q k ω s) (abs_nonneg _) hC0
  have hterm : ∀ i ∈ Finset.range m, φ (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
      * ((X (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω p - X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω p)
        * (X (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω q - X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω q))
      = φ (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
          * ((∫ s in Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)), bdrift p ω s ∂volume)
            * ∫ s in Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)), bdrift q ω s ∂volume)
        + φ (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
          * ((∫ s in Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)), bdrift p ω s ∂volume)
            * (LevyStochCalc.Brownian.Ito.vectorItoMartingale W ℱ hcoord H hHm hHp hHs q (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω
              - LevyStochCalc.Brownian.Ito.vectorItoMartingale W ℱ hcoord H hHm hHp hHs q (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω))
        + φ (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
          * ((∫ s in Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)), bdrift q ω s ∂volume)
            * (LevyStochCalc.Brownian.Ito.vectorItoMartingale W ℱ hcoord H hHm hHp hHs p (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω
              - LevyStochCalc.Brownian.Ito.vectorItoMartingale W ℱ hcoord H hHm hHp hHs p (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω))
        + (∑ k : Fin d, φ (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
            * LevyStochCalc.Brownian.Ito.polarQuadVarIncrement (W.W k) ℱ (hcoord k) (H p k) (H q k) (hHm p k) (hHm q k)
                (hHp p k) (hHp q k) (hHs p k) (hHs q k)
                (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω)
        + (∑ k : Fin d, ∑ l ∈ Finset.univ.erase k, φ (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
            * LevyStochCalc.Brownian.Ito.crossIncrement W hcoord (hHm p k) (hHp p k) (hHs p k) (hHm q l) (hHp q l)
                (hHs q l) k l (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω)
        + φ (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
          * ∫ s in Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)),
              ∑ k : Fin d, H p k ω s * H q k ω s ∂volume := by
    intro i _
    rw [hω i, _root_.Prove2MeSourceProof.h_1566953c59c85fa51b459ad0 hC0 hCH p q (LevyStochCalc.Brownian.Ito.unifGrid_nonneg hT.le m i)
      (LevyStochCalc.Brownian.Ito.unifGrid_lt_succ hT hm0 i).le ω, ← hswap i]
    simp only [mul_add, Finset.mul_sum]
    ring
  have hcomm1 : (∑ i ∈ Finset.range m, ∑ k : Fin d, φ (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
        * LevyStochCalc.Brownian.Ito.polarQuadVarIncrement (W.W k) ℱ (hcoord k) (H p k) (H q k) (hHm p k) (hHm q k)
            (hHp p k) (hHp q k) (hHs p k) (hHs q k)
            (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω)
      = ∑ k : Fin d, ∑ i ∈ Finset.range m, φ (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
          * LevyStochCalc.Brownian.Ito.polarQuadVarIncrement (W.W k) ℱ (hcoord k) (H p k) (H q k) (hHm p k) (hHm q k)
              (hHp p k) (hHp q k) (hHs p k) (hHs q k)
              (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω := Finset.sum_comm
  have hcomm2 : (∑ i ∈ Finset.range m, ∑ k : Fin d, ∑ l ∈ Finset.univ.erase k,
        φ (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
          * LevyStochCalc.Brownian.Ito.crossIncrement W hcoord (hHm p k) (hHp p k) (hHs p k) (hHm q l) (hHp q l)
              (hHs q l) k l (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω)
      = ∑ k : Fin d, ∑ l ∈ Finset.univ.erase k, ∑ i ∈ Finset.range m,
          φ (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
            * LevyStochCalc.Brownian.Ito.crossIncrement W hcoord (hHm p k) (hHp p k) (hHs p k) (hHm q l) (hHp q l)
                (hHs q l) k l (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_comm
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib, hcomm1, hcomm2]
end VectorQuadVar

end LevyStochCalc.Brownian.Ito


