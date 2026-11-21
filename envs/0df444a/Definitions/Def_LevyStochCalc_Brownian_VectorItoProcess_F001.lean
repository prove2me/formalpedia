-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_VectorItoProcess_F001
-- name    : LevyStochCalc_Brownian_VectorItoProcess_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:21:56.432185+00:00
-- url     : https://prove2.me/theorems/4e1386c0-e51d-4d33-a399-c0cac883116c
-- title:
--   Source declarations: LevyStochCalc.Brownian.VectorItoProcess
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.VectorItoProcess. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_VectorItoProcess_F000
import Definitions.Def_SourceProof_9a9fab4277e23ec64788cbe8

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Vector Itô processes and the moments of their increments

A vector Itô process is `X_t = X₀ + ∫_{[0,t]} b_s ds + ∑ₖ ∫_0^t H^{·,k}_s dWᵏ_s` with values in
`Fin n → ℝ`, driven by a `d`-dimensional Brownian motion. Each coordinate's increment across a
window is a drift increment plus a finite sum of Itô-integral increments, so its moments follow
from the drift bound, the increment moments of the scalar Itô integral and Jensen's inequality
for sums; the supremum norm on `Fin n → ℝ` is then controlled coordinatewise.

## Main statements

* `LevyStochCalc.Brownian.Ito.vectorItoProcess` — the process itself.
* `LevyStochCalc.Brownian.Ito.vectorItoProcess_sub` — the coordinate increment splits into a
  drift part and a sum of Itô-integral increments.
* `LevyStochCalc.Brownian.Ito.integral_sq_vectorItoProcess_sub_le` — the coordinate second
  moment `𝔼|ΔXᵐ|² ≤ 2(BΔt)² + 2d²C²Δt`.
* `LevyStochCalc.Brownian.Ito.integral_abs_vectorItoProcess_sub_le` — the coordinate first
  absolute moment `𝔼|ΔXᵐ| ≤ BΔt + dC√(Δt)`.
* `LevyStochCalc.Brownian.Ito.integral_norm_vectorItoProcess_sub_le` and
  `LevyStochCalc.Brownian.Ito.integral_sq_norm_vectorItoProcess_sub_le` — the same two moments
  for the supremum norm of the vector increment.
* `LevyStochCalc.Brownian.Ito.integrable_norm_vectorItoProcess_sub_pow_three` — the cube of the
  norm of the increment is integrable.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

section PiNorm

variable {n : ℕ}

end PiNorm

section FiniteSums

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {ι : Type*} [Fintype ι]

/-- A sum of two functions with integrable squares has integrable square, with second moment at
most twice the sum of bounds on theirs. -/
theorem integrable_sq_add_and_le {A B : Ω → ℝ} (hAm : Measurable A) (hBm : Measurable B)
    (hA : Integrable (fun ω => (A ω) ^ 2) P) (hB : Integrable (fun ω => (B ω) ^ 2) P)
    {a b : ℝ} (hAle : ∫ ω, (A ω) ^ 2 ∂P ≤ a) (hBle : ∫ ω, (B ω) ^ 2 ∂P ≤ b) :
    Integrable (fun ω => (A ω + B ω) ^ 2) P
      ∧ ∫ ω, (A ω + B ω) ^ 2 ∂P ≤ 2 * a + 2 * b := by
  have hdom : Integrable (fun ω => 2 * (A ω) ^ 2 + 2 * (B ω) ^ 2) P :=
    (hA.const_mul 2).add (hB.const_mul 2)
  have hpt : ∀ ω, (A ω + B ω) ^ 2 ≤ 2 * (A ω) ^ 2 + 2 * (B ω) ^ 2 := fun ω => by
    nlinarith [sq_nonneg (A ω - B ω)]
  have hmeas : Measurable fun ω => (A ω + B ω) ^ 2 := (hAm.add hBm).pow_const 2
  have hint : Integrable (fun ω => (A ω + B ω) ^ 2) P := by
    refine hdom.mono' hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hpt ω
  refine ⟨hint, ?_⟩
  calc ∫ ω, (A ω + B ω) ^ 2 ∂P ≤ ∫ ω, (2 * (A ω) ^ 2 + 2 * (B ω) ^ 2) ∂P :=
        MeasureTheory.integral_mono hint hdom hpt
    _ = 2 * ∫ ω, (A ω) ^ 2 ∂P + 2 * ∫ ω, (B ω) ^ 2 ∂P := by
        rw [MeasureTheory.integral_add (hA.const_mul 2) (hB.const_mul 2),
          MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    _ ≤ 2 * a + 2 * b := by linarith
/-- A sum of two functions with integrable absolute values has integrable absolute value, with
first absolute moment at most the sum of bounds on theirs. -/
theorem integrable_abs_add_and_le {A B : Ω → ℝ} (hAm : Measurable A) (hBm : Measurable B)
    (hA : Integrable (fun ω => |A ω|) P) (hB : Integrable (fun ω => |B ω|) P)
    {a b : ℝ} (hAle : ∫ ω, |A ω| ∂P ≤ a) (hBle : ∫ ω, |B ω| ∂P ≤ b) :
    Integrable (fun ω => |A ω + B ω|) P ∧ ∫ ω, |A ω + B ω| ∂P ≤ a + b := by
  have hdom : Integrable (fun ω => |A ω| + |B ω|) P := hA.add hB
  have hpt : ∀ ω, |A ω + B ω| ≤ |A ω| + |B ω| := fun ω => abs_add_le _ _
  have hmeas : Measurable fun ω => |A ω + B ω| := (hAm.add hBm).abs
  have hint : Integrable (fun ω => |A ω + B ω|) P := by
    refine hdom.mono' hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_abs]
    exact hpt ω
  refine ⟨hint, ?_⟩
  calc ∫ ω, |A ω + B ω| ∂P ≤ ∫ ω, (|A ω| + |B ω|) ∂P :=
        MeasureTheory.integral_mono hint hdom hpt
    _ = (∫ ω, |A ω| ∂P) + ∫ ω, |B ω| ∂P := MeasureTheory.integral_add hA hB
    _ ≤ a + b := add_le_add hAle hBle
/-- A sum of two functions with integrable absolute cubes has integrable absolute cube. -/
theorem integrable_abs_add_pow_three {A B : Ω → ℝ} (hAm : Measurable A) (hBm : Measurable B)
    (hA : Integrable (fun ω => |A ω| ^ 3) P) (hB : Integrable (fun ω => |B ω| ^ 3) P) :
    Integrable (fun ω => |A ω + B ω| ^ 3) P := by
  have hdom : Integrable (fun ω => 4 * (|A ω| ^ 3 + |B ω| ^ 3)) P := (hA.add hB).const_mul 4
  have hpt : ∀ ω, |A ω + B ω| ^ 3 ≤ 4 * (|A ω| ^ 3 + |B ω| ^ 3) := fun ω =>
    (pow_le_pow_left₀ (abs_nonneg _) (abs_add_le (A ω) (B ω)) 3).trans
      (add_pow_three_le_four (abs_nonneg _) (abs_nonneg _))
  have hmeas : Measurable fun ω => |A ω + B ω| ^ 3 := (hAm.add hBm).abs.pow_const 3
  refine hdom.mono' hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg _) 3)]
  exact hpt ω
end FiniteSums

section VectorProcess

open LevyStochCalc.Brownian.Multidim

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} (W : Multidim.MultidimBrownianMotion P d)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ)
  (H : Fin n → Fin d → Ω → ℝ → ℝ)
  (hHm : ∀ m k, Measurable (Function.uncurry (H m k)))
  (hHp : ∀ m k, Probability.ProgressivelyMeasurable ℱ (H m k))
  (hHs : ∀ (m : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H m k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)

/-- The Itô integral of the `(m, k)` entry of the diffusion matrix against the `k`-th Brownian
coordinate. -/
noncomputable def coordItoIntegral (m : Fin n) (k : Fin d) (t : ℝ) (ω : Ω) : ℝ :=
  stochasticIntegralBrownian (W.W k) ℱ (hcoord k) (H m k) (hHm m k) (hHp m k) (hHs m k) t ω
/-- The martingale part of the `m`-th coordinate of a vector Itô process. -/
noncomputable def vectorItoMartingale (m : Fin n) (t : ℝ) (ω : Ω) : ℝ :=
  ∑ k : Fin d, coordItoIntegral W ℱ hcoord H hHm hHp hHs m k t ω
/-- The vector Itô process `X_t = X₀ + ∫_{[0,t]} b_s ds + ∑ₖ ∫_0^t H^{·,k}_s dWᵏ_s`. -/
noncomputable def vectorItoProcess (X₀ : Ω → Fin n → ℝ) (bdrift : Fin n → Ω → ℝ → ℝ)
    (t : ℝ) (ω : Ω) : Fin n → ℝ := fun m =>
  X₀ ω m + (∫ s in Set.Icc (0 : ℝ) t, bdrift m ω s ∂volume)
    + vectorItoMartingale W ℱ hcoord H hHm hHp hHs m t ω
/-- Each entry's Itô integral is measurable for the σ-algebra at its time. -/
theorem stronglyMeasurable_coordItoIntegral (m : Fin n) (k : Fin d) (t : ℝ) :
    StronglyMeasurable[ℱ t] (coordItoIntegral W ℱ hcoord H hHm hHp hHs m k t) :=
  stochasticIntegralBrownian_stronglyAdapted (W.W k) ℱ (hcoord k) (H m k) (hHm m k) (hHp m k)
    (hHs m k) t
/-- Each entry's Itô integral is measurable. -/
theorem measurable_coordItoIntegral (m : Fin n) (k : Fin d) (t : ℝ) :
    Measurable (coordItoIntegral W ℱ hcoord H hHm hHp hHs m k t) :=
  ((stronglyMeasurable_coordItoIntegral W ℱ hcoord H hHm hHp hHs m k t).mono (ℱ.le t)).measurable
/-- The martingale part of a coordinate is measurable. -/
theorem measurable_vectorItoMartingale (m : Fin n) (t : ℝ) :
    Measurable (vectorItoMartingale W ℱ hcoord H hHm hHp hHs m t) :=
  Finset.measurable_sum _ fun k _ => measurable_coordItoIntegral W ℱ hcoord H hHm hHp hHs m k t
/-- The increment of the martingale part is the sum of the entries' increments. -/
theorem vectorItoMartingale_sub (m : Fin n) (u v : ℝ) (ω : Ω) :
    vectorItoMartingale W ℱ hcoord H hHm hHp hHs m v ω
        - vectorItoMartingale W ℱ hcoord H hHm hHp hHs m u ω
      = ∑ k : Fin d, (coordItoIntegral W ℱ hcoord H hHm hHp hHs m k v ω
        - coordItoIntegral W ℱ hcoord H hHm hHp hHs m k u ω) := by
  simp only [vectorItoMartingale, Finset.sum_sub_distrib]
/-- A vector Itô process is measurable in the sample point at each time. -/
theorem measurable_vectorItoProcess {X₀ : Ω → Fin n → ℝ}
    (hX₀ : ∀ m, Measurable fun ω => X₀ ω m) {bdrift : Fin n → Ω → ℝ → ℝ}
    (hbm : ∀ m, Measurable (Function.uncurry (bdrift m))) (t : ℝ) :
    Measurable (vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift t) := by
  refine measurable_pi_lambda _ fun m => ?_
  exact ((hX₀ m).add (measurable_setIntegral (hbm m) _)).add
    (measurable_vectorItoMartingale W ℱ hcoord H hHm hHp hHs m t)
/-- The increment of a coordinate of a vector Itô process is the drift's increment plus the
martingale part's. -/
theorem vectorItoProcess_sub (X₀ : Ω → Fin n → ℝ) (bdrift : Fin n → Ω → ℝ → ℝ)
    (hbm : ∀ m, Measurable (Function.uncurry (bdrift m))) {B : ℝ}
    (hB : ∀ (m : Fin n) (ω : Ω) (s : ℝ), |bdrift m ω s| ≤ B) {u v : ℝ} (hu : 0 ≤ u)
    (huv : u ≤ v) (m : Fin n) (ω : Ω) :
    vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift v ω m
        - vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift u ω m
      = (∫ s in Set.Ioc u v, bdrift m ω s ∂volume)
        + (vectorItoMartingale W ℱ hcoord H hHm hHp hHs m v ω
          - vectorItoMartingale W ℱ hcoord H hHm hHp hHs m u ω) := by
  simp only [vectorItoProcess]
  rw [← setIntegral_Icc_sub_Icc (Measurable.of_uncurry_left (hbm m)) (hB m ω) hu huv]
  ring
variable {C : ℝ} (hC0 : 0 ≤ C)
  (hCH : ∀ (m : Fin n) (k : Fin d) (ω : Ω) (s : ℝ), |H m k ω s| ≤ C)

include hC0 hCH in
/-- **Second moment of the martingale part's increment.** -/
theorem integral_sq_vectorItoMartingale_sub_le (m : Fin n) {u v : ℝ} (hu : 0 ≤ u) (huv : u < v) :
    Integrable (fun ω => (vectorItoMartingale W ℱ hcoord H hHm hHp hHs m v ω
        - vectorItoMartingale W ℱ hcoord H hHm hHp hHs m u ω) ^ 2) P
      ∧ ∫ ω, (vectorItoMartingale W ℱ hcoord H hHm hHp hHs m v ω
          - vectorItoMartingale W ℱ hcoord H hHm hHp hHs m u ω) ^ 2 ∂P
        ≤ (d : ℝ) ^ 2 * (C ^ 2 * (v - u)) := by
  have hk : ∀ k : Fin d,
      Integrable (fun ω => (coordItoIntegral W ℱ hcoord H hHm hHp hHs m k v ω
          - coordItoIntegral W ℱ hcoord H hHm hHp hHs m k u ω) ^ 2) P
        ∧ ∫ ω, (coordItoIntegral W ℱ hcoord H hHm hHp hHs m k v ω
            - coordItoIntegral W ℱ hcoord H hHm hHp hHs m k u ω) ^ 2 ∂P ≤ C ^ 2 * (v - u) :=
    fun k => _root_.Prove2MeSourceProof.h_9a9fab4277e23ec64788cbe8 (W.W k) ℱ (hcoord k) (H m k) (hHm m k) (hHp m k) (hHs m k)
      hC0 (hCH m k) hu huv
  obtain ⟨hint, hle⟩ := integrable_sq_sum_and_le (P := P)
    (f := fun (k : Fin d) ω => coordItoIntegral W ℱ hcoord H hHm hHp hHs m k v ω
      - coordItoIntegral W ℱ hcoord H hHm hHp hHs m k u ω)
    (fun k => (measurable_coordItoIntegral W ℱ hcoord H hHm hHp hHs m k v).sub
      (measurable_coordItoIntegral W ℱ hcoord H hHm hHp hHs m k u))
    (fun k => (hk k).1)
  simp_rw [vectorItoMartingale_sub W ℱ hcoord H hHm hHp hHs m u v]
  refine ⟨hint, ?_⟩
  have hsum : ∑ k : Fin d, ∫ ω, (coordItoIntegral W ℱ hcoord H hHm hHp hHs m k v ω
        - coordItoIntegral W ℱ hcoord H hHm hHp hHs m k u ω) ^ 2 ∂P
      ≤ (d : ℝ) * (C ^ 2 * (v - u)) := by
    calc ∑ k : Fin d, ∫ ω, (coordItoIntegral W ℱ hcoord H hHm hHp hHs m k v ω
          - coordItoIntegral W ℱ hcoord H hHm hHp hHs m k u ω) ^ 2 ∂P
        ≤ ∑ _k : Fin d, C ^ 2 * (v - u) := Finset.sum_le_sum fun k _ => (hk k).2
      _ = (d : ℝ) * (C ^ 2 * (v - u)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hcard : (Fintype.card (Fin d) : ℝ) = (d : ℝ) := by simp
  calc ∫ ω, (∑ k : Fin d, (coordItoIntegral W ℱ hcoord H hHm hHp hHs m k v ω
        - coordItoIntegral W ℱ hcoord H hHm hHp hHs m k u ω)) ^ 2 ∂P
      ≤ (Fintype.card (Fin d) : ℝ) * ∑ k : Fin d,
          ∫ ω, (coordItoIntegral W ℱ hcoord H hHm hHp hHs m k v ω
            - coordItoIntegral W ℱ hcoord H hHm hHp hHs m k u ω) ^ 2 ∂P := hle
    _ = (d : ℝ) * ∑ k : Fin d, ∫ ω, (coordItoIntegral W ℱ hcoord H hHm hHp hHs m k v ω
          - coordItoIntegral W ℱ hcoord H hHm hHp hHs m k u ω) ^ 2 ∂P := by rw [hcard]
    _ ≤ (d : ℝ) * ((d : ℝ) * (C ^ 2 * (v - u))) :=
        mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg d)
    _ = (d : ℝ) ^ 2 * (C ^ 2 * (v - u)) := by ring
section VectorMoments

variable (X₀ : Ω → Fin n → ℝ) (bdrift : Fin n → Ω → ℝ → ℝ)
  (hbm : ∀ m, Measurable (Function.uncurry (bdrift m))) {B : ℝ} (hB0 : 0 ≤ B)
  (hB : ∀ (m : Fin n) (ω : Ω) (s : ℝ), |bdrift m ω s| ≤ B)

end VectorMoments

end VectorProcess

end LevyStochCalc.Brownian.Ito


