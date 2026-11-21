-- Prove2me | Definitions.Def_SourceProof_3e3db1d7d302cb153d64875c
-- name    : SourceProof_3e3db1d7d302cb153d64875c
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:46:21.14639+00:00
-- url     : https://prove2.me/theorems/a9933399-0fcd-4f19-8a3b-7009d89dbb0a
-- title:
--   LevyStochCalc source module: SourceProof_3e3db1d7d302cb153d64875c
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.IsVectorItoVersion.integral_abs_quadVarRiemann_sub_le` comes from the `LevyStochCalc.Brownian.VectorItoQuadVarRiemannDecomposition` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_VectorItoQuadVarRiemannTermBounds_F000
import Definitions.Def_SourceProof_245b68e3cf8016f68cae5af6
import Definitions.Def_SourceProof_347771d47d14cf2e5f4e8715
import Definitions.Def_SourceProof_3f70385af64f50e254cd95c8
import Definitions.Def_SourceProof_4f9db7bae0e9e2e85d25391a
import Definitions.Def_SourceProof_8ef33315e8b9266ce62a44b6
import Definitions.Def_SourceProof_cc69b3b5abb273f29b8a03a8

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

theorem _root_.Prove2MeSourceProof.h_3e3db1d7d302cb153d64875c
    (h : IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift X)
    (hbm : ∀ m, Measurable (Function.uncurry (bdrift m))) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ (m : Fin n) (ω : Ω) (s : ℝ), |bdrift m ω s| ≤ B) (p q : Fin n)
    (hma : ∀ k : Fin d, Measurable (Function.uncurry fun ω s => H p k ω s + H q k ω s))
    (hpa : ∀ k : Fin d, Probability.ProgressivelyMeasurable ℱ fun ω s => H p k ω s + H q k ω s)
    (hqa : ∀ (k : Fin d) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖H p k ω s + H q k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {φ : (Fin n → ℝ) → ℝ} (hφc : Continuous φ) {Kφ : ℝ} (hKφ0 : 0 ≤ Kφ)
    (hφbd : ∀ x, |φ x| ≤ Kφ) {Mφ L : ℝ} (hMφ0 : 0 ≤ Mφ) (hL0 : 0 ≤ L)
    (hφaff : ∀ x y : Fin n → ℝ, |φ x - φ y| ≤ Mφ + L * ‖x - y‖)
    {T : ℝ} (hT : 0 < T) {m : ℕ} (hm0 : m ≠ 0) :
    Integrable (fun ω : Ω => (∑ i ∈ Finset.range m, φ (X (unifGrid T m i) ω)
          * ((X (unifGrid T m (i + 1)) ω p - X (unifGrid T m i) ω p)
            * (X (unifGrid T m (i + 1)) ω q - X (unifGrid T m i) ω q)))
        - ∫ s in Set.Ioc (0 : ℝ) T,
            φ (X s ω) * ∑ k : Fin d, H p k ω s * H q k ω s ∂volume) P
      ∧ ∫ ω, |(∑ i ∈ Finset.range m, φ (X (unifGrid T m i) ω)
          * ((X (unifGrid T m (i + 1)) ω p - X (unifGrid T m i) ω p)
            * (X (unifGrid T m (i + 1)) ω q - X (unifGrid T m i) ω q)))
        - ∫ s in Set.Ioc (0 : ℝ) T,
            φ (X s ω) * ∑ k : Fin d, H p k ω s * H q k ω s ∂volume| ∂P
      ≤ (m : ℝ) * (Kφ * (B * (T / (m : ℝ))) ^ 2)
        + (m : ℝ) * (Kφ * (B * (T / (m : ℝ)) * ((d : ℝ) * (C * Real.sqrt (T / (m : ℝ))))))
        + (m : ℝ) * (Kφ * (B * (T / (m : ℝ)) * ((d : ℝ) * (C * Real.sqrt (T / (m : ℝ))))))
        + (d : ℝ) * Real.sqrt (Kφ ^ 2
            * (3 * ((2 * (6 + gaussianFourthMoment) + 2) * (2 * C) ^ 4)) * (T ^ 2 / (m : ℝ)))
        + (d : ℝ) ^ 2 * Real.sqrt (Kφ ^ 2
            * ((6 + gaussianFourthMoment) * (C ^ 4 + C ^ 4) / 2) * (T ^ 2 / (m : ℝ)))
        + (Mφ * ((d : ℝ) * C ^ 2) * T
          + L * ((d : ℝ) * C ^ 2)
            * (T * ((n : ℝ) * (B * (T / (m : ℝ))
              + (d : ℝ) * (C * Real.sqrt (T / (m : ℝ))))))) := by
  classical
  -- the weight of the frozen Riemann sum
  have hwm : Measurable (Function.uncurry fun ω s => ∑ k : Fin d, H p k ω s * H q k ω s) :=
    Finset.measurable_sum _ fun k _ => (hHm p k).mul (hHm q k)
  have hA0 : (0 : ℝ) ≤ (d : ℝ) * C ^ 2 := by positivity
  have hA : ∀ (ω : Ω) (s : ℝ), |∑ k : Fin d, H p k ω s * H q k ω s| ≤ (d : ℝ) * C ^ 2 := by
    intro ω s
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hterm : ∀ k ∈ (Finset.univ : Finset (Fin d)), |H p k ω s * H q k ω s| ≤ C ^ 2 := by
      intro k _
      rw [abs_mul, pow_two]
      exact mul_le_mul (hCH p k ω s) (hCH q k ω s) (abs_nonneg _) hC0
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  -- the six groups
  obtain ⟨i1, b1⟩ := (_root_.Prove2MeSourceProof.h_8ef33315e8b9266ce62a44b6 h) hbm hB0 hB p q hφc hKφ0 hφbd hT hm0
  obtain ⟨i2, b2⟩ := (fun p2mMethodArg0 p2mMethodArg1 => _root_.Prove2MeSourceProof.h_4f9db7bae0e9e2e85d25391a p2mMethodArg0 p2mMethodArg1 h) hC0 hCH hbm hB0 hB p q hφc hKφ0 hφbd hT hm0
  obtain ⟨i3, b3⟩ := (fun p2mMethodArg0 p2mMethodArg1 => _root_.Prove2MeSourceProof.h_4f9db7bae0e9e2e85d25391a p2mMethodArg0 p2mMethodArg1 h) hC0 hCH hbm hB0 hB q p hφc hKφ0 hφbd hT hm0
  have hpol : ∀ k : Fin d, Integrable (fun ω : Ω => ∑ i ∈ Finset.range m,
        φ (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
          * LevyStochCalc.Brownian.Ito.polarQuadVarIncrement (W.W k) ℱ (hcoord k) (H p k) (H q k) (hHm p k) (hHm q k)
              (hHp p k) (hHp q k) (hHs p k) (hHs q k)
              (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω) P
      ∧ ∫ ω, |∑ i ∈ Finset.range m, φ (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
            * LevyStochCalc.Brownian.Ito.polarQuadVarIncrement (W.W k) ℱ (hcoord k) (H p k) (H q k) (hHm p k) (hHm q k)
                (hHp p k) (hHp q k) (hHs p k) (hHs q k)
                (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω| ∂P
        ≤ Real.sqrt (Kφ ^ 2 * (3 * ((2 * (6 + LevyStochCalc.Brownian.Ito.gaussianFourthMoment) + 2) * (2 * C) ^ 4))
          * (T ^ 2 / (m : ℝ))) := fun k =>
    (fun p2mMethodArg0 p2mMethodArg1 => _root_.Prove2MeSourceProof.h_3f70385af64f50e254cd95c8 p2mMethodArg0 p2mMethodArg1 h) hC0 hCH p q k (hma k) (hpa k) (hqa k) hφc hKφ0 hφbd hT hm0
  have hcr : ∀ (k : Fin d), ∀ l ∈ Finset.univ.erase k,
      Integrable (fun ω : Ω => ∑ i ∈ Finset.range m, φ (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
          * LevyStochCalc.Brownian.Ito.crossIncrement W hcoord (hHm p k) (hHp p k) (hHs p k) (hHm q l) (hHp q l)
              (hHs q l) k l (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω) P
        ∧ ∫ ω, |∑ i ∈ Finset.range m, φ (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
              * LevyStochCalc.Brownian.Ito.crossIncrement W hcoord (hHm p k) (hHp p k) (hHs p k) (hHm q l) (hHp q l)
                  (hHs q l) k l (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω| ∂P
          ≤ Real.sqrt (Kφ ^ 2 * ((6 + LevyStochCalc.Brownian.Ito.gaussianFourthMoment) * (C ^ 4 + C ^ 4) / 2)
            * (T ^ 2 / (m : ℝ))) := fun k l hl =>
    (fun p2mMethodArg0 p2mMethodArg1 => _root_.Prove2MeSourceProof.h_245b68e3cf8016f68cae5af6 p2mMethodArg0 p2mMethodArg1 h) hC0 hCH p q ((Finset.mem_erase.mp hl).1.symm)
      hφc hKφ0 hφbd hT hm0
  obtain ⟨i6, b6⟩ := (fun p2mMethodArg0 p2mMethodArg1 => _root_.Prove2MeSourceProof.h_cc69b3b5abb273f29b8a03a8 p2mMethodArg0 p2mMethodArg1 h) hC0 hCH hbm hB0 hB
    (fun ω s => ∑ k : Fin d, H p k ω s * H q k ω s) hwm hA0 hA hφc hφbd hMφ0 hL0 hφaff hT hm0
  -- integrability of the grouped sums
  have i4 : Integrable (fun ω : Ω => ∑ k : Fin d, ∑ i ∈ Finset.range m,
      φ (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
        * LevyStochCalc.Brownian.Ito.polarQuadVarIncrement (W.W k) ℱ (hcoord k) (H p k) (H q k) (hHm p k) (hHm q k)
            (hHp p k) (hHp q k) (hHs p k) (hHs q k)
            (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω) P :=
    MeasureTheory.integrable_finsetSum _ fun k _ => (hpol k).1
  have i5 : Integrable (fun ω : Ω => ∑ k : Fin d, ∑ l ∈ Finset.univ.erase k,
      ∑ i ∈ Finset.range m, φ (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
        * LevyStochCalc.Brownian.Ito.crossIncrement W hcoord (hHm p k) (hHp p k) (hHs p k) (hHm q l) (hHp q l)
            (hHs q l) k l (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω) P :=
    MeasureTheory.integrable_finsetSum _ fun k _ =>
      MeasureTheory.integrable_finsetSum _ fun l hl => (hcr k l hl).1
  -- the bounds on the two grouped sums
  have b4 : ∫ ω, |∑ k : Fin d, ∑ i ∈ Finset.range m, φ (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
        * LevyStochCalc.Brownian.Ito.polarQuadVarIncrement (W.W k) ℱ (hcoord k) (H p k) (H q k) (hHm p k) (hHm q k)
            (hHp p k) (hHp q k) (hHs p k) (hHs q k)
            (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω| ∂P
      ≤ (d : ℝ) * Real.sqrt (Kφ ^ 2
        * (3 * ((2 * (6 + LevyStochCalc.Brownian.Ito.gaussianFourthMoment) + 2) * (2 * C) ^ 4)) * (T ^ 2 / (m : ℝ))) := by
    refine (LevyStochCalc.Brownian.Ito.integral_abs_finsetSum_le _ _ (fun k _ => (hpol k).1) _
      (fun k _ => (hpol k).2)).trans ?_
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have b5 : ∫ ω, |∑ k : Fin d, ∑ l ∈ Finset.univ.erase k, ∑ i ∈ Finset.range m,
        φ (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
          * LevyStochCalc.Brownian.Ito.crossIncrement W hcoord (hHm p k) (hHp p k) (hHs p k) (hHm q l) (hHp q l)
              (hHs q l) k l (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω| ∂P
      ≤ (d : ℝ) ^ 2 * Real.sqrt (Kφ ^ 2
        * ((6 + LevyStochCalc.Brownian.Ito.gaussianFourthMoment) * (C ^ 4 + C ^ 4) / 2) * (T ^ 2 / (m : ℝ))) := by
    have hsqrt0 : (0 : ℝ) ≤ Real.sqrt (Kφ ^ 2
        * ((6 + LevyStochCalc.Brownian.Ito.gaussianFourthMoment) * (C ^ 4 + C ^ 4) / 2) * (T ^ 2 / (m : ℝ))) :=
      Real.sqrt_nonneg _
    refine (LevyStochCalc.Brownian.Ito.integral_abs_finsetSum_le _ _
      (fun k _ => MeasureTheory.integrable_finsetSum _ fun l hl => (hcr k l hl).1)
      (fun k => ∑ _l ∈ Finset.univ.erase k, Real.sqrt (Kφ ^ 2
        * ((6 + LevyStochCalc.Brownian.Ito.gaussianFourthMoment) * (C ^ 4 + C ^ 4) / 2) * (T ^ 2 / (m : ℝ))))
      (fun k _ => LevyStochCalc.Brownian.Ito.integral_abs_finsetSum_le _ _ (fun l hl => (hcr k l hl).1) _
        (fun l hl => (hcr k l hl).2))).trans ?_
    have hk : ∀ k : Fin d, ∑ _l ∈ Finset.univ.erase k, Real.sqrt (Kφ ^ 2
          * ((6 + LevyStochCalc.Brownian.Ito.gaussianFourthMoment) * (C ^ 4 + C ^ 4) / 2) * (T ^ 2 / (m : ℝ)))
        ≤ (d : ℝ) * Real.sqrt (Kφ ^ 2
          * ((6 + LevyStochCalc.Brownian.Ito.gaussianFourthMoment) * (C ^ 4 + C ^ 4) / 2) * (T ^ 2 / (m : ℝ))) := by
      intro k
      refine (Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
        (fun l _ _ => hsqrt0)).trans ?_
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    refine (Finset.sum_le_sum fun k _ => hk k).trans ?_
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring_nf
    exact le_rfl
  -- assemble
  have hae : (fun ω : Ω => |(∑ i ∈ Finset.range m, φ (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
        * ((X (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω p - X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω p)
          * (X (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω q - X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω q)))
      - ∫ s in Set.Ioc (0 : ℝ) T,
          φ (X s ω) * ∑ k : Fin d, H p k ω s * H q k ω s ∂volume|)
      =ᵐ[P] fun ω => |((((∑ i ∈ Finset.range m, φ (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
              * ((∫ s in Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)),
                    bdrift p ω s ∂volume)
                * ∫ s in Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)),
                    bdrift q ω s ∂volume))
            + (∑ i ∈ Finset.range m, φ (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
              * ((∫ s in Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)),
                    bdrift p ω s ∂volume)
                * (LevyStochCalc.Brownian.Ito.vectorItoMartingale W ℱ hcoord H hHm hHp hHs q (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω
                  - LevyStochCalc.Brownian.Ito.vectorItoMartingale W ℱ hcoord H hHm hHp hHs q (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω))))
            + (∑ i ∈ Finset.range m, φ (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
              * ((∫ s in Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)),
                    bdrift q ω s ∂volume)
                * (LevyStochCalc.Brownian.Ito.vectorItoMartingale W ℱ hcoord H hHm hHp hHs p (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω
                  - LevyStochCalc.Brownian.Ito.vectorItoMartingale W ℱ hcoord H hHm hHp hHs p (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω))))
            + (∑ k : Fin d, ∑ i ∈ Finset.range m, φ (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
              * LevyStochCalc.Brownian.Ito.polarQuadVarIncrement (W.W k) ℱ (hcoord k) (H p k) (H q k) (hHm p k) (hHm q k)
                  (hHp p k) (hHp q k) (hHs p k) (hHs q k)
                  (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω))
            + (∑ k : Fin d, ∑ l ∈ Finset.univ.erase k, ∑ i ∈ Finset.range m,
              φ (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
                * LevyStochCalc.Brownian.Ito.crossIncrement W hcoord (hHm p k) (hHp p k) (hHs p k) (hHm q l) (hHp q l)
                    (hHs q l) k l (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω)
          + ((∑ i ∈ Finset.range m, φ (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
              * ∫ s in Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)),
                  ∑ k : Fin d, H p k ω s * H q k ω s ∂volume)
            - ∫ s in Set.Ioc (0 : ℝ) T,
                φ (X s ω) * ∑ k : Fin d, H p k ω s * H q k ω s ∂volume)| := by
    filter_upwards [(fun p2mMethodArg0 p2mMethodArg1 => _root_.Prove2MeSourceProof.h_347771d47d14cf2e5f4e8715 p2mMethodArg0 p2mMethodArg1 h) hC0 hCH hbm hB p q φ hT hm0] with ω hω
    rw [hω]
    congr 1
    ring
  refine ⟨?_, ?_⟩
  · refine (((((i1.add i2).add i3).add i4).add i5).add i6).congr ?_
    filter_upwards [(fun p2mMethodArg0 p2mMethodArg1 => _root_.Prove2MeSourceProof.h_347771d47d14cf2e5f4e8715 p2mMethodArg0 p2mMethodArg1 h) hC0 hCH hbm hB p q φ hT hm0] with ω hω
    simp only [Pi.add_apply]
    rw [hω]
    ring
  rw [MeasureTheory.integral_congr_ae hae]
  exact LevyStochCalc.Brownian.Ito.integral_abs_add_le ((((i1.add i2).add i3).add i4).add i5) i6
    (LevyStochCalc.Brownian.Ito.integral_abs_add_le (((i1.add i2).add i3).add i4) i5
      (LevyStochCalc.Brownian.Ito.integral_abs_add_le ((i1.add i2).add i3) i4
        (LevyStochCalc.Brownian.Ito.integral_abs_add_le (i1.add i2) i3 (LevyStochCalc.Brownian.Ito.integral_abs_add_le i1 i2 b1 b2) b3) b4) b5) b6
end VectorQuadVar

end LevyStochCalc.Brownian.Ito


