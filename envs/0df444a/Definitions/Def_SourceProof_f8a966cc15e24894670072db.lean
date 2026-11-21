-- Prove2me | Definitions.Def_SourceProof_f8a966cc15e24894670072db
-- name    : SourceProof_f8a966cc15e24894670072db
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:48:19.427145+00:00
-- url     : https://prove2.me/theorems/62e25080-c413-4017-9e3b-ca0b57afa02f
-- title:
--   LevyStochCalc source module: SourceProof_f8a966cc15e24894670072db
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.IsVectorItoVersion.integral_abs_vectorItoFormula_le` comes from the `LevyStochCalc.Brownian.VectorItoFormula` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_VectorItoFormula_F000
import Definitions.Def_SourceProof_0362ffa5a8b426de4a0a426a
import Definitions.Def_SourceProof_3e3db1d7d302cb153d64875c
import Definitions.Def_SourceProof_6647e433b820760a28ba04c2
import Definitions.Def_SourceProof_724ac40b8d5293986a0749a0
import Definitions.Def_SourceProof_84dc228d7203d8f3c18ebbd6
import Definitions.Def_SourceProof_9e8c1965c746b09726c017d4
import Definitions.Def_SourceProof_cebf5e28c49b85cc9ea79d78

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Itô's formula for a vector Itô process on a uniform grid

The grid decomposition leaves four errors: the second-order Taylor remainder, one drift Riemann
sum per state index, one martingale Riemann sum per state-and-Brownian index pair, and one
weighted quadratic variation per pair of state indices. Under an affine oscillation bound
`A + K‖z − w‖` on the second derivative each is bounded by a function of the mesh whose limit is
proportional to `A`; a uniformly continuous second derivative supplies such a bound for every
`A > 0`, so the `L¹` defect of Itô's formula vanishes.

## Main statements

* `LevyStochCalc.Brownian.Ito.vectorItoGridError` — the mesh-error function.
* `LevyStochCalc.Brownian.Ito.tendsto_vectorItoGridError` — it vanishes as the mesh does.
* `LevyStochCalc.Brownian.Ito.IsVectorItoVersion.integral_abs_vectorItoFormula_le` — the `L¹`
  defect of Itô's formula on every uniform grid.
* `LevyStochCalc.Brownian.Ito.IsVectorItoVersion.itoFormula` — Itô's formula in the vector case.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology

universe u

section Formula

open LevyStochCalc.Brownian.Multidim

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} {W : Multidim.MultidimBrownianMotion P d}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ}
  {H : Fin n → Fin d → Ω → ℝ → ℝ}
  {hHm : ∀ p k, Measurable (Function.uncurry (H p k))}
  {hHp : ∀ p k, Probability.ProgressivelyMeasurable ℱ (H p k)}
  {hHs : ∀ (p : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
  {X₀ : Ω → Fin n → ℝ} {bdrift : Fin n → Ω → ℝ → ℝ} {X : ℝ → Ω → Fin n → ℝ}
  {C : ℝ} (hC0 : 0 ≤ C)
  (hCH : ∀ (p : Fin n) (k : Fin d) (ω : Ω) (s : ℝ), |H p k ω s| ≤ C)

include hC0 hCH in

theorem _root_.Prove2MeSourceProof.h_f8a966cc15e24894670072db
    (h : IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift X)
    (hX₀ : ∀ p : Fin n, Measurable fun ω => X₀ ω p)
    (hbm : ∀ p, Measurable (Function.uncurry (bdrift p))) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ (p : Fin n) (ω : Ω) (s : ℝ), |bdrift p ω s| ≤ B)
    (hma : ∀ (p q : Fin n) (k : Fin d),
      Measurable (Function.uncurry fun ω s => H p k ω s + H q k ω s))
    (hpa : ∀ (p q : Fin n) (k : Fin d),
      Probability.ProgressivelyMeasurable ℱ fun ω s => H p k ω s + H q k ω s)
    (hqa : ∀ (p q : Fin n) (k : Fin d) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖H p k ω s + H q k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {f : (Fin n → ℝ) → ℝ} {f' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ}
    {f'' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ}
    (hf : ∀ z, HasFDerivAt f (f' z) z) (hf' : ∀ z, HasFDerivAt f' (f'' z) z)
    {K₁ : ℝ} (hf'bd : ∀ z, ‖f' z‖ ≤ K₁)
    {K₂ : ℝ} (hK₂0 : 0 ≤ K₂) (hf''bd : ∀ z, ‖f'' z‖ ≤ K₂)
    {A K : ℝ} (hA0 : 0 ≤ A) (hK0 : 0 ≤ K) (hf''c : Continuous f'')
    (hf''aff : ∀ z w, ‖f'' z - f'' w‖ ≤ A + K * ‖z - w‖)
    (hmg : ∀ (p : Fin n) (k : Fin d),
      Measurable (Function.uncurry fun ω s => coordDeriv f' p (X s ω) * H p k ω s))
    (hpg : ∀ (p : Fin n) (k : Fin d), Probability.ProgressivelyMeasurable ℱ
      fun ω s => coordDeriv f' p (X s ω) * H p k ω s)
    (hqg : ∀ (p : Fin n) (k : Fin d) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖coordDeriv f' p (X s ω) * H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T) {m : ℕ} (hm0 : m ≠ 0) :
    Integrable (fun ω : Ω => f (X T ω) - f (X 0 ω)
        - ((∑ p : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
              coordDeriv f' p (X s ω) * bdrift p ω s ∂volume)
          + (∑ p : Fin n, ∑ k : Fin d, stochasticIntegralBrownian (W.W k) ℱ (hcoord k)
              (fun ω s => coordDeriv f' p (X s ω) * H p k ω s)
              (hmg p k) (hpg p k) (hqg p k) T ω)
          + 1 / 2 * ∑ p : Fin n, ∑ q : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
              coordDeriv₂ f'' p q (X s ω) * ∑ k : Fin d, H p k ω s * H q k ω s ∂volume)) P
      ∧ ∫ ω, |f (X T ω) - f (X 0 ω)
          - ((∑ p : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
                coordDeriv f' p (X s ω) * bdrift p ω s ∂volume)
            + (∑ p : Fin n, ∑ k : Fin d, stochasticIntegralBrownian (W.W k) ℱ (hcoord k)
                (fun ω s => coordDeriv f' p (X s ω) * H p k ω s)
                (hmg p k) (hpg p k) (hqg p k) T ω)
            + 1 / 2 * ∑ p : Fin n, ∑ q : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
                coordDeriv₂ f'' p q (X s ω)
                  * ∑ k : Fin d, H p k ω s * H q k ω s ∂volume)| ∂P
        ≤ vectorItoGridError (n : ℝ) (d : ℝ) B C T A K K₂ (T / (m : ℝ)) := by
  have hm' : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm0)
  have hmne : (m : ℝ) ≠ 0 := ne_of_gt hm'
  have hTm0 : (0 : ℝ) ≤ T / (m : ℝ) := (div_pos hT hm').le
  have hT0 : (0 : ℝ) ≤ T := hT.le
  have hf'd : Differentiable ℝ f' := fun z => (hf' z).differentiableAt
  have hf'c : Continuous f' := hf'd.continuous
  have hdecomp := (_root_.Prove2MeSourceProof.h_6647e433b820760a28ba04c2 (f := f) (f'' := f'') h) hbm hB hmg hpg hqg hT hm0
  -- (1) the Taylor remainder, transferred to the version
  obtain ⟨hZ1int0, hZ1le0⟩ := _root_.Prove2MeSourceProof.h_0362ffa5a8b426de4a0a426a W ℱ hcoord H hHm hHp
    hHs hC0 hCH X₀ hX₀ bdrift hbm hB0 hB hA0 hK0 hf hf' hf''c hf''aff hT hm0
  have hRae : (fun ω : Ω => LevyStochCalc.taylorRemainderNormed f f' f''
        (fun i => X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω) m)
      =ᵐ[P] fun ω : Ω => LevyStochCalc.taylorRemainderNormed f f' f''
        (fun i => LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω) m := by
    filter_upwards [h.ae_eq_all (LevyStochCalc.Brownian.Ito.unifGrid T m) fun i => LevyStochCalc.Brownian.Ito.unifGrid_nonneg hT.le m i] with ω hω
    have hfun : (fun i => X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
        = fun i => LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω :=
      funext hω
    rw [hfun]
  have e1 : (m : ℝ) * (B * (T / (m : ℝ))) ^ 3 = B ^ 3 * T * (T / (m : ℝ)) ^ 2 := by field_simp
  rw [e1] at hZ1le0
  have hZ1int : Integrable (fun ω : Ω => LevyStochCalc.taylorRemainderNormed f f' f''
      (fun i => X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω) m) P := hZ1int0.congr hRae.symm
  have hZ1le := le_trans (le_of_eq (MeasureTheory.integral_congr_ae (hRae.fun_comp abs))) hZ1le0
  -- (2) the drift Riemann sums
  have hZ2 := fun p : Fin n =>
    (fun p2mMethodArg0 p2mMethodArg1 => _root_.Prove2MeSourceProof.h_cc69b3b5abb273f29b8a03a8 p2mMethodArg0 p2mMethodArg1 h) hC0 hCH hbm hB0 hB (bdrift p) (hbm p) hB0 (hB p)
      (LevyStochCalc.continuous_coordDeriv hf'c p) (LevyStochCalc.abs_coordDeriv_le hf'bd p) le_rfl hK₂0
      (fun x y => by simpa using LevyStochCalc.abs_coordDeriv_sub_le hf' hf''bd p x y) hT hm0
  -- (3) the martingale Riemann sums
  have hZ3 : ∀ (p : Fin n) (k : Fin d),
      Integrable (fun ω : Ω => (∑ i ∈ Finset.range m, LevyStochCalc.coordDeriv f' p (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
            * (LevyStochCalc.Brownian.Ito.coordItoIntegral W ℱ hcoord H hHm hHp hHs p k (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω
              - LevyStochCalc.Brownian.Ito.coordItoIntegral W ℱ hcoord H hHm hHp hHs p k (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω))
          - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W k) ℱ (hcoord k)
              (fun ω s => LevyStochCalc.coordDeriv f' p (X s ω) * H p k ω s)
              (hmg p k) (hpg p k) (hqg p k) T ω) P
        ∧ ∫ ω, |(∑ i ∈ Finset.range m, LevyStochCalc.coordDeriv f' p (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
              * (LevyStochCalc.Brownian.Ito.coordItoIntegral W ℱ hcoord H hHm hHp hHs p k (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω
                - LevyStochCalc.Brownian.Ito.coordItoIntegral W ℱ hcoord H hHm hHp hHs p k (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω))
            - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W k) ℱ (hcoord k)
                (fun ω s => LevyStochCalc.coordDeriv f' p (X s ω) * H p k ω s)
                (hmg p k) (hpg p k) (hqg p k) T ω| ∂P
          ≤ Real.sqrt (C ^ 2 * (K₂ ^ 2 * (T * ((n : ℝ) * (2 * (B * (T / (m : ℝ))) ^ 2
              + 2 * ((d : ℝ) ^ 2 * (C ^ 2 * (T / (m : ℝ))))))))) := by
    intro p k
    have hfin : ∀ ω : Ω,
        (∑ i ∈ Finset.range m, LevyStochCalc.coordDeriv f' p (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
            * (LevyStochCalc.Brownian.Ito.coordItoIntegral W ℱ hcoord H hHm hHp hHs p k (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω
              - LevyStochCalc.Brownian.Ito.coordItoIntegral W ℱ hcoord H hHm hHp hHs p k (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω))
          = ∑ i : Fin m, LevyStochCalc.coordDeriv f' p (X (LevyStochCalc.Brownian.Ito.unifGrid T m (i : ℕ)) ω)
            * (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W k) ℱ (hcoord k) (H p k) (hHm p k) (hHp p k)
                  (hHs p k) (LevyStochCalc.Brownian.Ito.unifGrid T m ((i : ℕ) + 1)) ω
              - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W k) ℱ (hcoord k) (H p k) (hHm p k) (hHp p k)
                  (hHs p k) (LevyStochCalc.Brownian.Ito.unifGrid T m (i : ℕ)) ω) := fun ω =>
      (Fin.sum_univ_eq_sum_range (fun i => LevyStochCalc.coordDeriv f' p (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
        * (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W k) ℱ (hcoord k) (H p k) (hHm p k) (hHp p k)
              (hHs p k) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω
          - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W k) ℱ (hcoord k) (H p k) (hHm p k) (hHp p k)
              (hHs p k) (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)) m).symm
    have hmeas : Measurable (fun ω : Ω =>
        (∑ i ∈ Finset.range m, LevyStochCalc.coordDeriv f' p (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
            * (LevyStochCalc.Brownian.Ito.coordItoIntegral W ℱ hcoord H hHm hHp hHs p k (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω
              - LevyStochCalc.Brownian.Ito.coordItoIntegral W ℱ hcoord H hHm hHp hHs p k (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω))
          - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W k) ℱ (hcoord k)
              (fun ω s => LevyStochCalc.coordDeriv f' p (X s ω) * H p k ω s)
              (hmg p k) (hpg p k) (hqg p k) T ω) := by
      refine Measurable.sub (Finset.measurable_sum _ fun i _ =>
        (((LevyStochCalc.continuous_coordDeriv hf'c p).measurable.comp
            (h.measurable (LevyStochCalc.Brownian.Ito.unifGrid T m i))).mul
          ((LevyStochCalc.Brownian.Ito.measurable_coordItoIntegral W ℱ hcoord H hHm hHp hHs p k _).sub
            (LevyStochCalc.Brownian.Ito.measurable_coordItoIntegral W ℱ hcoord H hHm hHp hHs p k _)))) ?_
      exact ((LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_stronglyAdapted (W.W k) ℱ (hcoord k) _ (hmg p k)
        (hpg p k) (hqg p k) T).mono (ℱ.le T)).measurable
    have hV0 : (0 : ℝ) ≤ C ^ 2 * (K₂ ^ 2 * (T * ((n : ℝ) * (2 * (B * (T / (m : ℝ))) ^ 2
        + 2 * ((d : ℝ) ^ 2 * (C ^ 2 * (T / (m : ℝ)))))))) := by positivity
    refine _root_.Prove2MeSourceProof.h_84dc228d7203d8f3c18ebbd6 hmeas.aestronglyMeasurable hV0 ?_
    have hsq := (fun p2mMethodArg0 p2mMethodArg1 => _root_.Prove2MeSourceProof.h_cebf5e28c49b85cc9ea79d78 p2mMethodArg0 p2mMethodArg1 h) hC0 hCH hbm hB0 hB
      (LevyStochCalc.abs_coordDeriv_le hf'bd p) hK₂0 (LevyStochCalc.abs_coordDeriv_sub_le hf' hf''bd p) k
      (hHm p k) (hHp p k) (hHs p k) hC0 (hCH p k) (hmg p k) (hpg p k) (hqg p k) hT hm0
    simp only [hfin]
    refine hsq.trans (le_of_eq ?_)
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  -- (4) the weighted quadratic variations
  have hZ4 := fun p q : Fin n =>
    (fun p2mMethodArg0 p2mMethodArg1 => _root_.Prove2MeSourceProof.h_3e3db1d7d302cb153d64875c p2mMethodArg0 p2mMethodArg1 h) hC0 hCH hbm hB0 hB p q (hma p q) (hpa p q) (hqa p q)
      (LevyStochCalc.continuous_coordDeriv₂ hf''c p q) hK₂0 (LevyStochCalc.abs_coordDeriv₂_le hf''bd p q) hA0 hK0
      (_root_.Prove2MeSourceProof.h_9e8c1965c746b09726c017d4 hf''aff p q) hT hm0
  have e2 : (m : ℝ) * (K₂ * (B * (T / (m : ℝ))) ^ 2) = K₂ * B ^ 2 * T * (T / (m : ℝ)) := by
    field_simp
  have e3 : (m : ℝ) * (K₂ * (B * (T / (m : ℝ)) * ((d : ℝ) * (C * Real.sqrt (T / (m : ℝ))))))
      = K₂ * B * (d : ℝ) * C * T * Real.sqrt (T / (m : ℝ)) := by
    field_simp
  have e4 : T ^ 2 / (m : ℝ) = T * (T / (m : ℝ)) := by
    field_simp
  simp only [e2, e3, e4] at hZ4
  -- assemble the four families
  have hZ2int : Integrable (fun ω : Ω => ∑ p : Fin n,
      ((∑ i ∈ Finset.range m, LevyStochCalc.coordDeriv f' p (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
          * ∫ s in Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)), bdrift p ω s ∂volume)
        - ∫ s in Set.Ioc (0 : ℝ) T, LevyStochCalc.coordDeriv f' p (X s ω) * bdrift p ω s ∂volume)) P :=
    MeasureTheory.integrable_finsetSum _ fun p _ => (hZ2 p).1
  have hZ2le : ∫ ω, |∑ p : Fin n,
        ((∑ i ∈ Finset.range m, LevyStochCalc.coordDeriv f' p (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
            * ∫ s in Set.Ioc (LevyStochCalc.Brownian.Ito.unifGrid T m i) (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)), bdrift p ω s ∂volume)
          - ∫ s in Set.Ioc (0 : ℝ) T, LevyStochCalc.coordDeriv f' p (X s ω) * bdrift p ω s ∂volume)| ∂P
      ≤ (n : ℝ) * (0 * B * T + K₂ * B * (T * ((n : ℝ) * (B * (T / (m : ℝ))
        + (d : ℝ) * (C * Real.sqrt (T / (m : ℝ))))))) := by
    refine (LevyStochCalc.Brownian.Ito.integral_abs_finsetSum_le _ _ (fun p _ => (hZ2 p).1) _ (fun p _ => (hZ2 p).2)).trans ?_
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hZ3int : Integrable (fun ω : Ω => ∑ p : Fin n, ∑ k : Fin d,
      ((∑ i ∈ Finset.range m, LevyStochCalc.coordDeriv f' p (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
          * (LevyStochCalc.Brownian.Ito.coordItoIntegral W ℱ hcoord H hHm hHp hHs p k (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω
            - LevyStochCalc.Brownian.Ito.coordItoIntegral W ℱ hcoord H hHm hHp hHs p k (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω))
        - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W k) ℱ (hcoord k)
            (fun ω s => LevyStochCalc.coordDeriv f' p (X s ω) * H p k ω s)
            (hmg p k) (hpg p k) (hqg p k) T ω)) P :=
    MeasureTheory.integrable_finsetSum _ fun p _ =>
      MeasureTheory.integrable_finsetSum _ fun k _ => (hZ3 p k).1
  have hZ3le : ∫ ω, |∑ p : Fin n, ∑ k : Fin d,
        ((∑ i ∈ Finset.range m, LevyStochCalc.coordDeriv f' p (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
            * (LevyStochCalc.Brownian.Ito.coordItoIntegral W ℱ hcoord H hHm hHp hHs p k (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω
              - LevyStochCalc.Brownian.Ito.coordItoIntegral W ℱ hcoord H hHm hHp hHs p k (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω))
          - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W k) ℱ (hcoord k)
              (fun ω s => LevyStochCalc.coordDeriv f' p (X s ω) * H p k ω s)
              (hmg p k) (hpg p k) (hqg p k) T ω)| ∂P
      ≤ (n : ℝ) * ((d : ℝ) * Real.sqrt (C ^ 2 * (K₂ ^ 2 * (T * ((n : ℝ)
        * (2 * (B * (T / (m : ℝ))) ^ 2
          + 2 * ((d : ℝ) ^ 2 * (C ^ 2 * (T / (m : ℝ)))))))))) := by
    refine (LevyStochCalc.Brownian.Ito.integral_abs_finsetSum_le _ _
      (fun p _ => MeasureTheory.integrable_finsetSum _ fun k _ => (hZ3 p k).1)
      (fun _ => (d : ℝ) * Real.sqrt (C ^ 2 * (K₂ ^ 2 * (T * ((n : ℝ)
        * (2 * (B * (T / (m : ℝ))) ^ 2
          + 2 * ((d : ℝ) ^ 2 * (C ^ 2 * (T / (m : ℝ))))))))))
      (fun p _ => ?_)).trans ?_
    · refine (LevyStochCalc.Brownian.Ito.integral_abs_finsetSum_le _ _ (fun k _ => (hZ3 p k).1) _
        (fun k _ => (hZ3 p k).2)).trans ?_
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    · rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hZ4int : Integrable (fun ω : Ω => 1 / 2 * ∑ p : Fin n, ∑ q : Fin n,
      ((∑ i ∈ Finset.range m, LevyStochCalc.coordDeriv₂ f'' p q (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
          * ((X (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω p - X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω p)
            * (X (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω q - X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω q)))
        - ∫ s in Set.Ioc (0 : ℝ) T,
            LevyStochCalc.coordDeriv₂ f'' p q (X s ω) * ∑ k : Fin d, H p k ω s * H q k ω s ∂volume)) P :=
    (MeasureTheory.integrable_finsetSum _ fun p _ =>
      MeasureTheory.integrable_finsetSum _ fun q _ => (hZ4 p q).1).const_mul _
  have hZ4le : ∫ ω, |1 / 2 * ∑ p : Fin n, ∑ q : Fin n,
        ((∑ i ∈ Finset.range m, LevyStochCalc.coordDeriv₂ f'' p q (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
            * ((X (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω p - X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω p)
              * (X (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω q - X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω q)))
          - ∫ s in Set.Ioc (0 : ℝ) T,
              LevyStochCalc.coordDeriv₂ f'' p q (X s ω) * ∑ k : Fin d, H p k ω s * H q k ω s ∂volume)| ∂P
      ≤ 1 / 2 * ((n : ℝ) * ((n : ℝ) * (K₂ * B ^ 2 * T * (T / (m : ℝ))
        + K₂ * B * (d : ℝ) * C * T * Real.sqrt (T / (m : ℝ))
        + K₂ * B * (d : ℝ) * C * T * Real.sqrt (T / (m : ℝ))
        + (d : ℝ) * Real.sqrt (K₂ ^ 2
            * (3 * ((2 * (6 + LevyStochCalc.Brownian.Ito.gaussianFourthMoment) + 2) * (2 * C) ^ 4))
            * (T * (T / (m : ℝ))))
        + (d : ℝ) ^ 2 * Real.sqrt (K₂ ^ 2
            * ((6 + LevyStochCalc.Brownian.Ito.gaussianFourthMoment) * (C ^ 4 + C ^ 4) / 2) * (T * (T / (m : ℝ))))
        + (A * ((d : ℝ) * C ^ 2) * T
          + K * ((d : ℝ) * C ^ 2) * (T * ((n : ℝ) * (B * (T / (m : ℝ))
            + (d : ℝ) * (C * Real.sqrt (T / (m : ℝ)))))))))) := by
    have habs : ∀ ω : Ω, |1 / 2 * ∑ p : Fin n, ∑ q : Fin n,
          ((∑ i ∈ Finset.range m, LevyStochCalc.coordDeriv₂ f'' p q (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
              * ((X (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω p - X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω p)
                * (X (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω q - X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω q)))
            - ∫ s in Set.Ioc (0 : ℝ) T,
                LevyStochCalc.coordDeriv₂ f'' p q (X s ω) * ∑ k : Fin d, H p k ω s * H q k ω s ∂volume)|
        = 1 / 2 * |∑ p : Fin n, ∑ q : Fin n,
          ((∑ i ∈ Finset.range m, LevyStochCalc.coordDeriv₂ f'' p q (X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω)
              * ((X (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω p - X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω p)
                * (X (LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1)) ω q - X (LevyStochCalc.Brownian.Ito.unifGrid T m i) ω q)))
            - ∫ s in Set.Ioc (0 : ℝ) T,
                LevyStochCalc.coordDeriv₂ f'' p q (X s ω)
                  * ∑ k : Fin d, H p k ω s * H q k ω s ∂volume)| := by
      intro ω
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    simp_rw [habs]
    rw [MeasureTheory.integral_const_mul]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    refine (LevyStochCalc.Brownian.Ito.integral_abs_finsetSum_le _ _
      (fun p _ => MeasureTheory.integrable_finsetSum _ fun q _ => (hZ4 p q).1)
      (fun _ => (n : ℝ) * (K₂ * B ^ 2 * T * (T / (m : ℝ))
        + K₂ * B * (d : ℝ) * C * T * Real.sqrt (T / (m : ℝ))
        + K₂ * B * (d : ℝ) * C * T * Real.sqrt (T / (m : ℝ))
        + (d : ℝ) * Real.sqrt (K₂ ^ 2
            * (3 * ((2 * (6 + LevyStochCalc.Brownian.Ito.gaussianFourthMoment) + 2) * (2 * C) ^ 4))
            * (T * (T / (m : ℝ))))
        + (d : ℝ) ^ 2 * Real.sqrt (K₂ ^ 2
            * ((6 + LevyStochCalc.Brownian.Ito.gaussianFourthMoment) * (C ^ 4 + C ^ 4) / 2) * (T * (T / (m : ℝ))))
        + (A * ((d : ℝ) * C ^ 2) * T
          + K * ((d : ℝ) * C ^ 2) * (T * ((n : ℝ) * (B * (T / (m : ℝ))
            + (d : ℝ) * (C * Real.sqrt (T / (m : ℝ)))))))))
      (fun p _ => ?_)).trans ?_
    · refine (LevyStochCalc.Brownian.Ito.integral_abs_finsetSum_le _ _ (fun q _ => (hZ4 p q).1) _
        (fun q _ => (hZ4 p q).2)).trans ?_
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    · rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  refine ⟨(((hZ1int.add hZ2int).add hZ3int).add hZ4int).congr hdecomp.symm, ?_⟩
  refine le_trans (le_of_eq (MeasureTheory.integral_congr_ae (hdecomp.fun_comp abs))) ?_
  refine le_trans (_root_.Prove2MeSourceProof.h_724ac40b8d5293986a0749a0 hZ1int hZ2int hZ3int hZ4int hZ1le hZ2le hZ3le hZ4le)
    (le_of_eq ?_)
  unfold LevyStochCalc.Brownian.Ito.vectorItoGridError
  ring
end Formula

end LevyStochCalc.Brownian.Ito


