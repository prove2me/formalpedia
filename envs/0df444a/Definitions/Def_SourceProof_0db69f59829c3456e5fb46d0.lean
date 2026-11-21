-- Prove2me | Definitions.Def_SourceProof_0db69f59829c3456e5fb46d0
-- name    : SourceProof_0db69f59829c3456e5fb46d0
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:53:24.696497+00:00
-- url     : https://prove2.me/theorems/0dd0af8c-a76c-4f2c-b4bf-5f44ff77699e
-- title:
--   LevyStochCalc source module: SourceProof_0db69f59829c3456e5fb46d0
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.IsVectorItoVersion.itoFormula_localise` comes from the `LevyStochCalc.Brownian.ItoCutoff` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoCutoff_F001
import Definitions.Def_LevyStochCalc_Brownian_ItoCutoff_F002
import Definitions.Def_SourceProof_05b52d6373160625930b090a
import Definitions.Def_SourceProof_ae47f47307f762c81c3ce31c
import Definitions.Def_SourceProof_c9f8d91666f468ff1aabe966
import Definitions.Def_SourceProof_d86afb596da14bf8864c8c9c
import Definitions.Def_SourceProof_d995487e738cd5a8e87f428b

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Itô's formula for a twice continuously differentiable function

Multiplying `f` by a smooth box cutoff leaves it, together with its first two derivatives,
unchanged on a cube and makes them bounded and uniformly continuous. Along a path stopped before
it leaves that cube the two functions therefore give the same integrands, and the local property
of the Itô integral transfers the stochastic terms.

## Main statements

* `LevyStochCalc.cutoffFun` — the cut-off function.
* `LevyStochCalc.fderiv_cutoffFun` — its first two derivatives agree with `f`'s on the cube.
* `LevyStochCalc.Brownian.Ito.IsVectorItoVersion.itoFormula_of_contDiff` — Itô's formula for a
  twice continuously differentiable function, with no bound on its derivatives.
-/

namespace LevyStochCalc

open scoped Topology

section Cutoff

variable {n : ℕ}

end Cutoff

namespace Brownian.Ito

open MeasureTheory ProbabilityTheory LevyStochCalc.Brownian.Multidim LevyStochCalc.Probability
open scoped NNReal ENNReal

universe u

section Bounded

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

end Bounded

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


theorem _root_.Prove2MeSourceProof.h_0db69f59829c3456e5fb46d0
    (h : IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift X)
    {f : (Fin n → ℝ) → ℝ} {f' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ}
    {f'' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ}
    (hfC : ContDiff ℝ 2 f)
    (hf : ∀ z, HasFDerivAt f (f' z) z) (hf' : ∀ z, HasFDerivAt f' (f'' z) z)
    (hmg : ∀ (p : Fin n) (k : Fin d),
      Measurable (Function.uncurry fun ω s => coordDeriv f' p (X s ω) * H p k ω s))
    (hpg : ∀ (p : Fin n) (k : Fin d), Probability.ProgressivelyMeasurable ℱ
      fun ω s => coordDeriv f' p (X s ω) * H p k ω s)
    (hqg : ∀ (p : Fin n) (k : Fin d) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖coordDeriv f' p (X s ω) * H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T)
    (hbase : ∀ (g : (Fin n → ℝ) → ℝ) (g' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ)
      (g'' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ) (K₁ K₂ : ℝ),
      (∀ z, HasFDerivAt g (g' z) z) → (∀ z, HasFDerivAt g' (g'' z) z) →
      (∀ z, ‖g' z‖ ≤ K₁) → 0 ≤ K₂ → (∀ z, ‖g'' z‖ ≤ K₂) →
      Continuous g' → Continuous g'' →
      (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ z w : Fin n → ℝ, ‖z - w‖ < δ → ‖g'' z - g'' w‖ ≤ ε) →
      ∀ (hmG : ∀ (p : Fin n) (k : Fin d), Measurable (Function.uncurry
          fun ω s => coordDeriv g' p (X s ω) * H p k ω s))
        (hpG : ∀ (p : Fin n) (k : Fin d), Probability.ProgressivelyMeasurable ℱ
          fun ω s => coordDeriv g' p (X s ω) * H p k ω s)
        (hqG : ∀ (p : Fin n) (k : Fin d) (T' : ℝ), 0 < T' →
          ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
            (‖coordDeriv g' p (X s ω) * H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤),
      (fun ω : Ω => g (X T ω) - g (X 0 ω)) =ᵐ[P] fun ω : Ω =>
        (∑ p : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
            coordDeriv g' p (X s ω) * bdrift p ω s ∂volume)
          + (∑ p : Fin n, ∑ k : Fin d, stochasticIntegralBrownian (W.W k) ℱ (hcoord k)
              (fun ω s => coordDeriv g' p (X s ω) * H p k ω s)
              (hmG p k) (hpG p k) (hqG p k) T ω)
          + 1 / 2 * ∑ p : Fin n, ∑ q : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
              coordDeriv₂ g'' p q (X s ω) * ∑ k : Fin d, H p k ω s * H q k ω s ∂volume) :
    (fun ω : Ω => f (X T ω) - f (X 0 ω)) =ᵐ[P] fun ω : Ω =>
      (∑ p : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
          coordDeriv f' p (X s ω) * bdrift p ω s ∂volume)
        + (∑ p : Fin n, ∑ j : Fin d, stochasticIntegralBrownian (W.W j) ℱ (hcoord j)
            (fun ω s => coordDeriv f' p (X s ω) * H p j ω s)
            (hmg p j) (hpg p j) (hqg p j) T ω)
        + 1 / 2 * ∑ p : Fin n, ∑ q : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
            coordDeriv₂ f'' p q (X s ω) * ∑ j : Fin d, H p j ω s * H q j ω s ∂volume := by
  classical
  have hf'eq : f' = fderiv ℝ f := funext fun z => (hf z).fderiv.symm
  have hf''eq : f'' = fderiv ℝ (fderiv ℝ f) := by
    funext z
    have hz := (hf' z).fderiv
    rw [← hf'eq]
    exact hz.symm
  have hstep : ∀ m : ℕ, 0 < m → ∀ᵐ ω ∂P,
      ((T : ℝ) : WithTop ℝ) < LevyStochCalc.Probability.exitTime (fun ω t => X t ω) (m : ℝ) ω →
        f (X T ω) - f (X 0 ω)
          = (∑ p : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
                LevyStochCalc.coordDeriv f' p (X s ω) * bdrift p ω s ∂volume)
            + (∑ p : Fin n, ∑ j : Fin d, LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W j) ℱ (hcoord j)
                (fun ω s => LevyStochCalc.coordDeriv f' p (X s ω) * H p j ω s)
                (hmg p j) (hpg p j) (hqg p j) T ω)
            + 1 / 2 * ∑ p : Fin n, ∑ q : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
                LevyStochCalc.coordDeriv₂ f'' p q (X s ω)
                  * ∑ j : Fin d, H p j ω s * H q j ω s ∂volume := by
    intro m hm0
    have hR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm0
    set R : ℝ := (m : ℝ) with hRdef
    set g : (Fin n → ℝ) → ℝ := LevyStochCalc.cutoffFun f R with hgdef
    set τ : Ω → WithTop ℝ := LevyStochCalc.Probability.exitTime (fun ω t => X t ω) R with hτdef
    have hadapt : MeasureTheory.Adapted ℱ (fun r ω => X r ω) :=
      fun r => (h.adapted r).measurable
    have hτ : MeasureTheory.IsStoppingTime ℱ τ :=
      LevyStochCalc.Probability.isStoppingTime_exitTime (X := fun ω t => X t ω) hadapt
        (fun ω => h.continuous_path ω) R
    have hR32 : R < 3 * R / 2 := by linarith
    have hg'c : Continuous (fderiv ℝ g) := LevyStochCalc.continuous_fderiv_cutoffFun hfC R
    have hg''c : Continuous (fderiv ℝ (fderiv ℝ g)) := LevyStochCalc.continuous_fderiv_fderiv_cutoffFun hfC R
    have hgf : ∀ z, HasFDerivAt g (fderiv ℝ g z) z :=
      fun z => (LevyStochCalc.differentiable_cutoffFun hfC R z).hasFDerivAt
    have hgf' : ∀ z, HasFDerivAt (fderiv ℝ g) (fderiv ℝ (fderiv ℝ g) z) z :=
      fun z => (LevyStochCalc.differentiable_fderiv_cutoffFun hfC R z).hasFDerivAt
    obtain ⟨K₁, hK₁⟩ := _root_.Prove2MeSourceProof.h_d86afb596da14bf8864c8c9c hfC hR
    obtain ⟨K₂, hK₂0, hK₂⟩ := _root_.Prove2MeSourceProof.h_05b52d6373160625930b090a hfC hR
    have hK₁0 : (0 : ℝ) ≤ K₁ := le_trans (norm_nonneg _) (hK₁ 0)
    have hunif : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ z w : Fin n → ℝ, ‖z - w‖ < δ →
          ‖fderiv ℝ (fderiv ℝ g) z - fderiv ℝ (fderiv ℝ g) w‖ ≤ ε :=
      fun ε hε => LevyStochCalc.exists_delta_fderiv_fderiv_cutoffFun hfC hR hε
    -- the two families of integrands agree on the cube
    have hd1 : ∀ (p : Fin n) (z : Fin n → ℝ), ‖z‖ < 3 * R / 2 →
        LevyStochCalc.coordDeriv (fderiv ℝ g) p z = LevyStochCalc.coordDeriv f' p z := by
      intro p z hz
      rw [hf'eq]
      unfold LevyStochCalc.coordDeriv
      rw [LevyStochCalc.fderiv_cutoffFun (f := f) hR hz]
    have hd2 : ∀ (p q : Fin n) (z : Fin n → ℝ), ‖z‖ < 3 * R / 2 →
        LevyStochCalc.coordDeriv₂ (fderiv ℝ (fderiv ℝ g)) p q z = LevyStochCalc.coordDeriv₂ f'' p q z := by
      intro p q z hz
      rw [hf''eq]
      unfold LevyStochCalc.coordDeriv₂
      rw [LevyStochCalc.fderiv_fderiv_cutoffFun (f := f) hR hz]
    have hd0 : ∀ z : Fin n → ℝ, ‖z‖ < 3 * R / 2 → g z = f z := by
      intro z hz
      rw [hgdef, LevyStochCalc.cutoffFun, LevyStochCalc.boxCut_eq_one hR hz.le, mul_one]
    -- the cut integrands
    have hmgG : ∀ (p : Fin n) (j : Fin d),
        Measurable (Function.uncurry fun ω s =>
          LevyStochCalc.coordDeriv (fderiv ℝ g) p (X s ω) * H p j ω s) :=
      fun p j =>
        (h.measurable_uncurry_comp (LevyStochCalc.continuous_coordDeriv hg'c p).measurable).mul (hHm p j)
    have hpgG : ∀ (p : Fin n) (j : Fin d), LevyStochCalc.Probability.ProgressivelyMeasurable ℱ
        fun ω s => LevyStochCalc.coordDeriv (fderiv ℝ g) p (X s ω) * H p j ω s :=
      fun p j => (h.progressivelyMeasurable_comp (LevyStochCalc.continuous_coordDeriv hg'c p)).mul (hHp p j)
    have hqgG : ∀ (p : Fin n) (j : Fin d) (T' : ℝ), 0 < T' →
        ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
          (‖LevyStochCalc.coordDeriv (fderiv ℝ g) p (X s ω) * H p j ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
      intro p j
      refine LevyStochCalc.Brownian.Ito.energy_lt_top_of_abs_le_mul (c := K₁) hK₁0 (fun ω s => ?_) (hHs p j)
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (LevyStochCalc.abs_coordDeriv_le hK₁ p _) (abs_nonneg _)
    have hform := hbase g (fderiv ℝ g) (fderiv ℝ (fderiv ℝ g)) K₁ K₂ hgf hgf' hK₁ hK₂0 hK₂
      hg'c hg''c hunif hmgG hpgG hqgG
    have hSI : ∀ᵐ ω ∂P, ∀ (p : Fin n) (j : Fin d), ((T : ℝ) : WithTop ℝ) ≤ τ ω →
        LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W j) ℱ (hcoord j)
            (fun ω s => LevyStochCalc.coordDeriv (fderiv ℝ g) p (X s ω) * H p j ω s)
            (hmgG p j) (hpgG p j) (hqgG p j) T ω
          = LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W j) ℱ (hcoord j)
            (fun ω s => LevyStochCalc.coordDeriv f' p (X s ω) * H p j ω s)
            (hmg p j) (hpg p j) (hqg p j) T ω := by
      rw [MeasureTheory.ae_all_iff]
      intro p
      rw [MeasureTheory.ae_all_iff]
      intro j
      refine _root_.Prove2MeSourceProof.h_c9f8d91666f468ff1aabe966 τ (W.W j) ℱ (hcoord j) hτ
        (hmgG p j) (hpgG p j) (hqgG p j) (hmg p j) (hpg p j) (hqg p j) (fun ω s hs hle => ?_) hT
      have hnorm : ‖X s ω‖ ≤ R :=
        _root_.Prove2MeSourceProof.h_d995487e738cd5a8e87f428b (h.continuous_path ω) hs hle
      rw [hd1 p (X s ω) (lt_of_le_of_lt hnorm hR32)]
    filter_upwards [hform, hSI] with ω hω hSIω hlt
    have hball : ∀ s ∈ Set.Icc (0 : ℝ) T, ‖X s ω‖ < R := by
      intro s hs
      by_contra hcon
      have hmem : ∃ u ∈ Set.Icc (0 : ℝ) T, R ≤ ‖X u ω‖ := ⟨s, hs, not_lt.mp hcon⟩
      have := (_root_.Prove2MeSourceProof.h_0ae884fc5aa0cf4d6b9eb536 (X := fun ω t => X t ω)
        (h.continuous_path ω) R T).2 hmem
      exact absurd this (not_le.mpr hlt)
    have hballs : ∀ s ∈ Set.Ioc (0 : ℝ) T, ‖X s ω‖ < 3 * R / 2 := fun s hs =>
      lt_trans (hball s ⟨hs.1.le, hs.2⟩) hR32
    have hT' : ‖X T ω‖ < 3 * R / 2 :=
      lt_trans (hball T ⟨hT.le, le_rfl⟩) hR32
    have h0' : ‖X 0 ω‖ < 3 * R / 2 :=
      lt_trans (hball 0 ⟨le_rfl, hT.le⟩) hR32
    have hleτ : ((T : ℝ) : WithTop ℝ) ≤ τ ω := le_of_lt hlt
    have e1 : (∑ p : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
          LevyStochCalc.coordDeriv (fderiv ℝ g) p (X s ω) * bdrift p ω s ∂volume)
        = ∑ p : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
          LevyStochCalc.coordDeriv f' p (X s ω) * bdrift p ω s ∂volume := by
      refine Finset.sum_congr rfl fun p _ => ?_
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun s hs => ?_
      rw [hd1 p (X s ω) (hballs s hs)]
    have e2 : (∑ p : Fin n, ∑ j : Fin d, LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W j) ℱ (hcoord j)
            (fun ω s => LevyStochCalc.coordDeriv (fderiv ℝ g) p (X s ω) * H p j ω s)
            (hmgG p j) (hpgG p j) (hqgG p j) T ω)
        = ∑ p : Fin n, ∑ j : Fin d, LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W j) ℱ (hcoord j)
            (fun ω s => LevyStochCalc.coordDeriv f' p (X s ω) * H p j ω s)
            (hmg p j) (hpg p j) (hqg p j) T ω :=
      Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun j _ => hSIω p j hleτ
    have e3 : (1 / 2 * ∑ p : Fin n, ∑ q : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
            LevyStochCalc.coordDeriv₂ (fderiv ℝ (fderiv ℝ g)) p q (X s ω)
              * ∑ j : Fin d, H p j ω s * H q j ω s ∂volume)
        = 1 / 2 * ∑ p : Fin n, ∑ q : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
            LevyStochCalc.coordDeriv₂ f'' p q (X s ω)
              * ∑ j : Fin d, H p j ω s * H q j ω s ∂volume := by
      refine congrArg (fun x => 1 / 2 * x) ?_
      refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun s hs => ?_
      rw [hd2 p q (X s ω) (hballs s hs)]
    rw [← hd0 _ hT', ← hd0 _ h0', hω, e1, e2, e3]
  have hall : ∀ᵐ ω ∂P, ∀ m : ℕ, 0 < m →
      ((T : ℝ) : WithTop ℝ) < LevyStochCalc.Probability.exitTime (fun ω t => X t ω) (m : ℝ) ω →
        f (X T ω) - f (X 0 ω)
          = (∑ p : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
                LevyStochCalc.coordDeriv f' p (X s ω) * bdrift p ω s ∂volume)
            + (∑ p : Fin n, ∑ j : Fin d, LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W j) ℱ (hcoord j)
                (fun ω s => LevyStochCalc.coordDeriv f' p (X s ω) * H p j ω s)
                (hmg p j) (hpg p j) (hqg p j) T ω)
            + 1 / 2 * ∑ p : Fin n, ∑ q : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
                LevyStochCalc.coordDeriv₂ f'' p q (X s ω)
                  * ∑ j : Fin d, H p j ω s * H q j ω s ∂volume := by
    rw [MeasureTheory.ae_all_iff]
    intro m
    by_cases hm : 0 < m
    · filter_upwards [hstep m hm] with ω hω
      exact fun _ => hω
    · exact Filter.Eventually.of_forall fun ω hcon => absurd hcon hm
  filter_upwards [hall] with ω hω
  obtain ⟨K, hK⟩ := _root_.Prove2MeSourceProof.h_ae47f47307f762c81c3ce31c (X := fun ω t => X t ω)
    (h.continuous_path ω) hT.le
  exact hω (max K 1) (lt_of_lt_of_le Nat.zero_lt_one (le_max_right K 1))
    (hK (max K 1) (le_max_left K 1))
end Formula

end Brownian.Ito

end LevyStochCalc


