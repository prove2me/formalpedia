-- Prove2me | Definitions.Def_SourceProof_607e96fa91c679c474a24409
-- name    : SourceProof_607e96fa91c679c474a24409
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:24:33.437651+00:00
-- url     : https://prove2.me/theorems/f69a3e9e-429c-4c14-9f6d-a53017a6c278
-- title:
--   LevyStochCalc source module: SourceProof_607e96fa91c679c474a24409
-- statement:
--   The original source theorem `LevyStochCalc.Driver.product_rule` comes from the `LevyStochCalc.Driver.ProductRule` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionQuadVar_F000
import Definitions.Def_LevyStochCalc_Driver_ProductRule_F000
import Definitions.Def_SourceProof_7c0d8c620a9a0a0ece056f63
import Definitions.Def_SourceProof_f7873a967b51c0099c698616

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The product rule for a continuous Itô process and a pure-jump process

For a continuous version `X` of an Itô process and a bounded adapted process `Y` whose paths are
the sums of finitely many jumps, at the atoms of a Poisson random measure on a window of finite
intensity, the product satisfies

  `X_t Y_t − X_0 Y_0 = ∫_0^t Y_{s−} dX_s + Σ_{atoms (τ, e), τ ≤ t} X_τ ΔY_(τ, e)`

with no covariation term: on the dyadic grids of `[0, t]` the telescoping identity
`Σ Y_{t_k} (X_{t_{k+1}} − X_{t_k}) + Σ X_{t_{k+1}} (Y_{t_{k+1}} − Y_{t_k})` is exact, the first sum
is the Itô integral of the frozen process (`Brownian/LeftFreeze.lean`) plus a Riemann sum of the
drift, and the second converges pathwise to the jump sum (`Analysis/FiniteJumpSum.lean`).
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Driver

open LevyStochCalc.Analysis LevyStochCalc.Brownian.Ito

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]

section Core

variable (Y : ℝ → Ω → ℝ) {C : ℝ} (hYb : ∀ s ω, |Y s ω| ≤ C) (hYm : ∀ s, Measurable (Y s))
  {t : ℝ} (ht : 0 < t)

end Core

section Wrapper

variable [MeasurableSingletonClass E] [MeasurableSpace.CountablyGenerated E] {P : Measure Ω}
  [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] (N : Poisson.PoissonRandomMeasure P ν)

variable (W : LevyStochCalc.Brownian.BrownianMotion P) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hℱ : LevyStochCalc.Brownian.IsBrownianFiltration W ℱ) (H : Ω → ℝ → ℝ)
  (hm : Measurable (Function.uncurry H))
  (hp : Probability.ProgressivelyMeasurable ℱ H)
  (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)

include hℱ in

theorem _root_.Prove2MeSourceProof.h_607e96fa91c679c474a24409 {X₀ : Ω → ℝ} {bdrift : Ω → ℝ → ℝ} {X : ℝ → Ω → ℝ}
    (hX : IsItoVersion W ℱ hℱ H hm hp hq X₀ bdrift X)
    (hbm : Measurable (Function.uncurry bdrift)) {B : ℝ} (hB : ∀ ω s, |bdrift ω s| ≤ B)
    {R : Set (ℝ × E)} (hRm : MeasurableSet R)
    (hRfin : Poisson.referenceIntensity ν R ≠ ⊤) {g : Ω → ℝ × E → ℝ}
    (Y : ℝ → Ω → ℝ) {C : ℝ} (hYb : ∀ s ω, |Y s ω| ≤ C) (hYm : ∀ s, Measurable (Y s))
    (hYad : ∀ s, StronglyMeasurable[ℱ s] (Y s))
    (hY : ∀ᵐ ω ∂P, ∀ s,
      Y s ω = Y 0 ω + ∫ p in R ∩ Set.Ioc (0 : ℝ) s ×ˢ Set.univ, g ω p ∂(N.N ω))
    (Yminus : ℝ → Ω → ℝ) (hYmb : ∀ s ω, |Yminus s ω| ≤ C)
    (hYminus : ∀ᵐ ω ∂P, ∀ s,
      Yminus s ω = Y 0 ω + ∫ p in R ∩ Set.Ioo (0 : ℝ) s ×ˢ Set.univ, g ω p ∂(N.N ω))
    (hmm' : Measurable (Function.uncurry fun ω s => Yminus s ω * H ω s))
    (hmp' : Probability.ProgressivelyMeasurable ℱ fun ω s => Yminus s ω * H ω s)
    (hmq' : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖Yminus s ω * H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {t : ℝ} (ht : 0 < t) :
    ∀ᵐ ω ∂P, X t ω * Y t ω - X 0 ω * Y 0 ω
      = stochasticIntegralBrownian W ℱ hℱ (fun ω s => Yminus s ω * H ω s) hmm' hmp' hmq' t ω
        + (∫ s in Set.Ioc (0 : ℝ) t, Yminus s ω * bdrift ω s ∂volume)
        + ∫ p in R ∩ Set.Ioc (0 : ℝ) t ×ˢ Set.univ, X p.1 ω * g ω p ∂(N.N ω) := by
  classical
  have hmono := LevyStochCalc.Analysis.dyadicPartition_strictMono ht
  have h0 : ∀ (n : ℕ) (k : Fin (2 ^ n)), 0 ≤ LevyStochCalc.Analysis.dyadicPartition t n k.castSucc := fun n k => by
    rw [← LevyStochCalc.Analysis.dyadicPartition_zero t n]
    exact (hmono n).monotone (Fin.zero_le _)
  -- the atoms of the window
  have hdirac := LevyStochCalc.Poisson.ae_exists_eq_sum_dirac N hRm hRfin
  have hnat : ∀ᵐ ω ∂P, ∃ n : ℕ, N.N ω R = n := N.integer_valued hRm hRfin
  -- the increments of `X` over every cell of every grid
  set I := LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hm hp hq with hI
  have hinc : ∀ᵐ ω ∂P, ∀ (n : ℕ) (k : Fin (2 ^ n)),
      X (LevyStochCalc.Analysis.dyadicPartition t n k.succ) ω - X (LevyStochCalc.Analysis.dyadicPartition t n k.castSucc) ω
        = (∫ s in Set.Ioc (LevyStochCalc.Analysis.dyadicPartition t n k.castSucc) (LevyStochCalc.Analysis.dyadicPartition t n k.succ),
            bdrift ω s ∂volume)
          + (I (LevyStochCalc.Analysis.dyadicPartition t n k.succ) ω - I (LevyStochCalc.Analysis.dyadicPartition t n k.castSucc) ω) := by
    rw [ae_all_iff]
    intro n
    rw [ae_all_iff]
    intro k
    exact hX.sub_ae hbm hB (h0 n k) ((hmono n) (Fin.castSucc_lt_succ (i := k))).le
  -- associativity against the frozen integrands
  have hassoc : ∀ᵐ ω ∂P, ∀ n : ℕ, (LevyStochCalc.Brownian.Ito.leftFreeze Y hYb hYm ht n).integralAgainst I t ω
      = LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ
        (fun ω s => (LevyStochCalc.Brownian.Ito.leftFreeze Y hYb hYm ht n).eval s ω * H ω s)
        ((LevyStochCalc.Brownian.Ito.leftFreeze Y hYb hYm ht n).measurable_uncurry_eval_mul hm)
        ((LevyStochCalc.Brownian.Ito.leftFreeze Y hYb hYm ht n).progressivelyMeasurable_eval_mul ℱ
          (LevyStochCalc.Brownian.Ito.leftFreeze_adapt Y hYb hYm ht n ℱ hYad) hp)
        ((_root_.Prove2MeSourceProof.h_ab7ca2049b8b9b3eaf1b7768 (LevyStochCalc.Brownian.Ito.leftFreeze Y hYb hYm ht n)) hq) t ω := by
    rw [ae_all_iff]
    intro n
    exact _root_.Prove2MeSourceProof.h_f7873a967b51c0099c698616 W ℱ hℱ (LevyStochCalc.Brownian.Ito.leftFreeze Y hYb hYm ht n)
      (LevyStochCalc.Brownian.Ito.leftFreeze_adapt Y hYb hYm ht n ℱ hYad) H hm hp hq _ _ _ ht
  -- the frozen values converge to the left limits
  have hconv : ∀ᵐ ω ∂P, ∀ s, 0 < s → s ≤ t →
      Tendsto (fun n : ℕ => Y (LevyStochCalc.Analysis.leftPt t n s) ω) atTop (𝓝 (Yminus s ω)) := by
    filter_upwards [hdirac, hnat, hY, hYminus] with ω hS hnR hYω hYmω s hs _
    obtain ⟨S, hS⟩ := hS
    obtain ⟨nR, hnR⟩ := hnR
    haveI : IsFiniteMeasure ((N.N ω).restrict R) :=
      ⟨by rw [Measure.restrict_apply_univ, hnR]; exact ENNReal.natCast_lt_top _⟩
    refine (tendsto_const_nhds (x := Yminus s ω)).congr' ?_
    filter_upwards [_root_.Prove2MeSourceProof.h_730af81efd0792a1160b2da3 S
      (fun p => (((N.N ω).restrict R) {p}).toReal * g ω p) ht hs] with n hn
    rw [hYω, LevyStochCalc.Driver.setIntegral_Ioc_eq_jumpSum N hS, hn, hYmω, LevyStochCalc.Driver.setIntegral_Ioo_eq_jumpSumStrict N hS]
  -- the `L²` limit of the frozen Itô integrals, along a subsequence
  have hL2 := _root_.Prove2MeSourceProof.h_7c0d8c620a9a0a0ece056f63 W ℱ hℱ H hm hp hq Y hYb hYm hYad ht Yminus
    hYmb hmm' hmp' hmq' hconv
  obtain ⟨φ, hφ, hae⟩ := (tendstoInMeasure_of_tendsto_eLpNorm (μ := P) (p := 2) (by norm_num)
    (fun n => (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_memLp W ℱ hℱ _ _ _ _ t).aestronglyMeasurable)
    (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_memLp W ℱ hℱ _ _ _ _ t).aestronglyMeasurable
    (LevyStochCalc.Driver.tendsto_eLpNorm_two_of_tendsto_lintegral_sq hL2)).exists_seq_tendsto_ae
  -- assemble at a sample point
  filter_upwards [hdirac, hnat, hinc, hassoc, hae, hY, hYminus] with ω hS hnR hincω hassocω
    haeω hYω hYmω
  obtain ⟨S, hS⟩ := hS
  obtain ⟨nR, hnR⟩ := hnR
  haveI : IsFiniteMeasure ((N.N ω).restrict R) :=
    ⟨by rw [Measure.restrict_apply_univ, hnR]; exact ENNReal.natCast_lt_top _⟩
  obtain ⟨c, hc⟩ : ∃ c : ℝ × E → ℝ, c = fun p => (((N.N ω).restrict R) {p}).toReal * g ω p :=
    ⟨_, rfl⟩
  have hYc : ∀ s, Y s ω = Y 0 ω + LevyStochCalc.Analysis.jumpSum S c s := fun s => by
    have h1 := LevyStochCalc.Driver.setIntegral_Ioc_eq_jumpSum N (R := R) hS (g ω) s
    rw [hYω s, h1, hc]
  have hYmc : ∀ s, Yminus s ω = Y 0 ω + LevyStochCalc.Analysis.jumpSumStrict S c s := fun s => by
    have h1 := LevyStochCalc.Driver.setIntegral_Ioo_eq_jumpSumStrict N (R := R) hS (g ω) s
    rw [hYmω s, h1, hc]
  have hbω : Measurable (bdrift ω) := hbm.comp measurable_prodMk_left
  have hL : Tendsto (fun j => (LevyStochCalc.Brownian.Ito.leftFreeze Y hYb hYm ht (φ j)).integralAgainst I t ω) atTop
      (𝓝 (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ (fun ω s => Yminus s ω * H ω s) hmm' hmp' hmq'
        t ω)) := by
    refine haeω.congr fun j => ?_
    exact (hassocω (φ j)).symm
  have hcore := LevyStochCalc.Driver.product_rule_core Y hYb hYm ht ω (hX.continuous_path ω) hbω (hB ω) hincω hYc
    hYmc hφ hL
  have h1t := LevyStochCalc.Driver.setIntegral_Ioc_eq_jumpSum N (R := R) hS (fun p => X p.1 ω * g ω p) t
  rw [hcore, h1t]
  congr 1
  unfold LevyStochCalc.Analysis.jumpSum
  refine Finset.sum_congr rfl fun p _ => ?_
  split_ifs
  · rw [hc]; ring
  · rfl
end Wrapper

end LevyStochCalc.Driver


