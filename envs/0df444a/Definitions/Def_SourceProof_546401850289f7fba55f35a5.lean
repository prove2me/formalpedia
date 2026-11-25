-- Prove2me | Definitions.Def_SourceProof_546401850289f7fba55f35a5
-- name    : SourceProof_546401850289f7fba55f35a5
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T19:36:01.790674+00:00
-- url     : https://prove2.me/theorems/2b726bb3-2a72-4c42-8741-4f1741bbc2a9
-- title:
--   StochLean source theorem: ProbabilityTheory.exists_simplePredictable_tendstoUCP_preserves_zero_paths

import Definitions.Def_StochLean_Probability_Process_UCP_F001
import Definitions.Def_SourceProof_1a34da0744a1e367373a463f
import Definitions.Def_SourceProof_2e0d0236117e214012bd8888
import Definitions.Def_SourceProof_336029c999d97a8ccdc620fb
import Definitions.Def_SourceProof_53bca36d7403deaa0689f5ec
import Definitions.Def_SourceProof_9f2f3563711c68b81e63664c
import Definitions.Def_SourceProof_bf3b4f0165446cd3affab35f
import Definitions.Def_SourceProof_c85f5070e7769bac711d7f66
import Definitions.Def_SourceProof_e7710072ab29110bbbbd5d6b
import Definitions.Def_SourceProof_f60f6796fd78b83be1f764d1
import Mathlib.MeasureTheory.Integral.Indicator

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Source simple predictable density in the caglad UCP class

Protter II.10 with the first interval restored. Actual oscillation times of the
right-limit process and finite capped coefficients give the approximants. Their
number of cells is chosen from the proved vanishing exit probabilities. The source
allows unbounded finite coefficients, so no preliminary global coefficient bound
is imposed. No density assumption or general stochastic-integral selector is used.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} [IsFiniteMeasure P] {H : ℝ≥0 → Ω → ℝ}


theorem _root_.Prove2MeSourceProof.h_546401850289f7fba55f35a5
    (ha : Adapted F H) (hF : F.IsUsual P)
    (hc : HasCagladPaths H P) :
    ∃ S : ℕ → ℝ≥0 → Ω → ℝ, (∀ n, IsSimplePredictable (S n) F) ∧
      (∀ n ω, (∀ t, H t ω = 0) → ∀ t, S n t ω = 0) ∧ TendstoUCP P S atTop H := by
  classical
  let ε : ℕ → ℝ := fun k ↦ 1 / ((k : ℝ) + 1)
  have hε (k : ℕ) : 0 < ε k := by dsimp only [ε]; positivity
  have hεlim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hplim : Tendsto (fun k ↦ ENNReal.ofReal (ε k)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp hεlim
  have hτ (k n : ℕ) : IsStoppingTime F (ProbabilityTheory.oscillationTimes (ProbabilityTheory.rightLimitProcess H) (ε k) n) :=
    _root_.Prove2MeSourceProof.h_1a34da0744a1e367373a463f ((_root_.Prove2MeSourceProof.h_f60f6796fd78b83be1f764d1 ha) hF hc) hF
      (_root_.Prove2MeSourceProof.h_9f2f3563711c68b81e63664c (_root_.Prove2MeSourceProof.h_53bca36d7403deaa0689f5ec hc)) (ε k) n
  have hex (k : ℕ) : ∃ n : ℕ,
      P {ω | ProbabilityTheory.oscillationTimes (ProbabilityTheory.rightLimitProcess H) (ε k) n ω ≤ (k : WithTop ℝ≥0)} ≤
        ENNReal.ofReal (ε k) := by
    have hlim := _root_.Prove2MeSourceProof.h_336029c999d97a8ccdc620fb
      (fun n ↦ (hτ k n).measurable.mono (hτ k n).measurableSpace_le le_rfl)
      (_root_.Prove2MeSourceProof.h_e7710072ab29110bbbbd5d6b (_root_.Prove2MeSourceProof.h_53bca36d7403deaa0689f5ec hc) (hε k)) (k : ℝ≥0)
    obtain ⟨N, hN⟩ := ENNReal.tendsto_atTop_zero.mp hlim
      (ENNReal.ofReal (ε k)) (ENNReal.ofReal_pos.mpr (hε k))
    exact ⟨N, hN N le_rfl⟩
  choose N hN using hex
  let R (k : ℕ) := ProbabilityTheory.CagladApproximation.representation H ha hF hc (ε k) (hε k).le (N k) k
  refine ⟨fun k ↦ (R k).toProcess, fun k ↦ ⟨R k, rfl⟩, ?_, ?_⟩
  · intro k ω hzero t
    exact _root_.Prove2MeSourceProof.h_2e0d0236117e214012bd8888 H ha hF hc
      (ε k) (hε k).le (N k) k hzero t
  apply _root_.Prove2MeSourceProof.h_c85f5070e7769bac711d7f66.mpr
  intro T δ hδ
  apply ENNReal.tendsto_atTop_zero.mpr
  intro η hη
  obtain ⟨NT, hNT⟩ := exists_nat_ge T
  obtain ⟨NE, hNE⟩ := eventually_atTop.mp (hεlim.eventually_lt_const hδ)
  obtain ⟨NP, hNP⟩ := ENNReal.tendsto_atTop_zero.mp hplim η hη
  refine ⟨max NT (max NE NP), fun k hk ↦ ?_⟩
  have hTk : T ≤ (k : ℝ≥0) := hNT.trans (by
    exact_mod_cast (le_max_left NT (max NE NP)).trans hk)
  have hkε : ε k < δ := hNE k ((le_max_left NE NP).trans ((le_max_right NT (max NE NP)).trans hk))
  have hkp : ENNReal.ofReal (ε k) ≤ η :=
    hNP k ((le_max_right NE NP).trans ((le_max_right NT (max NE NP)).trans hk))
  apply le_trans ?_ ((hN k).trans hkp)
  apply measure_mono_ae
  filter_upwards [hc] with ω hω
  rintro ⟨t, ht, hbad⟩
  by_contra hn
  have hτk : (k : WithTop ℝ≥0) < ProbabilityTheory.oscillationTimes (ProbabilityTheory.rightLimitProcess H) (ε k) (N k) ω :=
    lt_of_not_ge hn
  have hbound := _root_.Prove2MeSourceProof.h_bf3b4f0165446cd3affab35f H ha hF hc
    (ε k) (hε k).le (N k) k hω (ht.trans hTk)
    ((WithTop.coe_le_coe.mpr (ht.trans hTk)).trans hτk.le)
  exact (not_lt_of_ge hbound) (hkε.trans hbad)
end ProbabilityTheory


