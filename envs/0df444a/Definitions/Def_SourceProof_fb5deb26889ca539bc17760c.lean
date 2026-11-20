-- Prove2me | Definitions.Def_SourceProof_fb5deb26889ca539bc17760c
-- name    : SourceProof_fb5deb26889ca539bc17760c
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T15:11:49.249692+00:00
-- url     : https://prove2.me/theorems/61944f06-c330-432b-8735-da6b86e113f1
-- title:
--   LevyStochCalc source module: SourceProof_fb5deb26889ca539bc17760c
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.ae_exists_forall_count_timeSlab_le_one` comes from the `LevyStochCalc.Poisson.Simplicity` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_Simplicity_F000
import Definitions.Def_LevyStochCalc_Poisson_Simplicity_F002
import Definitions.Def_SourceProof_08d1eee1718e4902ecd9936c
import Definitions.Def_SourceProof_521bf039082cd15fcfae08ee
import Definitions.Def_SourceProof_e5991b7ae0d55e70e03866a8

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Time-simplicity of a Poisson random measure on a finite-intensity set

On a set of finite reference intensity the count of a Poisson random measure exceeds one with
probability at most the square of the intensity. The reference intensity is a product with
Lebesgue measure in time, so the masses of the dyadic time slabs of such a set are the integrals
of an integrable density over intervals of vanishing length, and therefore have vanishing
supremum. A union bound then makes the probability that some slab of level `n` carries two or
more points tend to zero, so almost surely no two points share a time and every point is simple.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace LevyStochCalc.Poisson

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

section Tail

end Tail

section Mesh

end Mesh

section Simple


theorem _root_.Prove2MeSourceProof.h_fb5deb26889ca539bc17760c (N : PoissonRandomMeasure.{u, v, w} P ν)
    {B : Set (ℝ × E)} (hB : MeasurableSet B) (hfin : referenceIntensity ν B ≠ ⊤) :
    ∀ᵐ ω ∂P, ∃ n : ℕ, ∀ k : ℕ, N.N ω (B ∩ timeSlab n k ×ˢ Set.univ) ≤ 1 := by
  classical
  set C : ℕ → ℕ → Set (ℝ × E) := fun n k => B ∩ LevyStochCalc.Poisson.timeSlab n k ×ˢ Set.univ with hCdef
  have hCm : ∀ n k, MeasurableSet (C n k) := fun n k =>
    hB.inter ((LevyStochCalc.Poisson.measurableSet_timeSlab n k).prod MeasurableSet.univ)
  have hCfin : ∀ n k, LevyStochCalc.Poisson.referenceIntensity ν (C n k) ≠ ⊤ := fun n k =>
    ne_top_of_le_ne_top hfin (measure_mono Set.inter_subset_left)
  set R : ℕ → ℕ → ℝ≥0∞ := fun n k => LevyStochCalc.Poisson.referenceIntensity ν (C n k) with hRdef
  have hsum : ∀ n : ℕ, ∑' k : ℕ, R n k ≤ LevyStochCalc.Poisson.referenceIntensity ν B := by
    intro n
    have hdisj : Pairwise (Function.onFun Disjoint (C n)) := by
      intro i j hij
      refine Set.disjoint_left.mpr fun p hpi hpj => ?_
      exact Set.disjoint_left.mp (_root_.Prove2MeSourceProof.h_521bf039082cd15fcfae08ee n hij) hpi.2.1 hpj.2.1
    have hunion : (⋃ k : ℕ, C n k) = B ∩ Set.Ioi (0 : ℝ) ×ˢ Set.univ := by
      rw [hCdef, ← Set.inter_iUnion, ← Set.iUnion_prod_const, _root_.Prove2MeSourceProof.h_e5991b7ae0d55e70e03866a8]
    rw [hRdef, ← measure_iUnion hdisj (hCm n), hunion]
    exact measure_mono Set.inter_subset_left
  have hRint : ∀ n k, R n k = ∫⁻ x in LevyStochCalc.Poisson.timeSlab n k, LevyStochCalc.Poisson.sectionDensity ν B x := fun n k =>
    _root_.Prove2MeSourceProof.h_b53022bf4ec47748c83ffa9f hB (LevyStochCalc.Poisson.measurableSet_timeSlab n k)
  set A : ℕ → Set Ω := fun n => ⋃ k : ℕ, {ω | 2 ≤ N.N ω (C n k)} with hAdef
  have hAle : ∀ n : ℕ, P (A n) ≤ (⨆ k : ℕ, R n k) * LevyStochCalc.Poisson.referenceIntensity ν B := by
    intro n
    calc P (A n) ≤ ∑' k : ℕ, P {ω | 2 ≤ N.N ω (C n k)} := measure_iUnion_le _
      _ ≤ ∑' k : ℕ, R n k ^ 2 :=
          ENNReal.tsum_le_tsum fun k => LevyStochCalc.Poisson.measure_two_le_count_le N (hCm n k) (hCfin n k)
      _ ≤ ∑' k : ℕ, (⨆ j : ℕ, R n j) * R n k := by
          refine ENNReal.tsum_le_tsum fun k => ?_
          rw [sq]
          gcongr
          exact le_iSup (R n) k
      _ = (⨆ j : ℕ, R n j) * ∑' k : ℕ, R n k := ENNReal.tsum_mul_left
      _ ≤ (⨆ j : ℕ, R n j) * LevyStochCalc.Poisson.referenceIntensity ν B := by gcongr; exact hsum n
  have hsmall : ∀ ε : ℝ≥0∞, ε ≠ 0 → ∃ n : ℕ, P (A n) ≤ ε := by
    intro ε hε
    by_cases hR : LevyStochCalc.Poisson.referenceIntensity ν B = 0
    · exact ⟨0, (hAle 0).trans (by rw [hR, mul_zero]; exact bot_le)⟩
    · have hδ0 : ε / LevyStochCalc.Poisson.referenceIntensity ν B ≠ 0 := by
        intro h
        rcases ENNReal.div_eq_zero_iff.mp h with h1 | h1
        · exact hε h1
        · exact hfin h1
      obtain ⟨n, hn⟩ := _root_.Prove2MeSourceProof.h_08d1eee1718e4902ecd9936c
        (LevyStochCalc.Poisson.measurable_sectionDensity (ν := ν) hB)
        (by rw [LevyStochCalc.Poisson.lintegral_sectionDensity hB]; exact hfin) hδ0
      refine ⟨n, (hAle n).trans ?_⟩
      have hsupδ : (⨆ k : ℕ, R n k) ≤ ε / LevyStochCalc.Poisson.referenceIntensity ν B := by
        refine iSup_le fun k => ?_
        rw [hRint n k]
        exact le_trans
          (le_iSup (fun j : ℕ => ∫⁻ x in LevyStochCalc.Poisson.timeSlab n j, LevyStochCalc.Poisson.sectionDensity ν B x) k) hn
      calc (⨆ k : ℕ, R n k) * LevyStochCalc.Poisson.referenceIntensity ν B
          ≤ (ε / LevyStochCalc.Poisson.referenceIntensity ν B) * LevyStochCalc.Poisson.referenceIntensity ν B := by gcongr
        _ = ε := ENNReal.div_mul_cancel hR hfin
  have hzero : P (⋂ n : ℕ, A n) = 0 := by
    by_contra hne
    obtain ⟨c, hc0, hcx⟩ := exists_between (pos_iff_ne_zero.mpr hne)
    obtain ⟨n, hn⟩ := hsmall c hc0.ne'
    exact absurd (le_trans (measure_mono (Set.iInter_subset _ n)) hn) (not_le.mpr hcx)
  have hae : ∀ᵐ ω ∂P, ω ∉ ⋂ n : ℕ, A n := by
    rw [ae_iff]
    simpa only [not_not, Set.setOf_mem_eq] using hzero
  have hint : ∀ᵐ ω ∂P, ∀ n k : ℕ, ∃ m : ℕ, N.N ω (C n k) = m := by
    rw [ae_all_iff]
    intro n
    rw [ae_all_iff]
    intro k
    exact N.integer_valued (hCm n k) (hCfin n k)
  filter_upwards [hae, hint] with ω hω hωint
  simp only [Set.mem_iInter, not_forall] at hω
  obtain ⟨n, hn⟩ := hω
  simp only [hAdef, Set.mem_iUnion, not_exists, Set.mem_setOf_eq] at hn
  refine ⟨n, fun k => ?_⟩
  obtain ⟨m, hm⟩ := hωint n k
  have hnk := hn k
  rw [hm] at hnk ⊢
  have hm2 : m < 2 := by
    by_contra hc
    exact hnk (by exact_mod_cast Nat.le_of_not_lt hc)
  exact_mod_cast Nat.lt_succ_iff.mp hm2
end Simple

end LevyStochCalc.Poisson


