-- Prove2me | Definitions.Def_LevyStochCalc_Probability_PredictableModification_F001
-- name    : LevyStochCalc_Probability_PredictableModification_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T20:50:01.285859+00:00
-- url     : https://prove2.me/theorems/942eb1b3-3c81-418f-8b47-8d326c029f6f
-- title:
--   Source declarations: LevyStochCalc.Probability.PredictableModification
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Probability.PredictableModification. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoSimpleIntegrand_F000
import Definitions.Def_LevyStochCalc_Probability_PredictableModification_F000
import Definitions.Def_SourceProof_4ecfd1aa58bb4ad860581e64

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Predictable representatives of progressive integrands

The elementary integrands of the `L²` theory — finite sums of a coefficient measurable at the
left endpoint of a cell, carried on that cell — are predictable, and the predictable processes
are closed under pointwise upper limits. Since the elementary integrands are dense in the
progressive integrands of finite energy, a progressive integrand agrees with a predictable one
almost everywhere in time and sample point.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace LevyStochCalc.Probability

universe u

variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ mΩ}

section Cells

/-- The complement of a cell above the origin is predictable. -/
theorem measurableSet_predictableSigma_compl_Ioc {r q : ℝ} (hr : 0 ≤ r) :
    MeasurableSet[predictableSigma ℱ] ((Set.Ioc r q)ᶜ ×ˢ (Set.univ : Set Ω)) := by
  have h : ((Set.Ioc r q)ᶜ) ×ˢ (Set.univ : Set Ω)
      = (Set.Iic r ×ˢ (Set.univ : Set Ω)) ∪ (Set.Ioi q ×ˢ (Set.univ : Set Ω)) := by
    ext ⟨s, ω⟩
    simp only [Set.mem_prod, Set.mem_univ, and_true, Set.mem_union, Set.mem_compl_iff,
      Set.mem_Ioc, Set.mem_Iic, Set.mem_Ioi, not_and, not_le]
    constructor
    · intro hs
      rcases le_or_gt s r with h0 | h0
      · exact Or.inl h0
      · exact Or.inr (hs h0)
    · rintro (h0 | h0)
      · exact fun h1 => absurd h0 (not_le.mpr h1)
      · exact fun _ => h0
  rw [h]
  exact (measurableSet_predictableSigma_Iic_univ hr).union
    (measurableSet_predictableSigma_Ioi_prod MeasurableSet.univ)
/-- A coefficient measurable at the left endpoint of a cell, carried on that cell, is
predictable. -/
theorem measurable_predictableSigma_cell {r q : ℝ} (hr : 0 ≤ r) (hrq : r ≤ q) {ξ : Ω → ℝ}
    (hξ : Measurable[ℱ r] ξ) :
    Measurable[predictableSigma ℱ] fun p : ℝ × Ω => if r < p.1 ∧ p.1 ≤ q then ξ p.2 else 0 := by
  intro U hU
  by_cases h0 : (0 : ℝ) ∈ U
  · have hpre : (fun p : ℝ × Ω => if r < p.1 ∧ p.1 ≤ q then ξ p.2 else 0) ⁻¹' U
        = (Set.Ioc r q ×ˢ (ξ ⁻¹' U)) ∪ ((Set.Ioc r q)ᶜ ×ˢ (Set.univ : Set Ω)) := by
      ext ⟨s, ω⟩
      by_cases hs : r < s ∧ s ≤ q <;>
        simp [hs, h0, Set.mem_Ioc, Set.mem_preimage, Set.mem_prod]
    rw [hpre]
    exact (_root_.Prove2MeSourceProof.h_4ecfd1aa58bb4ad860581e64 hrq (hξ hU)).union
      (measurableSet_predictableSigma_compl_Ioc hr)
  · have hpre : (fun p : ℝ × Ω => if r < p.1 ∧ p.1 ≤ q then ξ p.2 else 0) ⁻¹' U
        = Set.Ioc r q ×ˢ (ξ ⁻¹' U) := by
      ext ⟨s, ω⟩
      by_cases hs : r < s ∧ s ≤ q <;>
        simp [hs, h0, Set.mem_Ioc, Set.mem_preimage, Set.mem_prod]
    rw [hpre]
    exact _root_.Prove2MeSourceProof.h_4ecfd1aa58bb4ad860581e64 hrq (hξ hU)
/-- **An adapted elementary integrand is predictable.** -/
theorem predictable_simpleEval {T : ℝ} (G : Brownian.Ito.SimplePredictable Ω T)
    (hG : ∀ i : Fin G.N, StronglyMeasurable[ℱ (G.partition i.castSucc)] (G.ξ i)) :
    Predictable ℱ fun ω s => G.eval s ω := by
  have hnn : ∀ i : Fin G.N, 0 ≤ G.partition i.castSucc := fun i => by
    have h := G.partition_strictMono.monotone (Fin.zero_le i.castSucc)
    rwa [G.partition_zero] at h
  have hle : ∀ i : Fin G.N, G.partition i.castSucc ≤ G.partition i.succ := fun i =>
    (G.partition_strictMono Fin.castSucc_lt_succ).le
  refine stronglyMeasurable_iff_measurable.mpr ?_
  have hrw : (fun p : ℝ × Ω => G.eval p.1 p.2)
      = fun p : ℝ × Ω => ∑ i : Fin G.N,
        (if G.partition i.castSucc < p.1 ∧ p.1 ≤ G.partition i.succ then G.ξ i p.2 else 0) := rfl
  rw [hrw]
  exact Finset.measurable_sum _ fun i _ =>
    measurable_predictableSigma_cell (hnn i) (hle i) (hG i).measurable
/-- **Predictable processes are closed under pointwise upper limits.** -/
theorem Predictable.limsup {H : ℕ → Ω → ℝ → ℝ} (h : ∀ k, Predictable ℱ (H k)) :
    Predictable ℱ fun ω s => Filter.limsup (fun k => H k ω s) Filter.atTop := by
  refine stronglyMeasurable_iff_measurable.mpr (Measurable.limsup fun k => ?_)
  exact (h k).measurable
end Cells

section Modification

open Brownian.Ito

variable {P : Measure Ω} [IsProbabilityMeasure P]

/-- The pointwise upper limit along a subsequence of elementary integrands. -/
noncomputable def limsupSimpleEval {T : ℝ} (G : ℕ → SimplePredictable Ω T) (ns : ℕ → ℕ) :
    Ω → ℝ → ℝ := fun ω s => limsup (fun i => (G (ns i)).eval s ω) atTop
end Modification

end LevyStochCalc.Probability


