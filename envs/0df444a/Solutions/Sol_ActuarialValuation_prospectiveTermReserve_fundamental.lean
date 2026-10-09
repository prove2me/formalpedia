-- Prove2me | solution 1 for ActuarialValuation.prospectiveTermReserve_fundamental
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T07:03:13.474062+00:00
-- url     : https://prove2.me/submissions/2852b33d-de3d-470a-969f-ba7c2694ab6b

import Mathlib
import Definitions.Def_actuarial_valuationSurvivalEvent
import Definitions.Def_actuarial_futureTermBenefitPV
import Definitions.Def_actuarial_futureTermPremiumPV
import Definitions.Def_actuarial_futureTermLossPV
import Definitions.Def_actuarial_prospectiveTermReservePV
import Theorems.Thm_ActuarialValuation_prospectiveTermReserve_denominator_identity
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open ActuarialValuation

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (K : Ω → ℕ) (hK : Measurable K)
    (v : ℝ) (n t : ℕ)
    (b π c : ℝ) (hq : 0 < (P (valuationSurvivalEvent K t)).toReal)
    :
    ((P (valuationSurvivalEvent K t)).toReal *
      prospectiveTermReservePV P K v n t b π =
      ∫ ω, futureTermLossPV K v n t b π ω ∂P)
    ∧ (prospectiveTermReservePV P K v n t b π =
      b * (∫ ω, futureTermBenefitPV K v n t ω ∂P) /
        (P (valuationSurvivalEvent K t)).toReal -
      π * (∫ ω, futureTermPremiumPV K v n t ω ∂P) /
        (P (valuationSurvivalEvent K t)).toReal)
    ∧ (prospectiveTermReservePV P K v n t (c * b) (c * π) =
      c * prospectiveTermReservePV P K v n t b π) := by
  have hdec (x y : ℝ) :
        prospectiveTermReservePV P K v n t x y =
      x * (∫ ω, futureTermBenefitPV K v n t ω ∂P) /
        (P (valuationSurvivalEvent K t)).toReal -
      y * (∫ ω, futureTermPremiumPV K v n t ω ∂P) /
        (P (valuationSurvivalEvent K t)).toReal := by
    classical
    let A : ℕ → Set Ω := fun k => {ω | K ω = k ∧ t ≤ k}
    let S : ℕ → Set Ω := fun j => {ω | t ≤ j ∧ j ≤ K ω}
    have hA (k : ℕ) : MeasurableSet (A k) := by
      by_cases ht : t ≤ k
      · have hm : MeasurableSet (K ⁻¹' {k}) := hK (measurableSet_singleton k)
        have heq : A k = K ⁻¹' {k} := by
          ext ω
          simp [A, ht]
        rw [heq]
        exact hm
      · simp [A, ht]
    have hS (j : ℕ) : MeasurableSet (S j) := by
      by_cases ht : t ≤ j
      · have hm : MeasurableSet (K ⁻¹' Set.Ici j) := hK measurableSet_Ici
        have heq : S j = K ⁻¹' Set.Ici j := by
          ext ω
          simp [S, ht]
        rw [heq]
        exact hm
      · simp [S, ht]
    have hB : Integrable (futureTermBenefitPV K v n t) P := by
      have hrepl : futureTermBenefitPV K v n t =
          fun ω => ∑ k ∈ Finset.range n,
            (A k).indicator (fun _ : Ω => v ^ (k + 1 - t)) ω := by
        funext ω
        by_cases hc : t ≤ K ω ∧ K ω < n
        · have hsingle : (∑ k ∈ Finset.range n,
                (A k).indicator (fun _ : Ω => v ^ (k + 1 - t)) ω) =
              (A (K ω)).indicator (fun _ : Ω => v ^ (K ω + 1 - t)) ω := by
            apply Finset.sum_eq_single (K ω)
            · intro k hk hneq
              have hn : ω ∉ A k := by
                intro ha
                exact hneq ha.1.symm
              simp [Set.indicator, hn]
            · intro hnot
              exact False.elim (hnot (Finset.mem_range.mpr hc.2))
          rw [hsingle]
          simp [futureTermBenefitPV, A, hc, Set.indicator]
        · have hz : (∑ k ∈ Finset.range n,
              (A k).indicator (fun _ : Ω => v ^ (k + 1 - t)) ω) = 0 := by
            apply Finset.sum_eq_zero
            intro k hk
            have hn : ω ∉ A k := by
              intro ha
              have heq : K ω = k := ha.1
              have ht : t ≤ k := ha.2
              have hklt : k < n := Finset.mem_range.mp hk
              apply hc
              constructor
              · simpa [heq] using ht
              · simpa [heq] using hklt
            simp [Set.indicator, hn]
          simp [futureTermBenefitPV, hc, hz]
      rw [hrepl]
      apply integrable_finset_sum
      intro k hk
      exact (integrable_const (v ^ (k + 1 - t))).indicator (hA k)
    have hP : Integrable (futureTermPremiumPV K v n t) P := by
      have hrepl : futureTermPremiumPV K v n t =
          fun ω => ∑ j ∈ Finset.range n,
            (S j).indicator (fun _ : Ω => v ^ (j - t)) ω := by
        funext ω
        unfold futureTermPremiumPV
        apply Finset.sum_congr rfl
        intro j hj
        by_cases hc : t ≤ j ∧ j ≤ K ω
        · simp [S, Set.indicator, hc]
        · simp [S, Set.indicator, hc]
      rw [hrepl]
      apply integrable_finset_sum
      intro j hj
      exact (integrable_const (v ^ (j - t))).indicator (hS j)
    have hlin :
        (∫ ω, futureTermLossPV K v n t x y ω ∂P) =
          x * (∫ ω, futureTermBenefitPV K v n t ω ∂P) -
          y * (∫ ω, futureTermPremiumPV K v n t ω ∂P) := by
      unfold futureTermLossPV
      rw [integral_sub (hB.const_mul x) (hP.const_mul y)]
      simp only [integral_const_mul]
    unfold prospectiveTermReservePV
    rw [hlin]
    ring
  have hscale :
      prospectiveTermReservePV P K v n t (c * b) (c * π) =
        c * prospectiveTermReservePV P K v n t b π := by
    rw [hdec (c * b) (c * π), hdec b π]
    ring
  exact ⟨
    prospectiveTermReserve_denominator_identity P K hK v n t b π hq,
    hdec b π, hscale
  ⟩
