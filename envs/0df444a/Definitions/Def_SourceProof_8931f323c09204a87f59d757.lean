-- Prove2me | Definitions.Def_SourceProof_8931f323c09204a87f59d757
-- name    : SourceProof_8931f323c09204a87f59d757
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T19:25:32.752813+00:00
-- url     : https://prove2.me/theorems/27f1dd74-716a-4f71-81ce-8f5bbc3da045
-- title:
--   LevyStochCalc source module: SourceProof_8931f323c09204a87f59d757
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.Compensated.simpleIntegral_term_condExp_compensated` comes from the `LevyStochCalc.Poisson.CompensatedMartingaleAdapted` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedMartingaleAdapted_F000
import Definitions.Def_LevyStochCalc_Poisson_CompensatedMartingaleAdapted_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Martingale property of the simple compensated-Poisson integral

`simpleIntegral N φ` is adapted to a Poisson filtration `ℱ` of `N`: each time-rectangle
`timeRect i t` lies in the past `Iic t ×ˢ univ`, so its compensated mass is `ℱ_t`-measurable,
and the coefficient `ξᵢ` is `ℱ_t`-measurable once `t` reaches the partition point (the term
vanishing before). Each summand is `P`-integrable, its conditional expectation satisfies
`𝔼[ξᵢ·Ñ(timeRect i t) | ℱ_s] =ᵐ ξᵢ·Ñ(timeRect i s)` for `0 ≤ s ≤ t`, and summing over the
partition gives the martingale property of `t ↦ simpleIntegral N φ t`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

set_option maxHeartbeats 1000000 in
-- The Case-B tower-property chain (`condExp_mul` + `condExp_condExp_of_le`) is
-- heartbeat-heavy; raise the budget for this single proof.

theorem _root_.Prove2MeSourceProof.h_8931f323c09204a87f59d757
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsPoissonFiltration N ℱ)
    {T : ℝ} (φ : SimplePredictable Ω E ν T) (i : Fin φ.N)
    (h_adapt_i : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (φ.partition i.castSucc)) (φ.ξ i))
    {s t : ℝ} (hst : s ≤ t) :
    P[fun ω => φ.ξ i ω * N.compensated (φ.timeRect i t) ω
        | ℱ s]
      =ᵐ[P] fun ω => φ.ξ i ω * N.compensated (φ.timeRect i s) ω := by
  obtain ⟨M, hM⟩ := φ.ξ_bounded i
  have hξmeas : Measurable (φ.ξ i) := φ.ξ_measurable i
  have hpc_lt_ps : φ.partition i.castSucc < φ.partition i.succ :=
    φ.partition_strictMono Fin.castSucc_lt_succ
  have hpc_nn : 0 ≤ φ.partition i.castSucc := by
    have := φ.partition_strictMono.monotone (Fin.zero_le i.castSucc)
    rwa [φ.partition_zero] at this
  have hAfin := φ.A_finite i
  have hAmeas := φ.A_measurable i
  have hξÑ_int : ∀ B : Set (ℝ × E), MeasurableSet B →
      LevyStochCalc.Poisson.referenceIntensity ν B ≠ ⊤ →
      MeasureTheory.Integrable ((φ.ξ i) * fun ω => N.compensated B ω) P := by
    intro B hBmeas hBfin
    refine MeasureTheory.Integrable.bdd_mul (LevyStochCalc.Poisson.Compensated.compensated_integrable N hBmeas hBfin)
      hξmeas.aestronglyMeasurable (c := |M|) ?_
    filter_upwards with ω; rw [Real.norm_eq_abs]; exact (hM ω).trans (le_abs_self _)
  change P[(φ.ξ i) * fun ω => N.compensated (φ.timeRect i t) ω | ℱ.seq s]
    =ᵐ[P] (φ.ξ i) * fun ω => N.compensated (φ.timeRect i s) ω
  by_cases hpc_s : φ.partition i.castSucc ≤ s
  · -- Case A
    have hs_nn : 0 ≤ s := hpc_nn.trans hpc_s
    have hξ_Fs : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ.seq s) (φ.ξ i) :=
      h_adapt_i.mono (ℱ.mono hpc_s)
    have h_min_pc_s : min (φ.partition i.castSucc) s = φ.partition i.castSucc := min_eq_left hpc_s
    have h_min_pc_t : min (φ.partition i.castSucc) t = φ.partition i.castSucc :=
      min_eq_left (hpc_s.trans hst)
    set bs := min (φ.partition i.succ) s with hbs
    set bt := min (φ.partition i.succ) t with hbt
    have hpc_le_bs : φ.partition i.castSucc ≤ bs := le_min hpc_lt_ps.le hpc_s
    have hbs_le_bt : bs ≤ bt := min_le_min (le_refl _) hst
    set newset : Set (ℝ × E) := Set.Ioc bs bt ×ˢ φ.A i with hnew
    have h_rect_s : φ.timeRect i s = Set.Ioc (φ.partition i.castSucc) bs ×ˢ φ.A i := by
      rw [LevyStochCalc.Poisson.Compensated.SimplePredictable.timeRect, h_min_pc_s]
    have h_rect_t : φ.timeRect i t = Set.Ioc (φ.partition i.castSucc) bt ×ˢ φ.A i := by
      rw [LevyStochCalc.Poisson.Compensated.SimplePredictable.timeRect, h_min_pc_t]
    have h_union : φ.timeRect i t = φ.timeRect i s ∪ newset := by
      rw [h_rect_t, h_rect_s, hnew, ← Set.union_prod, Set.Ioc_union_Ioc_eq_Ioc hpc_le_bs hbs_le_bt]
    have hrect_s_meas : MeasurableSet (φ.timeRect i s) := by
      rw [h_rect_s]; exact measurableSet_Ioc.prod hAmeas
    have hnew_meas : MeasurableSet newset := by rw [hnew]; exact measurableSet_Ioc.prod hAmeas
    have h_disj : Disjoint (φ.timeRect i s) newset := by
      rw [h_rect_s, hnew]
      exact Set.disjoint_left.mpr (fun p hp1 hp2 => absurd hp2.1.1 (not_lt.mpr hp1.1.2))
    have hrect_s_fin : LevyStochCalc.Poisson.referenceIntensity ν (φ.timeRect i s) ≠ ⊤ :=
      h_rect_s ▸ LevyStochCalc.Poisson.Compensated.referenceIntensity_Ioc_prod_ne_top hAfin
    have hnew_fin : LevyStochCalc.Poisson.referenceIntensity ν newset ≠ ⊤ := by
      rw [hnew]; exact LevyStochCalc.Poisson.Compensated.referenceIntensity_Ioc_prod_ne_top hAfin
    have hcompadd : (fun ω => N.compensated (φ.timeRect i t) ω) =ᵐ[P]
        (fun ω => N.compensated (φ.timeRect i s) ω) + fun ω => N.compensated newset ω :=
      h_union ▸ LevyStochCalc.Poisson.Compensated.compensated_union_ae N hrect_s_meas hnew_meas h_disj hrect_s_fin hnew_fin
    have hsplit : ((φ.ξ i) * fun ω => N.compensated (φ.timeRect i t) ω) =ᵐ[P]
        ((φ.ξ i) * fun ω => N.compensated (φ.timeRect i s) ω)
          + (φ.ξ i) * fun ω => N.compensated newset ω := by
      filter_upwards [hcompadd] with ω hω
      simp only [Pi.mul_apply, Pi.add_apply] at hω ⊢
      rw [hω]; ring
    refine (MeasureTheory.condExp_congr_ae hsplit).trans ?_
    have hint_s := hξÑ_int (φ.timeRect i s) hrect_s_meas hrect_s_fin
    have hint_new := hξÑ_int newset hnew_meas hnew_fin
    refine (MeasureTheory.condExp_add hint_s hint_new (ℱ.seq s)).trans ?_
    have hself := MeasureTheory.condExp_of_stronglyMeasurable (ℱ.le' s)
      (show @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ.seq s)
        ((φ.ξ i) * fun ω => N.compensated (φ.timeRect i s) ω) from
        LevyStochCalc.Poisson.Compensated.simpleIntegral_term_adapted_compensated N ℱ hℱ φ i s h_adapt_i) hint_s
    have hpull := MeasureTheory.condExp_mul_of_stronglyMeasurable_left
      (m := ℱ.seq s) hξ_Fs hint_new (LevyStochCalc.Poisson.Compensated.compensated_integrable N hnew_meas hnew_fin)
    have hnew_zero : P[fun ω => N.compensated newset ω | ℱ.seq s] =ᵐ[P] fun _ => (0 : ℝ) := by
      refine LevyStochCalc.Poisson.Compensated.compensated_condExp_Ioc_eq_zero N ℱ hℱ hs_nn hbs_le_bt (fun hlt => ?_) hAmeas hAfin
      have hps_gt : s < φ.partition i.succ := by
        by_contra hle; push Not at hle
        rw [hbs, hbt, min_eq_left hle, min_eq_left (hle.trans hst)] at hlt
        exact lt_irrefl _ hlt
      rw [hbs]; exact (min_eq_right hps_gt.le).ge
    rw [hself]
    filter_upwards [hpull, hnew_zero] with ω hp hz
    simp only [Pi.add_apply, Pi.mul_apply] at hp ⊢
    rw [hp, hz]; ring
  · -- Case B
    push Not at hpc_s
    have h_rect_s_empty : φ.timeRect i s = ∅ := by
      rw [LevyStochCalc.Poisson.Compensated.SimplePredictable.timeRect, min_eq_right hpc_s.le,
        min_eq_right (hpc_s.le.trans hpc_lt_ps.le), Set.Ioc_self, Set.empty_prod]
    have h_rhs_zero : ((φ.ξ i) * fun ω => N.compensated (φ.timeRect i s) ω) = fun _ => (0 : ℝ) := by
      funext ω; simp only [Pi.mul_apply]; rw [h_rect_s_empty]
      unfold LevyStochCalc.Poisson.PoissonRandomMeasure.compensated; simp
    rw [h_rhs_zero]
    have hrect_t_meas : MeasurableSet (φ.timeRect i t) := by
      rw [LevyStochCalc.Poisson.Compensated.SimplePredictable.timeRect]; exact measurableSet_Ioc.prod hAmeas
    have hrect_t_fin := LevyStochCalc.Poisson.Compensated.referenceIntensity_timeRect_ne_top φ i t
    set gt : Ω → ℝ := fun ω => N.compensated (φ.timeRect i t) ω with hgt
    set ft : Ω → ℝ := (φ.ξ i) * gt with hft
    have hpull : P[ft | ℱ.seq (φ.partition i.castSucc)] =ᵐ[P]
        (φ.ξ i) * P[gt | ℱ.seq (φ.partition i.castSucc)] :=
      MeasureTheory.condExp_mul_of_stronglyMeasurable_left
        (m := ℱ.seq (φ.partition i.castSucc)) h_adapt_i
        (hξÑ_int (φ.timeRect i t) hrect_t_meas hrect_t_fin)
        (LevyStochCalc.Poisson.Compensated.compensated_integrable N hrect_t_meas hrect_t_fin)
    have ht_zero : P[gt | ℱ.seq (φ.partition i.castSucc)] =ᵐ[P] fun _ => (0 : ℝ) := by
      rw [hgt, LevyStochCalc.Poisson.Compensated.SimplePredictable.timeRect]
      refine LevyStochCalc.Poisson.Compensated.compensated_condExp_Ioc_eq_zero N ℱ hℱ hpc_nn
        (min_le_min hpc_lt_ps.le (le_refl t)) (fun hlt => ?_) hAmeas hAfin
      have hpct : φ.partition i.castSucc ≤ t := by
        by_contra h; push Not at h
        rw [min_eq_right h.le, min_eq_right (h.le.trans hpc_lt_ps.le)] at hlt
        exact lt_irrefl _ hlt
      exact le_min (le_refl _) hpct
    have hpc_eq_zero : P[ft | ℱ.seq (φ.partition i.castSucc)] =ᵐ[P] fun _ => (0 : ℝ) := by
      filter_upwards [hpull, ht_zero] with ω hp hz
      rw [hp]; simp only [Pi.mul_apply]; rw [hz]; ring
    have hm₂pc := ℱ.le' (φ.partition i.castSucc)
    haveI : SigmaFinite (P.trim hm₂pc) := inferInstance
    have htower := MeasureTheory.condExp_condExp_of_le (μ := P) (f := ft)
      (ℱ.mono hpc_s.le) hm₂pc
    refine htower.symm.trans ((MeasureTheory.condExp_congr_ae hpc_eq_zero).trans ?_)
    exact Filter.EventuallyEq.of_eq (MeasureTheory.condExp_const (ℱ.le' s) (0 : ℝ))
end LevyStochCalc.Poisson.Compensated


