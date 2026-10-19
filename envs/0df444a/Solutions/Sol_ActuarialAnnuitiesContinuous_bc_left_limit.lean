-- Prove2me | solution 1 for ActuarialAnnuitiesContinuous.bc_left_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-16T14:01:13.272326+00:00
-- url     : https://prove2.me/submissions/fb97320d-55f5-477f-a8f6-57f36a4a38a2

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Tactic
import Definitions.Def_actuarial_bcLeftRiemann
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter MeasureTheory
open ActuarialAnnuitiesContinuous
theorem solution (H : ℕ) (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Icc (0 : ℝ) (H : ℝ))) :
    Tendsto (fun m : ℕ => bcLeftRiemann H (m+1) f) atTop
      (nhds (∫ t in (0 : ℝ)..(H : ℝ), f t)) := by
  classical
  by_cases hH : H = 0
  · subst H
    simpa [bcLeftRiemann] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0))
  have hcompact : IsCompact (Set.Icc (0 : ℝ) (H : ℝ)) := isCompact_Icc
  have huc := hcompact.uniformContinuousOn_of_continuous hf
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  let η : ℝ := ε/((H : ℝ)+1)
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨δ,hδ,hmod⟩ := (Metric.uniformContinuousOn_iff.mp huc) η hη
  have hinv : Tendsto (fun m : ℕ => (1 : ℝ)/((m : ℝ)+1))
      atTop (nhds 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hsmall : ∀ᶠ m : ℕ in atTop, (1 : ℝ)/((m : ℝ)+1)<δ :=
    hinv.eventually (eventually_lt_nhds hδ)
  obtain ⟨m0,hm0⟩ := Filter.eventually_atTop.1 hsmall
  refine ⟨m0, ?_⟩
  intro m hmg
  have hstep_small := hm0 m hmg
  let q : ℕ := m+1
  let N : ℕ := H*q
  let a : ℕ → ℝ := fun j => (j : ℝ)/(q : ℝ)
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (Nat.succ_pos m)
  have hqne : (q : ℝ) ≠ 0 := ne_of_gt hqpos
  have hδq : (1 : ℝ)/(q : ℝ) < δ := by
    simpa [q, Nat.cast_add, Nat.cast_one] using hstep_small
  have hspan : a N = (H : ℝ) := by
    dsimp [a,N]; push_cast; field_simp [hqne]
  have hstart : a 0 = 0 := by simp [a]
  have hwidth (j : ℕ) : a (j+1)-a j = (1 : ℝ)/(q : ℝ) := by
    dsimp [a]; push_cast; field_simp [hqne]; ring
  have hle (j : ℕ) : a j ≤ a (j+1) := by
    have hpos : (0 : ℝ) ≤ a (j+1)-a j := by
      rw [hwidth]; positivity
    linarith
  have hinc (j : ℕ) (hj : j < N) :
      Set.Icc (a j) (a (j+1)) ⊆ Set.Icc (0 : ℝ) (H : ℝ) := by
    intro x hx
    have hj1 : j+1 ≤ N := by omega
    have hright : a (j+1) ≤ (H : ℝ) := by
      dsimp [a,N]
      apply (div_le_iff₀ hqpos).mpr
      have : (((j+1 : ℕ) : ℝ) ≤ (H : ℝ)*(q : ℝ)) := by
        exact_mod_cast hj1
      simpa [Nat.cast_mul] using this
    have hleft : (0 : ℝ) ≤ a j := by dsimp [a]; positivity
    exact ⟨le_trans hleft hx.1, le_trans hx.2 hright⟩
  have hint (j : ℕ) (hj : j < N) :
      IntervalIntegrable f volume (a j) (a (j+1)) := by
    exact ContinuousOn.intervalIntegrable_of_Icc (hle j) (hf.mono (hinc j hj))
  have hcell (j : ℕ) (hj : j < N) :
      |∫ t in a j..a (j+1), f (a j)-f t| ≤ η/(q : ℝ) := by
    have hpoint (t : ℝ) (ht : t ∈ Set.uIoc (a j) (a (j+1))) :
        ‖f (a j)-f t‖ ≤ η := by
      have ht' : t ∈ Set.Ioc (a j) (a (j+1)) := by
        simpa only [Set.uIoc_of_le (hle j)] using ht
      have htI : t ∈ Set.Icc (a j) (a (j+1)) :=
        ⟨ht'.1.le,ht'.2⟩
      have hdist : dist (a j) t < δ := by
        calc
          dist (a j) t = t-a j := by
            rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr ht'.1.le)]
            ring
          _ ≤ a (j+1)-a j := sub_le_sub_right ht'.2 _
          _ = (1 : ℝ)/(q : ℝ) := hwidth j
          _ < δ := hδq
      have hh := hmod (a j) (hinc j hj ⟨le_rfl, hle j⟩)
        t (hinc j hj htI) hdist
      simpa [Real.dist_eq, Real.norm_eq_abs] using hh.le
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const hpoint
    rw [Real.norm_eq_abs] at hh
    rw [hwidth, abs_of_pos (div_pos one_pos hqpos)] at hh
    simpa [div_eq_mul_inv] using hh
  have hconst (j : ℕ) :
      (∫ t in a j..a (j+1), f (a j)) = f (a j)/(q : ℝ) := by
    rw [intervalIntegral.integral_const, hwidth]
    simp only [smul_eq_mul]
    ring
  have hsum :
      (∑ j ∈ Finset.range N, ∫ t in a j..a (j+1), f t) =
      ∫ t in (0 : ℝ)..(H : ℝ), f t := by
    convert intervalIntegral.sum_integral_adjacent_intervals (fun j hj => hint j hj)
      using 1 <;> simp [hstart, hspan]
  have hleft :
      bcLeftRiemann H q f =
      ∑ j ∈ Finset.range N, ∫ t in a j..a (j+1), f (a j) := by
    unfold bcLeftRiemann
    change (∑ j ∈ Finset.range N, f (a j)/(q : ℝ)) = _
    apply Finset.sum_congr rfl
    intro j hj
    exact (hconst j).symm
  have hdiff :
      bcLeftRiemann H q f -
      (∫ t in (0 : ℝ)..(H : ℝ), f t) =
      ∑ j ∈ Finset.range N,
        ∫ t in a j..a (j+1), (f (a j)-f t) := by
    rw [hleft, ← hsum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    rw [intervalIntegral.integral_sub
      (intervalIntegrable_const) (hint j (Finset.mem_range.mp hj))]
  have herr :
      |bcLeftRiemann H q f - (∫ t in (0 : ℝ)..(H : ℝ), f t)| ≤
        (H : ℝ)*η := by
    rw [hdiff]
    calc
      |∑ j ∈ Finset.range N, ∫ t in a j..a (j+1), f (a j)-f t| ≤
        ∑ j ∈ Finset.range N,
          |∫ t in a j..a (j+1), f (a j)-f t| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ Finset.range N, η/(q : ℝ) := by
        apply Finset.sum_le_sum
        intro j hj
        exact hcell j (Finset.mem_range.mp hj)
      _ = (H : ℝ)*η := by
        simp only [Finset.sum_const_zero, Finset.sum_const, Finset.card_range,
          nsmul_eq_mul]
        dsimp [N]; push_cast
        field_simp [hqne]
  have hfinal : (H : ℝ)*η < ε := by
    dsimp [η]
    have ht : (0 : ℝ) < (H : ℝ)+1 := by positivity
    calc
      (H : ℝ)*(ε/((H : ℝ)+1)) =
          ((H : ℝ)*ε)/((H : ℝ)+1) := by ring
      _ < ε := (div_lt_iff₀ ht).mpr (by nlinarith [hε])
  have hdist : dist (bcLeftRiemann H q f)
      (∫ t in (0 : ℝ)..(H : ℝ), f t) < ε := by
    rw [Real.dist_eq]
    exact lt_of_le_of_lt herr hfinal
  simpa [q] using hdist
