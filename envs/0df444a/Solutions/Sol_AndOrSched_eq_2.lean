-- Prove2me | solution 1 for AndOrSched.eq_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T01:25:25.571363+00:00
-- url     : https://prove2.me/submissions/56e34908-0914-4b65-b451-88e8fd17eee1

import Mathlib
import Definitions.Def_AndOrSched_Instance
import Definitions.Def_AndOrSched_LP1Feasible
import Definitions.Def_AndOrSched_fracC1
import Definitions.Def_AndOrSched_alphaPoint
open scoped Classical NNReal

open MeasureTheory

namespace AndOrSched.Aux_AO2

open AndOrSched

theorem cum_succ {J : Type} (x : J → ℕ → ℝ) (j : J) (t : ℕ) :
    cum x j (t + 1) = cum x j t + x j (t + 1) := by
  unfold cum
  rw [Finset.sum_Icc_succ_top (by omega)]

theorem cum_zero {J : Type} (x : J → ℕ → ℝ) (j : J) : cum x j 0 = 0 := by
  unfold cum; simp

theorem telescope {J : Type} (x : J → ℕ → ℝ) (j : J) (n : ℕ) :
    ∑ t ∈ Finset.range n, (cum x j n - cum x j t) = ∑ s ∈ Finset.Icc 1 n, (s : ℝ) * x j s := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_Icc_succ_top (by omega), ← ih, cum_succ]
    have e : ∀ t, cum x j n + x j (n + 1) - cum x j t = (cum x j n - cum x j t) + x j (n + 1) := by
      intro t; ring
    simp only [e, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    push_cast
    ring

end AndOrSched.Aux_AO2

open AndOrSched AndOrSched.Aux_AO2 in
theorem solution (I : Instance) (x : I.N → ℕ → ℝ) (hx : LP1Feasible I x) (j : I.N) :
    MeasureTheory.IntegrableOn (fun γ : ℝ => (alphaPoint x j γ : ℝ)) (Set.Ioc 0 1) ∧
    ∫ γ in Set.Ioc (0 : ℝ) 1, (alphaPoint x j γ : ℝ) ≤ fracC1 I x j := by
  set H := horizon I with hH
  obtain ⟨hcumH, _, _, _, hnn⟩ := hx
  have hcH : cum x j H = 1 := hcumH j
  -- monotonicity of the cumulative sum up to the horizon
  have hmono : ∀ t₁ t₂, t₁ ≤ t₂ → t₂ ≤ H → cum x j t₁ ≤ cum x j t₂ := by
    intro t₁ t₂ h12 h2H
    induction t₂ with
    | zero =>
      have : t₁ = 0 := by omega
      subst this; exact le_refl _
    | succ t ih =>
      rcases Nat.eq_or_lt_of_le h12 with h | h
      · rw [h]
      · rw [cum_succ]
        have := hnn j (t + 1) (Finset.mem_Icc.mpr ⟨by omega, h2H⟩)
        have := ih (by omega) (by omega)
        linarith
  have hc0 : ∀ t, t ≤ H → 0 ≤ cum x j t := fun t ht => by
    have := hmono 0 t (Nat.zero_le _) ht
    rwa [cum_zero] at this
  have hc1 : ∀ t, t ≤ H → cum x j t ≤ 1 := fun t ht => by
    have := hmono t H ht le_rfl
    rwa [hcH] at this
  -- alphaPoint as a count
  have hcount : ∀ γ ∈ Set.Ioc (0 : ℝ) 1, (alphaPoint x j γ : ℝ) =
      ∑ t ∈ Finset.range H, (Set.Ioi (cum x j t)).indicator (1 : ℝ → ℝ) γ := by
    intro γ hγ
    obtain ⟨hγ0, hγ1⟩ := hγ
    set τ := alphaPoint x j γ with hτ
    have hne : ({t : ℕ | γ ≤ cum x j t} : Set ℕ).Nonempty := ⟨H, by
      show γ ≤ cum x j H; rw [hcH]; exact hγ1⟩
    have hτmem : γ ≤ cum x j τ := Nat.sInf_mem hne
    have hτH : τ ≤ H := Nat.sInf_le (show γ ≤ cum x j H by rw [hcH]; exact hγ1)
    have hset : (Finset.range H).filter (fun t => cum x j t < γ) = Finset.range τ := by
      ext t
      simp only [Finset.mem_filter, Finset.mem_range]
      constructor
      · rintro ⟨htH, hlt⟩
        by_contra hge
        push_neg at hge
        have := hmono τ t hge htH.le
        linarith
      · intro htτ
        refine ⟨by omega, ?_⟩
        by_contra hge
        push_neg at hge
        have := Nat.sInf_le (show t ∈ {t : ℕ | γ ≤ cum x j t} from hge)
        exact absurd htτ (not_lt.mpr this)
    have hind : ∀ t, (Set.Ioi (cum x j t)).indicator (1 : ℝ → ℝ) γ =
        if cum x j t < γ then 1 else 0 := by
      intro t
      simp only [Set.indicator, Set.mem_Ioi, Pi.one_apply]
    simp only [hind]
    rw [← Finset.sum_filter, Finset.sum_const, hset, Finset.card_range, nsmul_eq_mul, mul_one]
  haveI : IsFiniteMeasure (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
    ⟨by rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]; exact measure_Ioc_lt_top⟩
  have hint_ind : ∀ t ∈ Finset.range H,
      Integrable ((Set.Ioi (cum x j t)).indicator (1 : ℝ → ℝ)) (volume.restrict (Set.Ioc 0 1)) :=
    fun t _ => (integrable_const (1 : ℝ)).indicator measurableSet_Ioi
  have hint_sum : IntegrableOn (fun γ : ℝ => ∑ t ∈ Finset.range H,
      (Set.Ioi (cum x j t)).indicator (1 : ℝ → ℝ) γ) (Set.Ioc 0 1) :=
    integrable_finsetSum _ hint_ind
  refine ⟨hint_sum.congr_fun (fun γ hγ => (hcount γ hγ).symm) measurableSet_Ioc, ?_⟩
  rw [setIntegral_congr_fun measurableSet_Ioc hcount, integral_finsetSum _ hint_ind]
  have hterm : ∀ t ∈ Finset.range H, ∫ γ in Set.Ioc (0 : ℝ) 1,
      (Set.Ioi (cum x j t)).indicator (1 : ℝ → ℝ) γ = 1 - cum x j t := by
    intro t ht
    have htH : t ≤ H := (Finset.mem_range.mp ht).le
    rw [integral_indicator_one measurableSet_Ioi, Measure.real,
      Measure.restrict_apply measurableSet_Ioi]
    have hset : Set.Ioi (cum x j t) ∩ Set.Ioc 0 1 = Set.Ioc (cum x j t) 1 := by
      ext γ
      simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Ioc]
      constructor
      · rintro ⟨h1, _, h3⟩; exact ⟨h1, h3⟩
      · rintro ⟨h1, h3⟩; exact ⟨h1, lt_of_le_of_lt (hc0 t htH) h1, h3⟩
    rw [hset, Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith [hc1 t htH])]
  rw [Finset.sum_congr rfl hterm]
  unfold fracC1
  rw [← hH, ← telescope x j H, hcH]
