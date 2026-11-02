-- Prove2me | solution 1 for AffineStorage.Ruin.theorem_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T23:52:45.007276+00:00
-- url     : https://prove2.me/submissions/6f98b702-50bc-4df2-93bf-3b0751b031b9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AffineStorage_Ruin_Model
import Theorems.Thm_AffineStorage_Ruin_eq_9
import Theorems.Thm_AffineStorage_Ruin_eq_10
import Theorems.Thm_AffineStorage_Ruin_eq_11
import Theorems.Thm_AffineStorage_Ruin_remark_3
open MeasureTheory ProbabilityTheory Filter Topology
open AffineStorage.Ruin

lemma affRuin_setIntegral_pos_aux {f : ℝ → ℝ} {s t : Set ℝ} (hs : MeasurableSet s)
    (hts : t ⊆ s) (ht : 0 < volume t) (hf : IntegrableOn f s)
    (hnn : ∀ x ∈ s, 0 ≤ f x) (hpos : ∀ x ∈ t, 0 < f x) : 0 < ∫ x in s, f x := by
  rw [setIntegral_pos_iff_support_of_nonneg_ae (ae_restrict_of_forall_mem hs hnn) hf]
  exact lt_of_lt_of_le ht (measure_mono fun x hx => ⟨(hpos x hx).ne', hts hx⟩)

theorem solution (P : Params) (hS : P.Standing) {Ω : Type*} [MeasurableSpace Ω]
    (B : Basis Ω) (hB : B.IsValid P) (Fs : ℝ → ℝ) (hF : IsPrimitiveF P Fs) :
    let ρ0 := rho B P 0
    let φμ := phi B P P.μ
    let Δ := I (G1 P) Fs 0 * I (G2 P) Fs P.μ - I (G1 P) Fs P.μ * I (G2 P) Fs 0
    (∀ ϑ, 0 < ϑ → ϑ ≠ P.μ →
        phi B P ϑ = -(∫ η in Set.Ioi ϑ, G P ρ0 φμ η * Real.exp (-(Fs η)))
          * Real.exp (Fs ϑ)) ∧
    Δ ≠ 0 ∧
    ρ0 = -(I (G3 P) Fs 0 * I (G2 P) Fs P.μ - I (G3 P) Fs P.μ * I (G2 P) Fs 0) / Δ ∧
    φμ = -(I (G1 P) Fs 0 * I (G3 P) Fs P.μ - I (G1 P) Fs P.μ * I (G3 P) Fs 0) / Δ := by
  intro ρ0 φμ Δ
  obtain ⟨hp, hr, hlp, hlm, hμ, -⟩ := id hS
  have h9 := eq_9 P hS B hB Fs hF
  have h10 := eq_10 P hS B hB Fs hF
  have h11 := eq_11 P hS B hB Fs hF
  obtain ⟨hi1, hi2, -⟩ := remark_3 P hS Fs hF
  -- splitting `(0, ∞) = (0, μ] ∪ (μ, ∞)`
  have hU : Set.Ioc 0 P.μ ∪ Set.Ioi P.μ = Set.Ioi 0 := Set.Ioc_union_Ioi_eq_Ioi hμ.le
  have hD : Disjoint (Set.Ioc 0 P.μ) (Set.Ioi P.μ) := Set.Ioc_disjoint_Ioi le_rfl
  have hsub1 : Set.Ioc 0 P.μ ⊆ Set.Ioi 0 := fun x hx => hx.1
  have hsub2 : Set.Ioi P.μ ⊆ Set.Ioi 0 := fun x hx => lt_trans hμ hx
  have split : ∀ g : ℝ → ℝ, IntegrableOn g (Set.Ioi 0) →
      ∫ η in Set.Ioi 0, g η = (∫ η in Set.Ioc 0 P.μ, g η) + ∫ η in Set.Ioi P.μ, g η := by
    intro g hg
    rw [← hU, setIntegral_union hD measurableSet_Ioi (hg.mono_set hsub1) (hg.mono_set hsub2)]
  set a := ∫ η in Set.Ioc 0 P.μ, G1 P η * Real.exp (-(Fs η)) with ha_def
  set b := I (G1 P) Fs P.μ with hb_def
  set c := ∫ η in Set.Ioc 0 P.μ, G2 P η * Real.exp (-(Fs η)) with hc_def
  set d := I (G2 P) Fs P.μ with hd_def
  have hI10 : I (G1 P) Fs 0 = a + b := split _ hi1
  have hI20 : I (G2 P) Fs 0 = c + d := split _ hi2
  have hpr : 0 < P.p / P.r := div_pos hp hr
  have hlr : 0 < P.lamPlus / P.r := div_pos hlp hr
  have hvol1 : 0 < volume (Set.Ioo 0 P.μ) := by simp [hμ]
  have hvol2 : 0 < volume (Set.Ioi P.μ) := by simp
  have ha : a < 0 := by
    have : 0 < ∫ η in Set.Ioc 0 P.μ, -(G1 P η * Real.exp (-(Fs η))) :=
      affRuin_setIntegral_pos_aux measurableSet_Ioc Set.Ioo_subset_Ioc_self hvol1
        (hi1.mono_set hsub1).neg
        (fun x _ => by simp only [G1]; nlinarith [Real.exp_pos (-(Fs x))])
        (fun x _ => by simp only [G1]; nlinarith [Real.exp_pos (-(Fs x))])
    rw [integral_neg] at this; linarith
  have hb : b < 0 := by
    have : 0 < ∫ η in Set.Ioi P.μ, -(G1 P η * Real.exp (-(Fs η))) :=
      affRuin_setIntegral_pos_aux measurableSet_Ioi subset_rfl hvol2
        (hi1.mono_set hsub2).neg
        (fun x _ => by simp only [G1]; nlinarith [Real.exp_pos (-(Fs x))])
        (fun x _ => by simp only [G1]; nlinarith [Real.exp_pos (-(Fs x))])
    rw [hb_def, I, ← neg_pos, ← integral_neg]; exact this
  have hc : c < 0 := by
    have : 0 < ∫ η in Set.Ioc 0 P.μ, -(G2 P η * Real.exp (-(Fs η))) := by
      refine affRuin_setIntegral_pos_aux measurableSet_Ioc Set.Ioo_subset_Ioc_self hvol1
        (hi2.mono_set hsub1).neg ?_ ?_
      · intro x hx
        simp only [G2]
        have h1 : 0 ≤ 1 / (P.μ - x) := by
          have := hx.2; exact div_nonneg zero_le_one (by linarith)
        have := Real.exp_pos (-(Fs x))
        have : 0 ≤ P.lamPlus / P.r * (1 / (P.μ - x)) * Real.exp (-(Fs x)) := by positivity
        nlinarith
      · intro x hx
        simp only [G2]
        have h1 : 0 < 1 / (P.μ - x) := by
          have := hx.2; exact div_pos one_pos (by linarith)
        have := Real.exp_pos (-(Fs x))
        have : 0 < P.lamPlus / P.r * (1 / (P.μ - x)) * Real.exp (-(Fs x)) := by positivity
        nlinarith
    rw [integral_neg] at this; linarith
  have hd : 0 < d := by
    rw [hd_def, I]
    refine affRuin_setIntegral_pos_aux measurableSet_Ioi subset_rfl hvol2
        (hi2.mono_set hsub2) ?_ ?_
    · intro x hx
      simp only [G2]
      have h1 : 1 / (P.μ - x) < 0 := by
        have : P.μ - x < 0 := by have := hx.out; linarith
        exact one_div_neg.mpr this
      have := Real.exp_pos (-(Fs x))
      have : 0 < P.lamPlus / P.r * (-(1 / (P.μ - x))) * Real.exp (-(Fs x)) := by
        have : 0 < -(1 / (P.μ - x)) := by linarith
        positivity
      nlinarith
    · intro x hx
      simp only [G2]
      have h1 : 1 / (P.μ - x) < 0 := by
        have : P.μ - x < 0 := by have := hx.out; linarith
        exact one_div_neg.mpr this
      have := Real.exp_pos (-(Fs x))
      have : 0 < P.lamPlus / P.r * (-(1 / (P.μ - x))) * Real.exp (-(Fs x)) := by
        have : 0 < -(1 / (P.μ - x)) := by linarith
        positivity
      nlinarith
  have hΔ : Δ = a * d - b * c := by
    simp only [Δ]; rw [hI10, hI20]; ring
  have hΔneg : Δ < 0 := by
    rw [hΔ]; nlinarith [mul_pos_of_neg_of_neg hb hc, mul_neg_of_neg_of_pos ha hd]
  have hΔne : Δ ≠ 0 := hΔneg.ne
  refine ⟨h9, hΔne, ?_, ?_⟩
  · simp only [ρ0]
    rw [eq_div_iff hΔne]
    simp only [Δ]
    linear_combination (I (G2 P) Fs P.μ) * h10 - (I (G2 P) Fs 0) * h11
  · simp only [φμ]
    rw [eq_div_iff hΔne]
    simp only [Δ]
    linear_combination (I (G1 P) Fs 0) * h11 - (I (G1 P) Fs P.μ) * h10
