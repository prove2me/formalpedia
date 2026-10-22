-- Prove2me | solution 1 for AssortSearch.SearchQC.f_mono_g_anti
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:57:40.144097+00:00
-- url     : https://prove2.me/submissions/6b319d00-c772-4beb-8ef9-a0e771292662

import Mathlib
import Definitions.Def_AssortSearch_SearchQC_Model
import Definitions.Def_AssortSearch_SearchQC_ProofTerms
set_option autoImplicit false
open AssortSearch.SearchQC

lemma as_hbar_mem (lam VS x : ℝ) (hlam : 0 < lam) (hVS : 0 < VS) (hx : 0 < x) :
    0 < Hbar lam VS x ∧ Hbar lam VS x < 1 := by
  unfold Hbar
  have h0 : 0 < lam * (x + VS) := by positivity
  have h1 : Real.exp (-(lam * (x + VS))) < 1 := by
    have := Real.exp_lt_exp.2 (show -(lam * (x + VS)) < 0 by linarith)
    simpa using this
  have h2 := Real.exp_pos (-(lam * (x + VS)))
  constructor <;> linarith

lemma as_cprime_anti (c : ℝ → ℝ) (hconc : ConcaveOn ℝ (Set.Icc 0 1) c)
    (hdiff : DifferentiableOn ℝ c (Set.Ioo 0 1)) :
    AntitoneOn (deriv c) (Set.Ioo 0 1) := by
  have hc : ConcaveOn ℝ (Set.Ioo 0 1) c := hconc.subset Set.Ioo_subset_Icc_self (convex_Ioo 0 1)
  exact hc.antitoneOn_deriv (fun x hx => hdiff.differentiableAt (Ioo_mem_nhds hx.1 hx.2))

lemma as_ratio_anti (lam VS a b : ℝ) (hlam : 0 < lam) (hVS : 0 < VS) (ha : 0 < a) (hab : a ≤ b) :
    Hbar lam VS b / (b + VS) ≤ Hbar lam VS a / (a + VS) := by
  have hb0 : 0 < b := by linarith
  have hs : 0 < a + VS := by positivity
  have ht : 0 < b + VS := by positivity
  have hst : a + VS ≤ b + VS := by linarith
  -- convexity of exp
  have hconv := convexOn_exp.2 (Set.mem_univ (-(lam * (b + VS)))) (Set.mem_univ (0 : ℝ))
    (show (0:ℝ) ≤ (a + VS) / (b + VS) by positivity)
    (show (0:ℝ) ≤ 1 - (a + VS) / (b + VS) by rw [sub_nonneg, div_le_one ht]; exact hst)
    (by ring)
  simp only [smul_eq_mul, mul_zero, add_zero, Real.exp_zero, mul_one] at hconv
  have e : (a + VS) / (b + VS) * -(lam * (b + VS)) = -(lam * (a + VS)) := by field_simp
  rw [e] at hconv
  unfold Hbar
  rw [div_le_div_iff₀ ht hs]
  have h3 : (a + VS) / (b + VS) * Real.exp (-(lam * (b + VS))) = (a + VS) * Real.exp (-(lam * (b + VS))) / (b + VS) := by ring
  have h4 : Real.exp (-(lam * (a + VS))) ≤ (a + VS) * Real.exp (-(lam * (b + VS))) / (b + VS) + (1 - (a + VS) / (b + VS)) := by
    rw [← h3]; exact hconv
  have h5 : (b + VS) * Real.exp (-(lam * (a + VS))) ≤ (a + VS) * Real.exp (-(lam * (b + VS))) + (b + VS) - (a + VS) := by
    have := mul_le_mul_of_nonneg_left h4 ht.le
    have e2 : (b + VS) * ((a + VS) * Real.exp (-(lam * (b + VS))) / (b + VS) + (1 - (a + VS) / (b + VS)))
        = (a + VS) * Real.exp (-(lam * (b + VS))) + (b + VS) - (a + VS) := by field_simp; ring
    linarith
  nlinarith

theorem solution {n : ℕ} (v : Fin n → ℝ) (v0 lam m : ℝ) (c : ℝ → ℝ)
    (S : Finset (Fin n))
    (hv : ∀ i, 0 < v i) (hv0 : 0 < v0) (hlam : 0 < lam)
    (hconc : ConcaveOn ℝ (Set.Icc 0 1) c) (hdiff : DifferentiableOn ℝ c (Set.Ioo 0 1)) :
    MonotoneOn (fFn m c lam (VS v v0 S)) (Set.Ioi 0) ∧
      AntitoneOn (gFn m c lam v S (VS v v0 S)) (Set.Ioi 0) := by
  have hanti := as_cprime_anti c hconc hdiff
  have hVS : 0 < VS v v0 S := by
    unfold VS
    have : 0 ≤ ∑ i ∈ S, v i := Finset.sum_nonneg (fun i _ => (hv i).le)
    linarith
  have hvle : ∀ i ∈ S, v i ≤ VS v v0 S := by
    intro i hi
    unfold VS
    have : v i ≤ ∑ j ∈ S, v j := Finset.single_le_sum (fun j _ => (hv j).le) hi
    linarith
  generalize VS v v0 S = V at hVS hvle ⊢
  constructor
  · intro a ha b hb hab
    simp only [Set.mem_Ioi] at ha hb
    unfold fFn
    have hHa := as_hbar_mem lam _ a hlam hVS ha
    have hHb := as_hbar_mem lam _ b hlam hVS hb
    have hmem : ∀ x : ℝ, 0 < x → Hbar lam (V) x * x / (x + V) ∈ Set.Ioo (0:ℝ) 1 := by
      intro x hx
      have hH := as_hbar_mem lam _ x hlam hVS hx
      have hq : 0 < x / (x + V) := by positivity
      have hq1 : x / (x + V) < 1 := by rw [div_lt_one (by positivity)]; linarith
      have e : Hbar lam (V) x * x / (x + V) = Hbar lam (V) x * (x / (x + V)) := by ring
      rw [e]
      exact ⟨mul_pos hH.1 hq, by nlinarith [hH.1, hH.2]⟩
    have hle : Hbar lam (V) a * a / (a + V) ≤ Hbar lam (V) b * b / (b + V) := by
      have h1 : Hbar lam (V) a ≤ Hbar lam (V) b := by
        unfold Hbar
        have : Real.exp (-(lam * (b + V))) ≤ Real.exp (-(lam * (a + V))) :=
          Real.exp_le_exp.2 (by nlinarith)
        linarith
      have h2 : a / (a + V) ≤ b / (b + V) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      have e1 : ∀ x : ℝ, Hbar lam (V) x * x / (x + V) = Hbar lam (V) x * (x / (x + V)) := fun x => by ring
      rw [e1, e1]
      exact mul_le_mul h1 h2 (by positivity) hHb.1.le
    have := hanti (hmem a ha) (hmem b hb) hle
    linarith
  · intro a ha b hb hab
    simp only [Set.mem_Ioi] at ha hb
    unfold gFn
    have hmem : ∀ x : ℝ, 0 < x → ∀ i ∈ S, Hbar lam (V) x * v i / (x + V) ∈ Set.Ioo (0:ℝ) 1 := by
      intro x hx i hi
      have hH := as_hbar_mem lam _ x hlam hVS hx
      have hvi : v i ≤ V := hvle i hi
      have hq : 0 < v i / (x + V) := by have := hv i; positivity
      have hq1 : v i / (x + V) < 1 := by rw [div_lt_one (by positivity)]; linarith
      have e : Hbar lam (V) x * v i / (x + V) = Hbar lam (V) x * (v i / (x + V)) := by ring
      rw [e]
      exact ⟨mul_pos hH.1 hq, by nlinarith [hH.1, hH.2]⟩
    have key : ∀ i ∈ S, deriv c (Hbar lam (V) a * v i / (a + V)) * v i ≤
        deriv c (Hbar lam (V) b * v i / (b + V)) * v i := by
      intro i hi
      have hle : Hbar lam (V) b * v i / (b + V) ≤ Hbar lam (V) a * v i / (a + V) := by
        have := as_ratio_anti lam _ a b hlam hVS ha hab
        have e1 : ∀ x : ℝ, Hbar lam (V) x * v i / (x + V) = (Hbar lam (V) x / (x + V)) * v i := fun x => by ring
        rw [e1, e1]
        exact mul_le_mul_of_nonneg_right this (hv i).le
      have := hanti (hmem b hb i hi) (hmem a ha i hi) hle
      exact mul_le_mul_of_nonneg_right this (hv i).le
    have := Finset.sum_le_sum key
    linarith
