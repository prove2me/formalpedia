-- Prove2me | solution 1 for AdaptiveStepIPM.WideNbhd.lemma_1c
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T18:52:54.753509+00:00
-- url     : https://prove2.me/submissions/2e15e124-2cf1-4a35-9b93-014e02ea7bc7

import Mathlib
import Definitions.Def_AdaptiveStepIPM_WideNbhd_Neighborhoods
import Definitions.Def_AdaptiveStepIPM_WideNbhd_Algorithm2
open AdaptiveStepIPM.WideNbhd Matrix

private theorem scaled_identity (x s d e : ℝ) (hx : 0 < x) (hs : 0 < s) :
    Real.sqrt (s / x) * d + Real.sqrt (x / s) * e =
      (s * d + x * e) / Real.sqrt (x * s) ∧
    (Real.sqrt (s / x) * d) * (Real.sqrt (x / s) * e) = d * e := by
  have ha := Real.sqrt_pos.mpr hx
  have hb := Real.sqrt_pos.mpr hs
  have ha2 := Real.sq_sqrt hx.le
  have hb2 := Real.sq_sqrt hs.le
  rw [Real.sqrt_div hs.le, Real.sqrt_div hx.le, Real.sqrt_mul hx.le]
  constructor
  · field_simp
    rw [ha2, hb2]
    ring
  · field_simp

private theorem direction_bounds {n m : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (x s : Fin n → ℝ) (hx : ∀ j, 0 < x j) (hs : ∀ j, 0 < s j)
    (γ : ℝ) (dx : Fin n → ℝ) (dy : Fin m → ℝ) (ds : Fin n → ℝ)
    (hd : IsDirection A x s γ dx dy ds) (j : Fin n) :
    -(norm2 (rvec γ x s) ^ 2 / 4) ≤ pvec x s dx j * qvec x s ds j ∧
    pvec x s dx j * qvec x s ds j ≤ rvec γ x s j ^ 2 / 4 := by
  classical
  let p := pvec x s dx
  let q := qvec x s ds
  let r := rvec γ x s
  have hpq : ∀ i, p i + q i = r i := by
    intro i
    exact (scaled_identity (x i) (s i) (dx i) (ds i) (hx i) (hs i)).1.trans
      (congrArg (fun z => z / Real.sqrt (x i * s i)) (hd.1 i))
  have hprod : ∀ i, p i * q i = dx i * ds i := by
    intro i
    exact (scaled_identity (x i) (s i) (dx i) (ds i) (hx i) (hs i)).2
  have hzero : ∑ i, p i * q i = 0 := by
    simp_rw [hprod]
    change dx ⬝ᵥ ds = 0
    have ht : dx ⬝ᵥ (Aᵀ *ᵥ dy) = 0 := by
      rw [dotProduct_transpose_mulVec, hd.2.1]
      simp
    have he := congrArg (fun v => dx ⬝ᵥ v) hd.2.2
    rw [dotProduct_add] at he
    simpa [ht] using he
  have hsum : ∑ i, (p i - q i) ^ 2 = ∑ i, r i ^ 2 := by
    calc
      _ = ∑ i, (r i ^ 2 - 4 * (p i * q i)) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [← hpq]
        ring
      _ = _ := by rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hzero]; ring
  have hj := Finset.single_le_sum (fun i _ => sq_nonneg (p i - q i)) (Finset.mem_univ j)
  rw [hsum] at hj
  have hn : norm2 r ^ 2 = ∑ i, r i ^ 2 :=
    Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg (r i))
  change -(norm2 r ^ 2 / 4) ≤ p j * q j ∧ p j * q j ≤ r j ^ 2 / 4
  rw [hn]
  have he := hpq j
  constructor
  · nlinarith [sq_nonneg (p j + q j)]
  · rw [← he]
    nlinarith [sq_nonneg (p j - q j)]


theorem solution {n m : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (x s : Fin n → ℝ)
    (hx : ∀ j, 0 < x j) (hs : ∀ j, 0 < s j) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (dx : Fin n → ℝ) (dy : Fin m → ℝ) (ds : Fin n → ℝ) (hd : IsDirection A x s γ dx dy ds) :
    normInfNeg (AdaptiveStepIPM.PredCorr.Pq x s dx ds) ≤ norm2 (rvec γ x s) ^ 2 / 4 ∧
      norm2 (rvec γ x s) ^ 2 / 4 ≤ (n : ℝ) * normInf (rvec γ x s) ^ 2 / 4 ∧
      normInfPos (AdaptiveStepIPM.PredCorr.Pq x s dx ds) ≤ normInf (rvec γ x s) ^ 2 / 4 ∧
      normInf (AdaptiveStepIPM.PredCorr.Pq x s dx ds) ≤ norm2 (rvec γ x s) ^ 2 / 4 := by
  classical
  rcases isEmpty_or_nonempty (Fin n) with he | he
  · simp [normInfNeg, normInfPos, normInf, norm2, rvec]
  let r := rvec γ x s
  let v := AdaptiveStepIPM.PredCorr.Pq x s dx ds
  have hN : 0 ≤ normInf r := by
    obtain ⟨j⟩ := he
    exact (abs_nonneg (r j)).trans (le_ciSup (Finite.bddAbove_range (fun j => |r j|)) j)
  have hr : ∀ j, |r j| ≤ normInf r := fun j => le_ciSup (Finite.bddAbove_range (fun j => |r j|)) j
  have hsq : ∀ j, r j ^ 2 ≤ normInf r ^ 2 := by
    intro j
    have := hr j
    nlinarith [sq_abs (r j), abs_nonneg (r j)]
  have hsum0 : 0 ≤ ∑ j, r j ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hnorm : norm2 r ^ 2 = ∑ j, r j ^ 2 := Real.sq_sqrt hsum0
  have hsum : norm2 r ^ 2 ≤ (n : ℝ) * normInf r ^ 2 := by
    rw [hnorm]
    calc
      _ ≤ ∑ _j : Fin n, normInf r ^ 2 := Finset.sum_le_sum fun j _ => hsq j
      _ = _ := by simp
  have hb : ∀ j, -(norm2 r ^ 2 / 4) ≤ v j ∧ v j ≤ r j ^ 2 / 4 :=
    fun j => direction_bounds A x s hx hs γ dx dy ds hd j
  have hcoord : ∀ j, r j ^ 2 ≤ norm2 r ^ 2 := by
    intro j
    rw [hnorm]
    exact Finset.single_le_sum (fun i _ => sq_nonneg _) (Finset.mem_univ j)
  refine ⟨?_, by dsimp [r] at hsum; linarith, ?_, ?_⟩
  · apply ciSup_le
    intro j
    change |min (v j) 0| ≤ norm2 r ^ 2 / 4
    rw [abs_of_nonpos (min_le_right _ _)]
    have := (hb j).1
    rw [min_def]
    split_ifs <;> nlinarith [sq_nonneg (norm2 r)]
  · apply ciSup_le
    intro j
    change |max (v j) 0| ≤ normInf r ^ 2 / 4
    rw [abs_of_nonneg (le_max_right _ _)]
    exact max_le (by have := (hb j).2; have := hsq j; linarith) (by positivity)
  · apply ciSup_le
    intro j
    apply abs_le.mpr
    exact ⟨(hb j).1, by have := (hb j).2; have := hcoord j; linarith⟩

#print axioms solution
