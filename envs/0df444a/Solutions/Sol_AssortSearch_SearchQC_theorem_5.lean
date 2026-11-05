-- Prove2me | solution 1 for AssortSearch.SearchQC.theorem_5
-- status  : ACCEPTED   (disprove)
-- author  : @tianyipeng
-- created : 2026-11-05T01:52:30.681876+00:00
-- url     : https://prove2.me/submissions/d85e6515-fa7e-4361-9e67-b8c8e1a919b9

import Mathlib
import Definitions.Def_AssortSearch_SearchQC_Model

open AssortSearch.SearchQC RetailVariety.Structure

namespace SearchQCCex

/-- Cost function of the counterexample: `c'' (q) = -20 (q - 3/20)^2 (q - 41/50)^2`,
`c(0) = 0`, `c'(1) = 0`. -/
noncomputable def cc (q : ℝ) : ℝ :=
  19357/150000 * q - 15129/100000 * q^2 + 3977/5000 * q^3 - 11869/6000 * q^4
    + 97/50 * q^5 - 2/3 * q^6

noncomputable def cc1 (q : ℝ) : ℝ :=
  19357/150000 - 15129/50000 * q + 11931/5000 * q^2 - 11869/1500 * q^3
    + 97/10 * q^4 - 4 * q^5

noncomputable def cc2 (q : ℝ) : ℝ :=
  -15129/50000 + 11931/2500 * q - 11869/500 * q^2 + 194/5 * q^3 - 20 * q^4

lemma hd1 (q : ℝ) : HasDerivAt cc (cc1 q) q := by
  have h1 := hasDerivAt_id q
  have h2 := hasDerivAt_pow 2 q
  have h3 := hasDerivAt_pow 3 q
  have h4 := hasDerivAt_pow 4 q
  have h5 := hasDerivAt_pow 5 q
  have h6 := hasDerivAt_pow 6 q
  have := ((((((h1.const_mul (19357/150000 : ℝ)).sub (h2.const_mul (15129/100000 : ℝ))).add
    (h3.const_mul (3977/5000 : ℝ))).sub (h4.const_mul (11869/6000 : ℝ))).add
    (h5.const_mul (97/50 : ℝ))).sub (h6.const_mul (2/3 : ℝ)))
  convert this using 1
  all_goals first
    | (ext x; simp only [cc, cc1, Pi.add_apply, Pi.sub_apply, id]; ring)
    | (ext x; simp only [cc, cc1, Pi.add_apply, Pi.sub_apply, id])
    | (simp only [cc1, cc2]; norm_num; ring)
    | (simp only [cc1, cc2]; norm_num)

lemma hd2 (q : ℝ) : HasDerivAt cc1 (cc2 q) q := by
  have h1 := hasDerivAt_id q
  have h2 := hasDerivAt_pow 2 q
  have h3 := hasDerivAt_pow 3 q
  have h4 := hasDerivAt_pow 4 q
  have h5 := hasDerivAt_pow 5 q
  have := (((((((hasDerivAt_const q (19357/150000 : ℝ)).sub (h1.const_mul (15129/50000 : ℝ))).add
    (h2.const_mul (11931/5000 : ℝ))).sub (h3.const_mul (11869/1500 : ℝ))).add
    (h4.const_mul (97/10 : ℝ))).sub (h5.const_mul (4 : ℝ))))
  convert this using 1
  all_goals first
    | (ext x; simp only [cc, cc1, Pi.add_apply, Pi.sub_apply, id]; ring)
    | (ext x; simp only [cc, cc1, Pi.add_apply, Pi.sub_apply, id])
    | (simp only [cc1, cc2]; norm_num; ring)
    | (simp only [cc1, cc2]; norm_num)

lemma cc2_nonpos (q : ℝ) : cc2 q ≤ 0 := by
  have : cc2 q = -20 * ((q - 3/20) * (q - 41/50))^2 := by unfold cc2; ring
  rw [this]; nlinarith [sq_nonneg ((q - 3/20) * (q - 41/50))]

lemma cc_concave : ConcaveOn ℝ (Set.Icc 0 1) cc :=
  concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc 0 1)
    (fun x _ => (hd1 x).continuousAt.continuousWithinAt)
    (fun x _ => (hd1 x).hasDerivWithinAt) (fun x _ => (hd2 x).hasDerivWithinAt)
    (fun x _ => cc2_nonpos x)

lemma cc1_anti : AntitoneOn cc1 (Set.Icc 0 1) :=
  antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 1)
    (fun x _ => (hd2 x).continuousAt.continuousWithinAt)
    (fun x _ => (hd2 x).hasDerivWithinAt) (fun x _ => cc2_nonpos x)

lemma cc_mono : MonotoneOn cc (Set.Icc 0 1) :=
  monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 1)
    (fun x _ => (hd1 x).continuousAt.continuousWithinAt)
    (fun x _ => (hd1 x).hasDerivWithinAt)
    (fun x hx => by
      rw [interior_Icc] at hx
      have h1 : cc1 1 ≤ cc1 x := cc1_anti ⟨hx.1.le, hx.2.le⟩ ⟨zero_le_one, le_refl _⟩ hx.2.le
      have h2 : cc1 1 = 0 := by unfold cc1; norm_num
      linarith)

lemma cc_smooth : ContDiffOn ℝ 2 cc (Set.Ioo 0 1) := by
  unfold cc; fun_prop

noncomputable def vv : Fin 2 → ℝ := ![249/50, 1]

lemma key (lam m x : ℝ) :
    hSI m cc lam vv (1/50) {0} 1 x =
      (m * (x / (x + 5) * (1 - Real.exp (-(lam * (x + 5)))))
          - cc (x / (x + 5) * (1 - Real.exp (-(lam * (x + 5))))))
      + (m * (249/50 / (x + 5) * (1 - Real.exp (-(lam * (x + 5)))))
          - cc (249/50 / (x + 5) * (1 - Real.exp (-(lam * (x + 5))))))
      - ∑ i ∈ ({0} : Finset (Fin 2)), profitSI m cc lam vv (1/50) {0} i := by
  have hs : ∑ i ∈ insert (1 : Fin 2) ({0} : Finset (Fin 2)), Function.update vv 1 x i
      = x + 249/50 := by
    rw [Finset.sum_insert (by decide), Finset.sum_singleton]
    simp [vv]
  have h1 : (1/50 : ℝ) + (x + 249/50) = x + 5 := by ring
  have h2 : (x + 249/50) + (1/50 : ℝ) = x + 5 := by ring
  unfold hSI lossSI profitAdd demandAdd demandSI share searchProb
  rw [hs, h1, h2]
  simp [vv]
  ring

lemma exp_val (k : ℕ) : Real.exp (-(Real.log 2 * (k : ℝ))) = 1 / 2 ^ k := by
  rw [Real.exp_neg, show Real.log 2 * (k : ℝ) = Real.log (2 ^ k) by rw [Real.log_pow]; ring,
    Real.exp_log (by positivity)]
  simp

end SearchQCCex

open SearchQCCex in
theorem solution : ¬ (∀ {n : ℕ} (v : Fin n → ℝ) (v0 lam m : ℝ) (c : ℝ → ℝ)
    (S : Finset (Fin n)) (j : Fin n),
    (∀ i, 0 < v i) → 0 < v0 → 0 < lam → j ∉ S →
    ConcaveOn ℝ (Set.Icc 0 1) c → MonotoneOn c (Set.Icc 0 1) →
    ContDiffOn ℝ 2 c (Set.Ioo 0 1) →
    QuasiconvexOn ℝ (Set.Ici 0) (hSI m c lam v v0 S j)) := by
  intro H
  have hq := H vv (1/50) (Real.log 2) (11/10) cc {0} 1
    (by intro i; fin_cases i <;> simp [vv] <;> norm_num) (by norm_num)
    (Real.log_pos (by norm_num)) (by decide) cc_concave cc_mono cc_smooth
  set h := hSI (11/10) cc (Real.log 2) vv (1/50) {0} 1 with hh
  have hconv := hq (max (h 0) (h 2))
  have h0 : (0 : ℝ) ∈ {x ∈ Set.Ici (0 : ℝ) | h x ≤ max (h 0) (h 2)} :=
    ⟨Set.mem_Ici.mpr le_rfl, le_max_left _ _⟩
  have h2 : (2 : ℝ) ∈ {x ∈ Set.Ici (0 : ℝ) | h x ≤ max (h 0) (h 2)} :=
    ⟨Set.mem_Ici.mpr (by norm_num), le_max_right _ _⟩
  have h1 := hconv h0 h2 (show (0 : ℝ) ≤ 1/2 by norm_num) (show (0 : ℝ) ≤ 1/2 by norm_num)
    (by norm_num)
  have h1' : h 1 ≤ max (h 0) (h 2) := by
    have := h1.2
    simpa using this
  have e0 : Real.exp (-(Real.log 2 * ((0 : ℝ) + 5))) = 1 / 2 ^ 5 := by
    rw [← exp_val 5]; norm_num
  have e1 : Real.exp (-(Real.log 2 * ((1 : ℝ) + 5))) = 1 / 2 ^ 6 := by
    rw [← exp_val 6]; norm_num
  have e2 : Real.exp (-(Real.log 2 * ((2 : ℝ) + 5))) = 1 / 2 ^ 7 := by
    rw [← exp_val 7]; norm_num
  have v0' : h 0 = _ := key (Real.log 2) (11/10) 0
  have v1' : h 1 = _ := key (Real.log 2) (11/10) 1
  have v2' : h 2 = _ := key (Real.log 2) (11/10) 2
  rw [e0] at v0'
  rw [e1] at v1'
  rw [e2] at v2'
  set C := ∑ i ∈ ({0} : Finset (Fin 2)), profitSI (11/10) cc (Real.log 2) vv (1/50) {0} i
  have a0 : h 0 < h 1 := by
    rw [v0', v1']; unfold cc; norm_num
  have a2 : h 2 < h 1 := by
    rw [v2', v1']; unfold cc; norm_num
  rcases le_max_iff.mp h1' with h' | h' <;> linarith
