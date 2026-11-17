-- Prove2me | Definitions.Def_RHCount_XiProduct_20261116_v1
-- name    : RHCount_XiProduct_20261116_v1
-- status  : Definition
-- author  : @bueno_ricardo
-- created : 2026-11-16T18:22:11.731206+00:00
-- url     : https://prove2.me/theorems/e1df9ea4-34a4-4bfc-88ea-9e52065a06ef
-- title:
--   Analytic foundations for the xi product
-- statement:
--   A reusable analytic support module for the concrete Riemann xi function: gamma estimates, canonical products, partial fractions, and the paired-kernel integral. The helper results are included with complete proofs to provide the imported analytic foundation for subsequent counting theorems. No Riemann hypothesis assumption or new axiom is introduced.
-- source:
--   Desenvolvimento RH — Ricardo Marangoni Brandão Bueno. Analytic sources smmercuri/zeta commit 3dab6480a82f1bfc5de0a59550e279cf50490033; PrimeNumberTheoremAnd commit 0a2c672d7533437e50f7a72596cb0ecd17352fbe. Partition of the completely checked actual_count_submission.lean into closed source sections. Complete sources, Apache-2.0 licenses and exact source manifest accompany the reproducibility archive. No novelty claim.

import Mathlib
/- Reduced submission: unused declarations and documentation removed. Retained proofs are complete. Full original sources and licenses accompany the archive. -/
/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
/-
Copyright (c) 2024 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
/-
Copyright (c) 2022 Abby J. Goldberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abby J. Goldberg, Mario Carneiro, Heather Macbeth
-/
/-
Copyright (c) 2025 Maksym Radziwill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors : Maksym Radziwill
-/
/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
/-
Copyright (c) 2024 James Sundstrom. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James Sundstrom
-/
/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus, Matteo Cipollina
-/
/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robby Sneiderman
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
section CountPort0
section
noncomputable def weierstrassE1 (w : ℂ) : ℂ := (1 - w) * Complex.exp w
@[simp] lemma weierstrassE1_zero : weierstrassE1 0 = 1 := by simp [weierstrassE1]
@[continuity, fun_prop]
lemma continuous_weierstrassE1 : Continuous weierstrassE1 := by
  unfold weierstrassE1; fun_prop
@[fun_prop]
lemma differentiable_weierstrassE1 : Differentiable ℂ weierstrassE1 := by
  unfold weierstrassE1; fun_prop
lemma weierstrassE1_eq_exp_log {w : ℂ} (hw : w ≠ 1) :
    weierstrassE1 w = Complex.exp (Complex.log (1 - w) + w) := by
  rw [weierstrassE1, Complex.exp_add, Complex.exp_log (sub_ne_zero.mpr hw.symm), mul_comm]
@[simp] lemma weierstrassE1_eq_zero_iff {w : ℂ} : weierstrassE1 w = 0 ↔ w = 1 := by
  rw [weierstrassE1, mul_eq_zero, or_iff_left (Complex.exp_ne_zero w), sub_eq_zero, eq_comm]
lemma weierstrassE1_ne_zero {w : ℂ} (hw : w ≠ 1) : weierstrassE1 w ≠ 0 :=
  weierstrassE1_eq_zero_iff.not.mpr hw
lemma Complex.norm_log_one_sub_add_self_le {w : ℂ} (hw : ‖w‖ ≤ 1 / 2) :
    ‖Complex.log (1 - w) + w‖ ≤ ‖w‖ ^ 2 := by
  have h1 : ‖w‖ < 1 := lt_of_le_of_lt hw (by norm_num)
  have key := Complex.norm_log_one_add_sub_self_le (z := -w) (by rwa [norm_neg])
  rw [show (1 : ℂ) + -w = 1 - w by ring, sub_neg_eq_add, norm_neg] at key
  refine key.trans ?_
  have hpos : (0 : ℝ) < 1 - ‖w‖ := by linarith
  have h2 : (1 - ‖w‖)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ hpos two_pos]
    linarith
  calc ‖w‖ ^ 2 * (1 - ‖w‖)⁻¹ / 2 ≤ ‖w‖ ^ 2 * 2 / 2 := by gcongr
    _ = ‖w‖ ^ 2 := by ring
lemma log_norm_weierstrassE1 {w : ℂ} (hw : w ≠ 1) :
    Real.log ‖weierstrassE1 w‖ = Real.log ‖1 - w‖ + w.re := by
  have h1 : ‖(1 : ℂ) - w‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hw.symm)
  have h2 : ‖Complex.exp w‖ ≠ 0 := norm_ne_zero_iff.mpr (Complex.exp_ne_zero w)
  rw [weierstrassE1, norm_mul, Real.log_mul h1 h2, Complex.norm_exp, Real.log_exp]
lemma norm_weierstrassE1_sub_one_le {w : ℂ} (hw : ‖w‖ ≤ 1 / 2) :
    ‖weierstrassE1 w - 1‖ ≤ 2 * ‖w‖ ^ 2 := by
  have hne : w ≠ 1 := by rintro rfl; rw [norm_one] at hw; linarith
  rw [weierstrassE1_eq_exp_log hne]
  have hl : ‖Complex.log (1 - w) + w‖ ≤ ‖w‖ ^ 2 := Complex.norm_log_one_sub_add_self_le hw
  have hl1 : ‖Complex.log (1 - w) + w‖ ≤ 1 := hl.trans (by nlinarith [norm_nonneg w])
  exact (Complex.norm_exp_sub_one_le hl1).trans (by linarith)
lemma hasDerivAt_weierstrassE1 (w : ℂ) :
    HasDerivAt weierstrassE1 (-w * Complex.exp w) w := by
  have h1 : HasDerivAt (fun z : ℂ => 1 - z) (-1) w := by
    simpa using (hasDerivAt_id w).const_sub (1 : ℂ)
  exact (h1.mul (Complex.hasDerivAt_exp w)).congr_deriv (by ring)
section CanonicalProduct
variable {ι : Type*} (ρ : ι → ℂ)
noncomputable def riemannXiCanonicalProduct (s : ℂ) : ℂ :=
  ∏' i, weierstrassE1 (s / ρ i)
@[simp] lemma riemannXiCanonicalProduct_zero : riemannXiCanonicalProduct ρ 0 = 1 := by
  simp [riemannXiCanonicalProduct]
lemma eventually_norm_inv_le (hsum : Summable fun i => ‖(ρ i)⁻¹‖ ^ 2) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ i in Filter.cofinite, ‖(ρ i)⁻¹‖ ≤ c := by
  filter_upwards [hsum.tendsto_cofinite_zero.eventually (eventually_lt_nhds (pow_pos hc 2))]
    with i hi
  exact (lt_of_pow_lt_pow_left₀ 2 hc.le hi).le
private lemma norm_weierstrassE1_div_sub_one_le {s : ℂ} (i : ι)
    (h : ‖s‖ * ‖(ρ i)⁻¹‖ ≤ 1 / 2) :
    ‖weierstrassE1 (s / ρ i) - 1‖ ≤ 2 * ‖s‖ ^ 2 * ‖(ρ i)⁻¹‖ ^ 2 := by
  have hnorm : ‖s / ρ i‖ = ‖s‖ * ‖(ρ i)⁻¹‖ := by rw [div_eq_mul_inv, norm_mul]
  refine (norm_weierstrassE1_sub_one_le (by rw [hnorm]; exact h)).trans_eq ?_
  rw [hnorm, mul_pow]; ring
lemma summable_norm_weierstrassE1_sub_one (hsum : Summable fun i => ‖(ρ i)⁻¹‖ ^ 2) (s : ℂ) :
    Summable fun i => ‖weierstrassE1 (s / ρ i) - 1‖ := by
  have hu : Summable (fun i => 2 * ‖s‖ ^ 2 * ‖(ρ i)⁻¹‖ ^ 2) := hsum.mul_left _
  have htail : ∀ᶠ i in Filter.cofinite, ‖(ρ i)⁻¹‖ ≤ 1 / (2 * (‖s‖ + 1)) :=
    eventually_norm_inv_le ρ hsum (by positivity)
  refine Summable.of_norm_bounded_eventually hu ?_
  filter_upwards [htail] with i hi
  have h : ‖s‖ * ‖(ρ i)⁻¹‖ ≤ 1 / 2 := by
    calc ‖s‖ * ‖(ρ i)⁻¹‖ ≤ ‖s‖ * (1 / (2 * (‖s‖ + 1))) :=
          mul_le_mul_of_nonneg_left hi (norm_nonneg _)
      _ ≤ 1 / 2 := by rw [mul_one_div, div_le_iff₀ (by positivity)]; nlinarith [norm_nonneg s]
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  exact norm_weierstrassE1_div_sub_one_le ρ i h
lemma multipliable_weierstrassE1 (hsum : Summable fun i => ‖(ρ i)⁻¹‖ ^ 2) (s : ℂ) :
    Multipliable fun i => weierstrassE1 (s / ρ i) := by
  have heq : (fun i => weierstrassE1 (s / ρ i))
      = fun i => 1 + (weierstrassE1 (s / ρ i) - 1) := by funext i; ring
  rw [heq]
  exact multipliable_one_add_of_summable (summable_norm_weierstrassE1_sub_one ρ hsum s)
lemma hasProdLocallyUniformlyOn_riemannXiCanonicalProduct
    (hsum : Summable fun i => ‖(ρ i)⁻¹‖ ^ 2) :
    HasProdLocallyUniformlyOn (fun i s => weierstrassE1 (s / ρ i))
      (riemannXiCanonicalProduct ρ) Set.univ := by
  apply hasProdLocallyUniformlyOn_of_forall_compact isOpen_univ
  intro K _ hK
  obtain ⟨R₀, hR₀⟩ := hK.isBounded.subset_closedBall 0
  set R : ℝ := max R₀ 1
  have hR1 : (1 : ℝ) ≤ R := le_max_right _ _
  have hRpos : (0 : ℝ) < R := lt_of_lt_of_le one_pos hR1
  have hKR : K ⊆ Metric.closedBall 0 R :=
    hR₀.trans (Metric.closedBall_subset_closedBall (le_max_left _ _))
  have hu : Summable (fun i => 2 * R ^ 2 * ‖(ρ i)⁻¹‖ ^ 2) := hsum.mul_left _
  have hcts : ∀ i, ContinuousOn (fun s => weierstrassE1 (s / ρ i) - 1) K := fun i => by
    fun_prop
  have htail : ∀ᶠ i in Filter.cofinite, ‖(ρ i)⁻¹‖ ≤ 1 / (2 * R) :=
    eventually_norm_inv_le ρ hsum (by positivity)
  have hbd : ∀ᶠ i in Filter.cofinite,
      ∀ s ∈ K, ‖weierstrassE1 (s / ρ i) - 1‖ ≤ 2 * R ^ 2 * ‖(ρ i)⁻¹‖ ^ 2 := by
    filter_upwards [htail] with i hi s hs
    have hsR : ‖s‖ ≤ R := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hKR hs
    have h : ‖s‖ * ‖(ρ i)⁻¹‖ ≤ 1 / 2 :=
      (mul_le_mul hsR hi (norm_nonneg _) hRpos.le).trans_eq (by field_simp)
    refine (norm_weierstrassE1_div_sub_one_le ρ i h).trans ?_
    gcongr
  convert Summable.hasProdUniformlyOn_one_add hK hu hbd hcts using 2 with s s i <;>
    simp [riemannXiCanonicalProduct]
theorem differentiable_riemannXiCanonicalProduct
    (hsum : Summable fun i => ‖(ρ i)⁻¹‖ ^ 2) :
    Differentiable ℂ (riemannXiCanonicalProduct ρ) := by
  rw [← differentiableOn_univ]
  have h := hasProdLocallyUniformlyOn_riemannXiCanonicalProduct ρ hsum
  rw [hasProdLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn] at h
  refine h.differentiableOn (.of_forall fun t => ?_) isOpen_univ
  exact DifferentiableOn.fun_finsetProd fun i _ =>
    (differentiable_weierstrassE1.comp (differentiable_id.div_const (ρ i))).differentiableOn
private lemma div_ne_one_of_forall_ne {s : ℂ} (hs : ∀ i, s ≠ ρ i) (i : ι) : s / ρ i ≠ 1 := by
  rcases eq_or_ne (ρ i) 0 with hρ | hρ
  · rw [hρ, div_zero]; exact zero_ne_one
  · exact fun h => hs i ((div_eq_one_iff_eq hρ).mp h)
lemma riemannXiCanonicalProduct_ne_zero_of_forall_ne
    (hsum : Summable fun i => ‖(ρ i)⁻¹‖ ^ 2) {s : ℂ} (hs : ∀ i, s ≠ ρ i) :
    riemannXiCanonicalProduct ρ s ≠ 0 := by
  have hfac : ∀ i, weierstrassE1 (s / ρ i) ≠ 0 :=
    fun i => weierstrassE1_ne_zero (div_ne_one_of_forall_ne ρ hs i)
  have hnsum : Summable (fun i => ‖weierstrassE1 (s / ρ i) - 1‖) :=
    summable_norm_weierstrassE1_sub_one ρ hsum s
  have hsplit : ∀ i, (1 : ℂ) + (weierstrassE1 (s / ρ i) - 1) = weierstrassE1 (s / ρ i) :=
    fun i => by ring
  have hcongr : riemannXiCanonicalProduct ρ s = ∏' i, (1 + (weierstrassE1 (s / ρ i) - 1)) := by
    rw [riemannXiCanonicalProduct]; exact tprod_congr fun i => (hsplit i).symm
  rw [hcongr]
  refine tprod_one_add_ne_zero_of_summable (fun i => ?_) hnsum
  rw [hsplit i]; exact hfac i
lemma summable_log_norm_weierstrassE1 (hsum : Summable fun i => ‖(ρ i)⁻¹‖ ^ 2) (s : ℂ) :
    Summable fun i => Real.log ‖weierstrassE1 (s / ρ i)‖ := by
  refine (summable_norm_weierstrassE1_sub_one ρ hsum s).summable_log_norm_one_add.congr fun i => ?_
  rw [show (1 : ℂ) + (weierstrassE1 (s / ρ i) - 1) = weierstrassE1 (s / ρ i) from by ring]
lemma log_norm_riemannXiCanonicalProduct (hsum : Summable fun i => ‖(ρ i)⁻¹‖ ^ 2) {s : ℂ}
    (hs : ∀ i, s ≠ ρ i) :
    Real.log ‖riemannXiCanonicalProduct ρ s‖ = ∑' i, Real.log ‖weierstrassE1 (s / ρ i)‖ := by
  have hpos : ∀ i, 0 < ‖weierstrassE1 (s / ρ i)‖ :=
    fun i => norm_pos_iff.mpr (weierstrassE1_ne_zero (div_ne_one_of_forall_ne ρ hs i))
  rw [riemannXiCanonicalProduct, (multipliable_weierstrassE1 ρ hsum s).norm_tprod,
    ← Real.rexp_tsum_eq_tprod hpos (summable_log_norm_weierstrassE1 ρ hsum s), Real.log_exp]
lemma log_norm_riemannXiCanonicalProduct_eq_tsum
    (hsum : Summable fun i => ‖(ρ i)⁻¹‖ ^ 2) {s : ℂ} (hs : ∀ i, s ≠ ρ i) :
    Real.log ‖riemannXiCanonicalProduct ρ s‖
      = ∑' i, (Real.log ‖1 - s / ρ i‖ + (s / ρ i).re) := by
  rw [log_norm_riemannXiCanonicalProduct ρ hsum hs]
  exact tsum_congr fun i => log_norm_weierstrassE1 (div_ne_one_of_forall_ne ρ hs i)
theorem analyticOrderNatAt_riemannXiCanonicalProduct
    (hsum : Summable fun i => ‖(ρ i)⁻¹‖ ^ 2) (hρ : ∀ i, ρ i ≠ 0) (a : ℂ) :
    analyticOrderNatAt (riemannXiCanonicalProduct ρ) a = {i | ρ i = a}.ncard := by
  classical
  have hSfin : {i | ρ i = a}.Finite := by
    rcases eq_or_ne a 0 with rfl | ha
    · exact Set.Finite.subset Set.finite_empty fun i hi => absurd hi (hρ i)
    · have hpos : (0 : ℝ) < ‖a⁻¹‖ := norm_pos_iff.mpr (inv_ne_zero ha)
      have hev : ∀ᶠ i in Filter.cofinite, ‖(ρ i)⁻¹‖ ^ 2 < ‖a⁻¹‖ ^ 2 :=
        hsum.tendsto_cofinite_zero.eventually (eventually_lt_nhds (pow_pos hpos 2))
      refine (Filter.eventually_cofinite.mp hev).subset ?_
      intro i hi
      simp only [Set.mem_ofPred_eq] at hi ⊢
      rw [hi]
      exact lt_irrefl _
  set S : Finset ι := hSfin.toFinset with hS
  have hSmem : ∀ i, i ∈ S ↔ ρ i = a := fun i => by
    simp only [hS, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
  set ρ' : ↥((S : Set ι)ᶜ) → ℂ := fun j => ρ ↑j
  have hsum' : Summable fun j : ↥((S : Set ι)ᶜ) => ‖(ρ' j)⁻¹‖ ^ 2 := hsum.subtype _
  have hTanalytic : AnalyticAt ℂ (riemannXiCanonicalProduct ρ') a :=
    (differentiable_riemannXiCanonicalProduct ρ' hsum').analyticAt a
  have hTne : riemannXiCanonicalProduct ρ' a ≠ 0 := by
    refine riemannXiCanonicalProduct_ne_zero_of_forall_ne ρ' hsum' fun j => ?_
    have hj : (↑j : ι) ∉ S := by
      have h := j.2; rwa [Set.mem_compl_iff, Finset.mem_coe] at h
    exact fun h => hj ((hSmem ↑j).mpr h.symm)
  have hg : AnalyticAt ℂ (fun s => weierstrassE1 (s / a)) a :=
    (by fun_prop : Differentiable ℂ fun s => weierstrassE1 (s / a)).analyticAt a
  have hsplit : riemannXiCanonicalProduct ρ
      = (fun s => weierstrassE1 (s / a)) ^ S.card * riemannXiCanonicalProduct ρ' := by
    funext s
    have hmulF : Multipliable
        ((fun i => weierstrassE1 (s / ρ i)) ∘ ((↑) : ↥(S : Set ι) → ι)) :=
      (S.finite_toSet).multipliable (fun i => weierstrassE1 (s / ρ i))
    have hmulT : Multipliable
        ((fun i => weierstrassE1 (s / ρ i)) ∘ ((↑) : ↥((S : Set ι)ᶜ) → ι)) :=
      multipliable_weierstrassE1 ρ' hsum' s
    have key := Multipliable.tprod_mul_tprod_compl hmulF hmulT
    have hhead : ∏' x : ↥(S : Set ι), weierstrassE1 (s / ρ ↑x)
        = weierstrassE1 (s / a) ^ S.card := by
      have h1 : ∏' x : ↥(S : Set ι), weierstrassE1 (s / ρ ↑x)
          = ∏ i ∈ S, weierstrassE1 (s / ρ i) :=
        Finset.tprod_subtype S (fun i => weierstrassE1 (s / ρ i))
      rw [h1, show (∏ i ∈ S, weierstrassE1 (s / ρ i)) = ∏ _i ∈ S, weierstrassE1 (s / a) from
        Finset.prod_congr rfl fun i hi => by rw [(hSmem i).mp hi], Finset.prod_const]
    simp only [Pi.mul_apply, Pi.pow_apply]
    rw [show riemannXiCanonicalProduct ρ s = ∏' i, weierstrassE1 (s / ρ i) from rfl, ← key, hhead,
      show riemannXiCanonicalProduct ρ' s = ∏' x : ↥((S : Set ι)ᶜ), weierstrassE1 (s / ρ ↑x)
        from rfl]
  have horderg : a ≠ 0 → analyticOrderAt (fun s => weierstrassE1 (s / a)) a = 1 := fun ha => by
    refine hg.analyticOrderAt_eq_one_of_zero_deriv_ne_zero ?_ ?_
    · simp [div_self ha]
    · have hu : HasDerivAt (fun s : ℂ => s / a) (1 / a) a := (hasDerivAt_id a).div_const a
      have hd := (hasDerivAt_weierstrassE1 _).comp a hu
      rw [show (fun s => weierstrassE1 (s / a)) = weierstrassE1 ∘ (fun s : ℂ => s / a) from rfl,
        hd.deriv]
      exact mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr (div_ne_zero ha ha))
        (Complex.exp_ne_zero _)) (one_div_ne_zero ha)
  have hhead_order : analyticOrderAt ((fun s => weierstrassE1 (s / a)) ^ S.card) a
      = (S.card : ℕ∞) := by
    rw [analyticOrderAt_pow hg]
    rcases Nat.eq_zero_or_pos S.card with h0 | hpos
    · rw [h0]; simp
    · have ha : a ≠ 0 := by
        obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos
        rw [← (hSmem i).mp hi]; exact hρ i
      rw [horderg ha]; simp
  have hTorder : analyticOrderAt (riemannXiCanonicalProduct ρ') a = 0 :=
    hTanalytic.analyticOrderAt_eq_zero.mpr hTne
  have hmain : analyticOrderAt (riemannXiCanonicalProduct ρ) a = (S.card : ℕ∞) := by
    rw [hsplit, analyticOrderAt_mul (hg.pow S.card) hTanalytic, hhead_order, hTorder, add_zero]
  rw [analyticOrderNatAt, hmain, ENat.toNat_natCast, Set.ncard_eq_toFinset_card _ hSfin, hS]
end CanonicalProduct
end
end CountPort0
section CountPort1
section
open scoped Real
namespace Real
theorem arctan_le_self {x : ℝ} (hx : 0 ≤ x) : arctan x ≤ x := by
  rcases hx.eq_or_lt with h | h
  · simp [← h]
  · have hlt := lt_tan (arctan_pos.2 h) (arctan_lt_pi_div_two x)
    rw [tan_arctan] at hlt
    exact hlt.le
end Real
end
end CountPort1
section CountPort2
section
namespace Complex
theorem ne_neg_natCast_of_re_pos {z : ℂ} (hz : 0 < z.re) (m : ℕ) : z ≠ -(m : ℂ) := by
  rintro rfl; exact absurd hz (by simp)
theorem differentiableAt_Gamma_of_re_pos {z : ℂ} (hz : 0 < z.re) :
    DifferentiableAt ℂ Complex.Gamma z :=
  Complex.differentiableAt_Gamma z (ne_neg_natCast_of_re_pos hz)
theorem isPreconnected_re_pos : IsPreconnected {z : ℂ | 0 < z.re} :=
  (convex_halfSpace_re_gt 0).isPreconnected
theorem differentiableOn_Gamma_re_pos : DifferentiableOn ℂ Complex.Gamma {z : ℂ | 0 < z.re} :=
  fun _ hz ↦ (differentiableAt_Gamma_of_re_pos hz).differentiableWithinAt
theorem analyticOnNhd_Gamma_re_pos : AnalyticOnNhd ℂ Complex.Gamma {z : ℂ | 0 < z.re} :=
  differentiableOn_Gamma_re_pos.analyticOnNhd (isOpen_re_gt 0)
theorem differentiableOn_digamma_re_pos :
    DifferentiableOn ℂ Complex.digamma {z : ℂ | 0 < z.re} := by
  rw [Complex.digamma_def]
  exact (differentiableOn_Gamma_re_pos.deriv (isOpen_re_gt 0)).div differentiableOn_Gamma_re_pos
    fun _ hz ↦ Complex.Gamma_ne_zero_of_re_pos hz
theorem differentiableAt_digamma {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ Complex.digamma s :=
  (differentiableOn_digamma_re_pos.analyticOnNhd (isOpen_re_gt 0) s hs).differentiableAt
end Complex
end
end CountPort2
section CountPort3
section
open MeasureTheory
open scoped Nat
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
private theorem integral_interval_eq {f f' : ℝ → E} {n : ℝ}
    (hf : ∀ x ∈ Set.uIcc n (n + 1), HasDerivAt f (f' x) x)
    (hf' : IntervalIntegrable f' volume n (n + 1)) :
    ∫ x in n..(n + 1), f x
      = (2⁻¹ : ℝ) • (f n + f (n + 1)) - ∫ x in n..(n + 1), bernoulliFun 1 (x - n) • f' x := by
  have hu : ∀ x ∈ Set.uIcc n (n + 1),
      HasDerivAt (fun y ↦ bernoulliFun 1 (y - n)) ((fun _ ↦ (1 : ℝ)) x) x := by
    intro x _
    have hcomp := (hasDerivAt_bernoulliFun 1 (x - n)).comp x ((hasDerivAt_id x).sub_const n)
    simp only [Nat.cast_one, Nat.sub_self, bernoulliFun_zero, mul_one] at hcomp
    exact hcomp
  have key := intervalIntegral.integral_smul_deriv_eq_deriv_smul hu hf intervalIntegrable_const hf'
  simp only [add_sub_cancel_left, sub_self, bernoulliFun_one, one_smul] at key
  simp only [bernoulliFun_one]
  rw [key]
  module
private theorem integral_bernoulliFun_smul_eq {g g' : ℝ → E} {n : ℝ} {q : ℕ} (hq : q ≠ 0)
    (hg : ∀ x ∈ Set.uIcc n (n + 1), HasDerivAt g (g' x) x)
    (hg' : IntervalIntegrable g' volume n (n + 1)) :
    ∫ x in n..(n + 1), bernoulliFun q (x - n) • g x
      = ((bernoulli (q + 1) : ℝ) / ((q : ℝ) + 1)) • (g (n + 1) - g n)
        - (1 / ((q : ℝ) + 1)) • ∫ x in n..(n + 1), bernoulliFun (q + 1) (x - n) • g' x := by
  have hq1 : ((q : ℝ) + 1) ≠ 0 := by positivity
  have hu : ∀ x ∈ Set.uIcc n (n + 1),
      HasDerivAt (fun y ↦ bernoulliFun (q + 1) (y - n) / ((q : ℝ) + 1))
        (bernoulliFun q (x - n)) x := by
    intro x _
    have hcomp := ((hasDerivAt_bernoulliFun (q + 1) (x - n)).comp x
      ((hasDerivAt_id x).sub_const n)).div_const ((q : ℝ) + 1)
    have hval : ((q + 1 : ℕ) : ℝ) * bernoulliFun ((q + 1) - 1) (x - n) * 1 / ((q : ℝ) + 1)
        = bernoulliFun q (x - n) := by
      rw [show (q + 1) - 1 = q by lia, mul_one]; push_cast
      exact mul_div_cancel_left₀ _ hq1
    rwa [hval] at hcomp
  have hu' : IntervalIntegrable (fun x ↦ bernoulliFun q (x - n)) volume n (n + 1) :=
    (by fun_prop : Continuous fun x ↦ bernoulliFun q (x - n)).intervalIntegrable _ _
  have key := intervalIntegral.integral_smul_deriv_eq_deriv_smul hu hg hu' hg'
  simp only [add_sub_cancel_left, sub_self, bernoulliFun_eval_zero,
    bernoulliFun_endpoints_eq_of_ne_one (show q + 1 ≠ 1 by lia)] at key
  have hfac : (∫ x in n..(n + 1), (bernoulliFun (q + 1) (x - n) / ((q : ℝ) + 1)) • g' x)
      = ((q : ℝ) + 1)⁻¹ • ∫ x in n..(n + 1), bernoulliFun (q + 1) (x - n) • g' x := by
    simp_rw [div_eq_inv_mul, mul_smul, intervalIntegral.integral_smul]
  rw [hfac] at key
  rw [one_div, smul_sub, key]
  module
private theorem integral_interval_eq_tower {n : ℝ} (F : ℕ → ℝ → E) {p : ℕ} (hp : 0 < p)
    (hderiv : ∀ q, q < p → ∀ x ∈ Set.uIcc n (n + 1), HasDerivAt (F q) (F (q + 1) x) x)
    (hF_int : ∀ q, 0 < q → q ≤ p → IntervalIntegrable (F q) volume n (n + 1)) :
    ∫ x in n..(n + 1), F 0 x
      = (2⁻¹ : ℝ) • (F 0 n + F 0 (n + 1))
        + ∑ q ∈ Finset.Ico 1 p,
            ((-1 : ℝ) ^ q * (bernoulli (q + 1) : ℝ) / ((q + 1)! : ℝ)) • (F q (n + 1) - F q n)
        + ((-1 : ℝ) ^ p / (p ! : ℝ)) • ∫ x in n..(n + 1), bernoulliFun p (x - n) • F p x := by
  revert hderiv hF_int
  induction p, hp using Nat.le_induction with
  | base =>
    intro hderiv hF_int
    have hbase := integral_interval_eq (f := F 0) (f' := F 1)
      (hderiv 0 one_pos) (hF_int 1 one_pos le_rfl)
    simp only [Finset.Ico_self, Finset.sum_empty, add_zero, pow_one, Nat.factorial_one,
      Nat.cast_one, div_one]
    rw [hbase]
    module
  | succ p hp ih =>
    intro hderiv hF_int
    have IH := ih (fun q hq ↦ hderiv q (Nat.lt_succ_of_lt hq))
      (fun q hq0 hqp ↦ hF_int q hq0 (hqp.trans (Nat.le_succ p)))
    have hrec := integral_bernoulliFun_smul_eq (g := F p) (g' := F (p + 1)) (n := n) (q := p)
      (Nat.one_le_iff_ne_zero.mp hp) (hderiv p (Nat.lt_succ_self p))
      (hF_int (p + 1) (Nat.succ_pos p) le_rfl)
    rw [Finset.sum_Ico_succ_top (by lia : 1 ≤ p), IH, hrec, pow_succ, Nat.factorial_succ]
    have hp0 : (p ! : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos p).ne'
    have hp1 : ((p : ℝ) + 1) ≠ 0 := by positivity
    push_cast
    match_scalars <;> field_simp
private theorem uIcc_add_natCast_subset_uIcc (a : ℝ) {N k : ℕ} (hk : k < N) :
    Set.uIcc (a + (k : ℝ)) (a + (k : ℝ) + 1) ⊆ Set.uIcc a (a + N) := by
  have hk1 : (k : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast hk
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  apply Set.uIcc_subset_uIcc <;> rw [Set.mem_uIcc] <;> left <;> constructor <;> linarith
private theorem integral_eq_tower_sum {a : ℝ} (F : ℕ → ℝ → E) {N p : ℕ} (hp : 0 < p)
    (hderiv : ∀ q, q < p → ∀ x ∈ Set.uIcc a (a + N), HasDerivAt (F q) (F (q + 1) x) x)
    (hF_int : ∀ q, 0 < q → q ≤ p → IntervalIntegrable (F q) volume a (a + N)) :
    ∫ x in a..(a + N), F 0 x
      = (∑ n ∈ Finset.range N, (2⁻¹ : ℝ) • (F 0 (a + n) + F 0 (a + n + 1)))
        + (∑ q ∈ Finset.Ico 1 p,
            ((-1 : ℝ) ^ q * (bernoulli (q + 1) : ℝ) / ((q + 1)! : ℝ)) • (F q (a + N) - F q a))
        + ((-1 : ℝ) ^ p / (p ! : ℝ)) • ∑ n ∈ Finset.range N,
            ∫ x in (a + n)..(a + n + 1), bernoulliFun p (x - (a + n)) • F p x := by
  have hsub : ∀ k, k < N → Set.uIcc (a + (k : ℝ)) (a + (k : ℝ) + 1) ⊆ Set.uIcc a (a + N) :=
    fun _ hk ↦ uIcc_add_natCast_subset_uIcc a hk
  have hcont0 : ContinuousOn (F 0) (Set.uIcc a (a + N)) := fun x hx ↦
    (hderiv 0 hp x hx).continuousAt.continuousWithinAt
  have hconcat :
      (∑ k ∈ Finset.range N, ∫ x in (a + (k : ℝ))..(a + (k : ℝ) + 1), F 0 x)
        = ∫ x in a..(a + N), F 0 x := by
    have h := intervalIntegral.sum_integral_adjacent_intervals (μ := volume) (f := F 0)
      (a := fun k ↦ a + (k : ℝ)) (n := N)
      (fun k hk ↦ by
        have := (hcont0.mono (hsub k hk)).intervalIntegrable (μ := volume)
        simpa [Nat.cast_add, Nat.cast_one, add_assoc] using this)
    simpa [add_assoc] using h
  have hstep : ∀ k ∈ Finset.range N,
      (∫ x in (a + (k : ℝ))..(a + (k : ℝ) + 1), F 0 x)
        = (2⁻¹ : ℝ) • (F 0 (a + (k : ℝ)) + F 0 (a + (k : ℝ) + 1))
          + (∑ q ∈ Finset.Ico 1 p,
              ((-1 : ℝ) ^ q * (bernoulli (q + 1) : ℝ) / ((q + 1)! : ℝ))
                • (F q (a + (k : ℝ) + 1) - F q (a + (k : ℝ))))
          + ((-1 : ℝ) ^ p / (p ! : ℝ))
              • ∫ x in (a + (k : ℝ))..(a + (k : ℝ) + 1),
                  bernoulliFun p (x - (a + (k : ℝ))) • F p x := by
    intro k hk
    rw [Finset.mem_range] at hk
    exact integral_interval_eq_tower (n := a + (k : ℝ)) F hp
      (fun q hq x hx ↦ hderiv q hq x (hsub k hk hx))
      (fun q hq0 hqp ↦ (hF_int q hq0 hqp).mono_set (hsub k hk))
  have hbern :
      (∑ k ∈ Finset.range N, ∑ q ∈ Finset.Ico 1 p,
          ((-1 : ℝ) ^ q * (bernoulli (q + 1) : ℝ) / ((q + 1)! : ℝ))
            • (F q (a + (k : ℝ) + 1) - F q (a + (k : ℝ))))
        = ∑ q ∈ Finset.Ico 1 p,
            ((-1 : ℝ) ^ q * (bernoulli (q + 1) : ℝ) / ((q + 1)! : ℝ)) • (F q (a + N) - F q a) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun q _ ↦ ?_)
    rw [← Finset.smul_sum]
    congr 1
    have h := Finset.sum_range_sub (fun k ↦ F q (a + (k : ℝ))) N
    simpa [Nat.cast_add, Nat.cast_one, add_assoc] using h
  rw [← hconcat, Finset.sum_congr rfl hstep, Finset.sum_add_distrib, Finset.sum_add_distrib,
    hbern, ← Finset.smul_sum, ← Finset.smul_sum]
omit [CompleteSpace E] in
private theorem sum_trapezoid_eq (a : ℝ) (g : ℝ → E) (N : ℕ) :
    ∑ n ∈ Finset.range N, (2⁻¹ : ℝ) • (g (a + (n : ℝ)) + g (a + (n : ℝ) + 1))
      = (∑ n ∈ Finset.range (N + 1), g (a + (n : ℝ))) - (2⁻¹ : ℝ) • (g a + g (a + (N : ℝ))) := by
  induction N with
  | zero => simp; module
  | succ M ih =>
    rw [Finset.sum_range_succ _ M, ih, Finset.sum_range_succ _ (M + 1)]
    push_cast
    simp only [← add_assoc]
    module
private theorem sum_eq_tower_integral {a : ℝ} (F : ℕ → ℝ → E) {N p : ℕ} (hp : 0 < p)
    (hderiv : ∀ q, q < p → ∀ x ∈ Set.uIcc a (a + N), HasDerivAt (F q) (F (q + 1) x) x)
    (hF_int : ∀ q, 0 < q → q ≤ p → IntervalIntegrable (F q) volume a (a + N)) :
    ∑ n ∈ Finset.range (N + 1), F 0 (a + n)
      = (∫ x in a..(a + N), F 0 x) + (2⁻¹ : ℝ) • (F 0 a + F 0 (a + N))
        - (∑ q ∈ Finset.Ico 1 p,
            ((-1 : ℝ) ^ q * (bernoulli (q + 1) : ℝ) / ((q + 1)! : ℝ)) • (F q (a + N) - F q a))
        - ((-1 : ℝ) ^ p / (p ! : ℝ)) • ∑ n ∈ Finset.range N,
            ∫ x in (a + n)..(a + n + 1), bernoulliFun p (x - (a + n)) • F p x := by
  rw [integral_eq_tower_sum F hp hderiv hF_int, sum_trapezoid_eq a (F 0) N]
  abel
omit [CompleteSpace E] in
private theorem sum_Ico_bernoulli_collapse (c : ℕ → E) (p : ℕ) :
    ∑ q ∈ Finset.Ico 1 p,
        ((-1 : ℝ) ^ q * (bernoulli (q + 1) : ℝ) / ((q + 1)! : ℝ)) • c q
      = -∑ k ∈ Finset.Ico 1 (p / 2 + 1),
          ((bernoulli (2 * k) : ℝ) / ((2 * k)! : ℝ)) • c (2 * k - 1) := by
  have hne : ∀ q ∈ Finset.Ico 1 p,
      ((-1 : ℝ) ^ q * (bernoulli (q + 1) : ℝ) / ((q + 1)! : ℝ)) • c q ≠ 0 → Odd q := by
    intro q hq hne0
    rw [Finset.mem_Ico] at hq
    by_contra hodd
    rw [Nat.not_odd_iff_even] at hodd
    apply hne0
    simp [bernoulli_eq_zero_of_odd hodd.add_one (by lia)]
  rw [← Finset.sum_filter_of_ne hne, ← Finset.sum_neg_distrib]
  refine Finset.sum_bij' (fun q _ ↦ (q + 1) / 2) (fun k _ ↦ 2 * k - 1) ?_ ?_ ?_ ?_ ?_
  · rintro q hq
    simp only [Finset.mem_filter, Finset.mem_Ico] at hq ⊢
    obtain ⟨⟨_, hqp⟩, m, rfl⟩ := hq
    lia
  · rintro k hk
    simp only [Finset.mem_filter, Finset.mem_Ico] at hk ⊢
    exact ⟨⟨by lia, by lia⟩, k - 1, by lia⟩
  · rintro q hq
    simp only [Finset.mem_filter, Finset.mem_Ico] at hq
    obtain ⟨_, m, rfl⟩ := hq
    change 2 * ((2 * m + 1 + 1) / 2) - 1 = 2 * m + 1
    lia
  · rintro k hk
    simp only [Finset.mem_Ico] at hk
    show (2 * k - 1 + 1) / 2 = k
    lia
  · rintro q hq
    simp only [Finset.mem_filter, Finset.mem_Ico] at hq
    obtain ⟨_, m, rfl⟩ := hq
    simp only [show (2 * m + 1 + 1) / 2 = m + 1 by lia]
    rw [show 2 * (m + 1) - 1 = 2 * m + 1 by lia, show 2 * (m + 1) = 2 * m + 1 + 1 by lia,
      Odd.neg_one_pow ⟨m, rfl⟩]
    module
private theorem sum_eq_tower_integral_even {a : ℝ} (F : ℕ → ℝ → E) {N p : ℕ} (hp : 0 < p)
    (hderiv : ∀ q, q < p → ∀ x ∈ Set.uIcc a (a + N), HasDerivAt (F q) (F (q + 1) x) x)
    (hF_int : ∀ q, 0 < q → q ≤ p → IntervalIntegrable (F q) volume a (a + N)) :
    ∑ n ∈ Finset.range (N + 1), F 0 (a + n)
      = (∫ x in a..(a + N), F 0 x) + (2⁻¹ : ℝ) • (F 0 a + F 0 (a + N))
        + (∑ k ∈ Finset.Ico 1 (p / 2 + 1),
            ((bernoulli (2 * k) : ℝ) / ((2 * k)! : ℝ))
              • (F (2 * k - 1) (a + N) - F (2 * k - 1) a))
        - ((-1 : ℝ) ^ p / (p ! : ℝ)) • ∑ n ∈ Finset.range N,
            ∫ x in (a + n)..(a + n + 1), bernoulliFun p (x - (a + n)) • F p x := by
  have hcol := sum_Ico_bernoulli_collapse (fun q ↦ F q (a + N) - F q a) p
  beta_reduce at hcol
  rw [sum_eq_tower_integral F hp hderiv hF_int, hcol]
  abel
omit [CompleteSpace E] in
private theorem sum_integral_bernoulliFun_eq (a : ℤ) (p N : ℕ) (G : ℝ → E)
    (hG : IntervalIntegrable G volume (a : ℝ) ((a : ℝ) + N)) :
    ∑ n ∈ Finset.range N,
        ∫ x in ((a : ℝ) + n)..((a : ℝ) + n + 1), bernoulliFun p (x - ((a : ℝ) + n)) • G x
      = ∫ x in (a : ℝ)..((a : ℝ) + N), bernoulliFun p (Int.fract x) • G x := by
  have hker : ∀ k, k < N → ∀ᵐ x ∂(volume : Measure ℝ),
      x ∈ Set.uIoc ((a : ℝ) + k) ((a : ℝ) + k + 1) →
        bernoulliFun p (x - ((a : ℝ) + k)) • G x = bernoulliFun p (Int.fract x) • G x := by
    intro k hk
    have hsing : {x : ℝ | x = (a : ℝ) + (k : ℝ) + 1}ᶜ ∈ (ae (volume : Measure ℝ)) := by
      rw [compl_mem_ae_iff, Set.ofPred_eq_eq_singleton]; exact Real.volume_singleton
    filter_upwards [hsing] with x hx hmem
    have hxne : x ≠ (a : ℝ) + (k : ℝ) + 1 := by simpa using hx
    rw [Set.uIoc_of_le (by linarith), Set.mem_Ioc] at hmem
    have hlt : x < (a : ℝ) + (k : ℝ) + 1 := lt_of_le_of_ne hmem.2 hxne
    have hfr : Int.fract x = x - ((a : ℝ) + (k : ℝ)) := by
      rw [← Int.fract_sub_intCast x (a + k), Int.fract_eq_self.mpr
        ⟨by push_cast; linarith [hmem.1], by push_cast; linarith⟩]
      push_cast; ring
    rw [hfr]
  have hint : ∀ k, k < N →
      IntervalIntegrable (fun x ↦ bernoulliFun p (Int.fract x) • G x) volume
        ((a : ℝ) + k) ((a : ℝ) + k + 1) := by
    intro k hk
    have hHk : IntervalIntegrable (fun x ↦ bernoulliFun p (x - ((a : ℝ) + k)) • G x) volume
        ((a : ℝ) + k) ((a : ℝ) + k + 1) :=
      (hG.mono_set (uIcc_add_natCast_subset_uIcc (a : ℝ) hk)).continuousOn_smul (by fun_prop)
    refine hHk.congr_ae ?_
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_uIoc]
    exact hker k hk
  rw [Finset.sum_congr rfl (fun k hk ↦
    intervalIntegral.integral_congr_ae (hker k (Finset.mem_range.mp hk)))]
  have h := intervalIntegral.sum_integral_adjacent_intervals (μ := volume)
    (f := fun x ↦ bernoulliFun p (Int.fract x) • G x) (a := fun k ↦ (a : ℝ) + (k : ℝ)) (n := N)
    (fun k hk ↦ by simpa [Nat.cast_add, Nat.cast_one, add_assoc] using hint k hk)
  simpa [Nat.cast_add, Nat.cast_one, add_assoc] using h
noncomputable def eulerMaclaurinRemainder (p : ℕ) (f : ℝ → E) (a b : ℝ) : E :=
  ((-1 : ℝ) ^ (p + 1) / (p ! : ℝ))
    • ∫ x in a..b, bernoulliFun p (Int.fract x) • iteratedDeriv p f x
theorem eulerMaclaurin_sum_eq {f : ℝ → E} (a : ℤ) {N p : ℕ} (hp : 0 < p)
    (hderiv : ∀ q, q < p → ∀ x ∈ Set.uIcc (a : ℝ) ((a : ℝ) + N),
      HasDerivAt (iteratedDeriv q f) (iteratedDeriv (q + 1) f x) x)
    (hf_int : ∀ q, 0 < q → q ≤ p →
      IntervalIntegrable (iteratedDeriv q f) volume (a : ℝ) ((a : ℝ) + N)) :
    ∑ n ∈ Finset.range (N + 1), f ((a : ℝ) + n)
      = (∫ x in (a : ℝ)..((a : ℝ) + N), f x) + (2⁻¹ : ℝ) • (f (a : ℝ) + f ((a : ℝ) + N))
        + (∑ k ∈ Finset.Ico 1 (p / 2 + 1),
            ((bernoulli (2 * k) : ℝ) / ((2 * k)! : ℝ))
              • (iteratedDeriv (2 * k - 1) f ((a : ℝ) + N) - iteratedDeriv (2 * k - 1) f (a : ℝ)))
        + eulerMaclaurinRemainder p f (a : ℝ) ((a : ℝ) + N) := by
  have hmain := sum_eq_tower_integral_even (a := (a : ℝ))
    (fun q ↦ iteratedDeriv q f) hp hderiv hf_int
  have hrem : eulerMaclaurinRemainder p f (a : ℝ) ((a : ℝ) + N)
      = -(((-1 : ℝ) ^ p / (p ! : ℝ)) • ∑ n ∈ Finset.range N,
          ∫ x in ((a : ℝ) + n)..((a : ℝ) + n + 1),
            bernoulliFun p (x - ((a : ℝ) + n)) • iteratedDeriv p f x) := by
    rw [eulerMaclaurinRemainder, ← sum_integral_bernoulliFun_eq a p N
      (iteratedDeriv p f) (hf_int p hp le_rfl), pow_succ, ← neg_smul]
    congr 1
    ring
  simp only [iteratedDeriv_zero] at hmain ⊢
  rw [hmain, hrem]
  abel
end
end CountPort3
section CountPort4
section
open MeasureTheory
open scoped Topology Nat
namespace Complex
theorem eulerMaclaurinRemainder_eq (p : ℕ) (f : ℝ → ℂ) (a b : ℝ) :
    eulerMaclaurinRemainder p f a b
      = (-1 : ℂ) ^ (p + 1) / (p ! : ℂ)
        * ∫ x in a..b, (bernoulliFun p (Int.fract x) : ℂ) * iteratedDeriv p f x := by
  rw [_root_.eulerMaclaurinRemainder]
  simp only [real_smul, ofReal_div, ofReal_pow, ofReal_neg, ofReal_one, ofReal_natCast]
theorem measurable_bernoulliFun_fract (p : ℕ) :
    Measurable (fun x : ℝ ↦ (bernoulliFun p (Int.fract x) : ℂ)) := by fun_prop
theorem exists_norm_bernoulliFun_fract_le (p : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, ‖(bernoulliFun p (Int.fract x) : ℂ)‖ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    (contDiff_bernoulliFun p).continuous.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun x ↦ ?_⟩
  rw [Complex.norm_real]
  exact (hC _ ⟨Int.fract_nonneg x, (Int.fract_lt_one x).le⟩).trans (le_max_left _ _)
theorem aestronglyMeasurable_ofReal_cpow_Ioi {c : ℝ} (hc : 0 ≤ c) (w : ℂ) :
    AEStronglyMeasurable (fun x : ℝ ↦ (x : ℂ) ^ w) (volume.restrict (Set.Ioi c)) := by
  refine ContinuousOn.aestronglyMeasurable (fun x hx ↦ ?_) measurableSet_Ioi
  exact (Complex.continuousAt_ofReal_cpow_const x w
    (Or.inr (lt_of_le_of_lt hc (Set.mem_Ioi.mp hx)).ne')).continuousWithinAt
theorem integrableOn_Ioi_bernoulliFun_fract_mul_of_norm_le (p : ℕ) {c : ℝ} {K : ℝ → ℂ}
    {h : ℝ → ℝ} (hh : IntegrableOn h (Set.Ioi c))
    (hK : AEStronglyMeasurable K (volume.restrict (Set.Ioi c)))
    (hbound : ∀ x ∈ Set.Ioi c, ‖K x‖ ≤ h x) :
    IntegrableOn (fun x : ℝ ↦ (bernoulliFun p (Int.fract x) : ℂ) * K x) (Set.Ioi c) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_bernoulliFun_fract_le p
  refine Integrable.mono' (g := fun x ↦ C * h x) (hh.const_mul C)
    ((measurable_bernoulliFun_fract p).aestronglyMeasurable.mul hK) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  rw [norm_mul]
  exact mul_le_mul (hC x) (hbound x hx) (norm_nonneg _) hC0
theorem sum_eq {f : ℝ → ℂ} (a : ℤ) {N p : ℕ} (hp : 0 < p)
    (hderiv : ∀ q, q < p → ∀ x ∈ Set.uIcc (a : ℝ) ((a : ℝ) + N),
      HasDerivAt (iteratedDeriv q f) (iteratedDeriv (q + 1) f x) x)
    (hf_int : ∀ q, 0 < q → q ≤ p →
      IntervalIntegrable (iteratedDeriv q f) volume (a : ℝ) ((a : ℝ) + N)) :
    ∑ n ∈ Finset.range (N + 1), f ((a : ℝ) + n)
      = (∫ x in (a : ℝ)..((a : ℝ) + N), f x) + (f (a : ℝ) + f ((a : ℝ) + N)) / 2
        + (∑ k ∈ Finset.Ico 1 (p / 2 + 1),
            ((bernoulli (2 * k) : ℝ) / ((2 * k)! : ℝ) : ℂ)
              * (iteratedDeriv (2 * k - 1) f ((a : ℝ) + N) - iteratedDeriv (2 * k - 1) f (a : ℝ)))
        + eulerMaclaurinRemainder p f (a : ℝ) ((a : ℝ) + N) := by
  rw [eulerMaclaurin_sum_eq a hp hderiv hf_int]
  simp only [real_smul, ofReal_div, ofReal_inv, ofReal_natCast, ofReal_ofNat]
  ring
private theorem hasDerivAt_cpow_closed_form (s : ℂ) (j : ℕ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt
      (fun y : ℝ ↦ (-1 : ℂ) ^ j * (ascPochhammer ℂ j).eval s * (y : ℂ) ^ (-s - (j : ℂ)))
      ((-1 : ℂ) ^ (j + 1) * (ascPochhammer ℂ (j + 1)).eval s * (x : ℂ) ^ (-s - ((j : ℂ) + 1)))
      x := by
  by_cases he : -s - (j : ℂ) = 0
  ·
    have hsj : s + (j : ℂ) = 0 := by linear_combination -he
    have hp : (ascPochhammer ℂ (j + 1)).eval s = 0 := by
      rw [ascPochhammer_succ_eval, hsj, mul_zero]
    rw [he, hp]
    simp only [Complex.cpow_zero, mul_one, mul_zero, zero_mul]
    exact hasDerivAt_const x _
  ·
    have hpow := hasDerivAt_ofReal_cpow_const (r := -s - (j : ℂ)) hx.ne' he
    have key : (-1 : ℂ) ^ (j + 1) * (ascPochhammer ℂ (j + 1)).eval s
          * (x : ℂ) ^ (-s - ((j : ℂ) + 1))
        = ((-1 : ℂ) ^ j * (ascPochhammer ℂ j).eval s)
          * ((-s - (j : ℂ)) * (x : ℂ) ^ ((-s - (j : ℂ)) - 1)) := by
      rw [show -s - ((j : ℂ) + 1) = (-s - (j : ℂ)) - 1 from by ring, ascPochhammer_succ_eval]
      ring
    rw [key]
    exact hpow.const_mul _
theorem iteratedDeriv_cpow_ofReal_neg (s : ℂ) (j : ℕ) {x : ℝ} (hx : 0 < x) :
    iteratedDeriv j (fun y : ℝ ↦ (y : ℂ) ^ (-s)) x
      = (-1 : ℂ) ^ j * (ascPochhammer ℂ j).eval s * (x : ℂ) ^ (-s - (j : ℂ)) := by
  induction j generalizing x with
  | zero => simp [ascPochhammer_zero]
  | succ j ih =>
    have heq : iteratedDeriv j (fun y : ℝ ↦ (y : ℂ) ^ (-s))
        =ᶠ[𝓝 x] fun y : ℝ ↦ (-1 : ℂ) ^ j * (ascPochhammer ℂ j).eval s * (y : ℂ) ^ (-s - (j : ℂ)) :=
      Filter.eventually_of_mem (Ioi_mem_nhds hx) fun y hy ↦ ih (Set.mem_Ioi.mp hy)
    rw [iteratedDeriv_succ, heq.deriv_eq, (hasDerivAt_cpow_closed_form s j hx).deriv]
    push_cast
    ring
theorem hasDerivAt_iteratedDeriv_cpow_ofReal_neg (s : ℂ) (j : ℕ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (iteratedDeriv j (fun y : ℝ ↦ (y : ℂ) ^ (-s)))
      (iteratedDeriv (j + 1) (fun y : ℝ ↦ (y : ℂ) ^ (-s)) x) x := by
  have heq : iteratedDeriv j (fun y : ℝ ↦ (y : ℂ) ^ (-s))
      =ᶠ[𝓝 x] fun y : ℝ ↦ (-1 : ℂ) ^ j * (ascPochhammer ℂ j).eval s * (y : ℂ) ^ (-s - (j : ℂ)) :=
    Filter.eventually_of_mem (Ioi_mem_nhds hx)
      fun y hy ↦ iteratedDeriv_cpow_ofReal_neg s j (Set.mem_Ioi.mp hy)
  rw [iteratedDeriv_cpow_ofReal_neg s (j + 1) hx]
  have hd := (hasDerivAt_cpow_closed_form s j hx).congr_of_eventuallyEq heq
  rw [show -s - ((j + 1 : ℕ) : ℂ) = -s - ((j : ℂ) + 1) by push_cast; ring]
  exact hd
theorem sum_cpow_eq (s : ℂ) (hs : s ≠ 1) (M N R : ℕ) (hN : 1 ≤ N) (hNR : N ≤ R) :
    ∑ n ∈ Finset.Icc N R, (n : ℂ) ^ (-s)
      = ((R : ℂ) ^ (1 - s) - (N : ℂ) ^ (1 - s)) / (1 - s)
        + ((N : ℂ) ^ (-s) + (R : ℂ) ^ (-s)) / 2
        - (∑ k ∈ Finset.Icc 1 M,
            ((bernoulli (2 * k) : ℝ) / ((2 * k)! : ℝ) : ℂ)
              * (ascPochhammer ℂ (2 * k - 1)).eval s
              * ((R : ℂ) ^ (-s - ((2 * k - 1 : ℕ) : ℂ))
                  - (N : ℂ) ^ (-s - ((2 * k - 1 : ℕ) : ℂ))))
        + eulerMaclaurinRemainder (2 * M + 1) (fun y : ℝ ↦ (y : ℂ) ^ (-s)) (N : ℝ) (R : ℝ) := by
  set f : ℝ → ℂ := fun y : ℝ ↦ (y : ℂ) ^ (-s) with hf
  have hNa : ((N : ℤ) : ℝ) = (N : ℝ) := Int.cast_natCast N
  have hRN : ((N : ℤ) : ℝ) + ((R - N : ℕ) : ℝ) = (R : ℝ) := by push_cast [Nat.cast_sub hNR]; ring
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hRpos : (0 : ℝ) < (R : ℝ) := lt_of_lt_of_le hN0 (by exact_mod_cast hNR)
  have hpos : Set.uIcc ((N : ℤ) : ℝ) (((N : ℤ) : ℝ) + ((R - N : ℕ) : ℝ)) ⊆ Set.Ioi (0 : ℝ) := by
    rw [hRN, hNa, Set.uIcc_of_le (by exact_mod_cast hNR)]
    exact fun x hx ↦ lt_of_lt_of_le hN0 hx.1
  have key := sum_eq (f := f) (N : ℤ) (N := R - N) (p := 2 * M + 1) (by positivity)
    (fun q _ x hx ↦ hasDerivAt_iteratedDeriv_cpow_ofReal_neg s q (hpos hx))
    (fun q _ _ ↦ ContinuousOn.intervalIntegrable fun x hx ↦
      (hasDerivAt_iteratedDeriv_cpow_ofReal_neg s q (hpos hx)).continuousAt.continuousWithinAt)
  rw [hRN, hNa, show Finset.Ico 1 ((2 * M + 1) / 2 + 1) = Finset.Icc 1 M from by
    ext x; rw [Finset.mem_Ico, Finset.mem_Icc]; lia] at key
  have hDeriv_eq : ∀ (j : ℕ) (x : ℝ), 0 < x →
      iteratedDeriv j f x
        = (-1 : ℂ) ^ j * (ascPochhammer ℂ j).eval s * (x : ℂ) ^ (-s - (j : ℂ)) :=
    fun j _ hx ↦ iteratedDeriv_cpow_ofReal_neg s j hx
  have hLHS : ∑ n ∈ Finset.Icc N R, (n : ℂ) ^ (-s)
      = ∑ n ∈ Finset.range (R - N + 1), f ((N : ℝ) + (n : ℝ)) := by
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range,
      show R + 1 - N = R - N + 1 from by lia]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [hf]; push_cast; ring_nf
  have hIeq : (∫ x in (N : ℝ)..(R : ℝ), f x)
      = ((R : ℂ) ^ (1 - s) - (N : ℂ) ^ (1 - s)) / (1 - s) := by
    simp only [hf]
    rw [integral_cpow (Or.inr ⟨fun h ↦ hs (neg_injective h), ?_⟩)]
    · rw [show -s + 1 = 1 - s from by ring]; push_cast; ring_nf
    · rw [Set.uIcc_of_le (by exact_mod_cast hNR : (N : ℝ) ≤ R), Set.mem_Icc]
      exact fun ⟨h1, _⟩ ↦ absurd h1 (not_le.mpr hN0)
  have hEeq : (f (N : ℝ) + f (R : ℝ)) / 2 = ((N : ℂ) ^ (-s) + (R : ℂ) ^ (-s)) / 2 := by
    simp only [hf]; push_cast; ring_nf
  have hBeq : ∑ k ∈ Finset.Icc 1 M,
        (bernoulli (2 * k) : ℝ) / ((2 * k)! : ℝ)
          * (iteratedDeriv (2 * k - 1) f (R : ℝ) - iteratedDeriv (2 * k - 1) f (N : ℝ))
      = -∑ k ∈ Finset.Icc 1 M,
          ((bernoulli (2 * k) : ℝ) / ((2 * k)! : ℝ) : ℂ)
            * (ascPochhammer ℂ (2 * k - 1)).eval s
            * ((R : ℂ) ^ (-s - ((2 * k - 1 : ℕ) : ℂ))
                - (N : ℂ) ^ (-s - ((2 * k - 1 : ℕ) : ℂ))) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    have hodd : (-1 : ℂ) ^ (2 * k - 1) = -1 :=
      Odd.neg_one_pow ⟨k - 1, by have := (Finset.mem_Icc.mp hk).1; lia⟩
    rw [hDeriv_eq _ _ hRpos, hDeriv_eq _ _ hN0, hodd]
    push_cast
    ring
  rw [hLHS, key, hIeq, hEeq, hBeq]
  ring
end Complex
end
end CountPort4
section CountPort5
section
open MeasureTheory
open scoped Topology Nat Real
namespace Complex.Stirling
private theorem isOpen_setOf_add_ofReal_ne_zero (s : ℂ) :
    IsOpen {y : ℝ | s + (y : ℂ) ≠ 0} :=
  isOpen_ne.preimage (continuous_const.add Complex.continuous_ofReal)
private theorem add_ofReal_ne_zero_of_re_pos {s : ℂ} (hs : 0 < s.re) {x : ℝ} (hx : 0 ≤ x) :
    s + (x : ℂ) ≠ 0 :=
  Complex.ne_zero_of_re_pos (by simp only [Complex.add_re, Complex.ofReal_re]; linarith)
private theorem hasDerivAt_inv_add_closed_form (s : ℂ) (j : ℕ) {x : ℝ} (hx : s + (x : ℂ) ≠ 0) :
    HasDerivAt (fun y : ℝ ↦ (-1 : ℂ) ^ j * (j ! : ℂ) * (s + (y : ℂ)) ^ (-(j + 1 : ℤ)))
      ((-1 : ℂ) ^ (j + 1) * ((j + 1)! : ℂ) * (s + (x : ℂ)) ^ (-(j + 1 + 1 : ℤ))) x := by
  have ha : HasDerivAt (fun w : ℂ ↦ s + w) 1 (x : ℂ) := by
    simpa using (hasDerivAt_id (x : ℂ)).const_add s
  have hres := (((hasDerivAt_zpow (-(j + 1 : ℤ)) (s + (x : ℂ)) (Or.inl hx)).comp (x : ℂ)
    ha).comp_ofReal).const_mul ((-1 : ℂ) ^ j * (j ! : ℂ))
  rw [show (-1 : ℂ) ^ (j + 1) * ((j + 1)! : ℂ) * (s + (x : ℂ)) ^ (-(j + 1 + 1 : ℤ))
      = (-1 : ℂ) ^ j * (j ! : ℂ)
        * (((-(j + 1) : ℤ) : ℂ) * (s + (x : ℂ)) ^ (-(j + 1 : ℤ) - 1) * 1) from by
    rw [show (-(j + 1 + 1 : ℤ)) = (-(j + 1 : ℤ) - 1) from by ring]
    push_cast [Nat.factorial_succ]
    ring]
  exact hres
theorem iteratedDeriv_inv_add_ofReal (s : ℂ) (j : ℕ) {x : ℝ} (hx : s + (x : ℂ) ≠ 0) :
    iteratedDeriv j (fun y : ℝ ↦ (s + (y : ℂ))⁻¹) x
      = (-1 : ℂ) ^ j * (j ! : ℂ) * (s + (x : ℂ)) ^ (-(j + 1 : ℤ)) := by
  induction j generalizing x with
  | zero => simp
  | succ j ih =>
    have heq : iteratedDeriv j (fun y : ℝ ↦ (s + (y : ℂ))⁻¹)
        =ᶠ[𝓝 x] fun y : ℝ ↦ (-1 : ℂ) ^ j * (j ! : ℂ) * (s + (y : ℂ)) ^ (-(j + 1 : ℤ)) :=
      Filter.eventually_of_mem ((isOpen_setOf_add_ofReal_ne_zero s).mem_nhds hx)
        fun y hy ↦ ih hy
    rw [iteratedDeriv_succ, heq.deriv_eq, (hasDerivAt_inv_add_closed_form s j hx).deriv]
    push_cast
    ring
theorem hasDerivAt_iteratedDeriv_inv_add_ofReal (s : ℂ) (j : ℕ) {x : ℝ} (hx : s + (x : ℂ) ≠ 0) :
    HasDerivAt (iteratedDeriv j (fun y : ℝ ↦ (s + (y : ℂ))⁻¹))
      (iteratedDeriv (j + 1) (fun y : ℝ ↦ (s + (y : ℂ))⁻¹) x) x := by
  have heq : iteratedDeriv j (fun y : ℝ ↦ (s + (y : ℂ))⁻¹)
      =ᶠ[𝓝 x] fun y : ℝ ↦ (-1 : ℂ) ^ j * (j ! : ℂ) * (s + (y : ℂ)) ^ (-(j + 1 : ℤ)) :=
    Filter.eventually_of_mem ((isOpen_setOf_add_ofReal_ne_zero s).mem_nhds hx)
      fun y hy ↦ iteratedDeriv_inv_add_ofReal s j hy
  rw [iteratedDeriv_inv_add_ofReal s (j + 1) hx]
  exact (hasDerivAt_inv_add_closed_form s j hx).congr_of_eventuallyEq heq
theorem intervalIntegrable_iteratedDeriv_inv_add_ofReal (s : ℂ) (hs : 0 < s.re) (j : ℕ)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    IntervalIntegrable (iteratedDeriv j (fun y : ℝ ↦ (s + (y : ℂ))⁻¹)) volume a b := by
  refine ContinuousOn.intervalIntegrable fun x hx ↦ (hasDerivAt_iteratedDeriv_inv_add_ofReal s j
    (add_ofReal_ne_zero_of_re_pos hs ((le_min ha hb).trans hx.1))).continuousAt.continuousWithinAt
theorem sum_inv_add_eq_digamma_sub (s : ℂ) (hs : 0 < s.re) (N : ℕ) :
    ∑ n ∈ Finset.range (N + 1), (s + (n : ℂ))⁻¹
      = Complex.digamma (s + (N : ℂ) + 1) - Complex.digamma s := by
  induction N with
  | zero =>
    rw [Finset.range_one, Finset.sum_singleton]
    simp only [Nat.cast_zero, add_zero]
    rw [Complex.digamma_apply_add_one s (ne_neg_natCast_of_re_pos hs)]
    ring
  | succ N ih =>
    have hre : 0 < (s + (N : ℂ) + 1).re := by
      simp only [Complex.add_re, Complex.natCast_re, Complex.one_re]
      linarith [Nat.cast_nonneg (α := ℝ) N]
    rw [Finset.sum_range_succ, ih]
    push_cast
    rw [show s + ((N : ℂ) + 1) + 1 = s + (N : ℂ) + 1 + 1 from by ring,
      show s + ((N : ℂ) + 1) = s + (N : ℂ) + 1 from by ring,
      Complex.digamma_apply_add_one (s + (N : ℂ) + 1) (ne_neg_natCast_of_re_pos hre)]
    ring
theorem sum_inv_add_eq (s : ℂ) (hs : 0 < s.re) (M N : ℕ) :
    Complex.digamma (s + (N : ℂ) + 1) - Complex.digamma s
      = (Complex.log (s + (N : ℂ)) - Complex.log s)
        + (s⁻¹ + (s + (N : ℂ))⁻¹) / 2
        - (∑ k ∈ Finset.Icc 1 M,
            (bernoulli (2 * k) : ℂ) / (2 * k)
              * ((s + (N : ℂ)) ^ (-(2 * k : ℤ)) - s ^ (-(2 * k : ℤ))))
        + eulerMaclaurinRemainder (2 * M + 1) (fun y : ℝ ↦ (s + (y : ℂ))⁻¹) 0 (N : ℝ) := by
  set f : ℝ → ℂ := fun y : ℝ ↦ (s + (y : ℂ))⁻¹ with hf
  have hsub : Set.uIcc ((0 : ℤ) : ℝ) (((0 : ℤ) : ℝ) + (N : ℝ)) ⊆ {y : ℝ | s + (y : ℂ) ≠ 0} := by
    rw [Int.cast_zero, zero_add, Set.uIcc_of_le (by positivity : (0 : ℝ) ≤ (N : ℝ))]
    exact fun y hy ↦ add_ofReal_ne_zero_of_re_pos hs hy.1
  have hderiv : ∀ q, q < 2 * M + 1 → ∀ x ∈ {y : ℝ | s + (y : ℂ) ≠ 0},
      HasDerivAt (iteratedDeriv q f) (iteratedDeriv (q + 1) f x) x :=
    fun q _ x hx ↦ hasDerivAt_iteratedDeriv_inv_add_ofReal s q hx
  have hint : ∀ q, 0 < q → q ≤ 2 * M + 1 →
      IntervalIntegrable (iteratedDeriv q f) volume ((0 : ℤ) : ℝ) (((0 : ℤ) : ℝ) + (N : ℝ)) := by
    intro q _ _
    rw [Int.cast_zero, zero_add]
    exact intervalIntegrable_iteratedDeriv_inv_add_ofReal s hs q le_rfl (by positivity)
  have key := Complex.sum_eq (f := f) (0 : ℤ) (N := N) (p := 2 * M + 1)
    (by positivity) (fun q hq x hx ↦ hderiv q hq x (hsub hx)) hint
  simp only [Int.cast_zero, zero_add] at key
  have hIco : Finset.Ico 1 ((2 * M + 1) / 2 + 1) = Finset.Icc 1 M := by
    ext x; rw [Finset.mem_Ico, Finset.mem_Icc]; lia
  rw [hIco] at key
  have hLHS : ∑ n ∈ Finset.range (N + 1), (s + (n : ℂ))⁻¹
      = ∑ n ∈ Finset.range (N + 1), f ((n : ℝ)) :=
    Finset.sum_congr rfl fun n _ ↦ by rw [hf]; push_cast; ring
  have hIeq : (∫ x in (0 : ℝ)..(N : ℝ), f x) = Complex.log (s + (N : ℂ)) - Complex.log s := by
    rw [hf]
    have hderiv_log : ∀ x ∈ Set.uIcc (0 : ℝ) (N : ℝ),
        HasDerivAt (fun y : ℝ ↦ Complex.log (s + (y : ℂ))) ((s + (x : ℂ))⁻¹) x := by
      intro x hx
      have hx0 : 0 ≤ x := (le_min le_rfl (Nat.cast_nonneg N)).trans hx.1
      have hmem : s + (x : ℂ) ∈ Complex.slitPlane :=
        Or.inl (by rw [Complex.add_re, Complex.ofReal_re]; linarith)
      have haff : HasDerivAt (fun w : ℂ ↦ s + w) 1 (x : ℂ) := by
        simpa using (hasDerivAt_id (x : ℂ)).const_add s
      simpa using ((Complex.hasDerivAt_log hmem).comp (x : ℂ) haff).comp_ofReal
    have hintf : IntervalIntegrable f volume (0 : ℝ) (N : ℝ) := by
      simpa using intervalIntegrable_iteratedDeriv_inv_add_ofReal s hs 0 le_rfl
        (by positivity : (0 : ℝ) ≤ (N : ℝ))
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv_log hintf]
    simp
  have hEeq : (f 0 + f (N : ℝ)) / 2 = (s⁻¹ + (s + (N : ℂ))⁻¹) / 2 := by
    simp [hf]
  have hBeq : (∑ k ∈ Finset.Icc 1 M,
        ((bernoulli (2 * k) : ℝ) / ((2 * k)! : ℝ) : ℂ)
          * (iteratedDeriv (2 * k - 1) f (N : ℝ) - iteratedDeriv (2 * k - 1) f 0))
      = -(∑ k ∈ Finset.Icc 1 M,
          (bernoulli (2 * k) : ℂ) / (2 * k)
            * ((s + (N : ℂ)) ^ (-(2 * k : ℤ)) - s ^ (-(2 * k : ℤ)))) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    have hfac : ((2 * k)! : ℂ) = (2 * k : ℂ) * ((2 * k - 1)! : ℂ) := by
      exact_mod_cast (Nat.mul_factorial_pred (by lia : 2 * k ≠ 0)).symm
    have h2k : (2 * k : ℂ) ≠ 0 := mul_ne_zero two_ne_zero (Nat.cast_ne_zero.mpr (by lia))
    have hfne : ((2 * k - 1)! : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
    rw [hf,
      iteratedDeriv_inv_add_ofReal s (2 * k - 1) (add_ofReal_ne_zero_of_re_pos hs (by positivity)),
      iteratedDeriv_inv_add_ofReal s (2 * k - 1) (add_ofReal_ne_zero_of_re_pos hs le_rfl),
      show (-1 : ℂ) ^ (2 * k - 1) = -1 from by
        rw [show 2 * k - 1 = 2 * (k - 1) + 1 from by lia, pow_succ, pow_mul]; simp,
      show (-(((2 * k - 1 : ℕ) : ℤ) + 1)) = -(2 * k : ℤ) from by lia]
    push_cast
    rw [hfac]
    simp only [add_zero]
    field_simp
    ring
  rw [← sum_inv_add_eq_digamma_sub s hs N, hLHS, key, hIeq, hEeq, hBeq]
  ring
private theorem zpow_neg_add_one_le_of_le {p : ℕ} {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    b ^ (-(↑p + 1 : ℤ)) ≤ a ^ (-(↑p + 1 : ℤ)) := by
  rw [show (-(↑p + 1 : ℤ)) = -↑(p + 1) by push_cast; ring, zpow_neg, zpow_neg, zpow_natCast,
    zpow_natCast]
  simpa using one_div_le_one_div_of_le (pow_pos ha _) (pow_le_pow_left₀ ha.le hab _)
private theorem integrableOn_Ioi_norm_zpow_inv_add (s : ℂ) (hs : 0 < s.re) (p : ℕ) (hp : 1 ≤ p) :
    IntegrableOn (fun x : ℝ ↦ ‖s + (x : ℂ)‖ ^ (-(↑p + 1 : ℤ))) (Set.Ioi (0 : ℝ)) := by
  have hsum : ∀ x : ℝ, s.re + x ≤ ‖s + (x : ℂ)‖ := fun x ↦ by
    simpa only [Complex.add_re, Complex.ofReal_re] using Complex.re_le_norm (s + (x : ℂ))
  have hmeas : Measurable (fun x : ℝ ↦ ‖s + (x : ℂ)‖ ^ (-(↑p + 1 : ℤ))) := by fun_prop
  rw [← Set.Ioc_union_Ioi_eq_Ioi (zero_le_one' ℝ)]
  apply IntegrableOn.union
  · apply Integrable.mono' (g := fun _ : ℝ ↦ s.re ^ (-(↑p + 1 : ℤ)))
      continuous_const.integrableOn_Ioc hmeas.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    rw [Real.norm_of_nonneg (by positivity)]
    exact zpow_neg_add_one_le_of_le hs (by linarith [hsum x, hx.1.le])
  · have hg2int : IntegrableOn (fun x : ℝ ↦ x ^ (-(↑p + 1 : ℤ))) (Set.Ioi (1 : ℝ)) := by
      have hlt : (-(↑p + 1 : ℝ)) < -1 := by
        have : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
        linarith
      apply (integrableOn_Ioi_rpow_of_lt hlt one_pos).congr_fun _ measurableSet_Ioi
      intro x _
      change x ^ (-(↑p + 1 : ℝ)) = x ^ (-(↑p + 1 : ℤ))
      rw [← Real.rpow_intCast x (-(↑p + 1 : ℤ))]; congr 1; push_cast; ring
    apply Integrable.mono' (g := fun x : ℝ ↦ x ^ (-(↑p + 1 : ℤ))) hg2int
      hmeas.aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hx0 : (0 : ℝ) < x := lt_trans one_pos hx
      rw [Real.norm_of_nonneg (by positivity)]
      exact zpow_neg_add_one_le_of_le hx0 (by linarith [hsum x, hs.le])
private theorem integral_Ioi_norm_zpow_inv_add_le (s : ℂ) (hs : 0 < s.re) (p : ℕ) (hp : 1 ≤ p) :
    ∫ x in Set.Ioi (0 : ℝ), ‖s + (x : ℂ)‖ ^ (-(↑p + 1 : ℤ))
      ≤ (∫ w in Set.Ioi (0 : ℝ), (1 + w ^ 2)⁻¹) * ‖s‖ ^ (-(p : ℤ)) := by
  set r := ‖s‖ with hr
  have hr0 : 0 < r := norm_pos_iff.mpr (Complex.ne_zero_of_re_pos hs)
  set F : ℝ → ℝ := fun x ↦ ‖s + (x : ℂ)‖ ^ (-(↑p + 1 : ℤ))
  have hscale : ∫ x in Set.Ioi (0 : ℝ), F x = r * ∫ x in Set.Ioi (0 : ℝ), F (r * x) := by
    have := MeasureTheory.integral_comp_mul_left_Ioi F 0 hr0
    simp only [mul_zero, smul_eq_mul] at this
    rw [this, ← mul_assoc, mul_inv_cancel₀ hr0.ne', one_mul]
  have hdomint : IntegrableOn (fun x : ℝ ↦ r ^ (-(↑p + 1 : ℤ)) * (1 + x ^ 2)⁻¹)
      (Set.Ioi (0 : ℝ)) := (integrable_inv_one_add_sq.const_mul _).integrableOn
  have hpt : ∀ x ∈ Set.Ioi (0 : ℝ), F (r * x) ≤ r ^ (-(↑p + 1 : ℤ)) * (1 + x ^ 2)⁻¹ := by
    intro x hx
    have hx0 : 0 < x := hx
    have hA0 : 0 < ‖s + ((r * x : ℝ) : ℂ)‖ :=
      norm_pos_iff.mpr (add_ofReal_ne_zero_of_re_pos hs (by positivity))
    have hkey : r ^ (p + 1) * (1 + x ^ 2) ≤ ‖s + ((r * x : ℝ) : ℂ)‖ ^ (p + 1) := by
      set A := ‖s + ((r * x : ℝ) : ℂ)‖ with hA
      have hrsq : r ^ 2 = s.re ^ 2 + s.im ^ 2 := by
        rw [hr, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
      have hAsq : A ^ 2 = (s.re + r * x) ^ 2 + s.im ^ 2 := by
        rw [hA, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
        simp only [Complex.add_re, Complex.ofReal_re, Complex.add_im, Complex.ofReal_im, add_zero]
        ring
      have hsq : r ^ 2 * (1 + x ^ 2) ≤ A ^ 2 := by
        rw [hAsq, hrsq]
        nlinarith [mul_nonneg hs.le (mul_nonneg hr0.le hx0.le)]
      have hAr : r ≤ A :=
        le_of_sq_le_sq (le_trans (by nlinarith [sq_nonneg x, hr0.le]) hsq) hA0.le
      obtain ⟨m, rfl⟩ : ∃ m, p = m + 1 := ⟨p - 1, by lia⟩
      calc r ^ (m + 1 + 1) * (1 + x ^ 2)
          = r ^ m * (r ^ 2 * (1 + x ^ 2)) := by ring
        _ ≤ A ^ m * A ^ 2 := mul_le_mul (pow_le_pow_left₀ hr0.le hAr m) hsq (by positivity)
              (pow_nonneg hA0.le m)
        _ = A ^ (m + 1 + 1) := by ring
    change ‖s + ((r * x : ℝ) : ℂ)‖ ^ (-(↑p + 1 : ℤ)) ≤ _
    rw [show (-(↑p + 1 : ℤ)) = -↑(p + 1) by push_cast; ring, zpow_neg, zpow_neg, zpow_natCast,
      zpow_natCast, ← mul_inv]
    simpa using one_div_le_one_div_of_le (by positivity) hkey
  have hFrint : IntegrableOn (fun x : ℝ ↦ F (r * x)) (Set.Ioi (0 : ℝ)) :=
    (integrableOn_Ioi_comp_mul_left_iff F 0 hr0).mpr
      (by rw [mul_zero]; exact integrableOn_Ioi_norm_zpow_inv_add s hs p hp)
  rw [hscale]
  have hpow : r * r ^ (-(↑p + 1 : ℤ)) = r ^ (-(p : ℤ)) := by
    have h1 : (-(p : ℤ)) = 1 + (-(↑p + 1)) := by ring
    rw [h1, zpow_add₀ hr0.ne', zpow_one]
  calc r * ∫ x in Set.Ioi (0 : ℝ), F (r * x)
      ≤ r * ∫ x in Set.Ioi (0 : ℝ), r ^ (-(↑p + 1 : ℤ)) * (1 + x ^ 2)⁻¹ :=
        mul_le_mul_of_nonneg_left
          (setIntegral_mono_on hFrint hdomint measurableSet_Ioi hpt) hr0.le
    _ = (r * r ^ (-(↑p + 1 : ℤ))) * ∫ x in Set.Ioi (0 : ℝ), (1 + x ^ 2)⁻¹ := by
        rw [integral_const_mul]; ring
    _ = (∫ w in Set.Ioi (0 : ℝ), (1 + w ^ 2)⁻¹) * ‖s‖ ^ (-(p : ℤ)) := by rw [hpow, ← hr]; ring
theorem integrableOn_Ioi_bernoulliFun_fract_iteratedDeriv_inv_add
    (s : ℂ) (hs : 0 < s.re) (p : ℕ) (hp : 1 ≤ p) :
    IntegrableOn (fun x : ℝ ↦ (bernoulliFun p (Int.fract x) : ℂ) *
        iteratedDeriv p (fun y : ℝ ↦ (s + (y : ℂ))⁻¹) x) (Set.Ioi (0 : ℝ)) := by
  have hCF : IntegrableOn (fun x : ℝ ↦ (bernoulliFun p (Int.fract x) : ℂ) *
      ((-1 : ℂ) ^ p * (p ! : ℂ) * (s + (x : ℂ)) ^ (-(↑p + 1 : ℤ)))) (Set.Ioi (0 : ℝ)) := by
    refine integrableOn_Ioi_bernoulliFun_fract_mul_of_norm_le p
      (h := fun x : ℝ ↦ (p ! : ℝ) * ‖s + (x : ℂ)‖ ^ (-(↑p + 1 : ℤ)))
      ((integrableOn_Ioi_norm_zpow_inv_add s hs p hp).const_mul _)
      (by fun_prop : Measurable (fun x : ℝ ↦
        (-1 : ℂ) ^ p * (p ! : ℂ) * (s + (x : ℂ)) ^ (-(↑p + 1 : ℤ)))).aestronglyMeasurable
      (fun x _ ↦ le_of_eq ?_)
    rw [norm_mul, norm_mul, norm_zpow, norm_pow, norm_neg, norm_one, one_pow, one_mul,
      Complex.norm_natCast]
  apply hCF.congr_fun _ measurableSet_Ioi
  intro x hx
  have hx0 : (0 : ℝ) < x := hx
  dsimp only
  rw [iteratedDeriv_inv_add_ofReal s p (add_ofReal_ne_zero_of_re_pos hs hx0.le)]
noncomputable def digammaRemainderIoi (s : ℂ) (p : ℕ) : ℂ :=
  (-1 : ℂ) ^ (p + 1) / (p ! : ℂ)
    * ∫ x in Set.Ioi (0 : ℝ), (bernoulliFun p (Int.fract x) : ℂ) *
        iteratedDeriv p (fun y : ℝ ↦ (s + (y : ℂ))⁻¹) x
private theorem norm_digammaRemainderIoi_le_of_bound {s : ℂ} (hs : 0 < s.re)
    {p : ℕ} (hp : 1 ≤ p) {CB : ℝ} (hCB : ∀ x : ℝ, ‖(bernoulliFun p (Int.fract x) : ℂ)‖ ≤ CB) :
    ‖digammaRemainderIoi s p‖ ≤ CB * (π / 2) * ‖s‖ ^ (-(p : ℤ)) := by
  have hpfac : (0 : ℝ) < (p ! : ℝ) := by exact_mod_cast Nat.factorial_pos p
  have hCB0 : 0 ≤ CB := (norm_nonneg _).trans (hCB 0)
  have hZ : (0 : ℝ) ≤ ‖s‖ ^ (-(p : ℤ)) := zpow_nonneg (norm_nonneg _) _
  have hJ : ‖∫ x in Set.Ioi (0 : ℝ), (bernoulliFun p (Int.fract x) : ℂ) *
        iteratedDeriv p (fun y : ℝ ↦ (s + (y : ℂ))⁻¹) x‖
      ≤ (CB * (p ! : ℝ)) * (π / 2 * ‖s‖ ^ (-(p : ℤ))) := by
    calc ‖∫ x in Set.Ioi (0 : ℝ), (bernoulliFun p (Int.fract x) : ℂ) *
                iteratedDeriv p (fun y : ℝ ↦ (s + (y : ℂ))⁻¹) x‖
        ≤ ∫ x in Set.Ioi (0 : ℝ), ‖(bernoulliFun p (Int.fract x) : ℂ) *
                  iteratedDeriv p (fun y : ℝ ↦ (s + (y : ℂ))⁻¹) x‖ :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ x in Set.Ioi (0 : ℝ), (CB * (p ! : ℝ)) * ‖s + (x : ℂ)‖ ^ (-(↑p + 1 : ℤ)) := by
          apply setIntegral_mono_on
            (integrableOn_Ioi_bernoulliFun_fract_iteratedDeriv_inv_add s hs p hp).norm
            ((integrableOn_Ioi_norm_zpow_inv_add s hs p hp).const_mul _) measurableSet_Ioi
          intro x hx
          rw [iteratedDeriv_inv_add_ofReal s p (add_ofReal_ne_zero_of_re_pos hs (hx : 0 < x).le),
            norm_mul, norm_mul, norm_mul, norm_zpow, norm_pow, norm_neg, norm_one, one_pow,
            one_mul, Complex.norm_natCast, ← mul_assoc]
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (hCB x) (by positivity))
            (zpow_nonneg (norm_nonneg _) _)
      _ = (CB * (p ! : ℝ)) * ∫ x in Set.Ioi (0 : ℝ), ‖s + (x : ℂ)‖ ^ (-(↑p + 1 : ℤ)) :=
          integral_const_mul ..
      _ ≤ (CB * (p ! : ℝ)) * (π / 2 * ‖s‖ ^ (-(p : ℤ))) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          simpa [integral_Ioi_inv_one_add_sq] using integral_Ioi_norm_zpow_inv_add_le s hs p hp
  rw [digammaRemainderIoi, norm_mul, norm_div, norm_pow, norm_neg, norm_one, one_pow,
    Complex.norm_natCast, one_div]
  calc (p ! : ℝ)⁻¹ * ‖∫ x in Set.Ioi (0 : ℝ), (bernoulliFun p (Int.fract x) : ℂ) *
              iteratedDeriv p (fun y : ℝ ↦ (s + (y : ℂ))⁻¹) x‖
      ≤ (p ! : ℝ)⁻¹ * ((CB * (p ! : ℝ)) * (π / 2 * ‖s‖ ^ (-(p : ℤ)))) :=
        mul_le_mul_of_nonneg_left hJ (by positivity)
    _ = CB * (π / 2) * ‖s‖ ^ (-(p : ℤ)) := by field_simp
theorem abs_bernoulliFun_le {k : ℕ} (hk : 1 ≤ k) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    |bernoulliFun k x| ≤ 4 * (k ! : ℝ) / (2 * π) ^ k := by
  rcases eq_or_lt_of_le hk with rfl | hk
  ·
    have hkey : (1 : ℝ) / 2 ≤ 4 * ((1 : ℕ)! : ℝ) / (2 * π) ^ (1 : ℕ) := by
      rw [pow_one, Nat.factorial_one, Nat.cast_one, le_div_iff₀ (by positivity)]
      nlinarith [Real.pi_lt_d2]
    rw [bernoulliFun_one, abs_le]
    constructor <;> [linarith [hx.1]; linarith [hx.2]]
  replace hk : 2 ≤ k := hk
  have hfac : (0 : ℝ) < (k ! : ℝ) := by exact_mod_cast Nat.factorial_pos k
  have hg : HasSum (fun n : ℤ ↦ (1 : ℝ) / (n : ℝ) ^ 2) (π ^ 2 / 3) := by
    have h := HasSum.of_nat_of_neg (f := fun m : ℤ ↦ (1 : ℝ) / (m : ℝ) ^ 2)
      (by simpa using hasSum_zeta_two) (by simpa using hasSum_zeta_two)
    simpa [show π ^ 2 / 6 + π ^ 2 / 6 = π ^ 2 / 3 by ring] using h
  have hbnd : ∀ n : ℤ, ‖(1 : ℂ) / (n : ℂ) ^ k * fourier n (x : AddCircle (1 : ℝ))‖
      ≤ (1 : ℝ) / (n : ℝ) ^ 2 := fun n ↦ by
    rw [norm_mul, fourier_apply, Circle.norm_coe, mul_one, norm_div, norm_one, norm_pow,
      Complex.norm_intCast]
    rcases eq_or_ne n 0 with rfl | hn
    · simp [zero_pow (show k ≠ 0 by lia)]
    · have h1 : (1 : ℝ) ≤ |(n : ℝ)| := by
        rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hn
      exact one_div_le_one_div_of_le (by positivity)
        (by rw [← sq_abs]; exact pow_le_pow_right₀ h1 hk)
  have hle := (hasSum_one_div_pow_mul_fourier_mul_bernoulliFun hk hx).norm_le_of_bounded hg hbnd
  have hnorm : ‖-(2 * (π : ℂ) * Complex.I) ^ k / (k ! : ℂ) * (bernoulliFun k x : ℂ)‖
      = (2 * π) ^ k / (k ! : ℝ) * |bernoulliFun k x| := by
    rw [norm_mul, norm_div, norm_neg, norm_pow,
      show ‖2 * (π : ℂ) * Complex.I‖ = 2 * π from by simp [abs_of_pos Real.pi_pos],
      Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs]
  have hπ12 : π ^ 2 / 3 ≤ 4 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
  rw [hnorm, div_mul_eq_mul_div, div_le_iff₀ hfac] at hle
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < (2 * π) ^ k)]
  linarith [mul_le_mul_of_nonneg_right hπ12 hfac.le]
theorem norm_digammaRemainderIoi_le' (s : ℂ) (hs : 0 < s.re) (p : ℕ) (hp : 1 ≤ p) :
    ‖digammaRemainderIoi s p‖ ≤ (p ! : ℝ) / (2 * π) ^ (p - 1) * ‖s‖ ^ (-(p : ℤ)) := by
  have hπ : 0 < π := Real.pi_pos
  refine (norm_digammaRemainderIoi_le_of_bound (CB := 4 * (p ! : ℝ) / (2 * π) ^ p) hs
    hp (fun x ↦ ?_)).trans (le_of_eq ?_)
  · rw [Complex.norm_real, Real.norm_eq_abs]
    exact abs_bernoulliFun_le hp ⟨Int.fract_nonneg x, (Int.fract_lt_one x).le⟩
  · have hpw : (2 * π) ^ p = (2 * π) ^ (p - 1) * (2 * π) := by
      conv_lhs => rw [show p = (p - 1) + 1 from by lia]
      rw [pow_succ]
    have hpwpos : (0 : ℝ) < (2 * π) ^ (p - 1) := by positivity
    rw [hpw]; field_simp; ring
end Complex.Stirling
end
end CountPort5
section CountPort6
section
open MeasureTheory Filter Topology
open scoped Nat Real
namespace Complex.Stirling
private theorem add_natCast_ne_zero_of_re_pos {w : ℂ} (hw : 0 < w.re) (j : ℕ) :
    w + (j : ℂ) ≠ 0 := by
  intro h
  have hre : 0 < (w + (j : ℂ)).re := by
    rw [Complex.add_re, Complex.natCast_re]; linarith [Nat.cast_nonneg (α := ℝ) j]
  rw [h] at hre; simp at hre
theorem tendsto_inv_add_natCast_atTop {s : ℂ} :
    Tendsto (fun N : ℕ ↦ (s + (N : ℂ))⁻¹) atTop (𝓝 0) := by
  have hnorm_top : Tendsto (fun N : ℕ ↦ ‖s + (N : ℂ)‖) atTop atTop := by
    have hev : ∀ N : ℕ, s.re + (N : ℝ) ≤ ‖s + (N : ℂ)‖ := fun N ↦ by
      calc s.re + (N : ℝ) = (s + (N : ℂ)).re := by simp
        _ ≤ ‖s + (N : ℂ)‖ := Complex.re_le_norm _
    exact tendsto_atTop_mono hev
      (tendsto_atTop_add_const_left atTop s.re tendsto_natCast_atTop_atTop)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simpa only [norm_inv, Pi.inv_def] using hnorm_top.inv_tendsto_atTop
private theorem tendsto_log_natCast_sub_log_add_atTop {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun N : ℕ ↦ Complex.log (N : ℂ) - Complex.log (s + (N : ℂ))) atTop (𝓝 0) := by
  have hsdiv : Tendsto (fun N : ℕ ↦ s / (N : ℂ)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine (tendsto_const_div_atTop_nhds_zero_nat ‖s‖).congr fun N ↦ ?_
    rw [norm_div, Complex.norm_natCast]
  have h1 : Tendsto (fun N : ℕ ↦ 1 + s / (N : ℂ)) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add hsdiv
  have hcont : ContinuousAt Complex.log 1 :=
    continuousAt_clog (Or.inl (by rw [Complex.one_re]; norm_num))
  have hlog : Tendsto (fun N : ℕ ↦ Complex.log (1 + s / (N : ℂ))) atTop (𝓝 0) := by
    have := (hcont.tendsto.comp h1)
    simpa [Function.comp_def, Complex.log_one] using this
  have hfact : ∀ᶠ N : ℕ in atTop,
      Complex.log (N : ℂ) - Complex.log (s + (N : ℂ)) = -Complex.log (1 + s / (N : ℂ)) := by
    filter_upwards [eventually_gt_atTop 0] with N hN
    have hNc : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by lia)
    have hr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    have hsNne : s + (N : ℂ) ≠ 0 := add_natCast_ne_zero_of_re_pos hs N
    have hxne : 1 + s / (N : ℂ) ≠ 0 := by
      rw [show 1 + s / (N : ℂ) = (s + (N : ℂ)) / (N : ℂ) by field_simp; ring]
      exact div_ne_zero hsNne hNc
    have hsN : s + (N : ℂ) = ((N : ℝ) : ℂ) * (1 + s / (N : ℂ)) := by
      rw [Complex.ofReal_natCast]; field_simp; ring
    rw [hsN, Complex.log_ofReal_mul hr hxne, ← Complex.natCast_log]
    ring
  refine Tendsto.congr' (hfact.mono fun N h ↦ h.symm) ?_
  simpa using hlog.neg
private theorem indicator_kernel_nonneg (n : ℕ) (x : ℝ) :
    0 ≤ (Set.Ioc 0 (n : ℝ)).indicator (fun y ↦ (1 - y / n) ^ n) x := by
  rw [Set.indicator_apply]
  split
  · rename_i hmem
    have hn0 : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le hmem.1 hmem.2
    have hx1 : x / (n : ℝ) ≤ 1 := (div_le_one hn0).mpr hmem.2
    exact pow_nonneg (by linarith) n
  · exact le_refl 0
private theorem indicator_kernel_le_exp (n : ℕ) (x : ℝ) :
    (Set.Ioc 0 (n : ℝ)).indicator (fun y ↦ (1 - y / n) ^ n) x ≤ Real.exp (-x) := by
  rw [Set.indicator_apply]
  split
  · rename_i hmem; exact Real.one_sub_div_pow_le_exp_neg hmem.2
  · exact (Real.exp_pos _).le
private theorem abs_indicator_sub_exp_le (n : ℕ) (x : ℝ) :
    |(Set.Ioc 0 (n : ℝ)).indicator (fun y ↦ (1 - y / n) ^ n) x - Real.exp (-x)|
      ≤ Real.exp (-x) := by
  rw [abs_le]
  refine ⟨by linarith [indicator_kernel_nonneg n x], ?_⟩
  linarith [indicator_kernel_le_exp n x, Real.exp_pos (-x)]
private theorem integrableOn_exp_mul_two_rpow {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntegrableOn (fun x : ℝ ↦ Real.exp (-x) * (x ^ (a - 1) + x ^ (b - 1))) (Set.Ioi 0) :=
  ((Real.GammaIntegral_convergent ha).add (Real.GammaIntegral_convergent hb)).congr_fun
    (fun x _ ↦ by simp only [Pi.add_apply]; ring) measurableSet_Ioi
private theorem rpow_sub_one_le_add {a b c x : ℝ} (hx : 0 < x) (hac : a ≤ c) (hcb : c ≤ b) :
    x ^ (c - 1) ≤ x ^ (a - 1) + x ^ (b - 1) := by
  rcases le_total 1 x with hx1 | hx1
  · have h := Real.rpow_le_rpow_of_exponent_le hx1 (show c - 1 ≤ b - 1 by linarith)
    have := Real.rpow_nonneg hx.le (a - 1); linarith
  · have h := Real.rpow_le_rpow_of_exponent_ge hx hx1 (show a - 1 ≤ c - 1 by linarith)
    have := Real.rpow_nonneg hx.le (b - 1); linarith
private theorem aestronglyMeasurable_abs_indicator_sub_exp_mul (a b : ℝ) (n : ℕ) :
    AEStronglyMeasurable (fun x : ℝ ↦
      |(Set.Ioc 0 (n : ℝ)).indicator (fun y ↦ (1 - y / n) ^ n) x - Real.exp (-x)|
        * (x ^ (a - 1) + x ^ (b - 1))) (volume.restrict (Set.Ioi 0)) := by
  have hW : ContinuousOn (fun x : ℝ ↦ x ^ (a - 1) + x ^ (b - 1)) (Set.Ioi 0) :=
    (continuousOn_id.rpow_const fun x hx ↦ Or.inl (ne_of_gt hx)).add
      (continuousOn_id.rpow_const fun x hx ↦ Or.inl (ne_of_gt hx))
  have hker : Measurable fun x : ℝ ↦
      (Set.Ioc 0 (n : ℝ)).indicator (fun y ↦ (1 - y / n) ^ n) x :=
    Measurable.indicator
      ((continuous_const.sub (continuous_id.div_const _)).pow n).measurable measurableSet_Ioc
  have hexp : Measurable fun x : ℝ ↦ Real.exp (-x) :=
    (Real.continuous_exp.comp continuous_neg).measurable
  have habs : Measurable fun x : ℝ ↦
      |(Set.Ioc 0 (n : ℝ)).indicator (fun y ↦ (1 - y / n) ^ n) x - Real.exp (-x)| := by
    simp only [abs_eq_max_neg]
    exact (hker.sub hexp).max (hker.sub hexp).neg
  exact (habs.aestronglyMeasurable).mul (hW.aestronglyMeasurable measurableSet_Ioi)
private theorem integrableOn_abs_indicator_sub_exp_mul {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (n : ℕ) :
    IntegrableOn (fun x : ℝ ↦
      |(Set.Ioc 0 (n : ℝ)).indicator (fun y ↦ (1 - y / n) ^ n) x - Real.exp (-x)|
        * (x ^ (a - 1) + x ^ (b - 1))) (Set.Ioi 0) := by
  refine (integrableOn_exp_mul_two_rpow ha hb).mono'
    (aestronglyMeasurable_abs_indicator_sub_exp_mul a b n) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx0 : (0 : ℝ) < x := hx
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_right (abs_indicator_sub_exp_le n x) (by positivity)
private theorem tendsto_integral_abs_indicator_sub_exp_mul {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Tendsto (fun n : ℕ ↦ ∫ x in Set.Ioi (0 : ℝ),
        |(Set.Ioc 0 (n : ℝ)).indicator (fun y ↦ (1 - y / n) ^ n) x - Real.exp (-x)|
          * (x ^ (a - 1) + x ^ (b - 1))) atTop (𝓝 0) := by
  set F : ℕ → ℝ → ℝ := fun n x ↦
    |(Set.Ioc 0 (n : ℝ)).indicator (fun y ↦ (1 - y / n) ^ n) x - Real.exp (-x)|
      * (x ^ (a - 1) + x ^ (b - 1)) with hFdef
  have h_bound : ∀ n, ∀ᵐ x ∂(volume.restrict (Set.Ioi 0)),
      ‖F n x‖ ≤ Real.exp (-x) * (x ^ (a - 1) + x ^ (b - 1)) := by
    intro n
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : (0 : ℝ) < x := hx
    rw [hFdef, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_right (abs_indicator_sub_exp_le n x) (by positivity)
  have h_lim : ∀ᵐ x ∂(volume.restrict (Set.Ioi 0)),
      Tendsto (fun n ↦ F n x) atTop (𝓝 (0 : ℝ)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : (0 : ℝ) < x := hx
    have hconv : Tendsto (fun n : ℕ ↦
        (Set.Ioc 0 (n : ℝ)).indicator (fun y ↦ (1 - y / n) ^ n) x) atTop
        (𝓝 (Real.exp (-x))) := by
      have key : Tendsto (fun n : ℕ ↦ (1 - x / (n : ℝ)) ^ n) atTop (𝓝 (Real.exp (-x))) := by
        refine (Real.tendsto_one_add_div_pow_exp (-x)).congr fun n ↦ ?_
        rw [neg_div, ← sub_eq_add_neg]
      refine key.congr' ?_
      filter_upwards [eventually_ge_atTop ⌈x⌉₊] with n hn
      have hmem : x ∈ Set.Ioc 0 (n : ℝ) := ⟨hx0, by rw [← Nat.ceil_le]; exact hn⟩
      exact (Set.indicator_of_mem hmem (fun y ↦ (1 - y / (n : ℝ)) ^ n)).symm
    have hz : Tendsto (fun n : ℕ ↦
        |(Set.Ioc 0 (n : ℝ)).indicator (fun y ↦ (1 - y / n) ^ n) x - Real.exp (-x)|)
        atTop (𝓝 0) := by simpa using (hconv.sub_const (Real.exp (-x))).abs
    rw [hFdef]; simpa using hz.mul_const (x ^ (a - 1) + x ^ (b - 1))
  have hmain := tendsto_integral_of_dominated_convergence (f := fun _ : ℝ ↦ (0 : ℝ))
    (fun x ↦ Real.exp (-x) * (x ^ (a - 1) + x ^ (b - 1)))
    (fun n ↦ aestronglyMeasurable_abs_indicator_sub_exp_mul a b n)
    (integrableOn_exp_mul_two_rpow ha hb) h_bound h_lim
  simpa [hFdef] using hmain
private theorem GammaSeq_eq_setIntegral_indicator {s : ℂ} (hs : 0 < s.re) {n : ℕ} (hn : n ≠ 0) :
    Complex.GammaSeq s n = ∫ x in Set.Ioi (0 : ℝ),
      ↑((Set.Ioc 0 (n : ℝ)).indicator (fun y ↦ (1 - y / n) ^ n) x) * (x : ℂ) ^ (s - 1) := by
  have hpoint : ∀ x : ℝ,
      ↑((Set.Ioc 0 (n : ℝ)).indicator (fun y ↦ (1 - y / n) ^ n) x) * (x : ℂ) ^ (s - 1)
        = (Set.Ioc 0 (n : ℝ)).indicator
            (fun y ↦ (((1 - y / n) ^ n : ℝ) : ℂ) * (y : ℂ) ^ (s - 1)) x := by
    intro x
    by_cases hx : x ∈ Set.Ioc 0 (n : ℝ)
    · simp only [Set.indicator_of_mem hx]
    · simp only [Set.indicator_of_notMem hx, Complex.ofReal_zero, zero_mul]
  rw [Complex.GammaSeq_eq_approx_Gamma_integral hs hn,
    intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ (n : ℝ)),
    setIntegral_congr_fun measurableSet_Ioi fun x _ ↦ hpoint x,
    MeasureTheory.setIntegral_indicator measurableSet_Ioc,
    Set.inter_eq_self_of_subset_right Set.Ioc_subset_Ioi_self]
private theorem integrableOn_Ioi_indicator_kernel_mul_cpow {s : ℂ} (hs : 0 < s.re) (n : ℕ) :
    IntegrableOn (fun x : ℝ ↦
        ↑((Set.Ioc 0 (n : ℝ)).indicator (fun y ↦ (1 - y / n) ^ n) x) * (x : ℂ) ^ (s - 1))
      (Set.Ioi (0 : ℝ)) := by
  refine (Real.GammaIntegral_convergent hs).mono' ?_ ?_
  · exact ((Complex.continuous_ofReal.measurable.comp
      (Measurable.indicator (by fun_prop) measurableSet_Ioc)).aestronglyMeasurable).mul
      (aestronglyMeasurable_ofReal_cpow_Ioi le_rfl (s - 1))
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : (0 : ℝ) < x := hx
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0, Complex.sub_re, Complex.one_re,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (indicator_kernel_nonneg n x)]
    exact mul_le_mul_of_nonneg_right (indicator_kernel_le_exp n x) (Real.rpow_nonneg hx0.le _)
private theorem norm_Gamma_sub_GammaSeq_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    {s : ℂ} (hsa : a ≤ s.re) (hsb : s.re ≤ b) {n : ℕ} (hn : 1 ≤ n) :
    ‖Complex.Gamma s - Complex.GammaSeq s n‖
      ≤ ∫ x in Set.Ioi (0 : ℝ),
          |(Set.Ioc 0 (n : ℝ)).indicator (fun y ↦ (1 - y / n) ^ n) x - Real.exp (-x)|
            * (x ^ (a - 1) + x ^ (b - 1)) := by
  have hs : 0 < s.re := lt_of_lt_of_le ha hsa
  set g : ℝ → ℝ := fun x ↦ (Set.Ioc 0 (n : ℝ)).indicator (fun y ↦ (1 - y / n) ^ n) x with hg
  have hΓint : IntegrableOn (fun x : ℝ ↦ (↑(Real.exp (-x)) * (x : ℂ) ^ (s - 1))) (Set.Ioi 0) :=
    Complex.GammaIntegral_convergent hs
  have hΓ : Complex.Gamma s = ∫ x in Set.Ioi (0 : ℝ), ↑(Real.exp (-x)) * (x : ℂ) ^ (s - 1) := by
    rw [Complex.Gamma_eq_integral hs, Complex.GammaIntegral]
  have hGSint : IntegrableOn (fun x : ℝ ↦ ↑(g x) * (x : ℂ) ^ (s - 1)) (Set.Ioi 0) := by
    simpa only [hg] using integrableOn_Ioi_indicator_kernel_mul_cpow hs n
  have hGS : Complex.GammaSeq s n = ∫ x in Set.Ioi (0 : ℝ), ↑(g x) * (x : ℂ) ^ (s - 1) := by
    simpa only [hg] using GammaSeq_eq_setIntegral_indicator hs (by lia : n ≠ 0)
  rw [hΓ, hGS, ← integral_sub hΓint hGSint]
  calc ‖∫ x in Set.Ioi (0 : ℝ),
          (↑(Real.exp (-x)) * (x : ℂ) ^ (s - 1) - ↑(g x) * (x : ℂ) ^ (s - 1))‖
      ≤ ∫ x in Set.Ioi (0 : ℝ),
          ‖↑(Real.exp (-x)) * (x : ℂ) ^ (s - 1) - ↑(g x) * (x : ℂ) ^ (s - 1)‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ x in Set.Ioi (0 : ℝ), |g x - Real.exp (-x)| * (x ^ (a - 1) + x ^ (b - 1)) := by
        refine setIntegral_mono_on (hΓint.sub hGSint).norm
          (integrableOn_abs_indicator_sub_exp_mul ha (lt_of_lt_of_le ha hab) n)
          measurableSet_Ioi fun x hx ↦ ?_
        have hx0 : (0 : ℝ) < x := hx
        rw [show (↑(Real.exp (-x)) * (x : ℂ) ^ (s - 1) - ↑(g x) * (x : ℂ) ^ (s - 1))
              = (↑(Real.exp (-x) - g x) : ℂ) * (x : ℂ) ^ (s - 1) by push_cast; ring,
          norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0, Complex.sub_re, Complex.one_re,
          Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
        exact mul_le_mul_of_nonneg_left (rpow_sub_one_le_add hx0 hsa hsb) (abs_nonneg _)
theorem tendstoLocallyUniformlyOn_gammaSeq :
    TendstoLocallyUniformlyOn (fun (n : ℕ) (s : ℂ) ↦ Complex.GammaSeq s n) Complex.Gamma
      atTop {s : ℂ | 0 < s.re} := by
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact (isOpen_re_gt 0)]
  intro K hKsub hK
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · exact tendstoUniformlyOn_empty
  obtain ⟨xa, hxaK, hxa⟩ := hK.exists_isMinOn hKne Complex.continuous_re.continuousOn
  obtain ⟨xb, hxbK, hxb⟩ := hK.exists_isMaxOn hKne Complex.continuous_re.continuousOn
  have ha : 0 < xa.re := hKsub hxaK
  have hab : xa.re ≤ xb.re := isMinOn_iff.mp hxa xb hxbK
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hev : ∀ᶠ n : ℕ in atTop, (∫ x in Set.Ioi (0 : ℝ),
      |(Set.Ioc 0 (n : ℝ)).indicator (fun y ↦ (1 - y / n) ^ n) x - Real.exp (-x)|
        * (x ^ (xa.re - 1) + x ^ (xb.re - 1))) < ε :=
    (tendsto_integral_abs_indicator_sub_exp_mul ha
      (lt_of_lt_of_le ha hab)).eventually (gt_mem_nhds hε)
  filter_upwards [hev, eventually_ge_atTop 1] with n hn hn1
  intro s hsK
  rw [Complex.dist_eq]
  calc ‖Complex.Gamma s - Complex.GammaSeq s n‖
      ≤ ∫ x in Set.Ioi (0 : ℝ),
          |(Set.Ioc 0 (n : ℝ)).indicator (fun y ↦ (1 - y / n) ^ n) x - Real.exp (-x)|
            * (x ^ (xa.re - 1) + x ^ (xb.re - 1)) :=
        norm_Gamma_sub_GammaSeq_le ha hab (isMinOn_iff.mp hxa s hsK) (isMaxOn_iff.mp hxb s hsK) hn1
    _ < ε := hn
theorem tendsto_log_sub_sum_inv_add {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun n : ℕ ↦ Complex.log (n : ℂ) - ∑ j ∈ Finset.range (n + 1), (s + (j : ℂ))⁻¹)
      atTop (𝓝 (Complex.digamma s)) := by
  have hΩ : s ∈ {z : ℂ | 0 < z.re} := hs
  have hdiff : ∀ᶠ n : ℕ in atTop, DifferentiableOn ℂ (fun w ↦ Complex.GammaSeq w n)
      {z : ℂ | 0 < z.re} := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have : NeZero (n : ℂ) := ⟨Nat.cast_ne_zero.mpr (by lia)⟩
    have hnum : DifferentiableOn ℂ (fun w : ℂ ↦ (n : ℂ) ^ w * (n ! : ℂ)) {z : ℂ | 0 < z.re} :=
      ((differentiable_const_cpow_of_neZero (n : ℂ)).mul_const _).differentiableOn
    have hprod : DifferentiableOn ℂ (fun w : ℂ ↦ ∏ j ∈ Finset.range (n + 1), (w + (j : ℂ)))
        {z : ℂ | 0 < z.re} :=
      DifferentiableOn.fun_finsetProd fun j _ ↦ (differentiable_id.add_const _).differentiableOn
    have hden : ∀ w ∈ {z : ℂ | 0 < z.re},
        (∏ j ∈ Finset.range (n + 1), (w + (j : ℂ))) ≠ 0 := fun w hw ↦
      Finset.prod_ne_zero_iff.mpr fun j _ ↦ add_natCast_ne_zero_of_re_pos hw j
    simp only [Complex.GammaSeq]
    exact hnum.div hprod hden
  have hgne : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hs
  have hkey := Complex.logDeriv_tendsto (isOpen_re_gt 0) hΩ
    tendstoLocallyUniformlyOn_gammaSeq hdiff hgne
  rw [Complex.digamma_def]
  refine hkey.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have : NeZero (n : ℂ) := ⟨Nat.cast_ne_zero.mpr (by lia)⟩
  have hcpow_ne : (n : ℂ) ^ s ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl (NeZero.ne _))
  have hfac_ne : (n ! : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos n).ne'
  have hAne : (n : ℂ) ^ s * (n ! : ℂ) ≠ 0 := mul_ne_zero hcpow_ne hfac_ne
  have hBne : (∏ j ∈ Finset.range (n + 1), (s + (j : ℂ))) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j _ ↦ add_natCast_ne_zero_of_re_pos hs j
  have hdA : DifferentiableAt ℂ (fun w : ℂ ↦ (n : ℂ) ^ w * (n ! : ℂ)) s :=
    ((differentiable_const_cpow_of_neZero (n : ℂ)).mul_const _).differentiableAt
  have hdB : DifferentiableAt ℂ (fun w : ℂ ↦ ∏ j ∈ Finset.range (n + 1), (w + (j : ℂ))) s :=
    DifferentiableAt.fun_finsetProd fun j _ ↦ (differentiable_id.add_const _).differentiableAt
  have hlogcpow : logDeriv (fun w : ℂ ↦ (n : ℂ) ^ w) s = Complex.log (n : ℂ) := by
    rw [logDeriv_apply, Complex.deriv_const_cpow differentiableAt_fun_id (n : ℂ)]
    simp only [deriv_id'']
    rw [mul_one, mul_div_assoc, div_self hcpow_ne, mul_one]
  have hlogprod : logDeriv (fun w : ℂ ↦ ∏ j ∈ Finset.range (n + 1), (w + (j : ℂ))) s
      = ∑ j ∈ Finset.range (n + 1), (s + (j : ℂ))⁻¹ := by
    rw [logDeriv_prod (fun j _ ↦ add_natCast_ne_zero_of_re_pos hs j)
      (fun j _ ↦ (differentiable_id.add_const _).differentiableAt)]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    have hderiv1 : deriv (fun w : ℂ ↦ w + (j : ℂ)) s = 1 := by simp
    rw [logDeriv_apply, hderiv1, one_div]
  rw [show (fun w ↦ Complex.GammaSeq w n)
      = fun w ↦ ((n : ℂ) ^ w * (n ! : ℂ)) / ∏ j ∈ Finset.range (n + 1), (w + (j : ℂ)) from by
        funext w; rw [Complex.GammaSeq],
    logDeriv_div s hAne hBne hdA hdB, logDeriv_mul_const s (n ! : ℂ) hfac_ne, hlogcpow, hlogprod]
theorem tendsto_digamma_sub_log_atTop {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun N : ℕ ↦ Complex.digamma (s + (N : ℂ) + 1) - Complex.log (s + (N : ℂ)))
      atTop (𝓝 0) := by
  have hI : Tendsto (fun N : ℕ ↦ Complex.digamma (s + (N : ℂ) + 1) - Complex.log (N : ℂ))
      atTop (𝓝 0) := by
    have hrw : ∀ N : ℕ, Complex.digamma (s + (N : ℂ) + 1) - Complex.log (N : ℂ)
        = Complex.digamma s
          - (Complex.log (N : ℂ) - ∑ j ∈ Finset.range (N + 1), (s + (j : ℂ))⁻¹) := by
      intro N
      rw [sum_inv_add_eq_digamma_sub s hs N]; ring
    have hlim := tendsto_const_nhds (x := Complex.digamma s) |>.sub (tendsto_log_sub_sum_inv_add hs)
    rw [sub_self] at hlim
    exact hlim.congr fun N ↦ (hrw N).symm
  have hII : Tendsto (fun N : ℕ ↦ Complex.log (N : ℂ) - Complex.log (s + (N : ℂ)))
      atTop (𝓝 0) := tendsto_log_natCast_sub_log_add_atTop hs
  have := hI.add hII
  rw [add_zero] at this
  exact this.congr fun N ↦ by ring
theorem digamma_eq_log_sub (s : ℂ) (hs : 0 < s.re) (M : ℕ) :
    Complex.digamma s = Complex.log s - (2 * s)⁻¹
      - (∑ k ∈ Finset.Icc 1 M, (bernoulli (2 * k) : ℂ) / (2 * k) * s ^ (-(2 * k : ℤ)))
      - digammaRemainderIoi s (2 * M + 1) := by
  have hs0 : s ≠ 0 := Complex.ne_zero_of_re_pos hs
  have hL1 : Tendsto (fun N : ℕ ↦ Complex.digamma (s + (N : ℂ) + 1) - Complex.log (s + (N : ℂ)))
      atTop (𝓝 0) := tendsto_digamma_sub_log_atTop hs
  have hL2 : Tendsto (fun N : ℕ ↦ (s + (N : ℂ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_add_natCast_atTop
  have hL3 : ∀ k : ℕ, 1 ≤ k →
      Tendsto (fun N : ℕ ↦ (s + (N : ℂ)) ^ (-(2 * k : ℤ))) atTop (𝓝 0) := by
    intro k hk
    have h2k : (2 * k) ≠ 0 := by lia
    have hrw : ∀ N : ℕ, (s + (N : ℂ)) ^ (-(2 * k : ℤ)) = ((s + (N : ℂ))⁻¹) ^ (2 * k) := by
      intro N
      rw [show (-(2 * k : ℤ)) = -((2 * k : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast,
        inv_pow]
    have hpow := hL2.pow (2 * k)
    rw [zero_pow h2k] at hpow
    exact hpow.congr fun N ↦ (hrw N).symm
  have hL4 : Tendsto
      (fun N : ℕ ↦ eulerMaclaurinRemainder (2 * M + 1)
        (fun y : ℝ ↦ (s + (y : ℂ))⁻¹) 0 (N : ℝ))
      atTop (𝓝 (digammaRemainderIoi s (2 * M + 1))) := by
    simp only [Complex.eulerMaclaurinRemainder_eq, digammaRemainderIoi]
    exact (intervalIntegral_tendsto_integral_Ioi 0
      (integrableOn_Ioi_bernoulliFun_fract_iteratedDeriv_inv_add s hs (2 * M + 1) (by lia))
      tendsto_natCast_atTop_atTop).const_mul _
  have hSplus : Tendsto (fun N : ℕ ↦ ∑ k ∈ Finset.Icc 1 M,
      (bernoulli (2 * k) : ℂ) / (2 * k) * (s + (N : ℂ)) ^ (-(2 * k : ℤ))) atTop (𝓝 0) := by
    have h := tendsto_finsetSum (Finset.Icc 1 M) (fun k hk ↦ by
      have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
      simpa only [mul_zero] using (hL3 k hk1).const_mul ((bernoulli (2 * k) : ℂ) / (2 * k)))
    simpa using h
  set seq : ℕ → ℂ := fun N ↦
    (Complex.digamma (s + (N : ℂ) + 1) - Complex.log (s + (N : ℂ)))
      + Complex.log s
      - (s⁻¹ + (s + (N : ℂ))⁻¹) / 2
      + (∑ k ∈ Finset.Icc 1 M, (bernoulli (2 * k) : ℂ) / (2 * k) * (s + (N : ℂ)) ^ (-(2 * k : ℤ)))
      - (∑ k ∈ Finset.Icc 1 M, (bernoulli (2 * k) : ℂ) / (2 * k) * s ^ (-(2 * k : ℤ)))
      - eulerMaclaurinRemainder (2 * M + 1)
          (fun y : ℝ ↦ (s + (y : ℂ))⁻¹) 0 (N : ℝ) with hseq
  have hconst : ∀ N : ℕ, Complex.digamma s = seq N := by
    intro N
    have h := sum_inv_add_eq s hs M N
    have hsplit : (∑ k ∈ Finset.Icc 1 M, (bernoulli (2 * k) : ℂ) / (2 * k)
          * ((s + (N : ℂ)) ^ (-(2 * k : ℤ)) - s ^ (-(2 * k : ℤ))))
        = (∑ k ∈ Finset.Icc 1 M,
            (bernoulli (2 * k) : ℂ) / (2 * k) * (s + (N : ℂ)) ^ (-(2 * k : ℤ)))
          - (∑ k ∈ Finset.Icc 1 M, (bernoulli (2 * k) : ℂ) / (2 * k) * s ^ (-(2 * k : ℤ))) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun k _ ↦ by ring
    rw [hsplit] at h
    simp only [hseq]
    linear_combination -h
  have htend : Tendsto seq atTop (𝓝 (Complex.log s - (2 * s)⁻¹
      - (∑ k ∈ Finset.Icc 1 M, (bernoulli (2 * k) : ℂ) / (2 * k) * s ^ (-(2 * k : ℤ)))
      - digammaRemainderIoi s (2 * M + 1))) := by
    have hcomb : Tendsto seq atTop (𝓝 (0 + Complex.log s - (s⁻¹ + 0) / 2 + 0
        - (∑ k ∈ Finset.Icc 1 M, (bernoulli (2 * k) : ℂ) / (2 * k) * s ^ (-(2 * k : ℤ)))
        - digammaRemainderIoi s (2 * M + 1))) := by
      rw [hseq]
      exact ((((hL1.add tendsto_const_nhds).sub
        ((tendsto_const_nhds.add hL2).div_const 2)).add hSplus).sub tendsto_const_nhds).sub hL4
    have hval : (0 + Complex.log s - (s⁻¹ + 0) / 2 + 0
          - (∑ k ∈ Finset.Icc 1 M, (bernoulli (2 * k) : ℂ) / (2 * k) * s ^ (-(2 * k : ℤ)))
          - digammaRemainderIoi s (2 * M + 1))
        = (Complex.log s - (2 * s)⁻¹
          - (∑ k ∈ Finset.Icc 1 M, (bernoulli (2 * k) : ℂ) / (2 * k) * s ^ (-(2 * k : ℤ)))
          - digammaRemainderIoi s (2 * M + 1)) := by
      field_simp
      ring
    rwa [hval] at hcomb
  exact tendsto_nhds_unique (tendsto_const_nhds.congr hconst) htend
theorem norm_digamma_sub_log_le' {a : ℝ} (ha : 0 < a) (s : ℂ) (has : a ≤ s.re) :
    ‖Complex.digamma s - Complex.log s + (2 * s)⁻¹‖
      ≤ (1 / 12 + 3 / (2 * π ^ 2 * a)) * ‖s‖ ^ (-(2 : ℤ)) := by
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have hs : 0 < s.re := lt_of_lt_of_le ha has
  have hnpos : 0 < ‖s‖ := norm_pos_iff.mpr (Complex.ne_zero_of_re_pos hs)
  have han : a ≤ ‖s‖ := le_trans has (Complex.re_le_norm s)
  have hsum : (∑ k ∈ Finset.Icc 1 1, (bernoulli (2 * k) : ℂ) / (2 * k) * s ^ (-(2 * k : ℤ)))
      = (bernoulli 2 : ℂ) / 2 * s ^ (-(2 : ℤ)) := by
    rw [Finset.Icc_self, Finset.sum_singleton]; norm_num
  have hexp := digamma_eq_log_sub s hs 1
  rw [hsum, show (2 * 1 + 1) = 3 from rfl] at hexp
  have hE : Complex.digamma s - Complex.log s + (2 * s)⁻¹
      = -((bernoulli 2 : ℂ) / 2 * s ^ (-(2 : ℤ))) - digammaRemainderIoi s 3 := by
    rw [hexp]; ring
  have hb2 : ‖(bernoulli 2 : ℂ) / 2‖ = 1 / 12 := by
    rw [bernoulli_two, norm_div, Complex.norm_ratCast]; norm_num
  have hR3 := norm_digammaRemainderIoi_le' s hs 3 (by norm_num)
  rw [show (3 ! : ℝ) = 6 from by norm_num [Nat.factorial], show (3 - 1) = 2 from rfl] at hR3
  have hsnorm3 : ‖s‖ ^ (-(3 : ℤ)) ≤ a⁻¹ * ‖s‖ ^ (-(2 : ℤ)) := by
    rw [show (-(3 : ℤ)) = -(2 : ℤ) + -(1 : ℤ) from by ring, zpow_add₀ hnpos.ne', zpow_neg_one,
      mul_comm (a⁻¹) (‖s‖ ^ (-(2 : ℤ)))]
    exact mul_le_mul_of_nonneg_left (inv_anti₀ ha han) (zpow_nonneg (norm_nonneg _) _)
  calc ‖Complex.digamma s - Complex.log s + (2 * s)⁻¹‖
      = ‖-((bernoulli 2 : ℂ) / 2 * s ^ (-(2 : ℤ))) - digammaRemainderIoi s 3‖ := by rw [hE]
    _ ≤ ‖-((bernoulli 2 : ℂ) / 2 * s ^ (-(2 : ℤ)))‖ + ‖digammaRemainderIoi s 3‖ :=
        norm_sub_le _ _
    _ = 1 / 12 * ‖s‖ ^ (-(2 : ℤ)) + ‖digammaRemainderIoi s 3‖ := by
        rw [norm_neg, norm_mul, norm_zpow, hb2]
    _ ≤ 1 / 12 * ‖s‖ ^ (-(2 : ℤ)) + 6 / (2 * π) ^ 2 * ‖s‖ ^ (-(3 : ℤ)) := by linarith [hR3]
    _ ≤ 1 / 12 * ‖s‖ ^ (-(2 : ℤ)) + 6 / (2 * π) ^ 2 * (a⁻¹ * ‖s‖ ^ (-(2 : ℤ))) := by
        linarith [mul_le_mul_of_nonneg_left hsnorm3 (by positivity : (0 : ℝ) ≤ 6 / (2 * π) ^ 2)]
    _ = (1 / 12 + 3 / (2 * π ^ 2 * a)) * ‖s‖ ^ (-(2 : ℤ)) := by
        have hane : a ≠ 0 := ha.ne'
        have hπne : π ≠ 0 := hπ.ne'
        field_simp
        ring
end Complex.Stirling
end
end CountPort6
section CountPort7
section
open MeasureTheory
open scoped Topology
namespace Complex
open Complex.Stirling
private theorem hasDerivAt_arctan_div (σ u : ℝ) :
    HasDerivAt (fun u : ℝ ↦ Real.arctan (u / σ)) (1 / (1 + (u / σ) ^ 2) * (1 / σ)) u := by
  have hd1 : HasDerivAt (fun u : ℝ ↦ u / σ) (1 / σ) u := (hasDerivAt_id u).div_const σ
  simpa only [Function.comp_def] using (Real.hasDerivAt_arctan (u / σ)).comp u hd1
private theorem hasDerivAt_log_sq_add {σ : ℝ} (hσ : 0 < σ) (u : ℝ) :
    HasDerivAt (fun u : ℝ ↦ Real.log (σ ^ 2 + u ^ 2)) ((σ ^ 2 + u ^ 2)⁻¹ * (2 * u)) u := by
  have hpos : (0 : ℝ) < σ ^ 2 + u ^ 2 := by positivity
  have hin : HasDerivAt (fun u : ℝ ↦ σ ^ 2 + u ^ 2) (2 * u) u := by
    simpa using (hasDerivAt_pow 2 u).const_add (σ ^ 2)
  simpa only [Function.comp_def] using (Real.hasDerivAt_log hpos.ne').comp u hin
private theorem log_one_add_sq_div {σ : ℝ} (hσ : 0 < σ) (t : ℝ) :
    Real.log (1 + t ^ 2 / σ ^ 2) = Real.log (σ ^ 2 + t ^ 2) - Real.log (σ ^ 2) := by
  have hσne : σ ≠ 0 := hσ.ne'
  rw [show (1 + t ^ 2 / σ ^ 2) = (σ ^ 2 + t ^ 2) / σ ^ 2 by field_simp,
    Real.log_div (by positivity) (by positivity)]
theorem hasDerivAt_log_norm {G : ℝ → ℂ} {g' : ℂ} {x : ℝ}
    (hG : HasDerivAt G g' x) (hne : G x ≠ 0) :
    HasDerivAt (fun t ↦ Real.log ‖G t‖) (g' / G x).re x := by
  have hpos : (0 : ℝ) < ‖G x‖ ^ 2 := by positivity
  have hnsq := HasDerivAt.norm_sq hG
  have hlog0 := (Real.hasDerivAt_log hpos.ne').comp x hnsq
  have hfun : (fun t ↦ Real.log ‖G t‖) = fun t ↦ (2 : ℝ)⁻¹ * Real.log (‖G t‖ ^ 2) := by
    funext t; rw [Real.log_pow]; push_cast; ring
  rw [hfun]
  have hval : (g' / G x).re
      = (2 : ℝ)⁻¹ * ((‖G x‖ ^ 2)⁻¹ * (2 * inner ℝ (G x) g')) := by
    rw [Complex.inner, ← Complex.normSq_eq_norm_sq, Complex.div_re, Complex.mul_re,
      Complex.conj_re, Complex.conj_im]
    ring
  rw [hval]
  exact hlog0.const_mul (2 : ℝ)⁻¹
theorem hasDerivAt_log_norm_Gamma_comp {φ : ℝ → ℂ} {φ' : ℂ} {x : ℝ}
    (hφ : HasDerivAt φ φ' x) (hre : 0 < (φ x).re) :
    HasDerivAt (fun u : ℝ ↦ Real.log ‖Complex.Gamma (φ u)‖)
      (φ' * Complex.digamma (φ x)).re x := by
  have hG : HasDerivAt (fun u : ℝ ↦ Complex.Gamma (φ u)) (deriv Complex.Gamma (φ x) * φ') x := by
    simpa only [Function.comp_def] using
      (differentiableAt_Gamma_of_re_pos hre).hasDerivAt.comp x hφ
  convert hasDerivAt_log_norm hG (Complex.Gamma_ne_zero_of_re_pos hre) using 2
  rw [Complex.digamma_def, logDeriv_apply]
  field_simp
theorem hasDerivAt_log_norm_Gamma_vertical {σ : ℝ} (hσ : 0 < σ) (t : ℝ) :
    HasDerivAt (fun τ : ℝ ↦ Real.log ‖Complex.Gamma ((σ : ℂ) + (τ : ℂ) * Complex.I)‖)
      (-(Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)).im) t := by
  have hpath : HasDerivAt (fun τ : ℝ ↦ (σ : ℂ) + (τ : ℂ) * Complex.I) Complex.I t := by
    simpa using ((Complex.ofRealCLM.hasDerivAt (x := t)).mul_const Complex.I).const_add (σ : ℂ)
  simpa [Complex.I_mul_re] using hasDerivAt_log_norm_Gamma_comp hpath (by simp [hσ])
theorem integral_im_log_add_ofReal_mul_I {σ : ℝ} (hσ : 0 < σ) (t : ℝ) :
    (∫ τ in (0 : ℝ)..t, (Complex.log ((σ : ℂ) + (τ : ℂ) * Complex.I)).im)
      = t * Real.arctan (t / σ) - σ / 2 * Real.log (1 + t ^ 2 / σ ^ 2) := by
  have hσne : σ ≠ 0 := hσ.ne'
  have harg : ∀ τ : ℝ, (Complex.log ((σ : ℂ) + (τ : ℂ) * Complex.I)).im = Real.arctan (τ / σ) := by
    intro τ
    have hre : ((σ : ℂ) + (τ : ℂ) * Complex.I).re = σ := by simp
    have him : ((σ : ℂ) + (τ : ℂ) * Complex.I).im = τ := by simp
    rw [Complex.log_im]
    have h1 : -(Real.pi / 2) < Complex.arg ((σ : ℂ) + (τ : ℂ) * Complex.I) :=
      Complex.neg_pi_div_two_lt_arg_iff.mpr (Or.inl (by rw [hre]; exact hσ))
    have h2 : Complex.arg ((σ : ℂ) + (τ : ℂ) * Complex.I) < Real.pi / 2 :=
      Complex.arg_lt_pi_div_two_iff.mpr (Or.inl (by rw [hre]; exact hσ))
    rw [← Real.arctan_tan h1 h2, Complex.tan_arg, hre, him]
  have hF : ∀ u : ℝ, HasDerivAt
      (fun u ↦ u * Real.arctan (u / σ) - σ / 2 * Real.log (σ ^ 2 + u ^ 2))
      (Real.arctan (u / σ)) u := by
    intro u
    have hp1 : HasDerivAt (fun u ↦ u * Real.arctan (u / σ))
        (1 * Real.arctan (u / σ) + u * (1 / (1 + (u / σ) ^ 2) * (1 / σ))) u :=
      (hasDerivAt_id u).mul (hasDerivAt_arctan_div σ u)
    have hp2 : HasDerivAt (fun u ↦ σ / 2 * Real.log (σ ^ 2 + u ^ 2))
        (σ / 2 * ((σ ^ 2 + u ^ 2)⁻¹ * (2 * u))) u := (hasDerivAt_log_sq_add hσ u).const_mul (σ / 2)
    have hval : 1 * Real.arctan (u / σ) + u * (1 / (1 + (u / σ) ^ 2) * (1 / σ))
          - σ / 2 * ((σ ^ 2 + u ^ 2)⁻¹ * (2 * u)) = Real.arctan (u / σ) := by
      have hne1 : (1 + (u / σ) ^ 2) ≠ 0 := by positivity
      field_simp
      ring
    exact hval ▸ hp1.sub hp2
  have hcont : IntervalIntegrable (fun τ ↦ Real.arctan (τ / σ)) volume 0 t :=
    (Real.continuous_arctan.comp (continuous_id.div_const σ)).intervalIntegrable 0 t
  rw [intervalIntegral.integral_congr (g := fun τ ↦ Real.arctan (τ / σ)) (fun τ _ ↦ harg τ),
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ ↦ hF u) hcont]
  rw [log_one_add_sq_div hσ]
  simp only [zero_mul, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
  ring
theorem continuousAt_digamma {z : ℂ} (hz : 0 < z.re) : ContinuousAt Complex.digamma z :=
  (differentiableAt_digamma hz).continuousAt
private theorem continuous_im_digamma_vertical {σ : ℝ} (hσ : 0 < σ) :
    Continuous (fun τ : ℝ ↦ (Complex.digamma ((σ : ℂ) + (τ : ℂ) * Complex.I)).im) :=
  continuous_iff_continuousAt.mpr fun τ ↦
    (Complex.continuous_im.continuousAt.comp
      (continuousAt_digamma (z := (σ : ℂ) + (τ : ℂ) * Complex.I) (by simpa using hσ))).comp
        (f := fun τ : ℝ ↦ (σ : ℂ) + (τ : ℂ) * Complex.I) (by fun_prop)
private theorem inv_two_z_im {σ : ℝ} (hσ : 0 < σ) (τ : ℝ) :
    ((2 * ((σ : ℂ) + (τ : ℂ) * Complex.I))⁻¹).im = -τ / (2 * (σ ^ 2 + τ ^ 2)) := by
  simp [Complex.inv_im, Complex.normSq_apply]; field_simp [hσ.ne']
private theorem integral_inv_two_z_im {σ : ℝ} (hσ : 0 < σ) (t : ℝ) :
    (∫ τ in (0 : ℝ)..t, ((2 * ((σ : ℂ) + (τ : ℂ) * Complex.I))⁻¹).im)
      = -(1 / 4) * Real.log (1 + t ^ 2 / σ ^ 2) := by
  rw [intervalIntegral.integral_congr (g := fun τ ↦ -τ / (2 * (σ ^ 2 + τ ^ 2)))
    (fun τ _ ↦ inv_two_z_im hσ τ)]
  have hH : ∀ u : ℝ, HasDerivAt (fun u ↦ -(1 / 4) * Real.log (σ ^ 2 + u ^ 2))
      (-u / (2 * (σ ^ 2 + u ^ 2))) u := by
    intro u
    have hval : -(1 / 4) * ((σ ^ 2 + u ^ 2)⁻¹ * (2 * u)) = -u / (2 * (σ ^ 2 + u ^ 2)) := by
      have : (σ ^ 2 + u ^ 2) ≠ 0 := by positivity
      field_simp; ring
    exact hval ▸ (hasDerivAt_log_sq_add hσ u).const_mul (-(1 / 4))
  have hcont : IntervalIntegrable (fun τ ↦ -τ / (2 * (σ ^ 2 + τ ^ 2))) volume 0 t := by
    apply Continuous.intervalIntegrable
    exact Continuous.div (by fun_prop) (by fun_prop) (fun x ↦ by positivity)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ ↦ hH u) hcont]
  rw [log_one_add_sq_div hσ]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero]
  ring
private theorem integral_inv_sq_add {σ : ℝ} (hσ : 0 < σ) (t : ℝ) :
    (∫ τ in (0 : ℝ)..t, (σ ^ 2 + τ ^ 2)⁻¹) = Real.arctan (t / σ) / σ := by
  have hF : ∀ u : ℝ, HasDerivAt (fun u ↦ Real.arctan (u / σ) / σ) ((σ ^ 2 + u ^ 2)⁻¹) u := by
    intro u
    have hval : 1 / (1 + (u / σ) ^ 2) * (1 / σ) / σ = (σ ^ 2 + u ^ 2)⁻¹ := by
      have hσne : σ ≠ 0 := hσ.ne'
      have : (1 + (u / σ) ^ 2) ≠ 0 := by positivity
      field_simp
    exact hval ▸ (hasDerivAt_arctan_div σ u).div_const σ
  have hcont : IntervalIntegrable (fun τ ↦ (σ ^ 2 + τ ^ 2)⁻¹) volume 0 t := by
    apply Continuous.intervalIntegrable
    exact Continuous.inv₀ (by fun_prop) (fun x ↦ by positivity)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ ↦ hF u) hcont]
  simp only [zero_div, Real.arctan_zero, sub_zero]
private noncomputable def imDigammaError (σ τ : ℝ) : ℝ :=
  (Complex.digamma ((σ : ℂ) + (τ : ℂ) * Complex.I) - Complex.log ((σ : ℂ) + (τ : ℂ) * Complex.I)
    + (2 * ((σ : ℂ) + (τ : ℂ) * Complex.I))⁻¹).im
private theorem continuous_im_log_vertical {σ : ℝ} (hσ : 0 < σ) :
    Continuous (fun τ : ℝ ↦ (Complex.log ((σ : ℂ) + (τ : ℂ) * Complex.I)).im) :=
  continuous_iff_continuousAt.mpr fun τ ↦
    Complex.continuous_im.continuousAt.comp
      ((by fun_prop : ContinuousAt (fun τ : ℝ ↦ (σ : ℂ) + (τ : ℂ) * Complex.I) τ).clog
        (Or.inl (by simpa using hσ)))
private theorem continuous_im_inv_two_z {σ : ℝ} (hσ : 0 < σ) :
    Continuous (fun τ : ℝ ↦ ((2 * ((σ : ℂ) + (τ : ℂ) * Complex.I))⁻¹).im) :=
  continuous_iff_continuousAt.mpr fun τ ↦
    Complex.continuous_im.continuousAt.comp
      ((by fun_prop : ContinuousAt (fun τ : ℝ ↦ 2 * ((σ : ℂ) + (τ : ℂ) * Complex.I)) τ).inv₀
        (mul_ne_zero two_ne_zero (Complex.ne_zero_of_re_pos (by simpa using hσ))))
private theorem continuous_imDigammaError {σ : ℝ} (hσ : 0 < σ) :
    Continuous (fun τ : ℝ ↦ imDigammaError σ τ) := by
  unfold imDigammaError; simp only [Complex.add_im, Complex.sub_im]
  exact ((continuous_im_digamma_vertical hσ).sub (continuous_im_log_vertical hσ)).add
    (continuous_im_inv_two_z hσ)
private theorem log_norm_Gamma_vertical_eq {σ : ℝ} (hσ : 0 < σ) (t : ℝ) :
    Real.log ‖Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖
      = Real.log ‖Complex.Gamma (σ : ℂ)‖ - t * Real.arctan (t / σ)
        + (σ / 2 - 1 / 4) * Real.log (1 + t ^ 2 / σ ^ 2)
        - ∫ τ in (0 : ℝ)..t, imDigammaError σ τ := by
  have ii_ψ : IntervalIntegrable
      (fun τ : ℝ ↦ (Complex.digamma ((σ : ℂ) + (τ : ℂ) * Complex.I)).im) volume 0 t :=
    (continuous_im_digamma_vertical hσ).intervalIntegrable 0 t
  have ii_log : IntervalIntegrable
      (fun τ : ℝ ↦ (Complex.log ((σ : ℂ) + (τ : ℂ) * Complex.I)).im) volume 0 t :=
    (continuous_im_log_vertical hσ).intervalIntegrable 0 t
  have ii_inv : IntervalIntegrable
      (fun τ : ℝ ↦ ((2 * ((σ : ℂ) + (τ : ℂ) * Complex.I))⁻¹).im) volume 0 t :=
    (continuous_im_inv_two_z hσ).intervalIntegrable 0 t
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun τ : ℝ ↦ Real.log ‖Complex.Gamma ((σ : ℂ) + (τ : ℂ) * Complex.I)‖)
    (fun x _ ↦ hasDerivAt_log_norm_Gamma_vertical hσ x) ii_ψ.neg
  rw [intervalIntegral.integral_neg, Complex.ofReal_zero, zero_mul, add_zero] at hftc
  have hE : (∫ τ in (0 : ℝ)..t, imDigammaError σ τ)
      = ((∫ τ in (0 : ℝ)..t, (Complex.digamma ((σ : ℂ) + (τ : ℂ) * Complex.I)).im)
          - ∫ τ in (0 : ℝ)..t, (Complex.log ((σ : ℂ) + (τ : ℂ) * Complex.I)).im)
        + ∫ τ in (0 : ℝ)..t, ((2 * ((σ : ℂ) + (τ : ℂ) * Complex.I))⁻¹).im := by
    rw [← intervalIntegral.integral_sub ii_ψ ii_log,
      ← intervalIntegral.integral_add (ii_ψ.sub ii_log) ii_inv]
    exact intervalIntegral.integral_congr fun τ _ ↦ by
      simp only [imDigammaError, Complex.add_im, Complex.sub_im]
  rw [integral_im_log_add_ofReal_mul_I hσ, integral_inv_two_z_im hσ] at hE
  linarith [hftc, hE]
private theorem log_norm_Gamma_bounded {a b : ℝ} (ha : 0 < a) :
    ∃ M : ℝ, ∀ σ ∈ Set.Icc a b, |Real.log ‖Complex.Gamma (σ : ℂ)‖| ≤ M := by
  have hcontOn : ContinuousOn (fun σ : ℝ ↦ Real.log ‖Complex.Gamma (σ : ℂ)‖) (Set.Icc a b) := by
    intro σ hσ
    have hsre : (0 : ℝ) < ((σ : ℂ)).re := by simpa using lt_of_lt_of_le ha hσ.1
    have hΓc : ContinuousAt (fun σ : ℝ ↦ Complex.Gamma (σ : ℂ)) σ :=
      (differentiableAt_Gamma_of_re_pos hsre).continuousAt.comp
        Complex.continuous_ofReal.continuousAt
    exact ((hΓc.norm).log
      (norm_ne_zero_iff.mpr (Complex.Gamma_ne_zero_of_re_pos hsre))).continuousWithinAt
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hcontOn
  exact ⟨M, fun σ hσ ↦ by simpa [Real.norm_eq_abs] using hM σ hσ⟩
private theorem pi_div_two_sub_arctan_bound {b σ t : ℝ} (hσ : 0 < σ) (hσb : σ ≤ b) (ht : 1 ≤ t) :
    0 ≤ Real.pi / 2 * t - t * Real.arctan (t / σ) ∧
    Real.pi / 2 * t - t * Real.arctan (t / σ) ≤ b := by
  have htpos : 0 < t := lt_of_lt_of_le one_pos ht
  have harc_lt : Real.arctan (t / σ) < Real.pi / 2 := Real.arctan_lt_pi_div_two _
  refine ⟨by nlinarith [harc_lt, htpos], ?_⟩
  have hxpos : 0 < t / σ := by positivity
  have hinv : Real.arctan (σ / t) = Real.pi / 2 - Real.arctan (t / σ) := by
    have := Real.arctan_inv_of_pos hxpos
    rwa [inv_div] at this
  have hB : Real.pi / 2 * t - t * Real.arctan (t / σ) = t * Real.arctan (σ / t) := by
    rw [hinv]; ring
  rw [hB]
  have h1 : Real.arctan (σ / t) ≤ σ / t := Real.arctan_le_self (by positivity)
  have h2 : t * Real.arctan (σ / t) ≤ t * (σ / t) := mul_le_mul_of_nonneg_left h1 htpos.le
  have h3 : t * (σ / t) = σ := by field_simp
  linarith [h2, h3, hσb]
private theorem abs_log_growth_term_le {a b σ t : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hσa : a ≤ σ) (hσb : σ ≤ b) (ht : 1 ≤ t) :
    |(σ / 2 - 1 / 4) * Real.log (1 + t ^ 2 / σ ^ 2) - (σ - 1 / 2) * Real.log t|
      ≤ (b / 2 + 1 / 4) * (|Real.log (1 / b ^ 2)| + |Real.log (1 + 1 / a ^ 2)|) := by
  have hσ : 0 < σ := lt_of_lt_of_le ha hσa
  have htpos : 0 < t := lt_of_lt_of_le one_pos ht
  have hb : 0 < b := lt_of_lt_of_le ha hab
  set y := 1 / t ^ 2 + 1 / σ ^ 2 with hy
  have hLid : Real.log (1 + t ^ 2 / σ ^ 2) - 2 * Real.log t = Real.log y := by
    rw [show (1 + t ^ 2 / σ ^ 2) = t ^ 2 * y by rw [hy]; field_simp,
      Real.log_mul (by positivity) (by positivity), Real.log_pow]
    push_cast; ring
  rw [show (σ / 2 - 1 / 4) * Real.log (1 + t ^ 2 / σ ^ 2) - (σ - 1 / 2) * Real.log t
      = (σ / 2 - 1 / 4) * Real.log y by
    rw [show (σ - 1 / 2) = 2 * (σ / 2 - 1 / 4) by ring, ← hLid]; ring, abs_mul]
  have hyU : y ≤ 1 + 1 / a ^ 2 := by
    have h1t : 1 / t ^ 2 ≤ 1 := by rw [div_le_one (by positivity)]; nlinarith [ht]
    have : 1 / σ ^ 2 ≤ 1 / a ^ 2 := one_div_le_one_div_of_le (by positivity) (by nlinarith [hσa])
    rw [hy]; linarith
  have hyL : 1 / b ^ 2 ≤ y := by
    have : 1 / b ^ 2 ≤ 1 / σ ^ 2 := one_div_le_one_div_of_le (by positivity) (by nlinarith [hσb])
    have : (0 : ℝ) < 1 / t ^ 2 := by positivity
    rw [hy]; linarith
  have hlogbound : |Real.log y| ≤ |Real.log (1 / b ^ 2)| + |Real.log (1 + 1 / a ^ 2)| := by
    have hup := Real.log_le_log (show (0 : ℝ) < y by rw [hy]; positivity) hyU
    have hlo := Real.log_le_log (show (0 : ℝ) < 1 / b ^ 2 by positivity) hyL
    rw [abs_le]
    constructor
    · linarith [neg_abs_le (Real.log (1 / b ^ 2)), abs_nonneg (Real.log (1 + 1 / a ^ 2))]
    · linarith [le_abs_self (Real.log (1 + 1 / a ^ 2)), abs_nonneg (Real.log (1 / b ^ 2))]
  exact mul_le_mul (by rw [abs_le]; constructor <;> nlinarith) hlogbound (abs_nonneg _)
    (by linarith)
private theorem abs_integral_imDigammaError_le {a : ℝ} (ha : 0 < a) (C₀ : ℝ) (hC₀ : 0 < C₀)
    (hbound : ∀ s : ℂ, a ≤ s.re →
      ‖Complex.digamma s - Complex.log s + (2 * s)⁻¹‖ ≤ C₀ * ‖s‖ ^ (-(2 : ℤ)))
    {σ : ℝ} (hσa : a ≤ σ) {t : ℝ} (ht : 0 ≤ t) :
    |∫ τ in (0 : ℝ)..t, imDigammaError σ τ| ≤ C₀ * Real.pi / (2 * a) := by
  have hσ : 0 < σ := lt_of_lt_of_le ha hσa
  have hpt : ∀ τ : ℝ, |imDigammaError σ τ| ≤ C₀ * (σ ^ 2 + τ ^ 2)⁻¹ := fun τ ↦ by
    have hsq : ‖(σ : ℂ) + (τ : ℂ) * Complex.I‖ ^ (2 : ℕ) = σ ^ 2 + τ ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_add_mul_I]
    have h2 := hbound ((σ : ℂ) + (τ : ℂ) * Complex.I) (by simpa using hσa)
    rw [show ‖(σ : ℂ) + (τ : ℂ) * Complex.I‖ ^ (-(2 : ℤ)) = (σ ^ 2 + τ ^ 2)⁻¹ by
      rw [zpow_neg, ← hsq]; norm_cast] at h2
    exact le_trans (Complex.abs_im_le_norm _) h2
  have iiE : IntervalIntegrable (fun τ ↦ |imDigammaError σ τ|) volume 0 t :=
    ((continuous_imDigammaError hσ).abs).intervalIntegrable 0 t
  have iiB : IntervalIntegrable (fun τ ↦ C₀ * (σ ^ 2 + τ ^ 2)⁻¹) volume 0 t :=
    (Continuous.mul continuous_const
      (Continuous.inv₀ (by fun_prop) (fun x ↦ by positivity))).intervalIntegrable 0 t
  have harc : Real.arctan (t / σ) ≤ Real.pi / 2 := le_of_lt (Real.arctan_lt_pi_div_two _)
  calc |∫ τ in (0 : ℝ)..t, imDigammaError σ τ|
      ≤ ∫ τ in (0 : ℝ)..t, |imDigammaError σ τ| :=
        intervalIntegral.abs_integral_le_integral_abs ht
    _ ≤ ∫ τ in (0 : ℝ)..t, C₀ * (σ ^ 2 + τ ^ 2)⁻¹ :=
        intervalIntegral.integral_mono_on ht iiE iiB (fun x _ ↦ hpt x)
    _ = C₀ * (Real.arctan (t / σ) / σ) := by
        rw [intervalIntegral.integral_const_mul, integral_inv_sq_add hσ]
    _ ≤ C₀ * (Real.pi / 2 / a) := mul_le_mul_of_nonneg_left (by gcongr) hC₀.le
    _ = C₀ * Real.pi / (2 * a) := by rw [div_div]; ring
theorem log_norm_Gamma_remainder_le {a b M C₀ : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hM : ∀ σ ∈ Set.Icc a b, |Real.log ‖Complex.Gamma (σ : ℂ)‖| ≤ M) (hC₀ : 0 < C₀)
    (hCb : ∀ s : ℂ, a ≤ s.re →
      ‖Complex.digamma s - Complex.log s + (2 * s)⁻¹‖ ≤ C₀ * ‖s‖ ^ (-(2 : ℤ)))
    {σ : ℝ} (hσa : a ≤ σ) (hσb : σ ≤ b) {t : ℝ} (ht : 1 ≤ t) :
    |Real.log ‖Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖
      - ((σ - 1 / 2) * Real.log t - Real.pi / 2 * t)|
      ≤ M + b + (b / 2 + 1 / 4) * (|Real.log (1 / b ^ 2)| + |Real.log (1 + 1 / a ^ 2)|)
        + C₀ * Real.pi / (2 * a) := by
  have hσ : 0 < σ := lt_of_lt_of_le ha hσa
  have ht0 : (0 : ℝ) ≤ t := le_trans zero_le_one ht
  rw [log_norm_Gamma_vertical_eq hσ]
  have hA := abs_le.mp (hM σ ⟨hσa, hσb⟩)
  obtain ⟨hB0, hBb⟩ := pi_div_two_sub_arctan_bound hσ hσb ht
  have hC := abs_le.mp (abs_log_growth_term_le ha hab hσa hσb ht)
  have hD := abs_le.mp (abs_integral_imDigammaError_le ha C₀ hC₀ hCb hσa ht0)
  rw [abs_le]
  refine ⟨?_, ?_⟩ <;> linarith [hA.1, hA.2, hB0, hBb, hC.1, hC.2, hD.1, hD.2]
private theorem log_norm_Gamma_remainder_bounded {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∃ K : ℝ, ∀ σ : ℝ, a ≤ σ → σ ≤ b → ∀ t : ℝ, 1 ≤ t →
      |Real.log ‖Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖
        - ((σ - 1 / 2) * Real.log t - Real.pi / 2 * t)| ≤ K := by
  obtain ⟨M, hM⟩ := log_norm_Gamma_bounded (a := a) (b := b) ha
  have hC₀ : (0 : ℝ) < 1 / 12 + 3 / (2 * Real.pi ^ 2 * a) := by positivity
  have hCb := fun s has ↦ Complex.Stirling.norm_digamma_sub_log_le' ha s has
  exact ⟨_, fun σ hσa hσb t ht ↦ log_norm_Gamma_remainder_le ha hab hM hC₀ hCb hσa hσb ht⟩
private theorem norm_Gamma_vertical_le_of_one_le {a b K : ℝ} (ha : 0 < a)
    (hK : ∀ σ : ℝ, a ≤ σ → σ ≤ b → ∀ t : ℝ, 1 ≤ t →
      |Real.log ‖Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖
        - ((σ - 1 / 2) * Real.log t - Real.pi / 2 * t)| ≤ K)
    {σ : ℝ} (hσa : a ≤ σ) (hσb : σ ≤ b) {τ : ℝ} (hτ : 1 ≤ τ) :
    Real.exp (-K) * τ ^ (σ - 1 / 2) * Real.exp (-(Real.pi / 2) * τ)
        ≤ ‖Complex.Gamma ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ ∧
      ‖Complex.Gamma ((σ : ℂ) + (τ : ℂ) * Complex.I)‖
        ≤ Real.exp K * τ ^ (σ - 1 / 2) * Real.exp (-(Real.pi / 2) * τ) := by
  have hσ : 0 < σ := lt_of_lt_of_le ha hσa
  have hτ0 : 0 < τ := lt_of_lt_of_le one_pos hτ
  have hsre : (0 : ℝ) < ((σ : ℂ) + (τ : ℂ) * Complex.I).re := by simp [hσ]
  have hG : 0 < ‖Complex.Gamma ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ :=
    norm_pos_iff.mpr (Complex.Gamma_ne_zero_of_re_pos hsre)
  set G := ‖Complex.Gamma ((σ : ℂ) + (τ : ℂ) * Complex.I)‖
  set P := τ ^ (σ - 1 / 2) * Real.exp (-(Real.pi / 2) * τ) with hPdef
  have hP : 0 < P := by rw [hPdef]; positivity
  have hlogP : Real.log P = (σ - 1 / 2) * Real.log τ - Real.pi / 2 * τ := by
    rw [hPdef, Real.log_mul (by positivity) (by positivity), Real.log_rpow hτ0, Real.log_exp]
    ring
  have hbnd := hK σ hσa hσb τ hτ
  rw [← hlogP, ← Real.log_div hG.ne' hP.ne'] at hbnd
  obtain ⟨hlo, hhi⟩ := abs_le.mp hbnd
  have heq : Real.exp (Real.log (G / P)) = G / P := Real.exp_log (div_pos hG hP)
  rw [show Real.exp (-K) * τ ^ (σ - 1 / 2) * Real.exp (-(Real.pi / 2) * τ) = Real.exp (-K) * P by
      rw [hPdef]; ring,
    show Real.exp K * τ ^ (σ - 1 / 2) * Real.exp (-(Real.pi / 2) * τ) = Real.exp K * P by
      rw [hPdef]; ring]
  exact ⟨(le_div_iff₀ hP).mp (heq ▸ Real.exp_le_exp.mpr hlo),
    (div_le_iff₀ hP).mp (heq ▸ Real.exp_le_exp.mpr hhi)⟩
theorem norm_Gamma_vertical_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ ≤ c₂ ∧ ∀ σ : ℝ, a ≤ σ → σ ≤ b → ∀ t : ℝ, 1 ≤ |t| →
      c₁ * |t| ^ (σ - 1 / 2) * Real.exp (-(Real.pi / 2) * |t|)
        ≤ ‖Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ∧
      ‖Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖
        ≤ c₂ * |t| ^ (σ - 1 / 2) * Real.exp (-(Real.pi / 2) * |t|) := by
  obtain ⟨K, hK⟩ := log_norm_Gamma_remainder_bounded ha hab
  have hK0 : 0 ≤ K := le_trans (abs_nonneg _) (hK a le_rfl hab 1 le_rfl)
  refine ⟨Real.exp (-K), Real.exp K, Real.exp_pos _,
    Real.exp_le_exp.mpr (by linarith), fun σ hσa hσb t ht ↦ ?_⟩
  have hnorm : ‖Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖
      = ‖Complex.Gamma ((σ : ℂ) + ((|t| : ℝ) : ℂ) * Complex.I)‖ := by
    rcases abs_choice t with h | h <;> rw [h]
    rw [show ((σ : ℂ) + (t : ℂ) * Complex.I)
      = starRingEnd ℂ ((σ : ℂ) + ((-t : ℝ) : ℂ) * Complex.I) by simp,
      Complex.Gamma_conj, Complex.norm_conj]
  rw [hnorm]
  exact norm_Gamma_vertical_le_of_one_le ha hK hσa hσb ht
end Complex
end
end CountPort7
section CountPort8
section
open Complex
namespace Complex
private theorem arg_pi_ne_pi : (↑Real.pi : ℂ).arg ≠ Real.pi := by
  rw [arg_ofReal_of_nonneg Real.pi_pos.le]; exact Real.pi_pos.ne
theorem Gammaℝ_conj (s : ℂ) : Gammaℝ (starRingEnd ℂ s) = starRingEnd ℂ (Gammaℝ s) := by
  rw [Gammaℝ_def, Gammaℝ_def, map_mul,
    show -starRingEnd ℂ s / 2 = starRingEnd ℂ (-s / 2) by simp only [map_div₀, map_neg, map_ofNat],
    show starRingEnd ℂ s / 2 = starRingEnd ℂ (s / 2) by simp only [map_div₀, map_ofNat],
    cpow_conj _ _ arg_pi_ne_pi, Gamma_conj, conj_ofReal]
theorem analyticAt_Gammaℝ {s : ℂ} (hs : 0 < s.re) : AnalyticAt ℂ Gammaℝ s := by
  refine DifferentiableOn.analyticOnNhd (fun z hz ↦ ?_) (Complex.isOpen_re_gt 0) s hs
  have hz2 : 0 < (z / 2).re := by
    have hz0 : (0 : ℝ) < z.re := hz
    rw [div_ofNat_re]; linarith
  exact (DifferentiableAt.const_cpow (differentiableAt_id.neg.div_const 2)
    (Or.inl (by exact_mod_cast Real.pi_ne_zero)) |>.mul
      ((Complex.differentiableAt_Gamma_of_re_pos hz2).comp z
        (differentiableAt_id.div_const 2))).differentiableWithinAt
theorem Gammaℝ_ne_zero_of_im_ne_zero {s : ℂ} (h : s.im ≠ 0) : Gammaℝ s ≠ 0 := by
  rw [Ne, Gammaℝ_eq_zero_iff]
  rintro ⟨n, rfl⟩
  simp at h
end Complex
private theorem completedRiemannZeta_eq_riemannZeta_mul_Gammaℝ {s : ℂ} (hs : s ≠ 0)
    (hΓ : Gammaℝ s ≠ 0) : completedRiemannZeta s = riemannZeta s * Gammaℝ s := by
  rw [riemannZeta_def_of_ne_zero hs, div_mul_cancel₀ _ hΓ]
private theorem conj_completedRiemannZeta₀_conj (s : ℂ) :
    starRingEnd ℂ (completedRiemannZeta₀ (starRingEnd ℂ s)) = completedRiemannZeta₀ s := by
  have hd : Differentiable ℂ fun z ↦ starRingEnd ℂ (completedRiemannZeta₀ (starRingEnd ℂ z)) :=
    fun z ↦ by
      simpa [Function.comp_def] using
        (differentiable_completedZeta₀ (starRingEnd ℂ z)).conj_conj
  refine (hd.differentiableOn.analyticOnNhd isOpen_univ).eqOn_of_preconnected_of_eventuallyEq
    (differentiable_completedZeta₀.differentiableOn.analyticOnNhd isOpen_univ) isPreconnected_univ
    (Set.mem_univ 2) ?_ (Set.mem_univ s)
  rw [Filter.eventuallyEq_iff_exists_mem]
  refine ⟨Complex.re ⁻¹' Set.Ioi 1,
    (continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds (by norm_num), fun t ht ↦ ?_⟩
  have ht : 1 < t.re := ht
  have htc : 1 < (starRingEnd ℂ t).re := by rwa [conj_re]
  have ht0 : t ≠ 0 := fun h ↦ by norm_num [h] at ht
  have htc0 : starRingEnd ℂ t ≠ 0 := by simpa using ht0
  have hΓc : Gammaℝ (starRingEnd ℂ t) ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by linarith)
  have hΓt : Gammaℝ t ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by linarith)
  have e (X : ℂ) : completedRiemannZeta₀ X = completedRiemannZeta X + 1 / X + 1 / (1 - X) := by
    linear_combination -completedRiemannZeta_eq X
  simp only [e, completedRiemannZeta_eq_riemannZeta_mul_Gammaℝ htc0 hΓc,
    completedRiemannZeta_eq_riemannZeta_mul_Gammaℝ ht0 hΓt, map_add, map_mul, map_div₀, map_one,
    map_sub, riemannZeta_conj, Gammaℝ_conj, conj_conj]
theorem completedRiemannZeta₀_conj (s : ℂ) :
    completedRiemannZeta₀ (starRingEnd ℂ s) = starRingEnd ℂ (completedRiemannZeta₀ s) := by
  rw [← conj_completedRiemannZeta₀_conj s, conj_conj]
noncomputable def riemannXi (s : ℂ) : ℂ :=
  (1 / 2) * (s * (s - 1)) * completedRiemannZeta₀ s + 1 / 2
theorem riemannXi_eq_mul_completedRiemannZeta {s : ℂ} (hs₀ : s ≠ 0) (hs₁ : s ≠ 1) :
    riemannXi s = (1 / 2) * (s * (s - 1)) * completedRiemannZeta s := by
  have h₁ : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs₁)
  rw [riemannXi, completedRiemannZeta_eq]
  field_simp
  ring
theorem differentiable_riemannXi : Differentiable ℂ riemannXi :=
  (((differentiable_id.mul (differentiable_id.sub_const 1)).const_mul (1 / 2)).mul
    differentiable_completedZeta₀).add_const (1 / 2)
theorem analyticOnNhd_riemannXi : AnalyticOnNhd ℂ riemannXi Set.univ :=
  differentiable_riemannXi.differentiableOn.analyticOnNhd isOpen_univ
theorem riemannXi_one_sub (s : ℂ) : riemannXi (1 - s) = riemannXi s := by
  simp only [riemannXi, completedRiemannZeta₀_one_sub]
  ring
theorem riemannXi_zero : riemannXi 0 = 1 / 2 := by simp [riemannXi]
theorem riemannXi_one : riemannXi 1 = 1 / 2 := by simp [riemannXi]
theorem riemannXi_conj (s : ℂ) : riemannXi (starRingEnd ℂ s) = starRingEnd ℂ (riemannXi s) := by
  simp [riemannXi, completedRiemannZeta₀_conj, map_ofNat]
theorem riemannXi_eq_prefactor_mul {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hΓ : Gammaℝ s ≠ 0) :
    riemannXi s = (1 / 2) * (s * (s - 1)) * Gammaℝ s * riemannZeta s := by
  rw [riemannXi_eq_mul_completedRiemannZeta hs0 hs1,
    completedRiemannZeta_eq_riemannZeta_mul_Gammaℝ hs0 hΓ]
  ring
private theorem ne_zero_and_ne_one {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) : s ≠ 0 ∧ s ≠ 1 :=
  ⟨fun h ↦ by simp [h] at h0, fun h ↦ by simp [h] at h1⟩
private theorem riemannXi_eq_prefactor_mul_riemannZeta {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    riemannXi s = (1 / 2) * (s * (s - 1)) * Gammaℝ s * riemannZeta s :=
  riemannXi_eq_prefactor_mul (ne_zero_and_ne_one h0 h1).1 (ne_zero_and_ne_one h0 h1).2
    (Gammaℝ_ne_zero_of_re_pos h0)
theorem prefactor_ne_zero_of {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hΓ : Gammaℝ s ≠ 0) :
    (1 / 2 : ℂ) * (s * (s - 1)) * Gammaℝ s ≠ 0 :=
  mul_ne_zero (mul_ne_zero (by norm_num) (mul_ne_zero hs0 (sub_ne_zero.mpr hs1))) hΓ
private theorem prefactor_ne_zero {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    (1 / 2 : ℂ) * (s * (s - 1)) * Gammaℝ s ≠ 0 :=
  prefactor_ne_zero_of (ne_zero_and_ne_one h0 h1).1 (ne_zero_and_ne_one h0 h1).2
    (Gammaℝ_ne_zero_of_re_pos h0)
theorem riemannXi_eq_zero_iff {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    riemannXi s = 0 ↔ riemannZeta s = 0 := by
  rw [riemannXi_eq_prefactor_mul_riemannZeta h0 h1, mul_eq_zero,
    or_iff_right (prefactor_ne_zero h0 h1)]
theorem meromorphicOrderAt_riemannXi_eq_riemannZeta {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    meromorphicOrderAt riemannXi s = meromorphicOrderAt riemannZeta s := by
  have hU : IsOpen {z : ℂ | 0 < z.re ∧ z.re < 1} :=
    (Complex.isOpen_re_gt 0).inter (isOpen_lt continuous_re continuous_const)
  have heq : riemannXi =ᶠ[nhds s]
      (fun z : ℂ ↦ (1 / 2) * (z * (z - 1)) * Gammaℝ z) * riemannZeta := by
    filter_upwards [hU.mem_nhds ⟨h0, h1⟩] with z hz
    simpa only [Pi.mul_apply] using riemannXi_eq_prefactor_mul_riemannZeta hz.1 hz.2
  rw [meromorphicOrderAt_congr (heq.filter_mono nhdsWithin_le_nhds)]
  exact meromorphicOrderAt_mul_of_ne_zero
    ((by fun_prop : AnalyticAt ℂ (fun z : ℂ ↦ (1 / 2 : ℂ) * (z * (z - 1))) s).mul
      (analyticAt_Gammaℝ h0)) (prefactor_ne_zero h0 h1)
end
end CountPort8
section CountPort9
section
open Complex Filter Topology MeasureTheory
noncomputable def logNormZetaIntegral (t : ℝ) : ℝ :=
  ∫ σ in Set.Ioi (1 / 2 : ℝ), Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖
theorem Real.summable_one_div_nat_add_two_rpow {p : ℝ} (hp : 1 < p) :
    Summable (fun n : ℕ ↦ 1 / ((n : ℝ) + 2) ^ p) := by
  refine ((Real.summable_one_div_nat_add_rpow 2 p).mpr hp).congr (fun n ↦ ?_)
  rw [abs_of_nonneg (by positivity)]
theorem Real.antitoneOn_rpow_neg_Icc {σ a b : ℝ} (hσ : 0 ≤ σ) (ha : 0 < a) :
    AntitoneOn (fun x : ℝ ↦ x ^ (-σ)) (Set.Icc a b) := fun x hx _ _ hxy ↦
  Real.rpow_le_rpow_of_nonpos (by simp only [Set.mem_Icc] at hx; linarith [hx.1]) hxy
    (neg_nonpos.mpr hσ)
theorem Real.integral_Ioi_le_tsum_of_window {a : ℕ → ℝ} {f : ℝ → ℝ} {c : ℝ} (k : ℕ)
    (hsum : Summable a) (hInt : IntegrableOn f (Set.Ioi c))
    (hcmp : ∀ N : ℕ, (∫ x in c..(c + (N : ℝ)), f x) ≤ ∑ i ∈ Finset.range N, a (i + k)) :
    (∫ x in Set.Ioi c, f x) ≤ ∑' n, a (n + k) :=
  le_of_tendsto_of_tendsto'
    (intervalIntegral_tendsto_integral_Ioi c hInt
      (tendsto_atTop_add_const_left _ c tendsto_natCast_atTop_atTop))
    ((summable_nat_add_iff k).mpr hsum).hasSum.tendsto_sum_nat hcmp
theorem Real.tsum_le_integral_Ioi_of_window {a : ℕ → ℝ} {f : ℝ → ℝ} {c : ℝ} (k : ℕ)
    (hsum : Summable a) (hInt : IntegrableOn f (Set.Ioi c))
    (hcmp : ∀ N : ℕ, ∑ i ∈ Finset.range N, a (i + k) ≤ ∫ x in c..(c + (N : ℝ)), f x) :
    ∑' n, a (n + k) ≤ ∫ x in Set.Ioi c, f x :=
  le_of_tendsto_of_tendsto'
    ((summable_nat_add_iff k).mpr hsum).hasSum.tendsto_sum_nat
    (intervalIntegral_tendsto_integral_Ioi c hInt
      (tendsto_atTop_add_const_left _ c tendsto_natCast_atTop_atTop)) hcmp
theorem Real.tsum_one_div_nat_add_rpow_le {a : ℝ} (m : ℕ) (hm : 0 < m) (ha : 1 < a) :
    ∑' n : ℕ, 1 / ((n : ℝ) + (m + 1)) ^ a ≤ (m : ℝ) ^ (1 - a) / (a - 1) := by
  have hneg : (-a : ℝ) < -1 := by linarith
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hsum : Summable (fun n : ℕ ↦ 1 / ((n : ℝ) + (m + 1)) ^ a) :=
    ((summable_nat_add_iff (m + 1)).mpr (Real.summable_nat_rpow.mpr hneg)).congr fun n ↦ by
      push_cast; rw [Real.rpow_neg (by positivity), one_div]
  have hcmp : ∀ N : ℕ, ∑ i ∈ Finset.range N, 1 / ((i : ℝ) + (m + 1)) ^ a
      ≤ ∫ x in (m : ℝ)..((m : ℝ) + (N : ℝ)), x ^ (-a) := fun N ↦ by
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun i _ ↦ ?_))
      (Real.antitoneOn_rpow_neg_Icc (by linarith : (0 : ℝ) ≤ a) hm0).sum_le_integral
    rw [show (m : ℝ) + ((i + 1 : ℕ) : ℝ) = (i : ℝ) + (m + 1) by push_cast; ring,
      Real.rpow_neg (by positivity), one_div]
  have hintval : ∫ x in Set.Ioi (m : ℝ), x ^ (-a) = (m : ℝ) ^ (1 - a) / (a - 1) := by
    rw [integral_Ioi_rpow_of_lt hneg hm0, show (-a + 1 : ℝ) = 1 - a by ring,
      div_eq_div_iff (ne_of_lt (by linarith : (1 - a : ℝ) < 0))
        (ne_of_gt (by linarith : (0 : ℝ) < a - 1))]
    ring
  rw [← hintval]
  exact Real.tsum_le_integral_Ioi_of_window 0 hsum (integrableOn_Ioi_rpow_of_lt hneg hm0) hcmp
theorem Real.tsum_one_div_nat_add_two_rpow_le_inv_sub_one {a : ℝ} (ha : 1 < a) :
    ∑' n : ℕ, 1 / ((n : ℝ) + 2) ^ a ≤ 1 / (a - 1) := by
  simpa [Real.one_rpow, one_add_one_eq_two] using Real.tsum_one_div_nat_add_rpow_le 1 one_pos ha
private theorem tendsto_tsum_one_div_nat_add_two_rpow_atTop :
    Tendsto (fun σ : ℝ ↦ ∑' n : ℕ, 1 / ((n : ℝ) + 2) ^ σ) atTop (𝓝 0) := by
  have hab : ∀ k : ℕ, Tendsto (fun σ : ℝ ↦ 1 / ((k : ℝ) + 2) ^ σ) atTop (𝓝 0) := by
    intro k
    have hb0 : -1 < ((k : ℝ) + 2)⁻¹ := by
      have : (0 : ℝ) < ((k : ℝ) + 2)⁻¹ := by positivity
      linarith
    have hb1 : ((k : ℝ) + 2)⁻¹ < 1 := by
      rw [inv_lt_one₀ (by positivity)]; linarith [Nat.cast_nonneg (α := ℝ) k]
    refine (tendsto_rpow_atTop_of_base_lt_one _ hb0 hb1).congr (fun σ ↦ ?_)
    rw [Real.inv_rpow (by positivity), one_div]
  have h_bound : ∀ᶠ σ : ℝ in atTop,
      ∀ k : ℕ, ‖1 / ((k : ℝ) + 2) ^ σ‖ ≤ 1 / ((k : ℝ) + 2) ^ (2 : ℝ) := by
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with σ hσ k
    rw [Real.norm_of_nonneg (by positivity)]
    refine one_div_le_one_div_of_le (by positivity) ?_
    exact Real.rpow_le_rpow_of_exponent_le (by linarith [Nat.cast_nonneg (α := ℝ) k]) hσ
  have := tendsto_tsum_of_dominated_convergence (g := fun _ : ℕ ↦ (0 : ℝ))
    (Real.summable_one_div_nat_add_two_rpow (by norm_num)) hab h_bound
  simpa using this
theorem norm_riemannZeta_sub_one_le {s : ℂ} (hs : 1 < s.re) :
    ‖riemannZeta s - 1‖ ≤ ∑' n : ℕ, 1 / ((n : ℝ) + 2) ^ s.re := by
  have hshift : Summable (fun n : ℕ ↦ 1 / ((n : ℂ) + 1) ^ s) := by
    have h := (summable_nat_add_iff 1).mpr (Complex.summable_one_div_nat_cpow.mpr hs)
    refine h.congr (fun n ↦ ?_)
    push_cast; ring_nf
  have htn : ∀ n : ℕ, ‖(1 : ℂ) / ((n : ℂ) + 2) ^ s‖ = 1 / ((n : ℝ) + 2) ^ s.re := by
    intro n
    rw [norm_div, norm_one]
    congr 1
    rw [show ((n : ℂ) + 2) = ((n + 2 : ℕ) : ℂ) by push_cast; ring,
      norm_natCast_cpow_of_pos (by positivity)]
    push_cast; ring
  have hz : riemannZeta s - 1 = ∑' n : ℕ, 1 / ((n : ℂ) + 2) ^ s := by
    have key : riemannZeta s = 1 + ∑' n : ℕ, 1 / ((n : ℂ) + 2) ^ s := by
      rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs, hshift.tsum_eq_zero_add]
      congr 1
      · simp
      · refine tsum_congr (fun n ↦ ?_); push_cast; ring_nf
    rw [key]; ring
  rw [hz]
  calc ‖∑' n : ℕ, 1 / ((n : ℂ) + 2) ^ s‖
      ≤ ∑' n : ℕ, ‖(1 : ℂ) / ((n : ℂ) + 2) ^ s‖ :=
        norm_tsum_le_tsum_norm
          ((Real.summable_one_div_nat_add_two_rpow hs).congr (fun n ↦ (htn n).symm))
    _ = ∑' n : ℕ, 1 / ((n : ℝ) + 2) ^ s.re := tsum_congr htn
theorem tendsto_riemannZeta_atTop_nhds_one (t : ℝ) :
    Tendsto (fun σ : ℝ ↦ riemannZeta ((σ : ℂ) + Complex.I * t)) atTop (𝓝 1) := by
  have h : Tendsto (fun σ : ℝ ↦ riemannZeta ((σ : ℂ) + Complex.I * t) - 1) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ tendsto_tsum_one_div_nat_add_two_rpow_atTop
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with σ hσ
    have hre : ((σ : ℂ) + Complex.I * t).re = σ := by simp
    have hb := norm_riemannZeta_sub_one_le (s := (σ : ℂ) + Complex.I * t) (by rw [hre]; exact hσ)
    rwa [hre] at hb
  have h1 := h.add_const (1 : ℂ)
  simpa using h1
theorem tendsto_arg_riemannZeta_atTop (t : ℝ) :
    Tendsto (fun σ : ℝ ↦ (riemannZeta ((σ : ℂ) + Complex.I * t)).arg) atTop (𝓝 0) := by
  have hcont : ContinuousAt Complex.arg 1 :=
    Complex.continuousAt_arg (by simp [Complex.mem_slitPlane_iff])
  have := hcont.tendsto.comp (tendsto_riemannZeta_atTop_nhds_one t)
  simpa [Function.comp_def] using this
private theorem tsum_one_div_nat_add_two_sq :
    ∑' n : ℕ, 1 / ((n : ℝ) + 2) ^ 2 = Real.pi ^ 2 / 6 - 1 := by
  have key := Summable.sum_add_tsum_nat_add 2 hasSum_zeta_two.summable
  rw [hasSum_zeta_two.tsum_eq, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_zero] at key
  norm_num at key
  simp only [one_div]
  linarith [key]
theorem Real.tsum_one_div_nat_add_two_rpow_le_mul_tsum {a σ : ℝ} (ha : 1 < a) (hσ : a ≤ σ) :
    ∑' n : ℕ, 1 / ((n : ℝ) + 2) ^ σ ≤ (2 : ℝ) ^ (a - σ) * ∑' n : ℕ, 1 / ((n : ℝ) + 2) ^ a := by
  rw [← tsum_mul_left]
  refine Summable.tsum_le_tsum (fun n ↦ ?_)
    (Real.summable_one_div_nat_add_two_rpow (ha.trans_le hσ))
    ((Real.summable_one_div_nat_add_two_rpow ha).mul_left _)
  have hxpos : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  have hx : (2 : ℝ) ≤ (n : ℝ) + 2 := by linarith [Nat.cast_nonneg (α := ℝ) n]
  rw [show (1 : ℝ) / ((n : ℝ) + 2) ^ σ = ((n : ℝ) + 2) ^ (-σ) by
        rw [Real.rpow_neg hxpos.le, one_div],
    show (2 : ℝ) ^ (a - σ) * (1 / ((n : ℝ) + 2) ^ a)
        = ((n : ℝ) + 2) ^ (-a) * (2 : ℝ) ^ (-(σ - a)) by
      rw [Real.rpow_neg hxpos.le, one_div, show a - σ = -(σ - a) by ring]; ring,
    show (-σ) = (-a) + (-(σ - a)) by ring, Real.rpow_add hxpos]
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_nonpos (by norm_num) hx (by linarith)) (Real.rpow_nonneg hxpos.le _)
theorem Real.tsum_one_div_nat_add_two_rpow_le_mul_exp_neg {a σ : ℝ} (ha : 1 < a) (hσ : a ≤ σ) :
    ∑' n : ℕ, 1 / ((n : ℝ) + 2) ^ σ
      ≤ ((∑' n : ℕ, 1 / ((n : ℝ) + 2) ^ a) * 2 ^ a) * Real.exp (-(Real.log 2 * σ)) := by
  refine (Real.tsum_one_div_nat_add_two_rpow_le_mul_tsum ha hσ).trans (le_of_eq ?_)
  rw [show a - σ = a + (-σ) by ring, Real.rpow_add (by norm_num : (0 : ℝ) < 2),
    show (2 : ℝ) ^ (-σ) = Real.exp (-(Real.log 2 * σ)) by
      rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]; congr 1; ring]
  ring
private theorem tsum_one_div_nat_add_two_rpow_le_mul_rpow {σ : ℝ} (hσ : 2 ≤ σ) :
    ∑' n : ℕ, 1 / ((n : ℝ) + 2) ^ σ ≤ (Real.pi ^ 2 / 6 - 1) * (2 : ℝ) ^ (2 - σ) := by
  have h := Real.tsum_one_div_nat_add_two_rpow_le_mul_tsum (by norm_num : (1 : ℝ) < 2) hσ
  rw [tsum_congr fun n : ℕ ↦ show 1 / ((n : ℝ) + 2) ^ (2 : ℝ) = 1 / ((n : ℝ) + 2) ^ 2 by
        rw [← Real.rpow_natCast]; norm_num,
    tsum_one_div_nat_add_two_sq, mul_comm] at h
  exact h
theorem norm_riemannZeta_sub_one_le_of_two_le_re {s : ℂ} (hs : 2 ≤ s.re) :
    ‖riemannZeta s - 1‖ ≤ Real.pi ^ 2 / 6 - 1 := by
  have h1 : ‖riemannZeta s - 1‖ ≤ ∑' n : ℕ, 1 / ((n : ℝ) + 2) ^ s.re :=
    norm_riemannZeta_sub_one_le (by linarith)
  have h2 : ∑' n : ℕ, 1 / ((n : ℝ) + 2) ^ s.re ≤ (Real.pi ^ 2 / 6 - 1) * (2 : ℝ) ^ (2 - s.re) :=
    tsum_one_div_nat_add_two_rpow_le_mul_rpow hs
  have h3 : (2 : ℝ) ^ (2 - s.re) ≤ 1 := by
    rw [show (1 : ℝ) = (2 : ℝ) ^ (0 : ℝ) from (Real.rpow_zero 2).symm]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hpos : (0 : ℝ) ≤ Real.pi ^ 2 / 6 - 1 := by nlinarith [Real.pi_gt_d2, Real.pi_pos]
  calc ‖riemannZeta s - 1‖ ≤ (Real.pi ^ 2 / 6 - 1) * (2 : ℝ) ^ (2 - s.re) := h1.trans h2
    _ ≤ (Real.pi ^ 2 / 6 - 1) * 1 := mul_le_mul_of_nonneg_left h3 hpos
    _ = Real.pi ^ 2 / 6 - 1 := mul_one _
theorem riemannZeta_mem_slitPlane_of_two_le_re {s : ℂ} (hs : 2 ≤ s.re) :
    riemannZeta s ∈ Complex.slitPlane := by
  have hb := norm_riemannZeta_sub_one_le_of_two_le_re hs
  have hlt : Real.pi ^ 2 / 6 - 1 < 1 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
  have hre : -‖riemannZeta s - 1‖ ≤ (riemannZeta s - 1).re :=
    neg_le_of_abs_le (abs_re_le_norm (riemannZeta s - 1))
  rw [Complex.sub_re, Complex.one_re] at hre
  rw [Complex.mem_slitPlane_iff]
  exact Or.inl (by linarith)
private theorem abs_log_norm_le_two_mul_norm_sub_one {w : ℂ} (hw : ‖w - 1‖ ≤ 1 / 2) :
    |Real.log ‖w‖| ≤ 2 * ‖w - 1‖ := by
  set ε : ℝ := ‖w - 1‖ with hε
  have htri : |‖w‖ - ‖(1 : ℂ)‖| ≤ ε := abs_norm_sub_norm_le w 1
  rw [norm_one, abs_le] at htri
  have hwlb : 1 - ε ≤ ‖w‖ := by linarith [htri.1]
  have hwub : ‖w‖ ≤ 1 + ε := by linarith [htri.2]
  have hwpos : 0 < ‖w‖ := by linarith
  rw [abs_le]
  refine ⟨?_, ?_⟩
  · have h1 := Real.one_sub_inv_le_log_of_pos hwpos
    have h1e : (0 : ℝ) < 1 - ε := by linarith
    have hinv1 := inv_anti₀ h1e hwlb
    have hle : (1 - ε)⁻¹ ≤ 1 + 2 * ε := by rw [inv_le_iff_one_le_mul₀ h1e]; nlinarith
    linarith
  · have h2 := Real.log_le_sub_one_of_pos hwpos
    linarith
theorem abs_log_norm_riemannZeta_le_exp {t σ : ℝ} (hσ : 4 ≤ σ) :
    |Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖|
      ≤ 8 * (Real.pi ^ 2 / 6 - 1) * Real.exp (-(Real.log 2 * σ)) := by
  set w : ℂ := riemannZeta ((σ : ℂ) + Complex.I * t)
  have hre : ((σ : ℂ) + Complex.I * t).re = σ := by simp
  have hb : ‖w - 1‖ ≤ ∑' n : ℕ, 1 / ((n : ℝ) + 2) ^ σ := by
    have hb0 := norm_riemannZeta_sub_one_le (s := (σ : ℂ) + Complex.I * t) (by rw [hre]; linarith)
    rwa [hre] at hb0
  have htl : ∑' n : ℕ, 1 / ((n : ℝ) + 2) ^ σ ≤ (Real.pi ^ 2 / 6 - 1) * (2 : ℝ) ^ (2 - σ) :=
    tsum_one_div_nat_add_two_rpow_le_mul_rpow (by linarith)
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hconv : (2 : ℝ) ^ (2 - σ) = 4 * Real.exp (-(Real.log 2 * σ)) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2),
      show Real.log 2 * (2 - σ) = Real.log 2 * 2 + -(Real.log 2 * σ) by ring, Real.exp_add,
      show Real.log 2 * 2 = Real.log (2 ^ 2) by rw [Real.log_pow]; ring,
      Real.exp_log (by norm_num)]
    norm_num
  have hbound : ‖w - 1‖ ≤ (Real.pi ^ 2 / 6 - 1) * (4 * Real.exp (-(Real.log 2 * σ))) := by
    rw [← hconv]; exact hb.trans htl
  have hsmall : ‖w - 1‖ ≤ 1 / 2 := by
    have hexple : Real.exp (-(Real.log 2 * σ)) ≤ Real.exp (-(Real.log 2 * 4)) := by
      apply Real.exp_le_exp.mpr; nlinarith [hl2]
    have hSle : Real.pi ^ 2 / 6 - 1 ≤ 2 := by nlinarith [Real.pi_lt_four, Real.pi_pos]
    have he4 : (4 : ℝ) * Real.exp (-(Real.log 2 * 4)) ≤ 1 / 4 := by
      have he : Real.exp (-(Real.log 2 * 4)) = (2 : ℝ) ^ (-(4 : ℝ)) := by
        rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]; ring_nf
      rw [he, Real.rpow_neg (by norm_num),
        show (2 : ℝ) ^ (4 : ℝ) = 16 by
          rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num]
      norm_num
    calc ‖w - 1‖ ≤ (Real.pi ^ 2 / 6 - 1) * (4 * Real.exp (-(Real.log 2 * σ))) := hbound
      _ ≤ 2 * (4 * Real.exp (-(Real.log 2 * 4))) := by
            apply mul_le_mul hSle ?_ (by positivity) (by norm_num)
            exact mul_le_mul_of_nonneg_left hexple (by norm_num)
      _ ≤ 2 * (1 / 4) := by linarith [he4]
      _ ≤ 1 / 2 := by norm_num
  calc |Real.log ‖w‖| ≤ 2 * ‖w - 1‖ := abs_log_norm_le_two_mul_norm_sub_one hsmall
    _ ≤ 2 * ((Real.pi ^ 2 / 6 - 1) * (4 * Real.exp (-(Real.log 2 * σ)))) := by linarith [hbound]
    _ = 8 * (Real.pi ^ 2 / 6 - 1) * Real.exp (-(Real.log 2 * σ)) := by ring
theorem Real.integrableOn_exp_neg_mul_Ioi {b : ℝ} (hb : 0 < b) (c : ℝ) :
    IntegrableOn (fun σ : ℝ ↦ Real.exp (-(b * σ))) (Set.Ioi c) := by
  simpa [neg_mul] using exp_neg_integrableOn_Ioi c hb
theorem continuousOn_log_norm_riemannZeta {t : ℝ} {S : Set ℝ}
    (hpole : ∀ σ ∈ S, ((σ : ℂ) + Complex.I * t) ≠ 1)
    (hzero : ∀ σ ∈ S, riemannZeta ((σ : ℂ) + Complex.I * t) ≠ 0) :
    ContinuousOn (fun σ : ℝ ↦ Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖) S := by
  have hpath : Continuous fun σ : ℝ ↦ ((σ : ℂ) + Complex.I * t) :=
    Complex.continuous_ofReal.add continuous_const
  have hcontζ : ContinuousOn (fun σ : ℝ ↦ riemannZeta ((σ : ℂ) + Complex.I * t)) S := by
    have hc : ContinuousOn riemannZeta {s : ℂ | s ≠ 1} :=
      fun s hs ↦ (differentiableAt_riemannZeta hs).continuousAt.continuousWithinAt
    exact hc.comp hpath.continuousOn hpole
  refine Real.continuousOn_log.comp hcontζ.norm (fun σ hσ ↦ ?_)
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff, norm_ne_zero_iff]
  exact hzero σ hσ
theorem integrableOn_log_norm_riemannZeta_Ioi {t : ℝ} (ht : t ≠ 0)
    (hne : ∀ σ : ℝ, (1 / 2 : ℝ) ≤ σ → riemannZeta ((σ : ℂ) + Complex.I * t) ≠ 0) :
    IntegrableOn (fun σ : ℝ ↦ Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖)
      (Set.Ioi (1 / 2 : ℝ)) := by
  set f : ℝ → ℝ := fun σ ↦ Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖ with hf
  have hne1 : ∀ σ : ℝ, ((σ : ℂ) + Complex.I * t) ≠ 1 := by
    intro σ h
    have him : ((σ : ℂ) + Complex.I * t).im = t := by simp
    rw [h] at him; simp only [one_im] at him; exact ht him.symm
  have hfcont : ContinuousOn f (Set.Ici (1 / 2 : ℝ)) :=
    continuousOn_log_norm_riemannZeta (fun σ _ ↦ hne1 σ) (fun σ hσ ↦ hne σ hσ)
  rw [← Set.Ioc_union_Ioi_eq_Ioi (show (1 / 2 : ℝ) ≤ 4 by norm_num)]
  apply IntegrableOn.union
  · exact (ContinuousOn.integrableOn_Icc
      (hfcont.mono Set.Icc_subset_Ici_self)).mono_set Set.Ioc_subset_Icc_self
  · have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
    have hmaj : IntegrableOn
        (fun σ : ℝ ↦ 8 * (Real.pi ^ 2 / 6 - 1) * Real.exp (-(Real.log 2 * σ)))
        (Set.Ioi (4 : ℝ)) := (Real.integrableOn_exp_neg_mul_Ioi hl2 4).const_mul _
    refine Integrable.mono' hmaj ?_ ?_
    · refine (hfcont.mono ?_).aestronglyMeasurable measurableSet_Ioi
      intro x hx
      exact le_of_lt (lt_trans (by norm_num) (Set.mem_Ioi.mp hx))
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with σ hσ
      have hσ4 : (4 : ℝ) < σ := Set.mem_Ioi.mp hσ
      rw [Real.norm_eq_abs, hf]
      exact abs_log_norm_riemannZeta_le_exp hσ4.le
private theorem summable_prime_cpow_neg {s : ℂ} (hs : 1 < s.re) :
    Summable (fun p : Nat.Primes ↦ (p : ℂ) ^ (-s)) := by
  have h : Summable (fun n : ℕ ↦ (n : ℂ) ^ (-s)) := by
    refine (Complex.summable_one_div_nat_cpow.mpr hs).congr (fun n ↦ ?_)
    rw [Complex.cpow_neg, one_div]
  exact h.comp_injective Nat.Primes.coe_nat_injective
theorem neg_tsum_one_div_le_log_norm_riemannZeta {σ t : ℝ} (hσ : 1 < σ) :
    -(∑' n : ℕ, 1 / ((n : ℝ) + 2) ^ σ)
      ≤ Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖ := by
  set s : ℂ := (σ : ℂ) + Complex.I * t with hs_def
  have hsre : s.re = σ := by simp [hs_def]
  have hs1 : 1 < s.re := hsre ▸ hσ
  have hsummand := summable_prime_cpow_neg hs1
  have hlog : Summable (fun p : Nat.Primes ↦ -Complex.log (1 - (p : ℂ) ^ (-s))) :=
    (hsummand.clog_one_sub).neg
  have hre : Summable (fun p : Nat.Primes ↦ (-Complex.log (1 - (p : ℂ) ^ (-s))).re) :=
    (Complex.hasSum_re hlog.hasSum).summable
  have hlogeq : Real.log ‖riemannZeta s‖
      = ∑' p : Nat.Primes, (-Complex.log (1 - (p : ℂ) ^ (-s))).re := by
    have hnorm : ‖riemannZeta s‖
        = Real.exp ((∑' p : Nat.Primes, -Complex.log (1 - (p : ℂ) ^ (-s))).re) := by
      rw [← riemannZeta_eulerProduct_exp_log hs1, Complex.norm_exp]
    rw [hnorm, Real.log_exp, Complex.re_tsum hlog]
  have hterm : ∀ p : Nat.Primes,
      -(1 / (p : ℝ) ^ σ) ≤ (-Complex.log (1 - (p : ℂ) ^ (-s))).re := by
    intro p
    have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.2.one_lt
    have hppos : (0 : ℝ) < (p : ℝ) := by positivity
    have hnormcp : ‖(p : ℂ) ^ (-s)‖ = (p : ℝ) ^ (-σ) := by
      rw [norm_natCast_cpow_of_pos p.2.pos, Complex.neg_re, hsre]
    have hlt1 : (p : ℝ) ^ (-σ) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)
    have hxne1 : (p : ℂ) ^ (-s) ≠ 1 := by
      intro h; rw [h, norm_one] at hnormcp; linarith
    have hwpos : 0 < ‖1 - (p : ℂ) ^ (-s)‖ :=
      norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hxne1))
    have hwle : ‖1 - (p : ℂ) ^ (-s)‖ ≤ 1 + (p : ℝ) ^ (-σ) := by
      calc ‖1 - (p : ℂ) ^ (-s)‖ ≤ ‖(1 : ℂ)‖ + ‖(p : ℂ) ^ (-s)‖ := norm_sub_le _ _
        _ = 1 + (p : ℝ) ^ (-σ) := by rw [norm_one, hnormcp]
    rw [Complex.neg_re, Complex.log_re, neg_le_neg_iff]
    calc Real.log ‖1 - (p : ℂ) ^ (-s)‖
        ≤ Real.log (1 + (p : ℝ) ^ (-σ)) := Real.log_le_log hwpos hwle
      _ ≤ (p : ℝ) ^ (-σ) := by
          have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + (p : ℝ) ^ (-σ) by linarith)
          linarith
      _ = 1 / (p : ℝ) ^ σ := by rw [Real.rpow_neg hppos.le, one_div]
  have hsum_tail : Summable (fun n : ℕ ↦ 1 / ((n : ℝ) + 2) ^ σ) :=
    Real.summable_one_div_nat_add_two_rpow hσ
  have hsum_prime : Summable (fun p : Nat.Primes ↦ 1 / (p : ℝ) ^ σ) :=
    (Real.summable_one_div_nat_rpow.mpr hσ).comp_injective Nat.Primes.coe_nat_injective
  have hcmp3 : ∑' p : Nat.Primes, 1 / (p : ℝ) ^ σ ≤ ∑' n : ℕ, 1 / ((n : ℝ) + 2) ^ σ := by
    have hi : Function.Injective (fun p : Nat.Primes ↦ (p : ℕ) - 2) := by
      intro p q h
      have hp := p.2.two_le
      have hq := q.2.two_le
      simp only at h
      exact Subtype.ext (by lia)
    have h := tsum_comp_le_tsum_of_inj hsum_tail (fun n ↦ by positivity) hi
    refine le_trans (le_of_eq ?_) h
    refine tsum_congr (fun p ↦ ?_)
    have hp2 : 2 ≤ (p : ℕ) := p.2.two_le
    have hcast : (((p : ℕ) - 2 : ℕ) : ℝ) + 2 = (p : ℝ) := by
      rw [Nat.cast_sub hp2]; push_cast; ring
    simp only [Function.comp_apply, hcast]
  rw [hlogeq]
  calc -(∑' n : ℕ, 1 / ((n : ℝ) + 2) ^ σ)
      ≤ -(∑' p : Nat.Primes, 1 / (p : ℝ) ^ σ) := neg_le_neg hcmp3
    _ = ∑' p : Nat.Primes, -(1 / (p : ℝ) ^ σ) := by rw [tsum_neg]
    _ ≤ ∑' p : Nat.Primes, (-Complex.log (1 - (p : ℂ) ^ (-s))).re :=
        Summable.tsum_le_tsum hterm hsum_prime.neg hre
theorem log_norm_riemannZeta_le_tsum_one_div {σ t : ℝ} (hσ : 1 < σ) :
    Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖ ≤ ∑' n : ℕ, 1 / ((n : ℝ) + 2) ^ σ := by
  set s : ℂ := (σ : ℂ) + Complex.I * t with hs_def
  have hsre : s.re = σ := by simp [hs_def]
  have hs1 : 1 < s.re := hsre ▸ hσ
  have htail := norm_riemannZeta_sub_one_le hs1
  rw [hsre] at htail
  have htnn : (0 : ℝ) ≤ ∑' n : ℕ, 1 / ((n : ℝ) + 2) ^ σ := tsum_nonneg (fun n ↦ by positivity)
  have hnorm_le : ‖riemannZeta s‖ ≤ 1 + ∑' n : ℕ, 1 / ((n : ℝ) + 2) ^ σ := by
    calc ‖riemannZeta s‖ = ‖1 + (riemannZeta s - 1)‖ := by congr 1; ring
      _ ≤ ‖(1 : ℂ)‖ + ‖riemannZeta s - 1‖ := norm_add_le _ _
      _ ≤ 1 + ∑' n : ℕ, 1 / ((n : ℝ) + 2) ^ σ := by rw [norm_one]; linarith
  have hpos : 0 < ‖riemannZeta s‖ := norm_pos_iff.mpr (riemannZeta_ne_zero_of_one_le_re hs1.le)
  calc Real.log ‖riemannZeta s‖
      ≤ Real.log (1 + ∑' n : ℕ, 1 / ((n : ℝ) + 2) ^ σ) := Real.log_le_log hpos hnorm_le
    _ ≤ ∑' n : ℕ, 1 / ((n : ℝ) + 2) ^ σ := by
        have := Real.log_le_sub_one_of_pos
          (show (0 : ℝ) < 1 + ∑' n : ℕ, 1 / ((n : ℝ) + 2) ^ σ by linarith)
        linarith
theorem abs_log_norm_riemannZeta_le_tsum_one_div {σ t : ℝ} (hσ : 1 < σ) :
    |Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖| ≤ ∑' n : ℕ, 1 / ((n : ℝ) + 2) ^ σ :=
  abs_le.mpr ⟨neg_tsum_one_div_le_log_norm_riemannZeta hσ,
    log_norm_riemannZeta_le_tsum_one_div hσ⟩
theorem neg_le_logNormZetaIntegral_of_majorant {a C b t : ℝ} {g : ℝ → ℝ}
    (hg_int : IntegrableOn g (Set.Ioi a)) (hgnn : ∀ σ ∈ Set.Ioi a, 0 ≤ g σ)
    (hgC : ∫ σ in Set.Ioi a, g σ ≤ C)
    (hle : ∀ σ ∈ Set.Ioi a, -g σ ≤ Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖)
    (hlog_int : IntegrableOn
      (fun σ : ℝ ↦ Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖) (Set.Ioi a)) :
    (-C ≤ ∫ σ in Set.Ioi a, Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖)
      ∧ (-C ≤ ∫ σ in Set.Ioo a b, Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖) := by
  have hsub : Set.Ioo a b ⊆ Set.Ioi a := fun x hx ↦ hx.1
  have hmono := setIntegral_mono_on hg_int.neg hlog_int measurableSet_Ioi hle
  have hmono' := setIntegral_mono_on (hg_int.mono_set hsub).neg (hlog_int.mono_set hsub)
    measurableSet_Ioo (fun σ hσ ↦ hle σ (hsub hσ))
  simp only [Pi.neg_apply, integral_neg] at hmono hmono'
  have hgle : ∫ σ in Set.Ioo a b, g σ ≤ C := by
    refine le_trans (setIntegral_mono_set hg_int ?_ hsub.eventuallyLE) hgC
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with σ hσ using hgnn σ hσ
  exact ⟨by linarith, by linarith⟩
theorem integrableOn_log_norm_riemannZeta_Ioi_of_one_lt {a : ℝ} (ha : 1 < a) (t : ℝ) :
    IntegrableOn (fun σ : ℝ ↦ Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖)
      (Set.Ioi a) := by
  have hre : ∀ σ : ℝ, ((σ : ℂ) + Complex.I * t).re = σ := fun σ ↦ by simp
  have hcontlog := continuousOn_log_norm_riemannZeta (S := Set.Ioi a)
    (fun σ hσ h ↦ by
      have hσ1 : 1 < σ := lt_trans ha hσ
      have h1 := hre σ
      rw [h, Complex.one_re] at h1
      linarith)
    (fun σ hσ ↦ riemannZeta_ne_zero_of_one_le_re (by rw [hre]; exact (lt_trans ha hσ).le))
  refine Integrable.mono' ((Real.integrableOn_exp_neg_mul_Ioi (Real.log_pos one_lt_two) a).const_mul
      ((∑' n : ℕ, 1 / ((n : ℝ) + 2) ^ a) * 2 ^ a))
    (hcontlog.aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with σ hσ
  rw [Real.norm_eq_abs]
  exact (abs_log_norm_riemannZeta_le_tsum_one_div (lt_trans ha hσ)).trans
    (Real.tsum_one_div_nat_add_two_rpow_le_mul_exp_neg ha hσ.le)
theorem neg_le_logNormZetaIntegral_of_tsum_le {a C b t : ℝ} {g : ℝ → ℝ} (ha : 1 < a)
    (hg_int : IntegrableOn g (Set.Ioi a))
    (hg : ∀ σ ∈ Set.Ioi a, ∑' n : ℕ, 1 / ((n : ℝ) + 2) ^ σ ≤ g σ)
    (hgC : ∫ σ in Set.Ioi a, g σ ≤ C) :
    (-C ≤ ∫ σ in Set.Ioi a, Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖)
      ∧ (-C ≤ ∫ σ in Set.Ioo a b, Real.log ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖) :=
  neg_le_logNormZetaIntegral_of_majorant hg_int
    (fun σ hσ ↦ (tsum_nonneg fun n ↦ by positivity).trans (hg σ hσ)) hgC
    (fun σ hσ ↦ by
      linarith [hg σ hσ, neg_tsum_one_div_le_log_norm_riemannZeta (t := t) (lt_trans ha hσ)])
    (integrableOn_log_norm_riemannZeta_Ioi_of_one_lt ha t)
end
end CountPort9
section CountPort10
public section
namespace Complex
lemma hasDerivAt_ofReal (x : ℝ) : HasDerivAt ofReal 1 x :=
  HasDerivAt.ofReal_comp <| hasDerivAt_id x
lemma deriv_ofReal (x : ℝ) : deriv ofReal x = 1 :=
  (hasDerivAt_ofReal x).deriv
lemma differentiableAt_ofReal (x : ℝ) : DifferentiableAt ℝ ofReal x :=
  (hasDerivAt_ofReal x).differentiableAt
end Complex
lemma DifferentiableAt.comp_ofReal {e : ℂ → ℂ} {z : ℝ} (hf : DifferentiableAt ℂ e z) :
    DifferentiableAt ℝ (fun x : ℝ ↦ e x) z :=
  hf.hasDerivAt.comp_ofReal.differentiableAt
lemma deriv.comp_ofReal {e : ℂ → ℂ} {z : ℝ} (hf : DifferentiableAt ℂ e z) :
    deriv (fun x : ℝ ↦ e x) z = deriv e z :=
  hf.hasDerivAt.comp_ofReal.deriv
lemma Differentiable.comp_ofReal {e : ℂ → ℂ} (h : Differentiable ℂ e) :
    Differentiable ℝ (fun x : ℝ ↦ e x) :=
  fun _ ↦ h.differentiableAt.comp_ofReal
lemma DifferentiableAt.ofReal_comp {z : ℝ} {f : ℝ → ℝ} (hf : DifferentiableAt ℝ f z) :
    DifferentiableAt ℝ (fun (y : ℝ) ↦ (f y : ℂ)) z :=
  hf.hasDerivAt.ofReal_comp.differentiableAt
lemma Differentiable.ofReal_comp {f : ℝ → ℝ} (hf : Differentiable ℝ f) :
    Differentiable ℝ (fun (y : ℝ) ↦ (f y : ℂ)) :=
  fun _ ↦ hf.differentiableAt.ofReal_comp
open Complex ContinuousLinearMap in
lemma HasDerivAt.of_hasDerivAt_ofReal_comp {z : ℝ} {f : ℝ → ℝ} {u : ℂ}
    (hf : HasDerivAt (fun y ↦ (f y : ℂ)) u z) :
    ∃ u' : ℝ, u = u' ∧ HasDerivAt f u' z := by
  lift u to ℝ
  · have H := (imCLM.hasFDerivAt.comp z hf.hasFDerivAt).hasDerivAt.deriv
    simp only [Function.comp_def, imCLM_apply, ofReal_im, deriv_const] at H
    rwa [eq_comm, comp_apply, imCLM_apply, toSpanSingleton_apply_one] at H
  refine ⟨u, rfl, ?_⟩
  convert! (reCLM.hasFDerivAt.comp z hf.hasFDerivAt).hasDerivAt
  rw [comp_apply, toSpanSingleton_apply_one, reCLM_apply, ofReal_re]
lemma DifferentiableAt.ofReal_comp_iff {z : ℝ} {f : ℝ → ℝ} :
    DifferentiableAt ℝ (fun (y : ℝ) ↦ (f y : ℂ)) z ↔ DifferentiableAt ℝ f z := by
  refine ⟨fun H ↦ ?_, ofReal_comp⟩
  obtain ⟨u, _, hu₂⟩ := H.hasDerivAt.of_hasDerivAt_ofReal_comp
  exact HasDerivAt.differentiableAt hu₂
lemma Differentiable.ofReal_comp_iff {f : ℝ → ℝ} :
    Differentiable ℝ (fun (y : ℝ) ↦ (f y : ℂ)) ↔ Differentiable ℝ f :=
  forall_congr' fun _ ↦ DifferentiableAt.ofReal_comp_iff
lemma deriv.ofReal_comp {z : ℝ} {f : ℝ → ℝ} :
    deriv (fun (y : ℝ) ↦ (f y : ℂ)) z = deriv f z := by
  by_cases hf : DifferentiableAt ℝ f z
  · exact hf.hasDerivAt.ofReal_comp.deriv
  · have hf' := mt DifferentiableAt.ofReal_comp_iff.mp hf
    rw [deriv_zero_of_not_differentiableAt hf, deriv_zero_of_not_differentiableAt hf',
      Complex.ofReal_zero]
end
end CountPort10
section CountPort11
section
open Real Complex MeasureTheory Filter Topology BoundedContinuousFunction SchwartzMap  BigOperators
open scoped ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}
@[ext] structure CS (n : ℕ) (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  toFun : ℝ → E
  h1 : ContDiff ℝ n toFun
  h2 : HasCompactSupport toFun
structure trunc extends (CS 2 ℝ) where
  h3 : (Set.Icc (-1) (1)).indicator 1 ≤ toFun
  h4 : toFun ≤ Set.indicator (Set.Ioo (-2) (2)) 1
structure W1 (n : ℕ) (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  toFun : ℝ → E
  smooth : ContDiff ℝ n toFun
  integrable : ∀ ⦃k⦄, k ≤ n → Integrable (iteratedDeriv k toFun)
abbrev W21 := W1 2 ℂ
section lemmas
noncomputable def funscale {E : Type*} (g : ℝ → E) (R x : ℝ) : E := g (R⁻¹ • x)
lemma contDiff_ofReal : ContDiff ℝ ∞ ofReal := by
  have key x : HasDerivAt ofReal 1 x := hasDerivAt_id x |>.ofReal_comp
  have key' : deriv ofReal = fun _ => 1 := by ext x ; exact (key x).deriv
  refine contDiff_infty_iff_deriv.mpr ⟨fun x => (key x).differentiableAt, ?_⟩
  simpa [key'] using contDiff_const
omit [NormedSpace ℝ E] in
lemma tendsto_funscale {f : ℝ → E} (hf : ContinuousAt f 0) (x : ℝ) :
    Tendsto (fun R => funscale f R x) atTop (𝓝 (f 0)) :=
  hf.tendsto.comp (by simpa using tendsto_inv_atTop_zero.mul_const x)
end lemmas
namespace CS
variable {f : CS n E} {R x v : ℝ}
instance : CoeFun (CS n E) (fun _ => ℝ → E) where coe := CS.toFun
instance : Coe (CS n ℝ) (CS n ℂ) where coe f := ⟨fun x => f x,
  contDiff_ofReal.of_le (mod_cast le_top) |>.comp f.h1, f.h2.comp_left (g := ofReal) rfl⟩
def neg (f : CS n E) : CS n E where
  toFun := -f
  h1 := f.h1.neg
  h2 := by simpa [HasCompactSupport, tsupport] using f.h2
instance : Neg (CS n E) where neg := neg
@[simp] lemma neg_apply {x : ℝ} : (-f) x = - (f x) := rfl
def smul (R : ℝ) (f : CS n E) : CS n E := ⟨R • f, f.h1.const_smul R, f.h2.smul_left⟩
instance : HSMul ℝ (CS n E) (CS n E) where hSMul := smul
@[simp] lemma smul_apply : (R • f) x = R • f x := rfl
lemma continuous (f : CS n E) : Continuous f := f.h1.continuous
noncomputable def deriv (f : CS (n + 1) E) : CS n E where
  toFun := _root_.deriv f
  h1 := (contDiff_succ_iff_deriv.mp f.h1).2.2
  h2 := f.h2.deriv
lemma hasDerivAt (f : CS (n + 1) E) (x : ℝ) : HasDerivAt f (f.deriv x) x :=
  (f.h1.differentiable (by simp)).differentiableAt.hasDerivAt
end CS
namespace trunc
instance : CoeFun trunc (fun _ => ℝ → ℝ) where coe f := f.toFun
instance : Coe trunc (CS 2 ℝ) where coe := trunc.toCS
lemma le_one (g : trunc) (x : ℝ) : g x ≤ 1 :=
  (g.h4 x).trans <| Set.indicator_le_self' (by simp) x
lemma zero (g : trunc) : g =ᶠ[𝓝 0] 1 := by
  have : Set.Icc (-1) 1 ∈ 𝓝 (0 : ℝ) := by apply Icc_mem_nhds <;> linarith
  exact eventually_of_mem this (fun x hx => le_antisymm (g.le_one x) (by simpa [hx] using g.h3 x))
@[simp] lemma zero_at {g : trunc} : g 0 = 1 := g.zero.eq_of_nhds
end trunc
namespace W1
instance : CoeFun (W1 n E) (fun _ => ℝ → E) where coe := W1.toFun
lemma continuous (f : W1 n E) : Continuous f := f.smooth.continuous
lemma differentiable (f : W1 (n + 1) E) : Differentiable ℝ f :=
  f.smooth.differentiable (by simp)
lemma iteratedDeriv_sub {f g : ℝ → E} (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g) :
    iteratedDeriv n (f - g) = iteratedDeriv n f - iteratedDeriv n g := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih =>
    have hf' : ContDiff ℝ n (deriv f) := hf.iterate_deriv' n 1
    have hg' : ContDiff ℝ n (deriv g) := hg.iterate_deriv' n 1
    have hfg : deriv (f - g) = deriv f - deriv g := by
      ext x ; apply deriv_sub
      · exact (hf.differentiable (by simp)).differentiableAt
      · exact (hg.differentiable (by simp)).differentiableAt
    simp_rw [iteratedDeriv_succ', ← ih hf' hg', hfg]
noncomputable def deriv (f : W1 (n + 1) E) : W1 n E where
  toFun := _root_.deriv f
  smooth := contDiff_succ_iff_deriv.mp f.smooth |>.2.2
  integrable k hk := by
    simpa [iteratedDeriv_succ'] using f.integrable (Nat.succ_le_succ hk)
lemma hasDerivAt (f : W1 (n + 1) E) (x : ℝ) : HasDerivAt f (f.deriv x) x :=
  f.differentiable.differentiableAt.hasDerivAt
def sub (f g : W1 n E) : W1 n E where
  toFun := f - g
  smooth := f.smooth.sub g.smooth
  integrable k hk := by
    have hf : ContDiff ℝ k f := f.smooth.of_le (by simp [hk])
    have hg : ContDiff ℝ k g := g.smooth.of_le (by simp [hk])
    simpa [iteratedDeriv_sub hf hg] using (f.integrable hk).sub (g.integrable hk)
instance : Sub (W1 n E) where sub := sub
lemma integrable_iteratedDeriv_Schwarz {f : 𝓢(ℝ, ℂ)} : Integrable (iteratedDeriv n f) := by
  induction n generalizing f with
  | zero => exact f.integrable
  | succ n ih => simpa [iteratedDeriv_succ'] using! ih (f := SchwartzMap.derivCLM ℝ ℂ f)
noncomputable def of_Schwartz (f : 𝓢(ℝ, ℂ)) : W1 n ℂ where
  toFun := f
  smooth := f.smooth n
  integrable _ _ := integrable_iteratedDeriv_Schwarz
end W1
namespace W21
variable {f : W21}
noncomputable def norm (f : ℝ → ℂ) : ℝ :=
    (∫ v, ‖f v‖) + (4 * π ^ 2)⁻¹ * (∫ v, ‖deriv (deriv f) v‖)
lemma norm_nonneg {f : ℝ → ℂ} : 0 ≤ norm f :=
  add_nonneg (integral_nonneg (fun t => by simp))
    (mul_nonneg (by positivity) (integral_nonneg (fun t => by simp)))
noncomputable instance : Norm W21 where norm := norm ∘ W1.toFun
noncomputable instance : Coe 𝓢(ℝ, ℂ) W21 where coe := W1.of_Schwartz
def ofCS2 (f : CS 2 ℂ) : W21 := by
  refine ⟨f, f.h1, fun k hk => ?_⟩ ; match k with
  | 0 => exact f.h1.continuous.integrable_of_hasCompactSupport f.h2
  | 1 => simpa using (f.h1.continuous_deriv one_le_two).integrable_of_hasCompactSupport f.h2.deriv
  | 2 => simpa [iteratedDeriv_succ] using
    (f.h1.iterate_deriv' 0 2).continuous.integrable_of_hasCompactSupport f.h2.deriv.deriv
instance : Coe (CS 2 ℂ) W21 where coe := ofCS2
instance : HMul (CS 2 ℂ) W21 (CS 2 ℂ) where
  hMul g f := ⟨g * f, g.h1.mul f.smooth, g.h2.mul_right⟩
instance : HMul (CS 2 ℝ) W21 (CS 2 ℂ) where hMul g f := (g : CS 2 ℂ) * f
lemma hf (f : W21) : Integrable f := f.integrable zero_le_two
lemma hf' (f : W21) : Integrable (deriv f) := by
  simpa [iteratedDeriv_succ] using f.integrable one_le_two
end W21
end
end CountPort11
section CountPort12
section
open FourierTransform Real Complex MeasureTheory Filter Topology BoundedContinuousFunction
  SchwartzMap VectorFourier BigOperators
local instance {E : Type*} : Coe (E → ℝ) (E → ℂ) := ⟨fun f n => f n⟩
section lemmas
@[simp]
theorem nnnorm_eq_of_mem_circle (z : Circle) : ‖z.val‖₊ = 1 := NNReal.coe_eq_one.mp z.norm_coe
@[simp]
theorem nnnorm_circle_smul (z : Circle) (s : ℂ) : ‖z • s‖₊ = ‖s‖₊ := by
  simp [show z • s = z.val * s from rfl]
noncomputable def e (u : ℝ) : ℝ →ᵇ ℂ where
  toFun v := 𝐞 (-v * u)
  map_bounded' :=
    ⟨2, fun x y => (dist_le_norm_add_norm _ _).trans (by simp [one_add_one_eq_two, Circle.norm_coe])⟩
@[simp] lemma e_apply (u : ℝ) (v : ℝ) : e u v = 𝐞 (-v * u) := rfl
theorem hasDerivAt_e {u x : ℝ} : HasDerivAt (e u) (-2 * π * u * I * e u x) x := by
  have l2 : HasDerivAt (fun v => -v * u) (-u) x := by
    simpa only [neg_mul_comm] using hasDerivAt_mul_const (-u)
  convert! (hasDerivAt_fourierChar (-x * u)).scomp x l2 using 1
  change _ = ((-u : ℝ) : ℂ) * _
  simp ; ring
@[simp] lemma F_neg {f : ℝ → ℂ} {u : ℝ} : 𝓕 (fun x => -f x) u = - 𝓕 f u := by
  simp [fourier_eq, integral_neg]
@[simp] lemma F_add {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (x : ℝ) :
    𝓕 (fun x => f x + g x) x = 𝓕 f x + 𝓕 g x := by
  have : Continuous fun p : ℝ × ℝ ↦ ((innerₗ ℝ) p.1) p.2 := continuous_inner
  have := fourierIntegral_add continuous_fourierChar this hf hg
  exact congr_fun this x
@[simp] lemma F_sub {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (x : ℝ) :
    𝓕 (fun x => f x - g x) x = 𝓕 f x - 𝓕 g x := by
  simpa [sub_eq_add_neg, Pi.neg_def] using F_add hf hg.neg x
@[simp] lemma F_mul {f : ℝ → ℂ} {c : ℂ} {u : ℝ} :
    𝓕 (fun x => c * f x) u = c * 𝓕 f u := by
  exact congr_fun (VectorFourier.fourierIntegral_const_smul 𝐞 _ _ f c) u
end lemmas
@[simp] lemma deriv_ofReal : deriv ofReal = fun _ => 1 := by
  ext x ; exact ((hasDerivAt_id x).ofReal_comp).deriv
lemma tendsto_intervalIntegral_zero_of_uniform_norm_bound
    {f : ℝ → ℝ → ℂ} {lo hi : ℝ} {B : ℝ → ℝ}
    (hB : Filter.Tendsto (fun T : ℝ => B T * |hi - lo|) Filter.atTop (nhds 0))
    (hf : ∀ᶠ T in Filter.atTop, ∀ x ∈ Set.uIoc lo hi, ‖f T x‖ ≤ B T) :
    Filter.Tendsto (fun T : ℝ => ∫ x in lo..hi, f T x) Filter.atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun T => norm_nonneg _) ?_ hB
  filter_upwards [hf] with T hT
  exact intervalIntegral.norm_integral_le_of_norm_le_const (fun x hx => hT x hx)
end
end CountPort12
section CountPort13
public section
open Filter Real
theorem Real.tendsto_pow_log_div_pow_atTop (a : ℝ) (b : ℝ) (ha : 0 < a) :
    Filter.Tendsto (fun x ↦ log x ^ b / x^a) Filter.atTop (nhds 0) := by
  apply Asymptotics.isLittleO_iff_tendsto' _|>.mp <| isLittleO_log_rpow_rpow_atTop _ ha
  filter_upwards [eventually_gt_atTop 0] with x hx
  intro h
  rw [rpow_eq_zero hx.le ha.ne.symm] at h
  exfalso
  linarith
end
end CountPort13
section CountPort14
section
open Complex Set Topology
open scoped Interval
variable {z w : ℂ} {c : ℝ}
namespace Rectangle
lemma symm : Rectangle z w = Rectangle w z := by
  simp [Rectangle, uIcc_comm]
end Rectangle
def RectangleBorder (z w : ℂ) : Set ℂ :=
  [[z.re, w.re]] ×ℂ {z.im} ∪ {z.re} ×ℂ [[z.im, w.im]] ∪
    [[z.re, w.re]] ×ℂ {w.im} ∪ {w.re} ×ℂ [[z.im, w.im]]
@[simp]
theorem preimage_equivRealProdCLM_reProdIm (s t : Set ℝ) :
    equivRealProdCLM.symm ⁻¹' (s ×ℂ t) = s ×ˢ t :=
  rfl
@[simp]
theorem ContinuousLinearEquiv.coe_toLinearEquiv_symm {R : Type*} {S : Type*} [Semiring R]
    [Semiring S] {σ : R →+* S} {σ' : S →+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
    (M : Type*) [TopologicalSpace M]
    [AddCommMonoid M] {M₂ : Type*} [TopologicalSpace M₂] [AddCommMonoid M₂] [Module R M]
    [Module S M₂] (e : M ≃SL[σ] M₂) :
    ⇑e.toLinearEquiv.symm = e.symm :=
  rfl
lemma mem_Rect {z w : ℂ} (zRe_lt_wRe : z.re ≤ w.re) (zIm_lt_wIm : z.im ≤ w.im) (p : ℂ) :
    p ∈ Rectangle z w ↔
      z.re ≤ p.re ∧ p.re ≤ w.re ∧ z.im ≤ p.im ∧ p.im ≤ w.im := by
  rw [Rectangle, uIcc_of_le zRe_lt_wRe, uIcc_of_le zIm_lt_wIm]
  exact and_assoc
theorem Set.left_not_mem_uIoo {a b : ℝ} : a ∉ Set.uIoo a b :=
  fun ⟨h1, h2⟩ ↦ (left_lt_sup.mp h2) (le_of_not_ge (inf_lt_left.mp h1))
theorem Set.right_not_mem_uIoo {a b : ℝ} : b ∉ Set.uIoo a b :=
  fun ⟨h1, h2⟩ ↦ (right_lt_sup.mp h2) (le_of_not_ge (inf_lt_right.mp h1))
theorem Set.ne_left_of_mem_uIoo {a b c : ℝ} (hc : c ∈ Set.uIoo a b) : c ≠ a :=
  fun h ↦ Set.left_not_mem_uIoo (h ▸ hc)
theorem Set.ne_right_of_mem_uIoo {a b c : ℝ} (hc : c ∈ Set.uIoo a b) : c ≠ b :=
  fun h ↦ Set.right_not_mem_uIoo (h ▸ hc)
lemma left_mem_rect (z w : ℂ) : z ∈ Rectangle z w := ⟨left_mem_uIcc, left_mem_uIcc⟩
lemma right_mem_rect (z w : ℂ) : w ∈ Rectangle z w := ⟨right_mem_uIcc, right_mem_uIcc⟩
lemma rect_subset_iff {z w z' w' : ℂ} :
    Rectangle z' w' ⊆ Rectangle z w ↔ z' ∈ Rectangle z w ∧ w' ∈ Rectangle z w := by
  use fun h ↦ ⟨h (left_mem_rect z' w'), h (right_mem_rect z' w')⟩
  intro ⟨⟨⟨hz're_ge, hz're_le⟩, ⟨hz'im_ge, hz'im_le⟩⟩,
    ⟨⟨hw're_ge, hw're_le⟩, ⟨hw'im_ge, hw'im_le⟩⟩⟩ x
    ⟨⟨hxre_ge, hxre_le⟩, ⟨hxim_ge, hxim_le⟩⟩
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · exact (le_inf hz're_ge hw're_ge).trans hxre_ge
  · exact (le_sup_iff.mp hxre_le).casesOn (fun h ↦ h.trans hz're_le)
      (fun h ↦ h.trans hw're_le)
  · exact (le_inf hz'im_ge hw'im_ge).trans hxim_ge
  · exact (le_sup_iff.mp hxim_le).casesOn (fun h ↦ h.trans hz'im_le)
      (fun h ↦ h.trans hw'im_le)
set_option linter.style.multiGoal false in
lemma RectSubRect {x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃ : ℝ} (x₀_le_x₁ : x₀ ≤ x₁)
    (x₁_le_x₂ : x₁ ≤ x₂) (x₂_le_x₃ : x₂ ≤ x₃) (y₀_le_y₁ : y₀ ≤ y₁)
    (y₁_le_y₂ : y₁ ≤ y₂) (y₂_le_y₃ : y₂ ≤ y₃) :
    Rectangle (x₁ + y₁ * I) (x₂ + y₂ * I) ⊆
      Rectangle (x₀ + y₀ * I) (x₃ + y₃ * I) := by
  rw [rect_subset_iff, mem_Rect, mem_Rect]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  all_goals simpa using by linarith
lemma RectSubRect' {z₀ z₁ z₂ z₃ : ℂ} (x₀_le_x₁ : z₀.re ≤ z₁.re)
    (x₁_le_x₂ : z₁.re ≤ z₂.re) (x₂_le_x₃ : z₂.re ≤ z₃.re)
    (y₀_le_y₁ : z₀.im ≤ z₁.im) (y₁_le_y₂ : z₁.im ≤ z₂.im)
    (y₂_le_y₃ : z₂.im ≤ z₃.im) :
    Rectangle z₁ z₂ ⊆ Rectangle z₀ z₃ := by
  rw [← re_add_im z₀, ← re_add_im z₁, ← re_add_im z₂, ← re_add_im z₃]
  exact RectSubRect x₀_le_x₁ x₁_le_x₂ x₂_le_x₃ y₀_le_y₁ y₁_le_y₂ y₂_le_y₃
lemma rectangleBorder_subset_rectangle (z w : ℂ) : RectangleBorder z w ⊆ Rectangle z w := by
  intro x hx
  obtain ⟨⟨h | h⟩ | h⟩ | h := hx
  · exact ⟨h.1, h.2 ▸ left_mem_uIcc⟩
  · exact ⟨h.1 ▸ left_mem_uIcc, h.2⟩
  · exact ⟨h.1, h.2 ▸ right_mem_uIcc⟩
  · exact ⟨h.1 ▸ right_mem_uIcc, h.2⟩
lemma rectangle_disjoint_singleton {z w p : ℂ}
    (h : (p.re < z.re ∧ p.re < w.re) ∨ (p.im < z.im ∧ p.im < w.im) ∨
      (z.re < p.re ∧ w.re < p.re) ∨ (z.im < p.im ∧ w.im < p.im)) :
    Disjoint (Rectangle z w) {p} := by
  refine disjoint_singleton_right.mpr (not_and_or.mpr ?_)
  obtain h | h | h | h := h
  · exact Or.inl (notMem_uIcc_of_lt h.1 h.2)
  · exact Or.inr (notMem_uIcc_of_lt h.1 h.2)
  · exact Or.inl (notMem_uIcc_of_gt h.1 h.2)
  · exact Or.inr (notMem_uIcc_of_gt h.1 h.2)
lemma rectangleBorder_disjoint_singleton {z w p : ℂ}
    (h : p.re ≠ z.re ∧ p.re ≠ w.re ∧ p.im ≠ z.im ∧ p.im ≠ w.im) :
    Disjoint (RectangleBorder z w) {p} := by
  refine disjoint_singleton_right.mpr ?_
  simp_rw [RectangleBorder, Set.mem_union, not_or]
  exact ⟨⟨⟨fun hc ↦ h.2.2.1 hc.2, fun hc ↦ h.1 hc.1⟩, fun hc ↦ h.2.2.2 hc.2⟩,
    fun hc ↦ h.2.1 hc.1⟩
lemma rectangle_subset_punctured_rect {z₀ z₁ z₂ z₃ p : ℂ}
    (hz : z₀.re ≤ z₁.re ∧ z₁.re ≤ z₂.re ∧ z₂.re ≤ z₃.re ∧
      z₀.im ≤ z₁.im ∧ z₁.im ≤ z₂.im ∧ z₂.im ≤ z₃.im)
    (hp : (p.re < z₁.re ∧ p.re < z₂.re) ∨ (p.im < z₁.im ∧ p.im < z₂.im) ∨
      (z₁.re < p.re ∧ z₂.re < p.re) ∨ (z₁.im < p.im ∧ z₂.im < p.im)) :
    Rectangle z₁ z₂ ⊆ Rectangle z₀ z₃ \ {p} :=
  Set.subset_sdiff.mpr ⟨by apply RectSubRect' <;> tauto, rectangle_disjoint_singleton hp⟩
lemma rectangleBorder_subset_punctured_rect {z₀ z₁ z₂ z₃ p : ℂ}
    (hz : z₀.re ≤ z₁.re ∧ z₁.re ≤ z₂.re ∧ z₂.re ≤ z₃.re ∧
      z₀.im ≤ z₁.im ∧ z₁.im ≤ z₂.im ∧ z₂.im ≤ z₃.im)
    (hp : p.re ≠ z₁.re ∧ p.re ≠ z₂.re ∧ p.im ≠ z₁.im ∧ p.im ≠ z₂.im) :
    RectangleBorder z₁ z₂ ⊆ Rectangle z₀ z₃ \ {p} :=
  Set.subset_sdiff.mpr ⟨
    (rectangleBorder_subset_rectangle _ _).trans (by apply RectSubRect' <;> tauto),
    rectangleBorder_disjoint_singleton hp⟩
lemma rectangle_mem_nhds_iff {z w p : ℂ} :
    Rectangle z w ∈ 𝓝 p ↔ p ∈ (Set.uIoo z.re w.re) ×ℂ (Set.uIoo z.im w.im) := by
  simp_rw [← mem_interior_iff_mem_nhds, Rectangle, Complex.interior_reProdIm, uIoo, uIcc,
    interior_Icc]
lemma mapsTo_rectangleBorder_left_re (z w : ℂ) :
    MapsTo (fun (y : ℝ) => ↑z.re + ↑y * I) [[z.im, w.im]] (RectangleBorder z w) :=
  (Set.mapsTo_image _ _).mono subset_rfl fun _ ↦
    by simp_all [verticalSegment_eq, RectangleBorder]
lemma mapsTo_rectangleBorder_right_re (z w : ℂ) :
    MapsTo (fun (y : ℝ) => ↑w.re + ↑y * I) [[z.im, w.im]] (RectangleBorder z w) :=
  (Set.mapsTo_image _ _).mono subset_rfl fun _ ↦
    by simp_all [verticalSegment_eq, RectangleBorder]
lemma mapsTo_rectangleBorder_left_im (z w : ℂ) :
    MapsTo (fun (x : ℝ) => ↑x + z.im * I) [[z.re, w.re]] (RectangleBorder z w) :=
  (Set.mapsTo_image _ _).mono subset_rfl fun _ ↦
    by simp_all [horizontalSegment_eq, RectangleBorder]
lemma mapsTo_rectangleBorder_right_im (z w : ℂ) :
    MapsTo (fun (x : ℝ) => ↑x + w.im * I) [[z.re, w.re]] (RectangleBorder z w) :=
  (Set.mapsTo_image _ _).mono subset_rfl fun _ ↦
    by simp_all [horizontalSegment_eq, RectangleBorder]
theorem not_mem_rectangleBorder_of_rectangle_mem_nhds {z w p : ℂ}
    (hp : Rectangle z w ∈ 𝓝 p) :
    p ∉ RectangleBorder z w := by
  refine Set.disjoint_right.mp (rectangleBorder_disjoint_singleton ?_) rfl
  have h1 := rectangle_mem_nhds_iff.mp hp
  exact ⟨Set.ne_left_of_mem_uIoo h1.1, Set.ne_right_of_mem_uIoo h1.1,
    Set.ne_left_of_mem_uIoo h1.2, Set.ne_right_of_mem_uIoo h1.2⟩
end
end CountPort14
section CountPort16
section
open Complex BigOperators Nat Classical Real Topology Filter
open Set MeasureTheory intervalIntegral Asymptotics
open scoped Interval
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f g : ℂ → E} {z w p c A : ℂ}
  {x x₁ x₂ y y₁ y₂ σ : ℝ}
noncomputable def HIntegral (f : ℂ → E) (x₁ x₂ y : ℝ) : E :=
    ∫ x in x₁..x₂, f (x + y * I)
noncomputable def VIntegral (f : ℂ → E) (x y₁ y₂ : ℝ) : E :=
    I • ∫ y in y₁..y₂, f (x + y * I)
lemma HIntegral_symm :
    HIntegral f x₁ x₂ y = -HIntegral f x₂ x₁ y := integral_symm _ _
lemma VIntegral_symm :
    VIntegral f x y₁ y₂ = -VIntegral f x y₂ y₁ := by
  simp_rw [VIntegral, integral_symm y₁ y₂, smul_neg, neg_neg]
noncomputable def RectangleIntegral (f : ℂ → E) (z w : ℂ) : E :=
    HIntegral f z.re w.re z.im - HIntegral f z.re w.re w.im +
    VIntegral f w.re z.im w.im - VIntegral f z.re z.im w.im
noncomputable abbrev RectangleIntegral' (f : ℂ → E) (z w : ℂ) : E :=
    (1 / (2 * π * I)) • RectangleIntegral f z w
abbrev HolomorphicOn (f : ℂ → E) (s : Set ℂ) : Prop :=
    DifferentiableOn ℂ f s
theorem existsDifferentiableOn_of_bddAbove [CompleteSpace E]
    {s : Set ℂ} {c : ℂ} (hc : s ∈ nhds c)
    (hd : HolomorphicOn f (s \ {c}))
    (hb : BddAbove (norm ∘ f '' (s \ {c}))) :
    ∃ (g : ℂ → E),
      HolomorphicOn g s ∧ Set.EqOn f g (s \ {c}) :=
  ⟨Function.update f c (limUnder (𝓝[{c}ᶜ] c) f),
    differentiableOn_update_limUnder_of_bddAbove hc hd hb,
    fun z hz ↦ if h : z = c then (hz.2 h).elim
      else by simp [h]⟩
theorem HolomorphicOn.vanishesOnRectangle [CompleteSpace E]
    {U : Set ℂ} (f_holo : HolomorphicOn f U)
    (hU : Rectangle z w ⊆ U) :
    RectangleIntegral f z w = 0 :=
  integral_boundary_rect_eq_zero_of_differentiableOn f z w
    (f_holo.mono hU)
theorem RectangleIntegral_congr (h : Set.EqOn f g (RectangleBorder z w)) :
    RectangleIntegral f z w = RectangleIntegral g z w := by
  unfold RectangleIntegral VIntegral
  congrm ?_ - ?_ + I • ?_ - I • ?_
  all_goals refine integral_congr fun _ _ ↦ h ?_
  · exact Or.inl <| Or.inl <| Or.inl ⟨by simpa, by simp⟩
  · exact Or.inl <| Or.inr ⟨by simpa, by simp⟩
  · exact Or.inr ⟨by simp, by simpa⟩
  · exact Or.inl <| Or.inl <| Or.inr ⟨by simp, by simpa⟩
theorem RectangleIntegral'_congr (h : Set.EqOn f g (RectangleBorder z w)) :
    RectangleIntegral' f z w = RectangleIntegral' g z w := by
  rw [RectangleIntegral', RectangleIntegral_congr h]
def RectangleBorderIntegrable (f : ℂ → E) (z w : ℂ) : Prop :=
    IntervalIntegrable (fun x => f (x + z.im * I)) volume z.re w.re ∧
    IntervalIntegrable (fun x => f (x + w.im * I)) volume z.re w.re ∧
    IntervalIntegrable (fun y => f (w.re + y * I)) volume z.im w.im ∧
    IntervalIntegrable (fun y => f (z.re + y * I)) volume z.im w.im
theorem RectangleBorderIntegrable.add {f g : ℂ → E}
    (hf : RectangleBorderIntegrable f z w) (hg : RectangleBorderIntegrable g z w) :
    RectangleIntegral (f + g) z w = RectangleIntegral f z w + RectangleIntegral g z w := by
  dsimp [RectangleIntegral, HIntegral, VIntegral]
  have h₁ := intervalIntegral.integral_add hf.1 hg.1
  have h₂ := intervalIntegral.integral_add hf.2.1 hg.2.1
  have h₃ := intervalIntegral.integral_add hf.2.2.1 hg.2.2.1
  have h₄ := intervalIntegral.integral_add hf.2.2.2 hg.2.2.2
  rw [h₁, h₂, h₃, h₄]
  module
omit [NormedSpace ℂ E] in
theorem ContinuousOn.rectangleBorder_integrable (hf : ContinuousOn f (RectangleBorder z w)) :
    RectangleBorderIntegrable f z w :=
  ⟨(hf.comp (by fun_prop) (mapsTo_rectangleBorder_left_im z w)).intervalIntegrable,
    (hf.comp (by fun_prop) (mapsTo_rectangleBorder_right_im z w)).intervalIntegrable,
    (hf.comp (by fun_prop) (mapsTo_rectangleBorder_right_re z w)).intervalIntegrable,
    (hf.comp (by fun_prop) (mapsTo_rectangleBorder_left_re z w)).intervalIntegrable⟩
omit [NormedSpace ℂ E] in
theorem ContinuousOn.rectangleBorderIntegrable (hf : ContinuousOn f (Rectangle z w)) :
    RectangleBorderIntegrable f z w :=
  ContinuousOn.rectangleBorder_integrable (hf.mono (rectangleBorder_subset_rectangle z w))
omit [NormedSpace ℂ E] in
theorem ContinuousOn.rectangleBorderNoPIntegrable
    (hf : ContinuousOn f (Rectangle z w \ {p})) (pNotOnBorder : p ∉ RectangleBorder z w) :
    RectangleBorderIntegrable f z w := by
  refine ContinuousOn.rectangleBorder_integrable (hf.mono (Set.subset_sdiff.mpr ?_))
  exact ⟨rectangleBorder_subset_rectangle z w, disjoint_singleton_right.mpr pNotOnBorder⟩
theorem HolomorphicOn.rectangleBorderIntegrable'
    (hf : HolomorphicOn f (Rectangle z w \ {p})) (hp : Rectangle z w ∈ nhds p) :
    RectangleBorderIntegrable f z w :=
  hf.continuousOn.rectangleBorderNoPIntegrable (not_mem_rectangleBorder_of_rectangle_mem_nhds hp)
theorem HolomorphicOn.rectangleBorderIntegrable (hf : HolomorphicOn f (Rectangle z w)) :
    RectangleBorderIntegrable f z w := hf.continuousOn.rectangleBorderIntegrable
lemma RectangleIntegralHSplit {a x₀ x₁ y₀ y₁ : ℝ}
    (f_int_x₀_a_bot : IntervalIntegrable (fun x => f (↑x + ↑y₀ * I)) volume x₀ a)
    (f_int_a_x₁_bot : IntervalIntegrable (fun x => f (↑x + ↑y₀ * I)) volume a x₁)
    (f_int_x₀_a_top : IntervalIntegrable (fun x => f (↑x + ↑y₁ * I)) volume x₀ a)
    (f_int_a_x₁_top : IntervalIntegrable (fun x => f (↑x + ↑y₁ * I)) volume a x₁) :
    RectangleIntegral f (x₀ + y₀ * I) (x₁ + y₁ * I) =
      RectangleIntegral f (x₀ + y₀ * I) (a + y₁ * I) +
      RectangleIntegral f (a + y₀ * I) (x₁ + y₁ * I) := by
  dsimp [RectangleIntegral, HIntegral, VIntegral]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, mul_one, mul_zero, add_zero, zero_add, sub_self]
  have h₁ := integral_add_adjacent_intervals f_int_x₀_a_bot f_int_a_x₁_bot
  have h₂ := integral_add_adjacent_intervals f_int_x₀_a_top f_int_a_x₁_top
  have h₁' :
      (∫ (x : ℝ) in x₀..a, f (↑x + ↑y₀ * I)) +
          ∫ (x : ℝ) in a..x₁, f (↑y₀ * I + ↑x) =
        ∫ (x : ℝ) in x₀..x₁, f (↑x + ↑y₀ * I) := by
    simpa [add_comm] using h₁
  have h₂' :
      (∫ (x : ℝ) in x₀..a, f (↑x + ↑y₁ * I)) +
          ∫ (x : ℝ) in a..x₁, f (↑y₁ * I + ↑x) =
        ∫ (x : ℝ) in x₀..x₁, f (↑x + ↑y₁ * I) := by
    simpa [add_comm] using h₂
  rw [← h₁', ← h₂']
  have hcomm₁ :
      ∫ (x : ℝ) in a..x₁, f (↑y₀ * I + ↑x) =
        ∫ (x : ℝ) in a..x₁, f (↑x + ↑y₀ * I) := by
    apply intervalIntegral.integral_congr
    intro x _
    exact congrArg f (by ring)
  have hcomm₂ :
      ∫ (x : ℝ) in a..x₁, f (↑y₁ * I + ↑x) =
        ∫ (x : ℝ) in a..x₁, f (↑x + ↑y₁ * I) := by
    apply intervalIntegral.integral_congr
    intro x _
    exact congrArg f (by ring)
  rw [hcomm₁, hcomm₂]
  abel
lemma RectangleIntegralHSplit' {a x₀ x₁ y₀ y₁ : ℝ}
    (ha : a ∈ [[x₀, x₁]])
    (hf : RectangleBorderIntegrable f (↑x₀ + ↑y₀ * I) (↑x₁ + ↑y₁ * I)) :
    RectangleIntegral f (x₀ + y₀ * I) (x₁ + y₁ * I) =
      RectangleIntegral f (x₀ + y₀ * I) (a + y₁ * I) +
      RectangleIntegral f (a + y₀ * I) (x₁ + y₁ * I) :=
  RectangleIntegralHSplit
    (IntervalIntegrable.mono (by simpa using hf.1) (uIcc_subset_uIcc left_mem_uIcc ha) le_rfl)
    (IntervalIntegrable.mono (by simpa using hf.1) (uIcc_subset_uIcc ha right_mem_uIcc) le_rfl)
    (IntervalIntegrable.mono (by simpa using hf.2.1) (uIcc_subset_uIcc left_mem_uIcc ha) le_rfl)
    (IntervalIntegrable.mono (by simpa using hf.2.1) (uIcc_subset_uIcc ha right_mem_uIcc) le_rfl)
lemma RectangleIntegralVSplit {b x₀ x₁ y₀ y₁ : ℝ}
    (f_int_y₀_b_left : IntervalIntegrable (fun y => f (x₀ + y * I)) volume y₀ b)
    (f_int_b_y₁_left : IntervalIntegrable (fun y => f (x₀ + y * I)) volume b y₁)
    (f_int_y₀_b_right : IntervalIntegrable (fun y => f (x₁ + y * I)) volume y₀ b)
    (f_int_b_y₁_right : IntervalIntegrable (fun y => f (x₁ + y * I)) volume b y₁) :
    RectangleIntegral f (x₀ + y₀ * I) (x₁ + y₁ * I) =
      RectangleIntegral f (x₀ + y₀ * I) (x₁ + b * I) +
      RectangleIntegral f (x₀ + b * I) (x₁ + y₁ * I) := by
  dsimp [RectangleIntegral, HIntegral, VIntegral]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, mul_one, mul_zero, add_zero, zero_add, sub_self]
  have h₁ := integral_add_adjacent_intervals f_int_y₀_b_left f_int_b_y₁_left
  have h₂ := integral_add_adjacent_intervals f_int_y₀_b_right f_int_b_y₁_right
  rw [← h₁, ← h₂]
  module
lemma RectangleIntegralVSplit' {b x₀ x₁ y₀ y₁ : ℝ}
    (hb : b ∈ [[y₀, y₁]])
    (hf : RectangleBorderIntegrable f (↑x₀ + ↑y₀ * I) (↑x₁ + ↑y₁ * I)) :
    RectangleIntegral f (x₀ + y₀ * I) (x₁ + y₁ * I) =
      RectangleIntegral f (x₀ + y₀ * I) (x₁ + b * I) +
      RectangleIntegral f (x₀ + b * I) (x₁ + y₁ * I) :=
  RectangleIntegralVSplit
    (IntervalIntegrable.mono (by simpa using hf.2.2.2) (uIcc_subset_uIcc left_mem_uIcc hb) le_rfl)
    (IntervalIntegrable.mono (by simpa using hf.2.2.2) (uIcc_subset_uIcc hb right_mem_uIcc) le_rfl)
    (IntervalIntegrable.mono (by simpa using hf.2.2.1) (uIcc_subset_uIcc left_mem_uIcc hb) le_rfl)
    (IntervalIntegrable.mono (by simpa using hf.2.2.1) (uIcc_subset_uIcc hb right_mem_uIcc) le_rfl)
set_option linter.style.multiGoal false in
lemma RectanglePullToNhdOfPole' [CompleteSpace E] {z₀ z₁ z₂ z₃ p : ℂ}
    (h_orientation : z₀.re ≤ z₃.re ∧ z₀.im ≤ z₃.im ∧
      z₁.re ≤ z₂.re ∧ z₁.im ≤ z₂.im)
    (hp : Rectangle z₁ z₂ ∈ 𝓝 p) (hz : Rectangle z₁ z₂ ⊆ Rectangle z₀ z₃)
    (fHolo : HolomorphicOn f (Rectangle z₀ z₃ \ {p})) :
    RectangleIntegral f z₀ z₃ = RectangleIntegral f z₁ z₂ := by
  obtain ⟨hz₀_re, hz₀_im, hz₁_re, hz₁_im⟩ := h_orientation
  have := rect_subset_iff.mp hz
  rw [Rectangle, uIcc_of_le hz₀_re, uIcc_of_le hz₀_im] at this
  obtain ⟨⟨⟨_, _⟩, ⟨_, _⟩⟩, ⟨_, _⟩, ⟨_, _⟩⟩ := this
  obtain ⟨⟨_, _⟩, ⟨_, _⟩⟩ :=
    (uIoo_of_le hz₁_re) ▸ (uIoo_of_le hz₁_im) ▸ rectangle_mem_nhds_iff.mp hp
  obtain ⟨_, _, _, _⟩ := show
      p.re < z₂.re ∧ p.re < z₃.re ∧ p.im < z₂.im ∧ p.im < z₃.im from
    ⟨by linarith, by linarith, by linarith, by linarith⟩
  obtain ⟨_, _, _, _⟩ := show
      z₀.re < p.re ∧ z₁.re < p.re ∧ z₀.im < p.im ∧ z₁.im < p.im from
    ⟨by linarith, by linarith, by linarith, by linarith⟩
  have fCont := fHolo.continuousOn
  have hbot : RectangleBorderIntegrable f (↑z₀.re + ↑z₀.im * I)
      (↑z₃.re + ↑z₃.im * I) := ?_
  have htop : RectangleBorderIntegrable f (↑z₀.re + ↑z₁.im * I)
      (↑z₃.re + ↑z₃.im * I) := ?_
  have hleft : RectangleBorderIntegrable f (↑z₀.re + ↑z₁.im * I)
      (↑z₃.re + ↑z₂.im * I) := ?_
  have hright : RectangleBorderIntegrable f (↑z₁.re + ↑z₁.im * I)
      (↑z₃.re + ↑z₂.im * I) := ?_
  all_goals try {
    refine ContinuousOn.rectangleBorder_integrable
      (fCont.mono (rectangleBorder_subset_punctured_rect ?_ ?_))
    · simp_all
    · simpa using ⟨by linarith, by linarith, by linarith, by linarith⟩
  }
  have hbot' : z₁.im ∈ [[z₀.im, z₃.im]] := ?_
  have htop' : z₂.im ∈ [[z₁.im, z₃.im]] := ?_
  have hleft' : z₁.re ∈ [[z₀.re, z₃.re]] := ?_
  have hright' : z₂.re ∈ [[z₁.re, z₃.re]] := ?_
  all_goals try {
    rw [Set.uIcc_of_le]
    constructor
    all_goals assumption
  }
  have hbot'' : Rectangle (↑z₀.re + ↑z₀.im * I) (↑z₃.re + ↑z₁.im * I) ⊆
    Rectangle z₀ z₃ \ {p} := ?_
  have htop'' : Rectangle (↑z₀.re + ↑z₂.im * I) (↑z₃.re + ↑z₃.im * I) ⊆
    Rectangle z₀ z₃ \ {p} := ?_
  have hleft'' : Rectangle (↑z₀.re + ↑z₁.im * I) (↑z₁.re + ↑z₂.im * I) ⊆
    Rectangle z₀ z₃ \ {p} := ?_
  have hright'' : Rectangle (↑z₂.re + ↑z₁.im * I) (↑z₃.re + ↑z₂.im * I) ⊆
    Rectangle z₀ z₃ \ {p} := ?_
  all_goals try { apply rectangle_subset_punctured_rect <;> simp_all }
  have h₁ := RectangleIntegralVSplit' hbot' hbot
  have h₂ := fHolo.vanishesOnRectangle hbot''
  have h₃ := RectangleIntegralVSplit' htop' htop
  have h₄ := fHolo.vanishesOnRectangle htop''
  have h₅ := RectangleIntegralHSplit' hleft' hleft
  have h₆ := fHolo.vanishesOnRectangle hleft''
  have h₇ := RectangleIntegralHSplit' hright' hright
  have h₈ := fHolo.vanishesOnRectangle hright''
  simp only [re_add_im] at *
  simp only [h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, zero_add, add_zero]
theorem RectangleIntegral.const_smul (f : ℂ → E) (z w c : ℂ) :
    RectangleIntegral (fun s => c • f s) z w = c • RectangleIntegral f z w := by
  simp [RectangleIntegral, HIntegral, VIntegral, smul_add, smul_sub, smul_smul, mul_comm]
theorem RectangleIntegral.translate (f : ℂ → E) (z w p : ℂ) :
    RectangleIntegral (fun s => f (s - p)) z w = RectangleIntegral f (z - p) (w - p) := by
  simp_rw [RectangleIntegral, HIntegral, VIntegral, sub_re, sub_im,
    ← intervalIntegral.integral_comp_sub_right]
  congr <;> ext <;> congr 1 <;> simp [Complex.ext_iff]
theorem RectangleIntegral.translate' (f : ℂ → E) (z w p : ℂ) :
    RectangleIntegral' (fun s => f (s - p)) z w = RectangleIntegral' f (z - p) (w - p) := by
  simp_rw [RectangleIntegral', RectangleIntegral.translate]
lemma Complex.inv_re_add_im : (x + y * I)⁻¹ = (x - I * y) / (x ^ 2 + y ^ 2) := by
  rw [Complex.inv_def, div_eq_mul_inv]
  congr <;> simp [conj_ofReal, normSq] <;> ring
lemma sq_add_sq_ne_zero (hy : y ≠ 0) : x ^ 2 + y ^ 2 ≠ 0 := by
  linarith [sq_nonneg x, sq_pos_iff.mpr hy]
lemma continuous_self_div_sq_add_sq (hy : y ≠ 0) :
    Continuous fun x => x / (x ^ 2 + y ^ 2) :=
  continuous_id.div (continuous_id.pow 2 |>.add continuous_const) (fun _ => sq_add_sq_ne_zero hy)
lemma integral_self_div_sq_add_sq (hy : y ≠ 0) :
    ∫ x in x₁..x₂, x / (x ^ 2 + y ^ 2) =
    Real.log (x₂ ^ 2 + y ^ 2) / 2 - Real.log (x₁ ^ 2 + y ^ 2) / 2 := by
  let f (x : ℝ) : ℝ := Real.log (x ^ 2 + y ^ 2) / 2
  have e1 {x} := HasDerivAt.add_const (y ^ 2) (by simpa using hasDerivAt_pow 2 x)
  have e2 {x} : HasDerivAt f (x / (x ^ 2 + y ^ 2)) x := by
    convert! (e1.log (sq_add_sq_ne_zero hy)).div_const 2 using 1
    field_simp
  have e3 : deriv f = fun x => x / (x ^ 2 + y ^ 2) := funext (fun _ => e2.deriv)
  have e4 : Continuous (deriv f) := by simpa only [e3] using continuous_self_div_sq_add_sq hy
  simp_rw [← e2.deriv]
  exact integral_deriv_eq_sub (fun _ _ => e2.differentiableAt) (e4.intervalIntegrable _ _)
lemma integral_const_div_sq_add_sq (hy : y ≠ 0) :
    ∫ x in x₁..x₂, y / (x ^ 2 + y ^ 2) = Real.arctan (x₂ / y) - Real.arctan (x₁ / y) := by
  nth_rewrite 1 [← div_mul_cancel₀ x₁ hy, ← div_mul_cancel₀ x₂ hy]
  simp_rw [← mul_integral_comp_mul_right, ← intervalIntegral.integral_const_mul,
    ← integral_one_div_one_add_sq]
  exact integral_congr fun x _ => by
    field_simp
    ring
set_option backward.isDefEq.respectTransparency false in
lemma integral_const_div_self_add_im (hy : y ≠ 0) :
    ∫ x : ℝ in x₁..x₂, A / (x + y * I) =
    A * (Real.log (x₂ ^ 2 + y ^ 2) / 2 - Real.log (x₁ ^ 2 + y ^ 2) / 2) -
    A * I * (Real.arctan (x₂ / y) - Real.arctan (x₁ / y)) := by
  have e1 {x : ℝ} : A / (x + y * I) = A * x / (x ^ 2 + y ^ 2) - A * I * y / (x ^ 2 + y ^ 2) := by
    ring_nf
    simp_rw [inv_re_add_im]
    ring
  have e2 : IntervalIntegrable (fun x ↦ A * x / (x ^ 2 + y ^ 2)) volume x₁ x₂ := by
    apply Continuous.intervalIntegrable
    simp_rw [mul_div_assoc]
    norm_cast
    exact continuous_const.mul (continuous_ofReal.comp (continuous_self_div_sq_add_sq hy))
  have e3 : IntervalIntegrable (fun x ↦ A * I * y / (x ^ 2 + y ^ 2)) volume x₁ x₂ := by
    apply Continuous.intervalIntegrable
    refine continuous_const.div (by fun_prop) (fun x => ?_)
    norm_cast
    exact sq_add_sq_ne_zero hy
  simp_rw [integral_congr (fun _ _ => e1), integral_sub e2 e3, mul_div_assoc]
  norm_cast
  simp_rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal,
    integral_self_div_sq_add_sq hy, integral_const_div_sq_add_sq hy]
lemma integral_const_div_re_add_self (hx : x ≠ 0) :
    ∫ y : ℝ in y₁..y₂, A / (x + y * I) =
    A / I * (Real.log (y₂ ^ 2 + (-x) ^ 2) / 2 - Real.log (y₁ ^ 2 + (-x) ^ 2) / 2) -
    A / I * I * (Real.arctan (y₂ / -x) - Real.arctan (y₁ / -x)) := by
  have l1 {y : ℝ} : A / (x + y * I) = A / I / (y + ↑(-x) * I) := by
    have e1 : x + y * I ≠ 0 := by
      contrapose! hx
      simpa using congr_arg re hx
    have e2 : y + I * ↑(-x) ≠ 0 := by
      contrapose! hx
      simpa using congr_arg im hx
    field_simp [*]
    push_cast
    ring_nf
    simp
  have l2 : -x ≠ 0 := by rwa [neg_ne_zero]
  simp_rw [l1, integral_const_div_self_add_im l2]
lemma ResidueTheoremAtOrigin' {z w c : ℂ}
    (h1 : z.re < 0) (h2 : z.im < 0) (h3 : 0 < w.re) (h4 : 0 < w.im) :
    RectangleIntegral (fun s => c / s) z w = 2 * I * π * c := by
  simp only [RectangleIntegral, HIntegral, VIntegral, smul_eq_mul]
  rw [integral_const_div_re_add_self h1.ne, integral_const_div_re_add_self h3.ne.symm]
  rw [integral_const_div_self_add_im h2.ne, integral_const_div_self_add_im h4.ne.symm]
  have l1 : z.im * w.re⁻¹ = (w.re * z.im⁻¹)⁻¹ := by group
  have l3 := arctan_inv_of_neg <| mul_neg_of_pos_of_neg h3 <| inv_lt_zero.mpr h2
  have l4 : w.im * z.re⁻¹ = (z.re * w.im⁻¹)⁻¹ := by group
  have l6 := arctan_inv_of_neg <| mul_neg_of_neg_of_pos h1 <| inv_pos.mpr h4
  have r1 : z.im * z.re⁻¹ = (z.re * z.im⁻¹)⁻¹ := by group
  have r3 := arctan_inv_of_pos <| mul_pos_of_neg_of_neg h1 <| inv_lt_zero.mpr h2
  have r4 : w.im * w.re⁻¹ = (w.re * w.im⁻¹)⁻¹ := by group
  have r6 := arctan_inv_of_pos <| mul_pos h3 <| inv_pos.mpr h4
  ring_nf
  simp only [one_div, inv_I, mul_neg, neg_mul, I_sq, neg_neg, arctan_neg, ofReal_neg,
    sub_neg_eq_add]
  rw [l1, l3, l4, l6, r1, r3, r4, r6]
  ring_nf
  simp only [I_sq, ofReal_sub, ofReal_mul, ofReal_ofNat, ofReal_div, ofReal_neg, ofReal_one]
  ring_nf
theorem ResidueTheoremInRectangle
    (zRe_le_wRe : z.re ≤ w.re) (zIm_le_wIm : z.im ≤ w.im)
    (pInRectInterior : Rectangle z w ∈ 𝓝 p) :
    RectangleIntegral' (fun s => c / (s - p)) z w = c := by
  simp only [rectangle_mem_nhds_iff, uIoo_of_le zRe_le_wRe, uIoo_of_le zIm_le_wIm,
    mem_reProdIm, mem_Ioo] at pInRectInterior
  rw [RectangleIntegral.translate', RectangleIntegral']
  have : 1 / (2 * ↑π * I) * (2 * I * ↑π * c) = c := by
    field_simp
  rwa [ResidueTheoremAtOrigin']
  all_goals simp [*]
lemma ResidueTheoremOnRectangleWithSimplePole {f g : ℂ → ℂ} {z w p A : ℂ}
    (zRe_le_wRe : z.re ≤ w.re) (zIm_le_wIm : z.im ≤ w.im)
    (pInRectInterior : Rectangle z w ∈ 𝓝 p) (gHolo : HolomorphicOn g (Rectangle z w))
    (principalPart : Set.EqOn (f - fun s ↦ A / (s - p)) g (Rectangle z w \ {p})) :
    RectangleIntegral' f z w = A := by
  have principalPart' : Set.EqOn f (g + (fun s ↦ A / (s - p))) (Rectangle z w \ {p}) :=
    fun s hs => by rw [Pi.add_apply, ← principalPart hs, Pi.sub_apply, sub_add_cancel]
  have : Set.EqOn f (g + (fun s ↦ A / (s - p))) (RectangleBorder z w) :=
    principalPart'.mono <| Set.subset_sdiff.mpr
      ⟨rectangleBorder_subset_rectangle z w,
        disjoint_singleton_right.mpr
          (not_mem_rectangleBorder_of_rectangle_mem_nhds pInRectInterior)⟩
  rw [RectangleIntegral'_congr this]
  have t1 : RectangleBorderIntegrable g z w :=
    gHolo.rectangleBorderIntegrable
  have t2 : HolomorphicOn (fun s ↦ A / (s - p)) (Rectangle z w \ {p}) := by
    apply DifferentiableOn.mono (t := {p}ᶜ)
    · apply DifferentiableOn.div
      · exact differentiableOn_const _
      · exact DifferentiableOn.sub differentiableOn_id (differentiableOn_const _)
      · exact fun x hx => by
          rw [sub_ne_zero]
          exact hx
    · rintro s ⟨_, hs⟩
      exact hs
  have t3 : RectangleBorderIntegrable (fun s ↦ A / (s - p)) z w :=
    HolomorphicOn.rectangleBorderIntegrable' t2 pInRectInterior
  rw [RectangleIntegral', RectangleBorderIntegrable.add t1 t3, smul_add]
  rw [gHolo.vanishesOnRectangle (by rfl), smul_zero, zero_add]
  exact ResidueTheoremInRectangle zRe_le_wRe zIm_le_wIm pInRectInterior
lemma IsBigO_to_BddAbove {f : ℂ → ℂ} {p : ℂ}
    (f_near_p : f =O[𝓝[≠] p] (1 : ℂ → ℂ)) :
    ∃ U ∈ 𝓝 p, BddAbove (norm ∘ f '' (U \ {p})) := by
  simp only [isBigO_iff, Pi.one_apply, one_mem, CStarRing.norm_of_mem_unitary, mul_one] at f_near_p
  obtain ⟨c, hc⟩ := f_near_p
  dsimp [Filter.Eventually, nhdsWithin] at hc
  rw [mem_inf_principal'] at hc
  obtain ⟨U, hU, ⟨U_is_open, p_in_U⟩⟩ := mem_nhds_iff.mp hc
  use U
  constructor
  · exact IsOpen.mem_nhds U_is_open p_in_U
  · refine bddAbove_def.mpr ?_
    use c
    intro y hy
    simp only [Function.comp_apply, mem_image, Set.mem_sdiff, mem_singleton_iff] at hy
    obtain ⟨x, ⟨x_in_U, x_not_p⟩, fxy⟩ := hy
    rw [← fxy]
    simpa [x_not_p] using hU x_in_U
theorem BddAbove_on_rectangle_of_bdd_near {z w p : ℂ} {f : ℂ → ℂ}
    (f_cont : ContinuousOn f (Rectangle z w \ {p}))
    (f_near_p : f =O[𝓝[≠] p] (1 : ℂ → ℂ)) :
    BddAbove (norm ∘ f '' (Rectangle z w \ {p})) := by
  obtain ⟨V, V_in_nhds, V_prop⟩ := IsBigO_to_BddAbove f_near_p
  rw [mem_nhds_iff] at V_in_nhds
  obtain ⟨W, W_subset, W_open, p_in_W⟩ := V_in_nhds
  set U := Rectangle z w
  have : U \ {p} = (U \ W) ∪ ((U ∩ W) \ {p}) := by
    ext x
    simp only [Set.mem_sdiff, mem_singleton_iff, mem_union, mem_inter_iff]
    constructor
    · intro ⟨xu, x_not_p⟩
      tauto
    · intro h
      rcases h with ⟨h1, h2⟩ | ⟨⟨h1, h2⟩, h3⟩
      · refine ⟨h1, ?_⟩
        intro h
        rw [← h] at p_in_W
        exact h2 p_in_W
      · tauto
  rw [this, image_union]
  apply BddAbove.union
  · apply IsCompact.bddAbove_image
    · apply IsCompact.diff _ W_open
      exact IsCompact.reProdIm isCompact_uIcc isCompact_uIcc
    · apply f_cont.norm.mono
      apply Set.sdiff_subset_sdiff_right
      simpa
  · exact V_prop.mono
      (image_mono <| Set.sdiff_subset_sdiff_left <| subset_trans inter_subset_right W_subset)
theorem ResidueTheoremOnRectangleWithSimplePole' {f : ℂ → ℂ} {z w p A : ℂ}
    (zRe_le_wRe : z.re ≤ w.re) (zIm_le_wIm : z.im ≤ w.im)
    (pInRectInterior : Rectangle z w ∈ 𝓝 p) (fHolo : HolomorphicOn f (Rectangle z w \ {p}))
    (near_p : (f - (fun s ↦ A / (s - p))) =O[𝓝[≠] p] (1 : ℂ → ℂ)) :
    RectangleIntegral' f z w = A := by
  set g := f - (fun s ↦ A / (s - p))
  have gHolo : HolomorphicOn g (Rectangle z w \ {p}) := by
    apply DifferentiableOn.sub fHolo
    intro s hs
    have : s - p ≠ 0 := sub_ne_zero.mpr hs.2
    exact  DifferentiableWithinAt.div (by fun_prop) (by fun_prop) this
  have := BddAbove_on_rectangle_of_bdd_near gHolo.continuousOn near_p
  obtain ⟨h, ⟨hHolo, hEq⟩⟩ := existsDifferentiableOn_of_bddAbove pInRectInterior gHolo this
  exact ResidueTheoremOnRectangleWithSimplePole zRe_le_wRe zIm_le_wIm pInRectInterior hHolo hEq
def HasSimplePolesOn (f : ℂ → ℂ) (s : Set ℂ) : Prop :=
  ∀ z ∈ s, (-1 : ℤ) ≤ meromorphicOrderAt f z
lemma HasSimplePolesOn.mono {f : ℂ → ℂ} {s t : Set ℂ}
    (h : HasSimplePolesOn f t) (hst : s ⊆ t) : HasSimplePolesOn f s := by
  intro z hz
  exact h z (hst hz)
end
end CountPort16
section CountPort17
section
open Finset Interval MeasureTheory
variable {𝕜 : Type*} [RCLike 𝕜] {f : ℝ → 𝕜} {a b : ℝ}
noncomputable def B1 (x : ℝ) : ℝ := x - ⌊x⌋₊ - 1 / 2
@[fun_prop]
lemma aestronglyMeasurable_B1 : AEStronglyMeasurable B1 := by
  unfold B1
  fun_prop
lemma abs_B1_le_half {x : ℝ} (hx : 0 ≤ x) : |B1 x| ≤ 1 / 2 := by
  unfold B1
  refine abs_le.mpr ⟨?_, ?_⟩
  · grind [Nat.floor_le hx]
  · grind [Nat.lt_succ_floor x]
lemma integral_deriv_mul_add_const (c : 𝕜) (hab : a ≤ b) (h_int : IntervalIntegrable (deriv f) volume a b)
    (hf_diff : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t) :
    ∫ t in a..b, (t + c) * deriv f t = (b + c) * f b - (a + c) * f a - ∫ t in a..b, f t := by
  rw [← Set.uIcc_of_le hab] at hf_diff
  have : ∀ t ∈ [[a, b]], HasDerivAt (fun (t : ℝ) ↦ t + c) 1 t := by
    intro t ht
    simp only [hasDerivAt_add_const_iff]
    convert! ContinuousLinearMap.hasDerivAt (RCLike.ofRealCLM (K := 𝕜)) using 1
    simp
  replace hf_diff := fun t ht ↦ (hf_diff t ht).hasDerivAt
  rw [intervalIntegral.integral_mul_deriv_eq_deriv_mul this hf_diff (by simp) h_int]
  simp
lemma intervalIntegrable_deriv_mul_B1 (ha : 0 ≤ a) (hab : a ≤ b) (h_cont : ContinuousOn (deriv f) [[a, b]]) :
    IntervalIntegrable (fun t ↦ deriv f t * B1 t) volume a b := by
  refine IntervalIntegrable.continuousOn_mul ?_ h_cont
  rw [intervalIntegrable_iff']
  apply MeasureTheory.Measure.integrableOn_of_bounded (by simp) (by fun_prop) (M := 1 / 2)
  filter_upwards [self_mem_ae_restrict (by measurability)] with x hx
  rw [Set.uIcc_of_le hab, Set.mem_Icc] at hx
  norm_cast
  exact abs_B1_le_half (by linarith)
lemma integral_deriv_mul_floor_add_one (ha : 0 ≤ a) (hab : a ≤ b)
    (hf_diff : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t) (h_cont : ContinuousOn (deriv f) [[a, b]]) :
    ∫ t in a..b, deriv f t * (⌊t⌋₊ + 1) = (b + 1 / 2) * f b - (a + 1 / 2) * f a - (∫ t in a..b, f t) - ∫ t in a..b, deriv f t * B1 t := by
  calc
  _ = ∫ t in a..b, (deriv f t * (t + 1 / 2) -deriv f t * B1 t) := by
    congr
    ext
    simp only [B1]
    push_cast
    ring
  _ = (∫ t in a..b, deriv f t * (t + 1 / 2)) - ∫ t in a..b, deriv f t * B1 t := by
    exact intervalIntegral.integral_sub (ContinuousOn.intervalIntegrable (by fun_prop)) (intervalIntegrable_deriv_mul_B1 ha hab h_cont)
  _ = _ := by
    conv => lhs; arg 1; arg 1; ext; rw [mul_comm]
    rw [integral_deriv_mul_add_const _ hab h_cont.intervalIntegrable hf_diff]
theorem sum_eq_integral_add_integral_deriv (ha : 0 ≤ a) (hab : a ≤ b)
    (hf_diff : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t)
    (h_cont : ContinuousOn (deriv f) [[a, b]]) :
    ∑ k ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, f k =
      f a * B1 a - f b * B1 b + (∫ t in a..b, f t) + ∫ t in a..b, deriv f t * B1 t  := by
  have := sum_mul_eq_sub_sub_integral_mul (fun _ ↦ 1) ha hab hf_diff (Set.uIcc_of_le hab ▸ h_cont).integrableOn_Icc
  simp only [mul_one, sum_const, Nat.card_Icc, tsub_zero, nsmul_eq_mul, Nat.cast_add,
    Nat.cast_one] at this
  rw [this, ← intervalIntegral.integral_of_le hab]
  rw [integral_deriv_mul_floor_add_one ha hab hf_diff h_cont]
  unfold B1
  push_cast
  ring
end
end CountPort17
section CountPort18
section
set_option lang.lemmaCmd true
open Complex Topology Filter Interval Set Asymptotics
lemma div_cpow_eq_cpow_neg (a x s : ℂ) : a / x ^ s = a * x ^ (-s) := by
  rw [div_eq_mul_inv, cpow_neg]
lemma div_rpow_eq_rpow_neg (a x s : ℝ) (hx : 0 ≤ x) : a / x ^ s = a * x ^ (-s) := by
  rw [div_eq_mul_inv, Real.rpow_neg hx]
lemma div_rpow_neg_eq_rpow_div {x y s : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    x ^ (-s) / y ^ (-s) = (y / x) ^ s := by
  rw [div_eq_mul_inv, Real.rpow_neg hx, Real.rpow_neg hy, Real.div_rpow hy hx]; field_simp
lemma div_rpow_eq_rpow_div_neg {x y s : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    x ^ s / y ^ s = (y / x) ^ (-s) := by
  convert div_rpow_neg_eq_rpow_div (s := -s) hx hy using 1; simp only [neg_neg]
local notation (name := riemannzeta) "ζ" => riemannZeta
local notation (name := derivriemannzeta) "ζ'" => deriv riemannZeta
theorem analyticAt_riemannZeta {s : ℂ} (s_ne_one : s ≠ 1) :
  AnalyticAt ℂ riemannZeta s := by
  apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
  filter_upwards [eventually_ne_nhds s_ne_one] with z hz using differentiableAt_riemannZeta hz
theorem differentiableAt_deriv_riemannZeta {s : ℂ} (s_ne_one : s ≠ 1) :
    DifferentiableAt ℂ ζ' s := by
  exact (analyticAt_riemannZeta s_ne_one).deriv.differentiableAt
noncomputable def riemannZeta0 (N : ℕ) (s : ℂ) : ℂ :=
  (∑ n ∈ Finset.range (N + 1), 1 / (n : ℂ) ^ s) +
  (- N ^ (1 - s)) / (1 - s) + (- N ^ (-s)) / 2
      + s * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1)
local notation (name := riemannzeta0) "ζ₀" => riemannZeta0
lemma riemannZeta0_apply (N : ℕ) (s : ℂ) : ζ₀ N s =
    (∑ n ∈ Finset.range (N + 1), 1 / (n : ℂ) ^ s) +
    ((- N ^ (1 - s)) / (1 - s) + (- N ^ (-s)) / 2
      + s * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-(s + 1))) := by
  simp_rw [riemannZeta0, div_cpow_eq_cpow_neg]; ring
lemma Real.differentiableAt_cpow_const_of_ne (s : ℂ) {x : ℝ} (xpos : 0 < x) :
    DifferentiableAt ℝ (fun (x : ℝ) ↦ (x : ℂ) ^ s) x := by
  apply DifferentiableAt.comp_ofReal (e := fun z ↦ z ^ s)
  apply DifferentiableAt.cpow (by simp) (by simp) (by simp [xpos])
lemma Complex.one_div_cpow_eq {s : ℂ} {x : ℝ} (x_ne : x ≠ 0) :
    1 / (x : ℂ) ^ s = (x : ℂ) ^ (-s) := by
  refine (eq_one_div_of_mul_eq_one_left ?_).symm
  rw [← cpow_add _ _ <| mod_cast x_ne, neg_add_cancel, cpow_zero]
lemma sum_eq_int_deriv {φ : ℝ → ℂ} {a b : ℝ} (apos : 0 ≤ a) (a_lt_b : a < b)
    (φDiff : ∀ x ∈ [[a, b]], HasDerivAt φ (deriv φ x) x)
    (derivφCont : ContinuousOn (deriv φ) [[a, b]]) :
    ∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, φ n =
      (∫ x in a..b, φ x) + (⌊b⌋₊ + 1 / 2 - b) * φ b - (⌊a⌋₊ + 1 / 2 - a) * φ a
        - ∫ x in a..b, (⌊x⌋ + 1 / 2 - x) * deriv φ x := by
  rw [uIcc_of_le a_lt_b.le] at φDiff
  convert sum_eq_integral_add_integral_deriv apos a_lt_b.le (fun t ht ↦ (φDiff t ht).differentiableAt) derivφCont using 1
  unfold B1
  push_cast
  suffices ∫ (x : ℝ) in a..b, (↑⌊x⌋ + 1 / 2 - ↑x) * deriv φ x = -∫ (t : ℝ) in a..b, deriv φ t * (↑t - ↑⌊t⌋₊ - 1 / 2) by
    rw [this]
    ring_nf!
  rw [← intervalIntegral.integral_neg]
  refine intervalIntegral.integral_congr fun x hx ↦ ?_
  rw [uIcc_of_le a_lt_b.le, mem_Icc] at hx
  rw [← Int.natCast_floor_eq_floor (by linarith)]
  norm_cast
  push_cast
  ring
lemma xpos_of_uIcc {a b : ℕ} (ha : a ∈ Ioo 0 b) {x : ℝ} (x_in : x ∈ [[(a : ℝ), b]]) :
    0 < x := by
  rw [uIcc_of_le (by exact_mod_cast ha.2.le), mem_Icc] at x_in
  linarith [(by exact_mod_cast ha.1 : (0 : ℝ) < a)]
lemma ZetaSum_aux1₁ {a b : ℕ} {s : ℂ} (s_ne_one : s ≠ 1) (ha : a ∈ Ioo 0 b) :
    (∫ (x : ℝ) in a..b, 1 / (x : ℂ) ^ s) =
    (b ^ (1 - s) - a ^ (1 - s)) / (1 - s) := by
  convert integral_cpow (a := a) (b := b) (r := -s) ?_ using 1
  · refine intervalIntegral.integral_congr fun x hx ↦ one_div_cpow_eq ?_
    exact (xpos_of_uIcc ha hx).ne'
  · norm_cast; ring_nf
  · right; refine ⟨(by grind), ?_⟩
    exact fun hx ↦ (lt_self_iff_false 0).mp <| xpos_of_uIcc ha hx
lemma ZetaSum_aux1φDiff {s : ℂ} {x : ℝ} (xpos : 0 < x) :
    HasDerivAt (fun (t : ℝ) ↦ 1 / (t : ℂ) ^ s) (deriv (fun (t : ℝ) ↦ 1 / (t : ℂ) ^ s) x) x := by
  exact hasDerivAt_deriv_iff.mpr <|
    DifferentiableAt.div (differentiableAt_const _)
      (Real.differentiableAt_cpow_const_of_ne s xpos) (by simp [cpow_eq_zero_iff, xpos.ne'])
lemma ZetaSum_aux1φderiv {s : ℂ} (s_ne_zero : s ≠ 0) {x : ℝ} (xpos : 0 < x) :
    deriv (fun (t : ℝ) ↦ 1 / (t : ℂ) ^ s) x = (fun (x : ℝ) ↦ -s * (x : ℂ) ^ (-(s + 1))) x := by
  let r := -s - 1
  have r_add1_ne_zero : r + 1 ≠ 0 := fun hr ↦ by simp [neg_ne_zero.mpr s_ne_zero, r] at hr
  have r_ne_neg1 : r ≠ -1 := fun hr ↦ (hr ▸ r_add1_ne_zero) <| by norm_num
  have hasDeriv := hasDerivAt_ofReal_cpow_const' xpos.ne' r_ne_neg1
  have := hasDeriv.deriv ▸ deriv_const_mul (-s) (hasDeriv).differentiableAt
  convert! this using 2
  · ext y
    by_cases y_zero : (y : ℂ) = 0
    · simp only [y_zero, ne_eq, s_ne_zero, not_false_eq_true, zero_cpow, div_zero,
      r_add1_ne_zero, zero_div, mul_zero]
    · have : (y : ℂ) ^ s ≠ 0 := fun hy ↦ y_zero ((cpow_eq_zero_iff _ _).mp hy).1
      simp only [one_div, sub_add_cancel, cpow_neg, neg_mul, r]
      field_simp
  · simp only [r]
    ring_nf
lemma ZetaSum_aux1derivφCont {s : ℂ} (s_ne_zero : s ≠ 0) {a b : ℕ} (ha : a ∈ Ioo 0 b) :
    ContinuousOn (deriv (fun (t : ℝ) ↦ 1 / (t : ℂ) ^ s)) [[a, b]] := by
  have : EqOn _ (fun (t : ℝ) ↦ -s * (t : ℂ) ^ (-(s + 1))) [[a, b]] :=
    fun x hx ↦ ZetaSum_aux1φderiv s_ne_zero <| xpos_of_uIcc ha hx
  refine continuous_ofReal.continuousOn.cpow_const ?_ |>.const_smul (c := -s) |>.congr this
  exact fun x hx ↦ ofReal_mem_slitPlane.mpr <| xpos_of_uIcc ha hx
set_option backward.isDefEq.respectTransparency false in
lemma ZetaSum_aux1 {a b : ℕ} {s : ℂ} (s_ne_one : s ≠ 1) (s_ne_zero : s ≠ 0) (ha : a ∈ Ioo 0 b) :
    ∑ n ∈ Finset.Ioc a b, 1 / (n : ℂ) ^ s =
    (b ^ (1 - s) - a ^ (1 - s)) / (1 - s) + 1 / 2 * (1 / b ^ (s)) - 1 / 2 * (1 / a ^ s)
      + s * ∫ x in a..b, (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-(s + 1)) := by
  let φ := fun (x : ℝ) ↦ 1 / (x : ℂ) ^ s
  let φ' := fun (x : ℝ) ↦ -s * (x : ℂ) ^ (-(s + 1))
  have xpos : ∀ x ∈ [[(a : ℝ), b]], 0 < x := fun x hx ↦ xpos_of_uIcc ha hx
  have φDiff : ∀ x ∈ [[(a : ℝ), b]], HasDerivAt φ (deriv φ x) x :=
    fun x hx ↦ ZetaSum_aux1φDiff (xpos x hx)
  have φderiv : ∀ x ∈ [[(a : ℝ), b]], deriv φ x = φ' x := by
    exact fun x hx ↦ ZetaSum_aux1φderiv s_ne_zero (xpos x hx)
  have derivφCont : ContinuousOn (deriv φ) [[a, b]] := ZetaSum_aux1derivφCont s_ne_zero ha
  convert sum_eq_int_deriv (by linarith) (by exact_mod_cast ha.2) φDiff derivφCont using 1
  · congr <;> simp only [Nat.floor_natCast]
  · rw [Nat.floor_natCast, Nat.floor_natCast, ← intervalIntegral.integral_const_mul]
    simp_rw [mul_div, ← mul_div, φ, ZetaSum_aux1₁ s_ne_one ha]
    conv => rhs; rw [sub_eq_add_neg]
    congr; any_goals norm_cast; simp only [one_div, add_sub_cancel_left]
    rw [← intervalIntegral.integral_neg, intervalIntegral.integral_congr]
    simp only [φ, one_div] at φderiv
    intro x hx; simp_rw [φderiv x hx, φ']; ring_nf
lemma ZetaSum_aux1_1' {a b x : ℝ} (apos : 0 < a) (hx : x ∈ Icc a b) : 0 < x :=
  lt_of_lt_of_le apos hx.1
lemma ZetaSum_aux1_1 {a b x : ℝ} (apos : 0 < a) (a_lt_b : a < b) (hx : x ∈ [[a, b]]) : 0 < x :=
  lt_of_lt_of_le apos (uIcc_of_le a_lt_b.le ▸ hx).1
lemma ZetaSum_aux1_2 {a b : ℝ} {c : ℝ} (apos : 0 < a) (a_lt_b : a < b)
    (h : c ≠ 0 ∧ 0 ∉ [[a, b]]) :
    ∫ (x : ℝ) in a..b, 1 / x ^ (c+1) = (a ^ (-c) - b ^ (-c)) / c := by
  rw [(by ring : (a ^ (-c) - b ^ (-c)) / c = (b ^ (-c) - a ^ (-c)) / (-c))]
  have := integral_rpow (a := a) (b := b) (r := -c-1) (Or.inr ⟨by simp [h.1], h.2⟩)
  simp only [sub_add_cancel] at this
  rw [← this]
  apply intervalIntegral.integral_congr
  intro x hx
  have : 0 ≤ x := (ZetaSum_aux1_1 apos a_lt_b hx).le
  simp [div_rpow_eq_rpow_neg _ _ _ this, sub_eq_add_neg, add_comm]
lemma ZetaSum_aux1_3 (x : ℝ) : ‖(⌊x⌋ + 1/2 - x)‖ ≤ 1/2 :=
  abs_le.mpr ⟨(by linarith [Int.lt_floor_add_one x]), (by linarith [Int.floor_le x])⟩
lemma ZetaSum_aux1_4' (x : ℝ) (hx : 0 < x) (s : ℂ) :
      ‖(⌊x⌋ + 1 / 2 - (x : ℝ)) / (x : ℂ) ^ (s + 1)‖ =
      ‖⌊x⌋ + 1 / 2 - x‖ / x ^ ((s + 1).re) := by
  simp_rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hx, ← norm_real]
  simp
lemma ZetaSum_aux1_4 {a b : ℝ} (apos : 0 < a) (a_lt_b : a < b) {s : ℂ} :
  ∫ (x : ℝ) in a..b, ‖(↑⌊x⌋ + (1 : ℝ) / 2 - ↑x) / (x : ℂ) ^ (s + 1)‖ =
    ∫ (x : ℝ) in a..b, |⌊x⌋ + 1 / 2 - x| / x ^ (s + 1).re := by
  apply intervalIntegral.integral_congr
  exact fun x hx ↦ ZetaSum_aux1_4' x (ZetaSum_aux1_1 apos a_lt_b hx) s
lemma ZetaSum_aux1_5a {a b : ℝ} (apos : 0 < a) {s : ℂ} (x : ℝ)
  (h : x ∈ Icc a b) : |↑⌊x⌋ + 1 / 2 - x| / x ^ (s.re + 1) ≤ 1 / x ^ (s.re + 1) := by
  apply div_le_div_of_nonneg_right _ _
  · exact le_trans (ZetaSum_aux1_3 x) (by norm_num)
  · apply Real.rpow_nonneg <| le_of_lt (ZetaSum_aux1_1' apos h)
lemma ZetaSum_aux1_5b {a b : ℝ} (apos : 0 < a) (a_lt_b : a < b) {s : ℂ} (σpos : 0 < s.re) :
  IntervalIntegrable (fun u ↦ 1 / u ^ (s.re + 1)) MeasureTheory.volume a b := by
  refine continuousOn_const.div ?_ ?_ |>.intervalIntegrable_of_Icc (le_of_lt a_lt_b)
  · exact continuousOn_id.rpow_const fun x hx ↦ Or.inl (ne_of_gt <| ZetaSum_aux1_1' apos hx)
  · exact fun x hx h ↦ by rw [Real.rpow_eq_zero] at h <;> linarith [ZetaSum_aux1_1' apos hx]
open MeasureTheory in
lemma measurable_floor_add_half_sub : Measurable fun (u : ℝ) ↦ ↑⌊u⌋ + 1 / 2 - u := by
  refine Measurable.add ?_ measurable_const |>.sub measurable_id
  exact Measurable.comp (by exact fun _ _ ↦ trivial) Int.measurable_floor
open MeasureTheory in
lemma ZetaSum_aux1_5c {a b : ℝ} {s : ℂ} :
    let g : ℝ → ℝ := fun u ↦ |↑⌊u⌋ + 1 / 2 - u| / u ^ (s.re + 1);
    AEStronglyMeasurable g
      (Measure.restrict volume (Ι a b)) := by
  intro
  refine (Measurable.div ?_ <| measurable_id.pow_const _).aestronglyMeasurable
  exact _root_.continuous_abs.measurable.comp measurable_floor_add_half_sub
lemma ZetaSum_aux1_5d {a b : ℝ} (apos : 0 < a) (a_lt_b : a < b) {s : ℂ} (σpos : 0 < s.re) :
  IntervalIntegrable (fun u ↦ |↑⌊u⌋ + 1 / 2 - u| / u ^ (s.re + 1)) MeasureTheory.volume a b := by
  set g : ℝ → ℝ := (fun u ↦ |↑⌊u⌋ + 1 / 2 - u| / u ^ (s.re + 1))
  apply ZetaSum_aux1_5b apos a_lt_b σpos |>.mono_fun ZetaSum_aux1_5c ?_
  filter_upwards with x
  simp only [Real.norm_eq_abs, one_div, norm_inv, abs_div, _root_.abs_abs]
  conv => rw [div_eq_mul_inv, ← one_div]; rhs; rw [← one_mul |x ^ (s.re + 1)|⁻¹]
  refine mul_le_mul ?_ (le_refl _) (by simp) <| by norm_num
  exact le_trans (ZetaSum_aux1_3 x) <| by norm_num
lemma ZetaSum_aux1_5 {a b : ℝ} (apos : 0 < a) (a_lt_b : a < b) {s : ℂ} (σpos : 0 < s.re) :
  ∫ (x : ℝ) in a..b, |⌊x⌋ + 1 / 2 - x| / x ^ (s.re + 1) ≤
    ∫ (x : ℝ) in a..b, 1 / x ^ (s.re + 1) := by
  apply intervalIntegral.integral_mono_on (le_of_lt a_lt_b) ?_ ?_
  · exact ZetaSum_aux1_5a apos
  · exact ZetaSum_aux1_5d apos a_lt_b σpos
  · exact ZetaSum_aux1_5b apos a_lt_b σpos
lemma ZetaBnd_aux1a {a b : ℝ} (apos : 0 < a) (a_lt_b : a < b) {s : ℂ} (σpos : 0 < s.re) :
    ∫ x in a..b, ‖(⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1)‖ ≤
      (a ^ (-s.re) - b ^ (-s.re)) / s.re := by
  calc
    _ = ∫ x in a..b, |(⌊x⌋ + 1 / 2 - x)| / x ^ (s+1).re := ZetaSum_aux1_4 apos a_lt_b
    _ ≤ ∫ x in a..b, 1 / x ^ (s.re + 1) := ZetaSum_aux1_5 apos a_lt_b σpos
    _ = (a ^ (-s.re) - b ^ (-s.re)) / s.re := ?_
  refine ZetaSum_aux1_2 (c := s.re) apos a_lt_b ⟨ne_of_gt σpos, ?_⟩
  exact fun h ↦ (lt_self_iff_false 0).mp <| ZetaSum_aux1_1 apos a_lt_b h
lemma Finset.Ioc_eq_Ico (M N : ℕ) : Finset.Ioc N M = Finset.Ico (N + 1) (M + 1) := by
  ext a; simp only [Finset.mem_Ioc, Finset.mem_Ico]; constructor <;> intro ⟨h₁, h₂⟩ <;> omega
lemma finsetSum_tendsto_tsum {N : ℕ} {f : ℕ → ℂ} (hf : Summable f) :
    Tendsto (fun (k : ℕ) ↦ ∑ n ∈ Finset.Ico N k, f n) atTop (𝓝 (∑' (n : ℕ), f (n + N))) := by
  have := Summable.hasSum_iff_tendsto_nat hf (m := ∑' (n : ℕ), f n) |>.mp hf.hasSum
  have const := tendsto_const_nhds (α := ℕ) (x := ∑ i ∈ Finset.range N, f i) (f := atTop)
  have := Filter.Tendsto.sub this const
  rw [← hf.sum_add_tsum_nat_add N, add_comm, add_sub_cancel_right] at this
  apply this.congr'
  filter_upwards [Filter.mem_atTop (N + 1)]
  intro M hM
  rw [Finset.sum_Ico_eq_sub]
  linarith
lemma Complex.cpow_tendsto {s : ℂ} (s_re_gt : 1 < s.re) :
    Tendsto (fun (x : ℕ) ↦ (x : ℂ) ^ (1 - s)) atTop (𝓝 0) := by
  have one_sub_s_re_ne : (1 - s).re ≠ 0 := by simp only [sub_re, one_re]; linarith
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp_rw [Complex.norm_natCast_cpow_of_re_ne_zero _ (one_sub_s_re_ne)]
  rw [(by simp only [sub_re, one_re, neg_sub] : (1 - s).re = - (s - 1).re)]
  apply (tendsto_rpow_neg_atTop _).comp tendsto_natCast_atTop_atTop; simp [s_re_gt]
lemma Complex.cpow_inv_tendsto {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun (x : ℕ) ↦ ((x : ℂ) ^ s)⁻¹) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp_rw [norm_inv, Complex.norm_natCast_cpow_of_re_ne_zero _ <| ne_of_gt hs]
  apply Filter.Tendsto.inv_tendsto_atTop
  exact (tendsto_rpow_atTop hs).comp tendsto_natCast_atTop_atTop
lemma ZetaSum_aux2a : ∃ C, ∀ (x : ℝ), ‖⌊x⌋ + 1 / 2 - x‖ ≤ C := by
  use 1 / 2; exact ZetaSum_aux1_3
lemma ZetaSum_aux3 {N : ℕ} {s : ℂ} (s_re_gt : 1 < s.re) :
    Tendsto (fun k ↦ ∑ n ∈ Finset.Ioc N k, 1 / (n : ℂ) ^ s) atTop
    (𝓝 (∑' (n : ℕ), 1 / (n + N + 1 : ℂ) ^ s)) := by
  let f := fun (n : ℕ) ↦ 1 / (n : ℂ) ^ s
  have hf := summable_one_div_nat_cpow.mpr s_re_gt
  simp_rw [Finset.Ioc_eq_Ico]
  convert finsetSum_tendsto_tsum (f := fun n ↦ f (n + 1)) (N := N) ?_ using 1
  · ext k
    rw [Finset.sum_Ico_add']
  · congr; ext n; simp only [one_div, Nat.cast_add, Nat.cast_one, f]
  · rwa [summable_nat_add_iff (k := 1)]
lemma integrableOn_of_Zeta0_fun {N : ℕ} (N_pos : 0 < N) {s : ℂ} (s_re_gt : 0 < s.re) :
    MeasureTheory.IntegrableOn (fun (x : ℝ) ↦ (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-(s + 1))) (Ioi N)
    MeasureTheory.volume := by
  obtain ⟨c, hc⟩ := ZetaSum_aux2a
  apply MeasureTheory.Integrable.bdd_mul (c := c) ?_ ?_
  · apply MeasureTheory.ae_of_all
    convert hc; simp only [← Complex.norm_real]; simp
  · apply integrableOn_Ioi_cpow_iff (by positivity) |>.mpr (by simp [s_re_gt])
  · refine Measurable.add ?_ measurable_const |>.sub (by fun_prop) |>.aestronglyMeasurable
    exact Measurable.comp (by exact fun _ _ ↦ trivial) Int.measurable_floor
lemma ZetaSum_aux2 {N : ℕ} (N_pos : 0 < N) {s : ℂ} (s_re_gt : 1 < s.re) :
    ∑' (n : ℕ), 1 / (n + N + 1 : ℂ) ^ s =
    (- N ^ (1 - s)) / (1 - s) - N ^ (-s) / 2
      + s * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-(s + 1)) := by
  have s_ne_zero : s ≠ 0 := fun hs ↦ by linarith [zero_re ▸ hs ▸ s_re_gt]
  have s_ne_one : s ≠ 1 := fun hs ↦ (lt_self_iff_false _).mp <| one_re ▸ hs ▸ s_re_gt
  apply tendsto_nhds_unique (X := ℂ) (Y := ℕ) (l := atTop)
    (f := fun k ↦ ((k : ℂ) ^ (1 - s) - (N : ℂ) ^ (1 - s)) / (1 - s) +
      1 / 2 * (1 / ↑k ^ s) - 1 / 2 * (1 / ↑N ^ s)
      + s * ∫ (x : ℝ) in (N : ℝ)..k, (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-(s + 1)))
    (b := (- N ^ (1 - s)) / (1 - s) - N ^ (-s) / 2
      + s * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-(s + 1)))
  · apply Filter.Tendsto.congr'
      (f₁ := fun (k : ℕ) ↦ ∑ n ∈ Finset.Ioc N k, 1 / (n : ℂ) ^ s) (l₁ := atTop)
    · apply Filter.eventually_atTop.mpr
      use N + 1
      intro k hk
      exact ZetaSum_aux1 (a := N) (b := k) s_ne_one s_ne_zero ⟨N_pos, hk⟩
    · exact ZetaSum_aux3 s_re_gt
  · apply (Tendsto.sub ?_ ?_).add (Tendsto.const_mul _ ?_)
    · rw [(by ring : -↑N ^ (1 - s) / (1 - s) = (0 - ↑N ^ (1 - s)) / (1 - s) + 0)]
      apply cpow_tendsto s_re_gt |>.sub_const _ |>.div_const _ |>.add
      simp_rw [mul_comm_div, one_mul, one_div, (by congr; ring : 𝓝 (0 : ℂ) = 𝓝 ((0 : ℂ) / 2))]
      apply Tendsto.div_const <| cpow_inv_tendsto (by positivity)
    · simp_rw [mul_comm_div, one_mul, one_div, cpow_neg]; exact tendsto_const_nhds
    · exact MeasureTheory.intervalIntegral_tendsto_integral_Ioi (a := N)
        (b := (fun (n : ℕ) ↦ (n : ℝ)))
        (integrableOn_of_Zeta0_fun N_pos <| by positivity) tendsto_natCast_atTop_atTop
open MeasureTheory in
lemma ZetaBnd_aux1b (N : ℕ) (Npos : 1 ≤ N) {σ t : ℝ} (σpos : 0 < σ) :
    ‖∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ ((σ + t * I) + 1)‖
    ≤ N ^ (-σ) / σ := by
  apply le_trans (by apply norm_integral_le_integral_norm)
  apply le_of_tendsto (x := atTop (α := ℝ)) (f := fun (t : ℝ) ↦ ∫ (x : ℝ) in N..t,
    ‖(⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (σ + t * I + 1)‖) ?_ ?_
  · apply intervalIntegral_tendsto_integral_Ioi (μ := volume) (l := atTop) (b := id)
      (f := fun (x : ℝ) ↦ ‖(⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (σ + t * I + 1)‖) N ?_ ?_ |>.congr' ?_
    · filter_upwards [Filter.mem_atTop ((N : ℝ))]
      intro u hu
      simp only [id_eq, intervalIntegral.integral_of_le hu, norm_div]
      apply setIntegral_congr_fun (by simp)
      intro x hx; beta_reduce
      iterate 2 (rw [norm_cpow_eq_rpow_re_of_pos (by linarith [hx.1])])
      simp
    · apply IntegrableOn.integrable ?_ |>.norm
      convert! integrableOn_of_Zeta0_fun (s := σ + t * I) Npos (by simp [σpos]) using 1
      simp_rw [div_eq_mul_inv, cpow_neg]
    · exact fun ⦃_⦄ a ↦ a
  · filter_upwards [mem_atTop (N + 1 : ℝ)] with t ht
    have : (N ^ (-σ) - t ^ (-σ)) / σ ≤ N ^ (-σ) / σ :=
      div_le_div_iff_of_pos_right σpos |>.mpr (by simp [Real.rpow_nonneg (by linarith)])
    apply le_trans ?_ this
    convert! ZetaBnd_aux1a (a := N) (b := t) (by positivity) (by linarith) ?_ <;> simp [σpos]
lemma ZetaBnd_aux1 (N : ℕ) (Npos : 1 ≤ N) {σ t : ℝ} (hσ : σ ∈ Ioc 0 2) (ht : 2 ≤ |t|) :
    ‖(σ + t * I) * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ ((σ + t * I) + 1)‖
    ≤ 2 * |t| * N ^ (-σ) / σ := by
  rw [norm_mul, mul_div_assoc]
  rw [Set.mem_Ioc] at hσ
  apply mul_le_mul ?_ (ZetaBnd_aux1b N Npos hσ.1) (norm_nonneg _) (by positivity)
  refine le_trans (by apply norm_add_le) ?_
  simp only [Complex.norm_of_nonneg hσ.1.le, Complex.norm_mul, norm_real, Real.norm_eq_abs, norm_I,
    mul_one]
  linarith [hσ.2]
lemma isOpen_aux : IsOpen {z : ℂ | z ≠ 1 ∧ 0 < z.re} := by
  refine IsOpen.inter isOpen_ne ?_
  exact isOpen_lt (g := fun (z : ℂ) ↦ z.re) (by continuity) (by continuity)
open MeasureTheory in
lemma integrable_log_over_pow {r : ℝ} (rneg : r < 0) {N : ℕ} (Npos : 0 < N) :
    IntegrableOn (fun (x : ℝ) ↦ ‖x ^ (r - 1)‖ * ‖Real.log x‖) <| Ioi N := by
  apply IntegrableOn.mono_set (hst := Set.Ioi_subset_Ici <| le_refl (N : ℝ))
  apply LocallyIntegrableOn.integrableOn_of_isBigO_atTop (g := fun x ↦ x ^ (r / 2 - 1))
  · apply ContinuousOn.abs ?_ |>.mul ?_ |>.locallyIntegrableOn (by simp)
    · apply ContinuousOn.rpow (by fun_prop) (by fun_prop)
      intro x hx; left; contrapose! Npos with h; exact_mod_cast h ▸ mem_Ici.mp hx
    · apply continuous_id.continuousOn.log ?_ |>.abs
      intro x hx; simp only [id_eq]; contrapose! Npos with h; exact_mod_cast h ▸ mem_Ici.mp hx
  · have := isLittleO_log_rpow_atTop (r := -r / 2) (by linarith) |>.isBigO
    rw [Asymptotics.isBigO_iff_eventually, Filter.eventually_atTop] at this
    obtain ⟨C, hC⟩ := this
    have hh := hC C (by simp)
    rw [Asymptotics.isBigO_atTop_iff_eventually_exists]
    have := Filter.eventually_atTop.mp hh
    obtain ⟨x₀, hx₀ ⟩ := this
    filter_upwards [hh, Filter.mem_atTop x₀, Filter.mem_atTop 1]
    intro x hx x_gt x_pos
    use C
    intro y hy
    simp only [norm_mul, Real.norm_eq_abs, _root_.abs_abs]
    simp only [Real.norm_eq_abs] at hx
    have y_pos : 0 < y := by linarith
    have : y ^ (r / 2 - 1) = y ^ (r - 1) * y ^ (-r / 2) := by
      rw [← Real.rpow_add y_pos]; ring_nf
    rw [this, abs_mul]
    have y_gt : y ≥ x₀ := by linarith
    have := hx₀ y y_gt
    simp only [Real.norm_eq_abs] at this
    rw [← mul_assoc, mul_comm C, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hbc := this) (a := |y ^ (r - 1)|) (ha := by simp)
  · have := integrableOn_Ioi_rpow_iff (s := r / 2 - 1) (t := N) (by simp [Npos]) |>.mpr
      (by linarith [rneg])
    exact integrableOn_Ioi_iff_integrableAtFilter_atTop_nhdsWithin.mp this |>.1
open MeasureTheory in
lemma integrableOn_of_Zeta0_fun_log {N : ℕ} (Npos : 0 < N) {s : ℂ} (s_re_gt : 0 < s.re) :
    IntegrableOn (fun (x : ℝ) ↦ (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-(s + 1)) * (-Real.log x)) (Ioi N)
    volume := by
  simp_rw [mul_assoc]
  obtain ⟨c, hc⟩ := ZetaSum_aux2a
  apply Integrable.bdd_mul (c := c) ?_ ?_ ?_
  · simp only [neg_add_rev, mul_neg, add_comm, ← sub_eq_add_neg]
    apply integrable_norm_iff ?_ |>.mp ?_ |>.neg
    · apply ContinuousOn.mul ?_ ?_ |>.aestronglyMeasurable (by simp)
      · intro x hx
        apply ContinuousWithinAt.cpow ?_ continuous_const.continuousWithinAt ?_
        · exact RCLike.continuous_ofReal.continuousWithinAt
        · simp only [ofReal_mem_slitPlane]; linarith [mem_Ioi.mp hx]
      · apply RCLike.continuous_ofReal.continuousOn.comp ?_ (mapsTo_image _ _)
        refine continuous_id.continuousOn.log ?_
        intro x hx; simp only [id_eq]; linarith [mem_Ioi.mp hx]
    · simp only [norm_mul, norm_real]
      have := integrable_log_over_pow (r := -s.re) (by linarith) Npos
      apply IntegrableOn.congr_fun this ?_ (by simp)
      intro x hx
      simp only [mul_eq_mul_right_iff, norm_eq_zero, Real.log_eq_zero]
      left
      have xpos : 0 < x := by linarith [mem_Ioi.mp hx]
      simp [norm_cpow_eq_rpow_re_of_pos xpos, Real.abs_rpow_of_nonneg xpos.le,
        abs_eq_self.mpr xpos.le]
  · apply Measurable.add ?_ measurable_const |>.sub (by fun_prop) |>.aestronglyMeasurable
    exact Measurable.comp (fun _ _ ↦ trivial) Int.measurable_floor
  · apply MeasureTheory.ae_of_all
    convert hc with _ x; simp only [← Complex.norm_real]; simp
open MeasureTheory in
lemma hasDerivAt_Zeta0Integral {N : ℕ} (Npos : 0 < N) {s : ℂ} (hs : s ∈ {s | 0 < s.re}) :
  HasDerivAt (fun z ↦ ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-z - 1))
    (∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (- s - 1) * (- Real.log x)) s := by
  simp only [mem_ofPred_eq] at hs
  set f : ℝ → ℂ := fun x ↦ (⌊x⌋ : ℂ) + 1 / 2 - x
  set F : ℂ → ℝ → ℂ := fun s x ↦ (x : ℂ) ^ (- s - 1) * f x
  set F' : ℂ → ℝ → ℂ := fun s x ↦ (x : ℂ) ^ (- s - 1) * (- Real.log x) * f x
  set ε := s.re / 2
  have ε_pos : 0 < ε := by aesop
  set bound : ℝ → ℝ := fun x ↦ |x ^ (- s.re / 2 - 1)| * |Real.log x|
  let μ : Measure ℝ := volume.restrict (Ioi (N : ℝ))
  have hF_meas : ∀ᶠ (z : ℂ) in 𝓝 s, AEStronglyMeasurable (F z) μ := by
    have : {z : ℂ | 0 < z.re} ∈ 𝓝 s := by
      rw [mem_nhds_iff]
      refine ⟨{z | 0 < z.re}, fun ⦃a⦄ a ↦ a, isOpen_lt continuous_const Complex.continuous_re, hs⟩
    filter_upwards [this] with z hz
    convert! integrableOn_of_Zeta0_fun Npos hz |>.aestronglyMeasurable using 1
    simp only [F, f]; ext x; ring_nf
  have hF_int : Integrable (F s) μ := by
    convert! integrableOn_of_Zeta0_fun Npos hs |>.integrable using 1
    simp only [F, f]; ext x; ring_nf
  have hF'_meas : AEStronglyMeasurable (F' s) μ := by
    convert! integrableOn_of_Zeta0_fun_log Npos hs |>.aestronglyMeasurable using 1
    simp only [F', f]; ext x; ring_nf
  have IoiSubIoi1 : (Ioi (N : ℝ)) ⊆ {x | 1 < x} :=
      fun x hx ↦ lt_of_le_of_lt (by simp only [Nat.one_le_cast]; omega) <| mem_Ioi.mp hx
  have measSetIoi1 : MeasurableSet {x : ℝ | 1 < x} := (isOpen_lt' 1).measurableSet
  have h_bound1 :
    ∀ᵐ (x : ℝ) ∂volume.restrict {x | 1 < x}, ∀ z ∈ Metric.ball s ε, ‖F' z x‖ ≤ bound x := by
    filter_upwards [self_mem_ae_restrict measSetIoi1] with x hx
    intro z hz
    simp only [F', f, bound]
    calc _ = ‖(x : ℂ) ^ (-z - 1)‖ * ‖-(Real.log x)‖ * ‖(⌊x⌋ + 1 / 2 - x)‖ := by
            simp only [mul_neg, one_div, neg_mul, norm_neg, norm_mul, norm_real, Real.norm_eq_abs,
              ← (by simp : (((⌊x⌋ + 2⁻¹ - x) : ℝ) : ℂ) = (⌊x⌋ : ℂ) + 2⁻¹ - ↑x),
              Complex.norm_real]
         _ = ‖x ^ (-z.re - 1)‖ * ‖-(Real.log x)‖ * ‖(⌊x⌋ + 1 / 2 - x)‖ := ?_
         _ = |x ^ (-z.re - 1)| * |(Real.log x)| * |(⌊x⌋ + 1 / 2 - x)| := by simp
         _ ≤ _ := ?_
    · congr! 2
      simp only [Real.norm_eq_abs, norm_cpow_eq_rpow_re_of_pos (by linarith),
        sub_re, neg_re, one_re]
      apply abs_eq_self.mpr ?_ |>.symm
      positivity
    · rw [mul_comm, ← mul_assoc]
      apply mul_le_mul_of_nonneg_right ?_ <| abs_nonneg _
      simp only [Metric.mem_ball, ε, Complex.dist_eq] at hz
      apply le_trans (b := 1 * |x ^ (-z.re - 1)|)
      · apply mul_le_mul_of_nonneg_right (le_trans (ZetaSum_aux1_3 _) (by norm_num)) <| abs_nonneg _
      · simp_rw [one_mul, Real.abs_rpow_of_nonneg (by linarith : 0 ≤ x)]
        apply Real.rpow_le_rpow_of_exponent_le <| le_abs.mpr (by left; exact hx.le)
        have := abs_le.mp <| le_trans (abs_re_le_norm (z-s)) hz.le
        simp only [sub_re, neg_le_sub_iff_le_add, tsub_le_iff_right] at this
        linarith [this.1]
  have h_bound : ∀ᵐ x ∂μ, ∀ z ∈ Metric.ball s ε, ‖F' z x‖ ≤ bound x := by
    apply ae_restrict_of_ae_restrict_of_subset IoiSubIoi1
    exact h_bound1
  have bound_integrable : Integrable bound μ := by
    simp only [bound]
    convert! integrable_log_over_pow (r := -s.re / 2) (by linarith) Npos using 0
  have h_diff : ∀ᵐ x ∂μ, ∀ z ∈ Metric.ball s ε, HasDerivAt (fun w ↦ F w x) (F' z x) z := by
    simp only [F, F', f]
    apply ae_restrict_of_ae_restrict_of_subset IoiSubIoi1
    filter_upwards [h_bound1, self_mem_ae_restrict measSetIoi1] with x _ one_lt_x
    intro z hz
    convert! HasDerivAt.mul_const (c := fun (w : ℂ) ↦ (x : ℂ) ^ (-w-1))
      (c' := (x : ℂ) ^ (-z-1) * -Real.log x) (d := (⌊x⌋ : ℝ) + 1 / 2 - x) ?_ using 1
    convert! HasDerivAt.comp (h := fun w ↦ -w-1) (h' := -1) (h₂ := fun w ↦ x ^ w)
      (h₂' := x ^ (-z-1) * Real.log x) (x := z) ?_ ?_ using 0
    · simp only [mul_neg, mul_one]; congr! 2
    · convert! HasDerivAt.const_cpow (c := (x : ℂ)) (f := fun w ↦ w) (f' := 1) (x := -z-1)
        (hasDerivAt_id _) ?_ using 1
      · simp only [mul_one, mul_eq_mul_left_iff, cpow_eq_zero_iff, ofReal_eq_zero, ne_eq]
        left
        rw [Complex.ofReal_log]
        linarith
      · right
        intro h
        simp only [Metric.mem_ball, ε, Complex.dist_eq,
          neg_eq_iff_eq_neg.mp <| sub_eq_zero.mp h] at hz
        have := (abs_le.mp <| le_trans (abs_re_le_norm (-1-s)) hz.le).1
        simp only [sub_re, neg_re, one_re, neg_le_sub_iff_le_add, le_neg_add_iff_add_le] at this
        linarith
    · apply hasDerivAt_id _ |>.neg |>.sub_const
  convert! (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := F) (F' := F') (x₀ := s)
    (s := Metric.ball s ε) (bound := bound) (μ := μ) (Metric.ball_mem_nhds s ε_pos)
    hF_meas hF_int hF'_meas h_bound bound_integrable h_diff).2 using 3
  · ext a; simp only [one_div, F, f]; ring_nf
  · simp only [one_div, mul_neg, neg_mul, neg_inj, F', f]; ring_nf
noncomputable def ζ₀' (N : ℕ) (s : ℂ) : ℂ :=
    ∑ n ∈ Finset.range (N + 1), -1 / (n : ℂ) ^ s * Real.log n +
    (-N ^ (1 - s) / (1 - s) ^ 2 + Real.log N * N ^ (1 - s) / (1 - s)) +
    Real.log N * N ^ (-s) / 2 +
    (1 * (∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (- s - 1)) +
    s * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (- s - 1) * (- Real.log x))
lemma HasDerivAt_neg_cpow_over2 {N : ℕ} (Npos : 0 < N) (s : ℂ) :
    HasDerivAt (fun x : ℂ ↦ -(N : ℂ) ^ (-x) / 2) (-((- Real.log N) * (N : ℂ) ^ (-s)) / 2) s := by
  convert! hasDerivAt_neg' s |>.const_cpow (c := N) (by aesop) |>.neg |>.div_const _ using 1
  simp [mul_comm]
lemma HasDerivAt_cpow_over_var (N : ℕ) {z : ℂ} (z_ne_zero : z ≠ 0) :
    HasDerivAt (fun z ↦ -(N : ℂ) ^ z / z)
      (((N : ℂ) ^ z / z ^ 2) - (Real.log N * N ^ z / z)) z := by
  simp_rw [div_eq_mul_inv]
  convert! HasDerivAt.mul (c := fun z ↦ - (N : ℂ) ^ z) (d := fun z ↦ z⁻¹)
    (c' := - (N : ℂ) ^ z * Real.log N)
    (d' := - (z ^ 2)⁻¹) ?_ ?_ using 1
  · simp only [natCast_log, neg_mul, mul_neg, neg_neg]
    ring_nf
  · simp only [natCast_log, neg_mul]
    apply HasDerivAt.neg
    convert! HasDerivAt.const_cpow (c := (N : ℂ)) (f := id) (f' := 1) (x := z) (hasDerivAt_id z)
      (by simp [z_ne_zero]) using 1
    simp only [id_eq, mul_one]
  · exact hasDerivAt_inv z_ne_zero
lemma HasDerivAtZeta0 {N : ℕ} (Npos : 0 < N) {s : ℂ} (reS_pos : 0 < s.re) (s_ne_one : s ≠ 1) :
    HasDerivAt (ζ₀ N) (ζ₀' N s) s := by
  unfold riemannZeta0 ζ₀'
  apply HasDerivAt.fun_sum ?_ |>.add ?_ |>.add ?_ |>.add ?_
  · intro n _
    convert! hasDerivAt_neg' s |>.const_cpow (c := n) (by aesop) using 1
    all_goals (ring_nf; simp [cpow_neg])
  · convert! HasDerivAt.comp (h₂ := fun z ↦ -(N : ℂ) ^ z / z) (h := fun z ↦ 1 - z) (h' := -1)
      (h₂' := ((N : ℂ) ^ (1 - s) / (1 - s) ^ 2 - Real.log (N : ℝ) * (N : ℂ) ^ (1 - s) / (1 - s)))
      (x := s) ?_ ?_ using 1
    · ring_nf
    · exact HasDerivAt_cpow_over_var N (by rw [sub_ne_zero]; exact s_ne_one.symm)
    · convert! hasDerivAt_const s _ |>.sub (hasDerivAt_id _) using 1; simp
  · convert! HasDerivAt_neg_cpow_over2 Npos s using 1; simp only [natCast_log, neg_mul, neg_neg]
  · simp_rw [div_cpow_eq_cpow_neg, neg_add, ← sub_eq_add_neg]
    convert! hasDerivAt_id s |>.mul <| hasDerivAt_Zeta0Integral Npos reS_pos using 1
lemma HolomorphicOn_riemannZeta0 {N : ℕ} (N_pos : 0 < N) :
    HolomorphicOn (ζ₀ N) {s : ℂ | s ≠ 1 ∧ 0 < s.re} :=
  fun _ ⟨hs₁, hs₂⟩ ↦ (HasDerivAtZeta0 N_pos hs₂ hs₁).differentiableAt.differentiableWithinAt
lemma HolomorphicOn_riemannZeta :
    HolomorphicOn ζ {s : ℂ | s ≠ 1} := by
  intro z hz
  simp only [mem_ofPred_eq] at hz
  exact (differentiableAt_riemannZeta hz).differentiableWithinAt
lemma isPathConnected_aux : IsPathConnected {z : ℂ | z ≠ 1 ∧ 0 < z.re} := by
  use (2 : ℂ)
  constructor
  · simp
  intro w hw; simp only [ne_eq, mem_ofPred_eq] at hw
  by_cases w_im : w.im = 0
  · apply JoinedIn.trans (y := 1 + I)
    · let f : ℝ → ℂ := fun t ↦ (1 + I) * t + 2 * (1 - t)
      have cont : Continuous f := by continuity
      apply JoinedIn.ofLine cont.continuousOn (by simp [f]) (by simp [f])
      simp only [unitInterval, ne_eq, image_subset_iff, preimage_ofPred_eq, add_re, mul_re, one_re,
        I_re, add_zero, ofReal_re, one_mul, add_im, one_im, I_im, zero_add, ofReal_im, mul_zero,
        sub_zero, re_ofNat, sub_re, im_ofNat, sub_im, sub_self, f]
      intro x hx; simp only [mem_Icc] at hx
      refine ⟨?_, by linarith⟩
      intro h
      rw [Complex.ext_iff] at h; simp [(by apply And.right; simpa [w_im] using h : x = 0)] at h
    · let f : ℝ → ℂ := fun t ↦ w * t + (1 + I) * (1 - t)
      have cont : Continuous f := by continuity
      apply JoinedIn.ofLine cont.continuousOn (by simp [f]) (by simp [f])
      simp only [unitInterval, ne_eq, image_subset_iff, preimage_ofPred_eq, add_re, mul_re,
        ofReal_re, ofReal_im, mul_zero, sub_zero, one_re, I_re, add_zero, sub_re, one_mul, add_im,
        one_im, I_im, zero_add, sub_im, sub_self, f]
      intro x hx; simp only [mem_Icc] at hx
      simp only [mem_ofPred_eq]
      constructor
      · intro h
        refine hw.1 ?_
        rw [Complex.ext_iff] at h
        have : x = 1 := by linarith [(by apply And.right; simpa [w_im] using h : 1 - x = 0)]
        rw [Complex.ext_iff, one_re, one_im]; exact ⟨by simpa [this, w_im] using h, w_im⟩
      · by_cases hxx : x = 0
        · simp only [hxx]; linarith
        · have : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hxx)
          have : 0 ≤ 1 - x := by linarith
          have := hw.2
          positivity
  · let f : ℝ → ℂ := fun t ↦ w * t + 2 * (1 - t)
    have cont : Continuous f := by continuity
    apply JoinedIn.ofLine cont.continuousOn (by simp [f]) (by simp [f])
    simp only [unitInterval, ne_eq, image_subset_iff, preimage_ofPred_eq, add_re, mul_re, ofReal_re,
      ofReal_im, mul_zero, sub_zero, re_ofNat, sub_re, one_re, im_ofNat, sub_im, one_im, sub_self,
      f]
    intro x hx; simp only [mem_Icc] at hx
    constructor
    · intro h
      rw [Complex.ext_iff] at h;
      simp [(by apply And.right; simpa [w_im] using h : x = 0)] at h
    · by_cases hxx : x = 0
      · simp only [hxx]; linarith
      · have : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hxx)
        have : 0 ≤ 1 - x := by linarith
        have := hw.2
        positivity
lemma Zeta0EqZeta {N : ℕ} (N_pos : 0 < N) {s : ℂ} (reS_pos : 0 < s.re) (s_ne_one : s ≠ 1) :
    ζ₀ N s = riemannZeta s := by
  let f := riemannZeta
  let g := ζ₀ N
  let U := {z : ℂ | z ≠ 1 ∧ 0 < z.re}
  have f_an : AnalyticOnNhd ℂ f U := by
    apply (HolomorphicOn_riemannZeta.analyticOnNhd isOpen_ne).mono
    simp only [ne_eq, ofPred_subset_ofPred, and_imp, U]
    exact fun a ha _ ↦ ha
  have g_an : AnalyticOnNhd ℂ g U := (HolomorphicOn_riemannZeta0 N_pos).analyticOnNhd isOpen_aux
  have preconU : IsPreconnected U := by
    apply IsConnected.isPreconnected
    apply (IsOpen.isConnected_iff_isPathConnected isOpen_aux).mpr isPathConnected_aux
  have h2 : (2 : ℂ) ∈ U := by simp [U]
  have s_mem : s ∈ U := by simp [U, reS_pos, s_ne_one]
  convert (AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq f_an g_an preconU h2 ?_ s_mem).symm
  have u_mem : {z : ℂ | 1 < z.re} ∈ 𝓝 (2 : ℂ) := by
    apply mem_nhds_iff.mpr
    use {z : ℂ | 1 < z.re}
    simp only [ofPred_subset_ofPred, imp_self, forall_const, mem_ofPred_eq, re_ofNat,
      Nat.one_lt_ofNat, and_true, true_and]
    exact isOpen_lt (by continuity) (by continuity)
  filter_upwards [u_mem]
  intro z hz
  simp only [f,g, zeta_eq_tsum_one_div_nat_cpow hz, riemannZeta0_apply]
  nth_rewrite 2 [neg_div]
  rw [← sub_eq_add_neg, ← ZetaSum_aux2 N_pos hz,
    ← (summable_one_div_nat_cpow.mpr hz).sum_add_tsum_nat_add (N + 1)]
  norm_cast
lemma le_trans₄ {α : Type*} [Preorder α] {a b c d : α} : a ≤ b → b ≤ c → c ≤ d → a ≤ d :=
  fun hab hbc hcd ↦ le_trans (le_trans hab hbc) hcd
lemma logt_gt_one {t : ℝ} (t_ge : 3 ≤ t) : 1 < Real.log t :=
  (Real.lt_log_iff_exp_lt (by linarith)).mpr (by linarith [Real.exp_one_lt_d9])
lemma Nat.self_div_floor_bound {t : ℝ} (t_ge : 1 ≤ |t|) : let N := ⌊|t|⌋₊;
    (|t| / N) ∈ Icc 1 2 := by
  intro N
  have Npos : 0 < N := Nat.floor_pos.mpr (by linarith)
  have N_le_t : N ≤ |t| := Nat.floor_le <| abs_nonneg _
  constructor
  · apply le_div_iff₀ (by simp [Npos]) |>.mpr; simp [N_le_t]
  · apply div_le_iff₀ (by positivity) |>.mpr
    suffices |t| < N + 1 by linarith [(by exact_mod_cast (by omega) : 1 ≤ (N : ℝ))]
    apply Nat.lt_floor_add_one
lemma UpperBnd_aux5 {σ t : ℝ} (t_ge : 3 < |t|) (σ_le : σ ≤ 2) : (|t| / ⌊|t|⌋₊) ^ σ ≤ 4 := by
  obtain ⟨h₁, h₂⟩ := Nat.self_div_floor_bound (by linarith)
  calc _ ≤ ((|t| / ↑⌊|t|⌋₊) ^ (2 : ℝ)) := by gcongr
       _ ≤ (2 : ℝ) ^ (2 : ℝ) := by gcongr
       _ = 4 := by norm_num
lemma UpperBnd_aux6 {σ t : ℝ} (t_ge : 3 < |t|) (hσ : σ ∈ Ioc (1 / 2) 2)
    (neOne : σ + t * I ≠ 1) (Npos : 0 < ⌊|t|⌋₊) (N_le_t : ⌊|t|⌋₊ ≤ |t|) :
    ⌊|t|⌋₊ ^ (1 - σ) / ‖1 - (σ + t * I)‖ ≤ |t| ^ (1 - σ) * 2 ∧
    ⌊|t|⌋₊ ^ (-σ) / 2 ≤ |t| ^ (1 - σ) ∧ ⌊|t|⌋₊ ^ (-σ) / σ ≤ 8 * |t| ^ (-σ) := by
  have bnd := UpperBnd_aux5 t_ge hσ.2
  have bnd' : (|t| / ⌊|t|⌋₊) ^ σ ≤ 2 * |t| := by linarith
  split_ands
  · apply (div_le_iff₀ <| norm_pos_iff.mpr <| sub_ne_zero_of_ne neOne.symm).mpr
    conv => rw [mul_assoc]; rhs; rw [mul_comm]
    apply (div_le_iff₀ <| Real.rpow_pos_of_pos (by linarith) _).mp
    rw [div_rpow_eq_rpow_div_neg (by positivity) (by positivity), neg_sub]
    refine le_trans₄ ?_ bnd' ?_
    · exact Real.rpow_le_rpow_of_exponent_le (one_le_div (by positivity) |>.mpr N_le_t) (by simp)
    · apply (mul_le_mul_iff_right₀ (by norm_num)).mpr; simpa using abs_im_le_norm (1 - (σ + t * I))
  · apply div_le_iff₀ (by norm_num) |>.mpr
    rw [Real.rpow_sub (by linarith), Real.rpow_one, div_mul_eq_mul_div, mul_comm]
    apply div_le_iff₀ (by positivity) |>.mp
    convert! bnd' using 1
    rw [← Real.rpow_neg (by linarith), div_rpow_neg_eq_rpow_div (by positivity) (by positivity)]
  · apply div_le_iff₀ (by linarith [hσ.1]) |>.mpr
    rw [mul_assoc, mul_comm, mul_assoc]
    apply div_le_iff₀' (by positivity) |>.mp
    apply le_trans ?_ (by linarith [hσ.1] : 4 ≤ σ * 8)
    convert! bnd using 1; exact div_rpow_neg_eq_rpow_div (by positivity) (by positivity)
lemma DerivUpperBnd_aux7_1 {x σ t : ℝ} (hx : 1 ≤ x) :
    let s := ↑σ + ↑t * I;
    ‖(↑⌊x⌋ + 1 / 2 - ↑x) * (x : ℂ) ^ (-s - 1) * -↑x.log‖ = |(↑⌊x⌋ + 1 / 2 - x)| * x ^ (-σ - 1) * x.log := by
  have xpos : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have : ‖(x.log : ℂ)‖ = x.log := Complex.norm_of_nonneg <| Real.log_nonneg hx
  simp [← norm_real, this, Complex.norm_cpow_eq_rpow_re_of_pos xpos, ← Real.norm_eq_abs, ← ofReal_ofNat,
    ← ofReal_inv, ← ofReal_add, ← ofReal_sub, ← ofReal_intCast, one_div]
lemma DerivUpperBnd_aux7_2 {x σ : ℝ} (hx : 1 ≤ x) :
    |(↑⌊x⌋ + 1 / 2 - x)| * x ^ (-σ - 1) * x.log ≤ x ^ (-σ - 1) * x.log := by
  rw [← one_mul (x ^ (-σ - 1) * Real.log x), mul_assoc]
  apply mul_le_mul_of_nonneg_right _ (by bound)
  exact le_trans (ZetaSum_aux1_3 x) (by norm_num)
lemma DerivUpperBnd_aux7_3 {x σ : ℝ} (xpos : 0 < x) (σnz : σ ≠ 0) :
    HasDerivAt (fun t ↦ -(1 / σ ^ 2 * t ^ (-σ) + 1 / σ * t ^ (-σ) * Real.log t))
      (x ^ (-σ - 1) * Real.log x) x := by
  have h1 := Real.hasDerivAt_rpow_const (p := -σ) (Or.inl xpos.ne.symm)
  have h2 := h1.const_mul (1 / σ^2)
  have cancel : 1 / σ^2 * σ = 1 / σ := by field_simp
  rw [neg_mul, mul_neg, ← mul_assoc, cancel] at h2
  have h3 := Real.hasDerivAt_log xpos.ne.symm
  have h4 := HasDerivAt.mul (h1.const_mul (1 / σ)) h3
  have cancel := Real.rpow_add xpos (-σ) (-1)
  have : -σ + -1 = -σ - 1 := by rfl
  rw [← Real.rpow_neg_one x, mul_assoc (1 / σ) (x ^ (-σ)), ← cancel, this] at h4
  convert! h2.add h4 |>.neg using 1
  field_simp; ring
lemma DerivUpperBnd_aux7_3' {a σ : ℝ} (apos : 0 < a) (σnz : σ ≠ 0) :
    ∀ x ∈ Ici a, HasDerivAt (fun t ↦ -(1 / σ ^ 2 * t ^ (-σ) + 1 / σ * t ^ (-σ) * Real.log t))
      (x ^ (-σ - 1) * Real.log x) x := by
  intro x hx
  simp at hx
  exact DerivUpperBnd_aux7_3 (by linarith) σnz
lemma DerivUpperBnd_aux7_nonneg {a σ : ℝ} (ha : 1 ≤ a) :
    ∀ x ∈ Ioi a, 0 ≤ x ^ (-σ - 1) * Real.log x := by
  intro x hx
  simp at hx
  bound
lemma DerivUpperBnd_aux7_tendsto {σ : ℝ} (σpos : 0 < σ) :
    Tendsto (fun t ↦ -(1 / σ ^ 2 * t ^ (-σ) + 1 / σ * t ^ (-σ) * Real.log t)) atTop (nhds 0) := by
  have h1 := tendsto_rpow_neg_atTop σpos
  have h2 := h1.const_mul (1 / σ^2)
  have h3 : Tendsto (fun t : ℝ ↦ t ^ (-σ) * Real.log t) atTop (nhds 0) := by
    have := Real.tendsto_pow_log_div_pow_atTop σ 1 σpos
    simp only [Real.rpow_one] at this
    apply Tendsto.congr' _ this
    filter_upwards [eventually_ge_atTop 0] with x hx
    rw [mul_comm]
    apply div_rpow_eq_rpow_neg _ _ _ hx
  have h4 := h3.const_mul (1 / σ)
  have h5 := (h2.add h4).neg
  convert h5 using 1
  · ext; ring
  simp
open MeasureTheory in
lemma DerivUpperBnd_aux7_4 {a σ : ℝ} (σpos : 0 < σ) (ha : 1 ≤ a) :
    IntegrableOn (fun x ↦ x ^ (-σ - 1) * Real.log x) (Ioi a) volume := by
  apply integrableOn_Ioi_deriv_of_nonneg' (l := 0)
  · exact DerivUpperBnd_aux7_3' (by linarith) (by linarith)
  · exact DerivUpperBnd_aux7_nonneg ha
  · exact DerivUpperBnd_aux7_tendsto σpos
open MeasureTheory in
lemma DerivUpperBnd_aux7_5 {a σ : ℝ} (σpos : 0 < σ) (ha : 1 ≤ a) :
    IntegrableOn (fun x ↦ |(↑⌊x⌋ + (1 : ℝ) / 2 - x)| * x ^ (-σ - 1) * Real.log x)
      (Ioi a) volume := by
  simp_rw [mul_assoc]
  apply Integrable.bdd_mul (c := 1 / 2) <| DerivUpperBnd_aux7_4 σpos ha
  · exact Measurable.aestronglyMeasurable <| Measurable.abs measurable_floor_add_half_sub
  apply ae_of_all
  intro x
  simp only [Real.norm_eq_abs, _root_.abs_abs]
  exact  ZetaSum_aux1_3 x
open MeasureTheory in
lemma DerivUpperBnd_aux7_integral_eq {a σ : ℝ} (ha : 1 ≤ a) (σpos : 0 < σ) :
    ∫ (x : ℝ) in Ioi a, x ^ (-σ - 1) * Real.log x =
      1 / σ^2 * a ^ (-σ) + 1 / σ * a ^ (-σ) * Real.log a := by
  convert integral_Ioi_of_hasDerivAt_of_nonneg'
    (DerivUpperBnd_aux7_3' (by linarith) (by linarith))
    (DerivUpperBnd_aux7_nonneg ha) (DerivUpperBnd_aux7_tendsto σpos) using 1
  ring
open MeasureTheory in
theorem DerivUpperBnd_aux7 {A σ t : ℝ} (t_gt : 3 < |t|) (hσ : σ ∈ Icc (1 - A / |t|.log) 2) :
    let N := ⌊|t|⌋₊;
    let s := ↑σ + ↑t * I;
    0 < N → ↑N ≤ |t| → s ≠ 1 → 1 / 2 < σ →
    ‖s * ∫ (x : ℝ) in Ioi (N : ℝ), (↑⌊x⌋ + 1 / 2 - ↑x) * (x : ℂ) ^ (-s - 1) * -↑x.log‖ ≤
      6 * |t| * ↑N ^ (-σ) / σ * |t|.log := by
  intro N s Npos N_le_t neOne σ_gt
  have σpos : 0 < σ := lt_trans (by norm_num) σ_gt
  rw [norm_mul, (by ring : 6 * |t| * ↑N ^ (-σ) / σ * Real.log |t| = (2 * |t|) * (3 * ↑N ^ (-σ) / σ * Real.log |t|))]
  apply mul_le_mul _ _ (by positivity) (by positivity)
  · apply le_trans (by apply norm_add_le)
    simp [abs_of_pos σpos]
    linarith [hσ.2]
  apply le_trans (by apply norm_integral_le_integral_norm)
  calc ∫ (x : ℝ) in Ioi (N : ℝ), ‖(↑⌊x⌋ + 1 / 2 - ↑x) * (x : ℂ) ^ (-s - 1) * -↑x.log‖
    _ = ∫ (x : ℝ) in Ioi (N : ℝ), |(↑⌊x⌋ + 1 / 2 - x)| * x ^ (-σ - 1) * x.log := by
      apply setIntegral_congr_fun (by measurability)
      intro x hx
      simp only [mem_Ioi] at hx
      exact DerivUpperBnd_aux7_1 (lt_of_le_of_lt (mod_cast Npos) hx).le
    _ ≤ ∫ (x : ℝ) in Ioi (N : ℝ), x ^ (-σ - 1) * x.log := by
      apply setIntegral_mono_on _ _ (by measurability)
      · intro x hx
        exact DerivUpperBnd_aux7_2 (lt_of_le_of_lt (mod_cast Npos) hx).le
      · apply DerivUpperBnd_aux7_5 σpos (mod_cast Npos)
      apply DerivUpperBnd_aux7_4 σpos (mod_cast Npos)
    _ = 1 / σ^2 * N ^ (-σ) + 1 / σ * N ^ (-σ) * Real.log N :=
      DerivUpperBnd_aux7_integral_eq (mod_cast Npos) σpos
    _ ≤ 3 * ↑N ^ (-σ) / σ * |t|.log := by
      have h2 : 1 / σ * ↑N ^ (-σ) * Real.log ↑N ≤ ↑N ^ (-σ) / σ * Real.log |t| := calc
        _ = ↑N ^ (-σ) / σ * Real.log N := by ring
        _ ≤ _ := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact Real.log_le_log (mod_cast Npos) N_le_t
      have : 2 ≤ 2 * Real.log |t| := by
        nth_rewrite 1  [← mul_one 2]
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact logt_gt_one t_gt.le |>.le
      have h1 : 1 / σ^2 * ↑N ^ (-σ) ≤ 2 * ↑N ^ (-σ) / σ * Real.log |t| := calc
        1 / σ^2 * ↑N ^ (-σ) = (↑N ^ (-σ) / σ) * (1 / σ) := by ring
        _ ≤ ↑N ^ (-σ) / σ * (2 * Real.log |t|):= by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply le_trans _ this
          exact (one_div_le σpos (by norm_num)).mpr σ_gt.le
        _ = _ := by ring
      convert! add_le_add h1 h2 using 1
      ring
set_option backward.isDefEq.respectTransparency false in
lemma deriv_fun_re {t : ℝ} {f : ℂ → ℂ} (diff : ∀ (σ : ℝ), DifferentiableAt ℂ f (↑σ + ↑t * I)) :
    (deriv fun {σ₂ : ℝ} ↦ f (σ₂ + t * I)) = fun (σ : ℝ) ↦ deriv f (σ + t * I) := by
  ext σ
  have := deriv_comp (h := fun (σ : ℝ) ↦ σ + t * I) (h₂ := f) σ (diff σ) ?_
  · simp only [deriv_add_const', _root_.deriv_ofReal, mul_one] at this
    exact this
  · apply DifferentiableAt.add_const _ <| differentiableAt_ofReal σ
set_option backward.isDefEq.respectTransparency false in
lemma Zeta_eq_int_derivZeta {σ₁ σ₂ t : ℝ} (t_ne_zero : t ≠ 0) :
    (∫ σ in σ₁..σ₂, ζ' (σ + t * I)) = ζ (σ₂ + t * I) - ζ (σ₁ + t * I) := by
  have diff : ∀ (σ : ℝ), DifferentiableAt ℂ ζ (σ + t * I) := by
    intro σ
    refine differentiableAt_riemannZeta ?_
    contrapose! t_ne_zero; apply And.right; simpa [Complex.ext_iff] using t_ne_zero
  apply intervalIntegral.integral_deriv_eq_sub'
  · exact deriv_fun_re diff
  · intro s _
    apply DifferentiableAt.comp
    · exact (diff s).restrictScalars ℝ
    · exact DifferentiableAt.add_const (c := t * I) <| differentiableAt_ofReal _
  · apply ContinuousOn.comp (g := ζ') ?_ ?_ (mapsTo_image _ _)
    · apply HasDerivAt.continuousOn (f' := deriv <| ζ')
      intro x hx
      apply hasDerivAt_deriv_iff.mpr
      replace hx : x ≠ 1 := by
        contrapose! hx
        simp only [hx, mem_image, Complex.ext_iff, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im,
          I_im, mul_one, sub_self, add_zero, one_re, add_im, mul_im, zero_add, one_im, not_exists,
          not_and]
        exact fun _ _ _ ↦ t_ne_zero
      exact differentiableAt_deriv_riemannZeta hx
    · exact continuous_ofReal.continuousOn.add continuousOn_const
theorem summable_complex_then_summable_real_part (f : ℕ → ℂ)
    (h : Summable f) : Summable (fun n ↦ (f n).re) := by
  rcases h with ⟨s, hs⟩
  exact ⟨s.re,  hasSum_re hs⟩
open ArithmeticFunction (vonMangoldt)
local notation "Λ" => vonMangoldt
open scoped ComplexOrder in
theorem dlog_riemannZeta_bdd_on_vertical_lines_generalized
    (σ₀ σ₁ t : ℝ) (σ₀_gt_one : 1 < σ₀) (σ₀_lt_σ₁ : σ₀ ≤ σ₁) :
    ‖(- ζ' (σ₁ + t * I) / ζ (σ₁ + t * I))‖ ≤ ‖ζ' σ₀ / ζ σ₀‖ := by
  let s₁ := σ₁ + t * I
  have s₁_re_eq_sigma : s₁.re = σ₁ := by
    rw [add_re, ofReal_re, mul_I_re, ofReal_im]
    ring
  have s₀_re_eq_sigma : (↑σ₀ : ℂ).re = σ₀ := by
    rw [ofReal_re]
  let s₀ := σ₀
  have σ₁_gt_one : 1 < σ₁ := by exact lt_of_le_of_lt' σ₀_lt_σ₁ σ₀_gt_one
  have s₀_gt_one : 1 < (↑σ₀ : ℂ).re := by exact σ₀_gt_one
  have s₁_re_geq_one : 1 < s₁.re := by exact lt_of_lt_of_eq σ₁_gt_one (id (Eq.symm s₁_re_eq_sigma))
  rw [← (ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div s₁_re_geq_one)]
  unfold LSeries
  have summable_von_mangoldt_at_σ₀ : Summable (fun i ↦ LSeries.term (fun n ↦ ↑(Λ n)) σ₀ i) := by
    exact ArithmeticFunction.LSeriesSummable_vonMangoldt σ₀_gt_one
  have summable_re_von_mangoldt_at_σ₀ :
      Summable (fun i ↦ (LSeries.term (fun n ↦ ↑(Λ n)) σ₀ i).re) := by
    exact summable_complex_then_summable_real_part (LSeries.term (fun n ↦ ↑(Λ n)) σ₀)
      summable_von_mangoldt_at_σ₀
  have summable_abs_value : Summable (fun i ↦ ‖LSeries.term (fun n ↦ ↑(Λ n)) s₁ i‖) := by
    rw [summable_norm_iff]
    exact ArithmeticFunction.LSeriesSummable_vonMangoldt s₁_re_geq_one
  apply le_trans <| norm_tsum_le_tsum_norm summable_abs_value
  rw [← norm_neg, ← neg_div, ← ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div s₀_gt_one]
  unfold LSeries
  rw [← re_eq_norm.mpr, re_tsum summable_von_mangoldt_at_σ₀]
  · apply Summable.tsum_mono summable_abs_value summable_re_von_mangoldt_at_σ₀
    intro n
    beta_reduce
    apply le_trans <| LSeries.norm_term_le_of_re_le_re (s := σ₀) _ _ _
    · rw [re_eq_norm.mpr]
      apply LSeries.term_nonneg
      exact_mod_cast ArithmeticFunction.vonMangoldt_nonneg
    · rwa [s₁_re_eq_sigma, s₀_re_eq_sigma]
  · apply tsum_nonneg
    intro n
    apply LSeries.term_nonneg
    exact_mod_cast ArithmeticFunction.vonMangoldt_nonneg
end
end CountPort18
section CountPort19
section
open Complex Filter Topology MeasureTheory Set
private lemma norm_sub_one_le_norm_of_half_le_re {z : ℂ} (hz : 1 / 2 ≤ z.re) :
    ‖z - 1‖ ≤ ‖z‖ := by
  refine le_of_sq_le_sq ?_ (norm_nonneg z)
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.sub_re, Complex.one_re,
    Complex.sub_im, Complex.one_im, sub_zero]
  nlinarith [hz]
theorem norm_Gamma_le_strip_quarter_two :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ w : ℂ, (1 : ℝ) / 4 ≤ w.re → w.re ≤ 2 →
      ‖Complex.Gamma w‖ ≤ C₀ * (1 + ‖w‖ ^ ((3 : ℝ) / 2)) := by
  obtain ⟨c₁, c₂, hc₁, hc₁₂, H⟩ :=
    norm_Gamma_vertical_le (a := 1 / 4) (b := 2) (by norm_num) (by norm_num)
  have hc₂ : 0 < c₂ := lt_of_lt_of_le hc₁ hc₁₂
  obtain ⟨M₀, hM₀⟩ :=
    ((isCompact_Icc (a := (1 / 4 : ℝ)) (b := 2)).reProdIm
        (isCompact_Icc (a := (-1 : ℝ)) (b := 1))).exists_bound_of_continuousOn
      fun w hw ↦ (differentiableAt_Gamma_of_re_pos (by
        rw [mem_reProdIm] at hw; linarith [hw.1.1])).continuousAt.continuousWithinAt
  refine ⟨max c₂ M₀, lt_of_lt_of_le hc₂ (le_max_left _ _), fun w hw1 hw2 ↦ ?_⟩
  have hnormnn : (0 : ℝ) ≤ ‖w‖ ^ ((3 : ℝ) / 2) := Real.rpow_nonneg (norm_nonneg _) _
  have hC₀ : (0 : ℝ) ≤ max c₂ M₀ := hc₂.le.trans (le_max_left _ _)
  by_cases himw : 1 ≤ |w.im|
  ·
    have hexp : Real.exp (-(Real.pi / 2) * |w.im|) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [mul_nonneg Real.pi_pos.le (abs_nonneg w.im)])
    have hrpow : |w.im| ^ (w.re - 1 / 2) ≤ ‖w‖ ^ ((3 : ℝ) / 2) :=
      (Real.rpow_le_rpow_of_exponent_le himw (by linarith)).trans
        (Real.rpow_le_rpow (abs_nonneg _) (Complex.abs_im_le_norm w) (by norm_num))
    have hub := (H w.re hw1 hw2 w.im himw).2
    rw [Complex.re_add_im] at hub
    calc ‖Complex.Gamma w‖
        ≤ c₂ * |w.im| ^ (w.re - 1 / 2) * Real.exp (-(Real.pi / 2) * |w.im|) := hub
      _ ≤ c₂ * ‖w‖ ^ ((3 : ℝ) / 2) * 1 := by gcongr
      _ ≤ max c₂ M₀ * (1 + ‖w‖ ^ ((3 : ℝ) / 2)) := by
            nlinarith [mul_le_mul_of_nonneg_right (le_max_left c₂ M₀) hnormnn]
  ·
    have hwK := hM₀ w (by
      rw [mem_reProdIm]
      exact ⟨⟨hw1, hw2⟩, (abs_lt.mp (not_le.mp himw)).1.le, (abs_lt.mp (not_le.mp himw)).2.le⟩)
    nlinarith [le_max_right c₂ M₀]
theorem norm_Gamma_le_exp_halfplane :
    ∃ Cγ : ℝ, 0 < Cγ ∧ ∀ z : ℂ, (1 : ℝ) / 4 ≤ z.re → 1 ≤ ‖z‖ →
      ‖Complex.Gamma z‖ ≤ Real.exp (Cγ * (‖z‖ * Real.log ‖z‖ + 1)) := by
  obtain ⟨C₀, hC₀, hstrip⟩ := norm_Gamma_le_strip_quarter_two
  have aux : ∀ n : ℕ, ∀ z : ℂ, (1 : ℝ) / 4 ≤ z.re → z.re ≤ 2 + n → 1 ≤ ‖z‖ →
      ‖Complex.Gamma z‖ ≤ C₀ * (1 + ‖z‖ ^ ((3 : ℝ) / 2)) * ‖z‖ ^ n := by
    intro n
    induction n with
    | zero => exact fun z hz1 hz2 _ ↦ by simpa using hstrip z hz1 (by simpa using hz2)
    | succ n ih =>
        intro z hz1 hz2 hz3
        by_cases hcase : z.re ≤ 2 + n
        · exact (ih z hz1 hcase hz3).trans (by gcongr; exact Nat.le_succ n)
        · have hrebig : (2 : ℝ) < z.re :=
            lt_of_le_of_lt (le_add_of_nonneg_right (Nat.cast_nonneg n)) (not_le.mp hcase)
          have hwre : (z - 1).re = z.re - 1 := by simp
          have hwne : z - 1 ≠ 0 := fun hh ↦ by rw [hh, Complex.zero_re] at hwre; linarith
          have hstep : Complex.Gamma z = (z - 1) * Complex.Gamma (z - 1) := by
            rw [← Complex.Gamma_add_one (z - 1) hwne]; congr 1; ring
          have hw_norm1 : (1 : ℝ) ≤ ‖z - 1‖ :=
            le_trans (by rw [hwre]; linarith)
              ((le_abs_self _).trans (abs_re_le_norm (z - 1)))
          have hih := ih (z - 1) (by rw [hwre]; linarith)
            (by rw [hwre]; push_cast at hz2 ⊢; linarith) hw_norm1
          have hnorm_le : ‖z - 1‖ ≤ ‖z‖ := norm_sub_one_le_norm_of_half_le_re (by linarith)
          rw [hstep, norm_mul, pow_succ]
          calc ‖z - 1‖ * ‖Complex.Gamma (z - 1)‖
              ≤ ‖z‖ * (C₀ * (1 + ‖z‖ ^ ((3 : ℝ) / 2)) * ‖z‖ ^ n) :=
                mul_le_mul hnorm_le (hih.trans (by gcongr)) (norm_nonneg _) (norm_nonneg _)
            _ = C₀ * (1 + ‖z‖ ^ ((3 : ℝ) / 2)) * (‖z‖ ^ n * ‖z‖) := by ring
  refine ⟨max (5 / 2) (Real.log (2 * C₀)),
    lt_of_lt_of_le (by norm_num) (le_max_left _ _), fun z hz1 hz3 ↦ ?_⟩
  set N := ‖z‖ with hN
  have hN0 : (0 : ℝ) < N := lt_of_lt_of_le one_pos hz3
  have hL0 : (0 : ℝ) ≤ Real.log N := Real.log_nonneg hz3
  have hNL : (0 : ℝ) ≤ N * Real.log N := mul_nonneg hN0.le hL0
  set n := ⌊z.re⌋₊ with hn
  have hn_le : (n : ℝ) ≤ N :=
    (Nat.floor_le (by linarith)).trans ((le_abs_self _).trans (abs_re_le_norm z))
  have hbase := aux n z hz1 (by linarith [Nat.lt_floor_add_one z.re]) hz3
  rw [← hN] at hbase
  have h1le : (1 : ℝ) ≤ N ^ ((3 : ℝ) / 2) := Real.one_le_rpow hz3 (by norm_num)
  have hpow : N ^ n ≤ Real.exp (N * Real.log N) := by
    rw [← Real.rpow_natCast N n, Real.rpow_def_of_pos hN0]
    exact Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left hn_le hL0])
  have hkey : C₀ * (1 + N ^ ((3 : ℝ) / 2)) * N ^ n
      ≤ Real.exp (Real.log (2 * C₀) + Real.log N * (3 / 2)) * Real.exp (N * Real.log N) := by
    rw [Real.exp_add, Real.exp_log (by positivity), ← Real.rpow_def_of_pos hN0]
    exact mul_le_mul (by nlinarith [mul_nonneg hC₀.le (sub_nonneg.mpr h1le)]) hpow
      (by positivity) (by positivity)
  refine (hbase.trans hkey).trans ?_
  rw [← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have hCγ1 : (5 : ℝ) / 2 ≤ max (5 / 2) (Real.log (2 * C₀)) := le_max_left _ _
  nlinarith [le_max_right (5 / 2 : ℝ) (Real.log (2 * C₀)), hNL,
    mul_nonneg (by linarith : (0 : ℝ) ≤ N - 1) hL0, mul_nonneg (sub_nonneg.mpr hCγ1) hNL]
theorem norm_riemannZeta_sub_head_le {s : ℂ} (hs : (1 : ℝ) / 2 ≤ s.re) :
    ‖s * ∫ x in Set.Ioi (2 : ℝ), (↑⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1)‖
      ≤ Real.sqrt 2 * ‖s‖ := by
  have hσpos : 0 < s.re := by linarith
  have key := ZetaBnd_aux1b 2 (by norm_num) (σ := s.re) (t := s.im) hσpos
  simp only [Nat.cast_ofNat, Complex.re_add_im] at key
  have hb2 : (2 : ℝ) ^ (-s.re) / s.re ≤ Real.sqrt 2 := by
    calc (2 : ℝ) ^ (-s.re) / s.re = (2 : ℝ) ^ (-s.re) * (1 / s.re) := by ring
      _ ≤ (2 : ℝ) ^ (-(1 / 2) : ℝ) * 2 :=
          mul_le_mul (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith))
            (by rw [div_le_iff₀ hσpos]; linarith) (by positivity)
            (Real.rpow_pos_of_pos (by norm_num) _).le
      _ = Real.sqrt 2 := by
          rw [mul_comm]; nth_rewrite 1 [← Real.rpow_one (2 : ℝ)]
          rw [← Real.rpow_add (by norm_num), Real.sqrt_eq_rpow]; congr 1; norm_num
  rw [norm_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right (key.trans hb2) (norm_nonneg s)
theorem norm_riemannZeta_le_const_mul_of_half_le_re :
    ∃ Cζ : ℝ, 0 < Cζ ∧ ∀ s : ℂ, (1 : ℝ) / 2 ≤ s.re → 2 ≤ ‖s‖ → ‖riemannZeta s‖ ≤ Cζ * ‖s‖ := by
  refine ⟨5 + Real.sqrt 2, by positivity, fun s hs hsnorm ↦ ?_⟩
  have hσpos : 0 < s.re := by linarith
  have hsqrt2 : Real.sqrt 2 ≤ 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  have hs1 : s ≠ 1 := by rintro rfl; rw [norm_one] at hsnorm; norm_num at hsnorm
  by_cases hcase : 2 ≤ s.re
  ·
    have hb := norm_riemannZeta_sub_one_le_of_two_le_re hcase
    have h2 := norm_sub_norm_le (riemannZeta s) 1
    rw [norm_one] at h2
    nlinarith [Real.sqrt_nonneg 2, Real.pi_le_four, Real.pi_pos,
      mul_nonneg (Real.sqrt_nonneg 2) (by linarith : (0 : ℝ) ≤ ‖s‖)]
  ·
    have hs0 : s ≠ 0 := by rintro rfl; simp at hσpos
    have hexp : riemannZeta s
        = (∑ n ∈ Finset.range 3, 1 / ((n : ℂ)) ^ s)
          + (-(((2 : ℕ) : ℂ) ^ (1 - s))) / (1 - s)
          + (-(((2 : ℕ) : ℂ) ^ (-s))) / 2
          + s * ∫ x in Set.Ioi (2 : ℝ), (↑⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1) :=
      (Zeta0EqZeta (N := 2) (by norm_num) hσpos hs1).symm
    have hA : ‖∑ n ∈ Finset.range 3, 1 / ((n : ℂ)) ^ s‖ ≤ 2 := by
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
      simp only [Nat.cast_zero, Nat.cast_one, Complex.zero_cpow hs0, Complex.one_cpow,
        div_zero, div_one, zero_add]
      refine (norm_add_le _ _).trans ?_
      rw [norm_one, norm_div, norm_one, norm_natCast_cpow_of_pos (by norm_num : 0 < 2)]
      have hden : (0 : ℝ) < ((2 : ℕ) : ℝ) ^ s.re := by positivity
      linarith [(div_le_one hden).mpr (Real.one_le_rpow (by norm_num) (by linarith))]
    have hB : ‖(-(((2 : ℕ) : ℂ) ^ (1 - s))) / (1 - s)‖ ≤ Real.sqrt 2 := by
      rw [norm_div, norm_neg, norm_natCast_cpow_of_pos (by norm_num : 0 < 2), Complex.sub_re,
        Complex.one_re]
      have h1s : (1 : ℝ) ≤ ‖1 - s‖ := by
        rw [show (1 : ℂ) - s = -(s - 1) by ring, norm_neg]
        have hh := norm_sub_norm_le s 1
        rw [norm_one] at hh; linarith
      refine (div_le_self (Real.rpow_nonneg (by norm_num) _) h1s).trans ?_
      rw [show ((2 : ℕ) : ℝ) = (2 : ℝ) by norm_num, Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    have hC : ‖(-(((2 : ℕ) : ℂ) ^ (-s))) / 2‖ ≤ 1 / 2 := by
      rw [norm_div, norm_neg, norm_natCast_cpow_of_pos (by norm_num : 0 < 2), Complex.neg_re,
        show ‖(2 : ℂ)‖ = 2 by norm_num, div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
      simpa using Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith : -s.re ≤ 0)
    rw [hexp]
    refine norm_add₄_le.trans ((add_le_add (add_le_add (add_le_add hA hB) hC)
      (norm_riemannZeta_sub_head_le hs)).trans ?_)
    linarith
theorem norm_riemannXi_le_exp :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, 2 ≤ ‖s‖ →
      ‖riemannXi s‖ ≤ Real.exp (C * (‖s‖ * Real.log ‖s‖)) := by
  obtain ⟨Cγ, hCγ, hγ⟩ := norm_Gamma_le_exp_halfplane
  obtain ⟨Cζ, hCζ, hζ⟩ := norm_riemannZeta_le_const_mul_of_half_le_re
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set C₀ : ℝ := Cγ / 2 + 3 + (|Real.log Cζ| + Cγ) / (2 * Real.log 2) with hC₀def
  have hfrac : 0 ≤ (|Real.log Cζ| + Cγ) / (2 * Real.log 2) :=
    div_nonneg (add_nonneg (abs_nonneg _) hCγ.le) (by positivity)
  have hC0 : 0 < C₀ := by rw [hC₀def]; linarith [hfrac, hCγ]
  have main : ∀ s : ℂ, (1 : ℝ) / 2 ≤ s.re → 2 ≤ ‖s‖ →
      ‖riemannXi s‖ ≤ Real.exp (C₀ * (‖s‖ * Real.log ‖s‖)) := by
    intro s hs hsnorm
    have hσpos : 0 < s.re := by linarith
    have hN0 : 0 < ‖s‖ := by linarith
    have hL0 : 0 ≤ Real.log ‖s‖ := Real.log_nonneg (by linarith)
    have hs0 : s ≠ 0 := by rintro rfl; simp at hN0
    have hs1 : s ≠ 1 := by rintro rfl; rw [norm_one] at hsnorm; norm_num at hsnorm
    have hhalf : ‖s / 2‖ = ‖s‖ / 2 := by rw [norm_div, show ‖(2 : ℂ)‖ = 2 by norm_num]
    set P := ‖s‖ * Real.log ‖s‖ with hP
    have hP0 : 0 ≤ P := mul_nonneg hN0.le hL0
    have hPlow : 2 * Real.log 2 ≤ P := by
      rw [hP]
      nlinarith [Real.log_le_log (by norm_num : (0 : ℝ) < 2) hsnorm, hl2, hL0,
        mul_nonneg (by linarith : (0 : ℝ) ≤ ‖s‖ - 2) hL0]
    have hlogP : Real.log ‖s‖ ≤ P := by
      rw [hP]; nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ ‖s‖ - 1) hL0]
    have hpre : ‖(1 / 2 : ℂ) * (s * (s - 1))‖ ≤ ‖s‖ ^ 2 := by
      rw [norm_mul, norm_mul, show ‖(1 / 2 : ℂ)‖ = 1 / 2 by norm_num]
      nlinarith [mul_le_mul_of_nonneg_left (by simpa using norm_sub_le s 1) (norm_nonneg s),
        mul_nonneg (norm_nonneg s) (by linarith : (0 : ℝ) ≤ ‖s‖ - 1)]
    have hΓnorm : ‖Gammaℝ s‖ ≤ Real.exp (Cγ * (1 / 2 * P + 1)) := by
      rw [Gammaℝ_def, norm_mul]
      have hπ : ‖(↑Real.pi : ℂ) ^ (-s / 2)‖ ≤ 1 := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
        refine Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.pi_gt_three]) ?_
        rw [Complex.div_ofNat_re, Complex.neg_re]; linarith
      have hG : ‖s / 2‖ * Real.log ‖s / 2‖ ≤ 1 / 2 * P := by
        rw [hhalf, hP]
        have hlogle : Real.log (‖s‖ / 2) ≤ Real.log ‖s‖ :=
          Real.log_le_log (by linarith) (by linarith)
        nlinarith [Real.log_nonneg (show (1 : ℝ) ≤ ‖s‖ / 2 by linarith),
          mul_le_mul_of_nonneg_left hlogle (by linarith : (0 : ℝ) ≤ ‖s‖ / 2)]
      refine (mul_le_mul hπ (hγ (s / 2) (by rw [Complex.div_ofNat_re]; linarith)
        (by rw [hhalf]; linarith)) (norm_nonneg _) (by norm_num)).trans ?_
      exact (one_mul _).trans_le
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by linarith) hCγ.le))
    have hcombine : ‖riemannXi s‖ ≤ ‖s‖ ^ 2 * Real.exp (Cγ * (1 / 2 * P + 1)) * (Cζ * ‖s‖) := by
      rw [riemannXi_eq_prefactor_mul hs0 hs1 (Gammaℝ_ne_zero_of_re_pos hσpos), norm_mul, norm_mul]
      exact mul_le_mul (mul_le_mul hpre hΓnorm (norm_nonneg _) (by positivity))
        (hζ s hs hsnorm) (norm_nonneg _) (by positivity)
    have hrw : ‖s‖ ^ 2 * Real.exp (Cγ * (1 / 2 * P + 1)) * (Cζ * ‖s‖)
        = Real.exp (Real.log Cζ + 3 * Real.log ‖s‖ + Cγ * (1 / 2 * P + 1)) := by
      have hcube : ‖s‖ ^ 3 = Real.exp (3 * Real.log ‖s‖) := by
        rw [← Real.rpow_natCast ‖s‖ 3, Real.rpow_def_of_pos hN0]; congr 1; push_cast; ring
      rw [Real.exp_add, Real.exp_add, Real.exp_log hCζ, ← hcube]; ring
    refine (hcombine.trans_eq hrw).trans (Real.exp_le_exp.mpr ?_)
    have hconst : Real.log Cζ + Cγ ≤ ((|Real.log Cζ| + Cγ) / (2 * Real.log 2)) * P :=
      calc Real.log Cζ + Cγ ≤ |Real.log Cζ| + Cγ := by linarith [le_abs_self (Real.log Cζ)]
        _ = ((|Real.log Cζ| + Cγ) / (2 * Real.log 2)) * (2 * Real.log 2) := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left hPlow hfrac
    rw [hC₀def]
    linarith [hconst, hlogP]
  refine ⟨4 * C₀, by linarith [hC0], fun s hsnorm ↦ ?_⟩
  by_cases hcase : (1 : ℝ) / 2 ≤ s.re
  · refine (main s hcase hsnorm).trans (Real.exp_le_exp.mpr ?_)
    linarith [mul_nonneg hC0.le (mul_nonneg (by linarith : (0 : ℝ) ≤ ‖s‖)
      (Real.log_nonneg (by linarith : (1 : ℝ) ≤ ‖s‖)))]
  · rw [not_le] at hcase
    have hre' : (1 : ℝ) / 2 ≤ (1 - s).re := by simp; linarith
    have hnorm_ge : ‖s‖ ≤ ‖1 - s‖ := by simpa using norm_sub_one_le_norm_of_half_le_re hre'
    have hnorm_le : ‖1 - s‖ ≤ 2 * ‖s‖ := by
      have := norm_sub_le (1 : ℂ) s; rw [norm_one] at this; linarith
    have hloga0 : 0 ≤ Real.log ‖1 - s‖ := Real.log_nonneg (by linarith)
    rw [← riemannXi_one_sub s]
    refine (main (1 - s) hre' (hsnorm.trans hnorm_ge)).trans (Real.exp_le_exp.mpr ?_)
    have hloga : Real.log ‖1 - s‖ ≤ 2 * Real.log ‖s‖ := by
      have h1 : Real.log ‖1 - s‖ ≤ Real.log (2 * ‖s‖) := Real.log_le_log (by linarith) hnorm_le
      rw [Real.log_mul (by norm_num) (by linarith)] at h1
      linarith [Real.log_le_log (by norm_num : (0 : ℝ) < 2) hsnorm]
    have hala : ‖1 - s‖ * Real.log ‖1 - s‖ ≤ 4 * (‖s‖ * Real.log ‖s‖) := by
      nlinarith [mul_le_mul_of_nonneg_right hnorm_le hloga0,
        mul_le_mul_of_nonneg_left hloga (by linarith [norm_nonneg s] : (0 : ℝ) ≤ 2 * ‖s‖)]
    linarith [mul_le_mul_of_nonneg_left hala hC0.le]
end
end CountPort19
section CountPort20
section
open Complex Filter Topology MeasureTheory Set Function MeromorphicOn Metric
open scoped ENNReal NNReal
private theorem meromorphic_riemannXi : Meromorphic riemannXi :=
  fun z ↦ (analyticOnNhd_riemannXi z (mem_univ z)).meromorphicAt
theorem logCounting_riemannXi_le :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 2 ≤ R →
      Function.locallyFinsuppWithin.logCounting (MeromorphicOn.divisor riemannXi ⊤) R
        ≤ C * (R * Real.log R) := by
  obtain ⟨Cξ, hCξ, hξ⟩ := norm_riemannXi_le_exp
  refine ⟨Cξ + 1 / 2, by linarith, fun R hR ↦ ?_⟩
  have hRpos : (0 : ℝ) < R := by linarith
  simp only [Set.top_eq_univ]
  rw [Function.locallyFinsuppWithin.logCounting_divisor_eq_circleAverage_sub_const
      meromorphic_riemannXi hRpos.ne',
    (analyticOnNhd_riemannXi 0 (mem_univ 0)).meromorphicTrailingCoeffAt_of_ne_zero
      (by rw [riemannXi_zero]; norm_num),
    riemannXi_zero,
    show Real.log ‖(1 : ℂ) / 2‖ = -Real.log 2 from by
      rw [Complex.norm_div, norm_one, Complex.norm_ofNat, one_div, Real.log_inv]]
  have hca : Real.circleAverage (fun x ↦ Real.log ‖riemannXi x‖) 0 R ≤ Cξ * (R * Real.log R) := by
    refine Real.circleAverage_mono_on_of_le_circle
      (MeromorphicOn.circleIntegrable_log_norm (fun z _ ↦ meromorphic_riemannXi z)) fun x hx ↦ ?_
    rw [mem_sphere_iff_norm, sub_zero, abs_of_pos hRpos] at hx
    by_cases hzero : riemannXi x = 0
    · rw [hzero, norm_zero, Real.log_zero]
      exact mul_nonneg hCξ.le (mul_nonneg hRpos.le (Real.log_nonneg (by linarith)))
    · rw [Real.log_le_iff_le_exp (norm_pos_iff.mpr hzero), ← hx]
      exact hξ x (by rw [hx]; exact hR)
  have hl2R : Real.log 2 ≤ 1 / 2 * (R * Real.log R) := by
    linarith [Real.log_le_log (show (0 : ℝ) < 2 by norm_num) hR,
      mul_nonneg (show (0 : ℝ) ≤ R - 2 by linarith)
        (Real.log_nonneg (show (1 : ℝ) ≤ R by linarith))]
  linarith
theorem divisor_riemannXi_nonneg : 0 ≤ MeromorphicOn.divisor riemannXi (⊤ : Set ℂ) :=
  analyticOnNhd_riemannXi.divisor_nonneg
theorem divisor_riemannXi_cast_nonneg (z : ℂ) :
    (0 : ℝ) ≤ ((MeromorphicOn.divisor riemannXi ⊤ z : ℤ) : ℝ) := by
  exact_mod_cast divisor_riemannXi_nonneg z
theorem divisor_riemannXi_toNat_cast (z : ℂ) :
    (((MeromorphicOn.divisor riemannXi ⊤ z).toNat : ℕ) : ℝ)
      = ((MeromorphicOn.divisor riemannXi ⊤ z : ℤ) : ℝ) := by
  exact_mod_cast Int.toNat_of_nonneg (divisor_riemannXi_nonneg z)
theorem divisor_riemannXi_apply_zero : MeromorphicOn.divisor riemannXi (⊤ : Set ℂ) 0 = 0 := by
  have hanalytic : AnalyticAt ℂ riemannXi 0 := analyticOnNhd_riemannXi 0 (mem_univ 0)
  change MeromorphicOn.divisor riemannXi univ 0 = 0
  rw [MeromorphicOn.divisor_apply (fun z _ ↦ meromorphic_riemannXi z) (mem_univ 0),
    hanalytic.meromorphicOrderAt_eq,
    analyticOrderAt_eq_zero.mpr (Or.inr (by rw [riemannXi_zero]; norm_num))]
  rfl
noncomputable def riemannXiZeroCount (R : ℝ) : ℝ :=
  ∑ᶠ z, ((MeromorphicOn.divisor riemannXi (Metric.closedBall 0 R) z : ℤ) : ℝ)
theorem divisor_riemannXi_closedBall_eq (R : ℝ) {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) R) :
    MeromorphicOn.divisor riemannXi (closedBall 0 R) z = MeromorphicOn.divisor riemannXi ⊤ z := by
  rw [MeromorphicOn.divisor_apply (fun w _ ↦ meromorphic_riemannXi w) hz]
  change _ = MeromorphicOn.divisor riemannXi univ z
  rw [MeromorphicOn.divisor_apply (fun w _ ↦ meromorphic_riemannXi w) (mem_univ z)]
theorem tsum_toNat_divisor_closedBall (R : ℝ) :
    ∑' z : closedBall (0 : ℂ) R, ((MeromorphicOn.divisor riemannXi ⊤ (z : ℂ)).toNat : ℝ≥0∞)
      = ENNReal.ofReal (riemannXiZeroCount R) := by
  have hsupp : (Function.support
      fun w : ℂ ↦ ((MeromorphicOn.divisor riemannXi (closedBall 0 R) w : ℤ) : ℝ)).Finite :=
    ((MeromorphicOn.divisor riemannXi (closedBall 0 R)).finiteSupport
      (isCompact_closedBall 0 R)).subset fun z hz ↦ by simpa [Function.mem_support] using hz
  have hnn : ∀ w : ℂ, (0 : ℝ) ≤ ((MeromorphicOn.divisor riemannXi (closedBall 0 R) w : ℤ) : ℝ) :=
    fun w ↦ by exact_mod_cast (analyticOnNhd_riemannXi.mono (subset_univ _)).divisor_nonneg w
  rw [riemannXiZeroCount, ← tsum_eq_finsum (L := SummationFilter.unconditional ℂ) hsupp,
    ENNReal.ofReal_tsum_of_nonneg hnn (summable_of_hasFiniteSupport hsupp),
    tsum_subtype (closedBall (0 : ℂ) R)
      (fun w ↦ ((MeromorphicOn.divisor riemannXi ⊤ w).toNat : ℝ≥0∞))]
  refine tsum_congr fun w ↦ ?_
  by_cases hw : w ∈ closedBall (0 : ℂ) R
  · rw [Set.indicator_of_mem hw, divisor_riemannXi_closedBall_eq R hw,
      ← divisor_riemannXi_toNat_cast w, ENNReal.ofReal_natCast]
  · rw [Set.indicator_of_notMem hw,
      Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hw]
    simp
theorem riemannXiZeroCount_le :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 2 ≤ R → riemannXiZeroCount R ≤ C * (R * Real.log R) := by
  obtain ⟨CN, hCN, hN⟩ := logCounting_riemannXi_le
  have hl2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨4 * CN / Real.log 2, by positivity, fun R hR ↦ ?_⟩
  have hRpos : (0 : ℝ) < R := by linarith
  have h2Rabs : |2 * R| = 2 * R := abs_of_pos (by linarith)
  have hRHSnn : ∀ z : ℂ, 0 ≤ ((Function.locallyFinsuppWithin.toClosedBall (2 * R)
      (MeromorphicOn.divisor riemannXi ⊤)) z : ℝ) * Real.log (2 * R * ‖z‖⁻¹) := fun z ↦ by
    by_cases hz2R : z ∈ closedBall (0 : ℂ) (2 * R)
    · rcases eq_or_ne z 0 with rfl | hz0
      · simp
      · have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz0
        have hznorm : ‖z‖ ≤ 2 * R := by simpa [Metric.mem_closedBall, dist_eq_norm] using hz2R
        rw [Function.locallyFinsuppWithin.toClosedBall_eval_within _ (by rwa [h2Rabs])]
        exact mul_nonneg (divisor_riemannXi_cast_nonneg z)
          (Real.log_nonneg (by rw [le_mul_inv_iff₀ hzpos]; linarith))
    · rw [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ (by rw [h2Rabs]; exact hz2R)]
      simp
  have hkey : Real.log 2 * riemannXiZeroCount R ≤
      Function.locallyFinsuppWithin.logCounting (MeromorphicOn.divisor riemannXi ⊤) (2 * R) := by
    rw [show Function.locallyFinsuppWithin.logCounting (MeromorphicOn.divisor riemannXi ⊤) (2 * R)
          = ∑ᶠ z, ((Function.locallyFinsuppWithin.toClosedBall (2 * R)
              (MeromorphicOn.divisor riemannXi ⊤)) z : ℝ) * Real.log (2 * R * ‖z‖⁻¹)
            + ((MeromorphicOn.divisor riemannXi ⊤) 0 : ℝ) * Real.log (2 * R) from by
        simp only [Function.locallyFinsuppWithin.logCounting, AddMonoidHom.coe_mk, ZeroHom.coe_mk]]
    rw [divisor_riemannXi_apply_zero, Int.cast_zero, zero_mul, add_zero, riemannXiZeroCount,
      mul_finsum]
    refine finsum_le_finsum' ?_ ?_ ?_
    · refine ((MeromorphicOn.divisor riemannXi (closedBall 0 R)).finiteSupport
        (isCompact_closedBall 0 R)).subset (fun z hz ↦ ?_)
      simp only [Function.mem_support, ne_eq, mul_eq_zero, not_or, Int.cast_eq_zero] at hz
      simpa [Function.mem_support] using hz.2
    · refine ((Function.locallyFinsuppWithin.toClosedBall (2 * R)
        (MeromorphicOn.divisor riemannXi ⊤)).finiteSupport
          (isCompact_closedBall 0 |2 * R|)).subset (fun z hz ↦ ?_)
      simpa [Function.mem_support, Int.cast_eq_zero]
        using Function.support_mul_subset_left _ _ hz
    · intro z
      dsimp only
      by_cases hzR : z ∈ closedBall (0 : ℂ) R
      ·
        rw [divisor_riemannXi_closedBall_eq R hzR]
        rcases eq_or_ne z 0 with rfl | hz0
        · rw [divisor_riemannXi_apply_zero]; simp
        · have hznorm : ‖z‖ ≤ R := by simpa [Metric.mem_closedBall, dist_eq_norm] using hzR
          have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz0
          rw [Function.locallyFinsuppWithin.toClosedBall_eval_within _ (by
            rw [h2Rabs]; simp only [Metric.mem_closedBall, dist_eq_norm, sub_zero]; linarith)]
          have hloglow : Real.log 2 ≤ Real.log (2 * R * ‖z‖⁻¹) :=
            Real.log_le_log (by norm_num) (by rw [le_mul_inv_iff₀ hzpos]; linarith)
          linarith [mul_le_mul_of_nonneg_left hloglow (divisor_riemannXi_cast_nonneg z)]
      ·
        rw [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hzR, Int.cast_zero, mul_zero]
        exact hRHSnn z
  have hlog2R : Real.log (2 * R) ≤ 2 * Real.log R := by
    rw [Real.log_mul (by norm_num) (ne_of_gt hRpos)]
    linarith [Real.log_le_log (show (0 : ℝ) < 2 by norm_num) hR]
  have hstep : CN * (2 * R * Real.log (2 * R)) ≤ 4 * CN * (R * Real.log R) := by
    rw [show 4 * CN * (R * Real.log R) = CN * (2 * R * (2 * Real.log R)) by ring]
    gcongr
  rw [div_mul_eq_mul_div, le_div_iff₀ hl2]
  linarith [hkey.trans ((hN (2 * R) (by linarith)).trans hstep)]
private theorem exists_dyadic_shell {x : ℝ} (hx : 1 < x) :
    ∃ k : ℕ, (2 : ℝ) ^ k ≤ x ∧ x < 2 ^ (k + 1) := by
  obtain ⟨n, hn1, hn2⟩ :=
    exists_mem_Ico_zpow (by linarith : (0 : ℝ) < x) (by norm_num : (1 : ℝ) < 2)
  have hn0 : 0 ≤ n := by
    by_contra h
    rw [not_le] at h
    have h1 : (2 : ℝ) ^ (n + 1) ≤ (2 : ℝ) ^ (0 : ℤ) :=
      zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by lia)
    rw [zpow_zero] at h1; linarith
  exact ⟨n.toNat, by rw [← zpow_natCast, Int.toNat_of_nonneg hn0]; exact hn1,
    by rw [← zpow_natCast (2 : ℝ) (n.toNat + 1), Nat.cast_add, Nat.cast_one,
        Int.toNat_of_nonneg hn0]; exact hn2⟩
theorem summable_riemannXiDivisor_norm_rpow {p : ℝ} (hp : 1 < p) :
    Summable (fun z : ℂ ↦ ((MeromorphicOn.divisor riemannXi ⊤ z : ℤ) : ℝ) * ‖z‖ ^ (-p)) := by
  obtain ⟨Cn, hCn, hn⟩ := riemannXiZeroCount_le
  set g : ℂ → ℝ := fun z ↦ ((MeromorphicOn.divisor riemannXi ⊤ z : ℤ) : ℝ) * ‖z‖ ^ (-p) with hg
  have hgnn : ∀ z, 0 ≤ g z := fun z ↦ mul_nonneg (divisor_riemannXi_cast_nonneg z) (by positivity)
  rw [show g = fun z ↦ ((Real.toNNReal (g z) : ℝ≥0) : ℝ) from
      funext fun z ↦ (Real.coe_toNNReal _ (hgnn z)).symm,
    ← ENNReal.tsum_coe_ne_top_iff_summable_coe]
  change (∑' z : ℂ, ENNReal.ofReal (g z)) ≠ ∞
  set s : ℝ := (2 : ℝ) ^ (-p) with hs
  set r : ℝ := 2 * s with hr
  have hreq : r = (2 : ℝ) ^ (1 - p) := by
    rw [hr, hs, sub_eq_add_neg, Real.rpow_add (by norm_num), Real.rpow_one]
  have hr0 : 0 < r := by rw [hreq]; positivity
  have hr1 : r < 1 := by
    rw [hreq]; exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  set A : ℕ → Set ℂ := fun k ↦ {z | (2 : ℝ) ^ k ≤ ‖z‖ ∧ ‖z‖ < (2 : ℝ) ^ (k + 1)}
  have hcover : (univ : Set ℂ) ⊆ closedBall (0 : ℂ) 1 ∪ ⋃ k : ℕ, A k := fun z _ ↦ by
    by_cases h1 : ‖z‖ ≤ 1
    · exact Or.inl (by simpa [Metric.mem_closedBall, dist_eq_norm] using h1)
    · exact Or.inr (mem_iUnion.mpr (exists_dyadic_shell (not_le.mp h1)))
  set B : ℕ → ℝ := fun k ↦ 2 * Cn * Real.log 2 * (((k : ℝ) + 1) * r ^ k) with hB
  have hBnn : ∀ k, 0 ≤ B k := fun k ↦ by rw [hB]; positivity
  have hBsum : Summable B := by
    have h1 := summable_pow_mul_geometric_of_norm_lt_one 1 (r := r)
      (by rwa [Real.norm_eq_abs, abs_of_nonneg hr0.le])
    rw [hB]
    exact (((h1.add (summable_geometric_of_lt_one hr0.le hr1)).congr
      fun k ↦ by rw [pow_one]; ring).mul_left _)
  have hshell : ∀ k : ℕ, ∑' z : A k, ENNReal.ofReal (g z) ≤ ENNReal.ofReal (B k) := fun k ↦ by
    have h2k1 : (2 : ℝ) ≤ 2 ^ (k + 1) := by
      simpa using pow_le_pow_right₀ one_le_two (Nat.le_add_left 1 k)
    have hskeq : ((2 : ℝ) ^ k) ^ (-p) = s ^ k := by
      rw [hs, ← Real.rpow_natCast ((2 : ℝ) ^ (-p)) k, ← Real.rpow_natCast (2 : ℝ) k,
        ← Real.rpow_mul (by norm_num), ← Real.rpow_mul (by norm_num), mul_comm]
    have hlognn : 0 ≤ Cn * (2 ^ (k + 1) * Real.log (2 ^ (k + 1))) :=
      mul_nonneg hCn.le (mul_nonneg (by positivity)
        (Real.log_nonneg (one_le_pow₀ (by norm_num))))
    calc ∑' z : A k, ENNReal.ofReal (g z)
        ≤ ∑' z : A k, ((MeromorphicOn.divisor riemannXi ⊤ (z : ℂ)).toNat : ℝ≥0∞)
            * ENNReal.ofReal (s ^ k) := by
          refine ENNReal.tsum_le_tsum fun z ↦ ?_
          rw [← ENNReal.ofReal_natCast, divisor_riemannXi_toNat_cast,
            ← ENNReal.ofReal_mul (divisor_riemannXi_cast_nonneg _)]
          refine ENNReal.ofReal_le_ofReal ?_
          simp only [hg]
          exact mul_le_mul_of_nonneg_left
            (hskeq ▸ Real.rpow_le_rpow_of_nonpos (by positivity) z.2.1 (by linarith))
            (divisor_riemannXi_cast_nonneg _)
      _ = (∑' z : A k, ((MeromorphicOn.divisor riemannXi ⊤ (z : ℂ)).toNat : ℝ≥0∞))
            * ENNReal.ofReal (s ^ k) := ENNReal.tsum_mul_right
      _ ≤ ENNReal.ofReal (riemannXiZeroCount (2 ^ (k + 1))) * ENNReal.ofReal (s ^ k) := by
          rw [← tsum_toNat_divisor_closedBall]
          gcongr
          exact ENNReal.tsum_mono_subtype
            (fun w ↦ ((MeromorphicOn.divisor riemannXi ⊤ w).toNat : ℝ≥0∞))
            fun z hz ↦ by simpa [Metric.mem_closedBall, dist_eq_norm] using hz.2.le
      _ ≤ ENNReal.ofReal (Cn * (2 ^ (k + 1) * Real.log (2 ^ (k + 1))))
            * ENNReal.ofReal (s ^ k) := by gcongr; exact hn _ h2k1
      _ = ENNReal.ofReal (B k) := by
          rw [← ENNReal.ofReal_mul hlognn]
          simp only [hB]
          congr 1
          rw [Real.log_pow, pow_succ, hr, mul_pow]
          push_cast; ring
  have hinner : (∑' z : closedBall (0 : ℂ) 1, ENNReal.ofReal (g z)) ≠ ∞ := by
    refine (summable_of_hasFiniteSupport (Set.Finite.subset
      (((MeromorphicOn.divisor riemannXi (closedBall 0 1)).finiteSupport
        (isCompact_closedBall 0 1)).preimage Subtype.coe_injective.injOn)
      fun z hz ↦ ?_)).tsum_ofReal_ne_top
    rw [Set.mem_preimage, Function.mem_support, divisor_riemannXi_closedBall_eq 1 z.2]
    exact fun h0 ↦ hz (by simp only [hg]; rw [h0]; simp)
  have hBtop : (∑' k : ℕ, ENNReal.ofReal (B k)) ≠ ∞ := by
    rw [← ENNReal.ofReal_tsum_of_nonneg hBnn hBsum]; exact ENNReal.ofReal_ne_top
  refine ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hinner, hBtop⟩) ?_
  calc ∑' z : ℂ, ENNReal.ofReal (g z)
      = ∑' z : (univ : Set ℂ), ENNReal.ofReal (g z) := (tsum_univ _).symm
    _ ≤ ∑' z : (closedBall (0 : ℂ) 1 ∪ (⋃ k : ℕ, A k) : Set ℂ), ENNReal.ofReal (g z) :=
        ENNReal.tsum_mono_subtype (fun w ↦ ENNReal.ofReal (g w)) hcover
    _ ≤ (∑' z : closedBall (0 : ℂ) 1, ENNReal.ofReal (g z))
          + ∑' z : (⋃ k : ℕ, A k : Set ℂ), ENNReal.ofReal (g z) :=
        ENNReal.tsum_union_le (fun w ↦ ENNReal.ofReal (g w)) _ _
    _ ≤ (∑' z : closedBall (0 : ℂ) 1, ENNReal.ofReal (g z)) + ∑' k : ℕ, ENNReal.ofReal (B k) := by
        gcongr
        exact (ENNReal.tsum_iUnion_le_tsum (fun w ↦ ENNReal.ofReal (g w)) A).trans
          (ENNReal.tsum_le_tsum hshell)
theorem summable_inv_norm_sq_riemannXiZeros :
    Summable (fun i : (z : (MeromorphicOn.divisor riemannXi ⊤).support) ×
        Fin (MeromorphicOn.divisor riemannXi ⊤ (z : ℂ)).toNat ↦ ‖((i.1 : ℂ))⁻¹‖ ^ 2) := by
  rw [summable_sigma_of_nonneg (fun _ ↦ by positivity)]
  refine ⟨fun x ↦ (hasSum_fintype _).summable, ?_⟩
  refine ((summable_riemannXiDivisor_norm_rpow (show (1 : ℝ) < 2 by norm_num)).subtype
    (MeromorphicOn.divisor riemannXi ⊤).support).congr fun z ↦ ?_
  rw [tsum_fintype]
  simp only [Function.comp_apply, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, divisor_riemannXi_toNat_cast]
  rw [norm_inv, inv_pow, ← Real.rpow_natCast ‖z.1‖ 2, ← Real.rpow_neg (norm_nonneg _)]
  norm_num
end
end CountPort20
section CountPort21
section
open Complex Filter Topology MeromorphicOn Set Function Metric
abbrev RiemannXiZerosIndex : Type :=
  (z : (MeromorphicOn.divisor riemannXi ⊤).support) ×
    Fin (MeromorphicOn.divisor riemannXi ⊤ (z : ℂ)).toNat
abbrev riemannXiZeros (i : RiemannXiZerosIndex) : ℂ := (i.1 : ℂ)
theorem riemannXiZeros_ne_zero (i : RiemannXiZerosIndex) : riemannXiZeros i ≠ 0 := by
  intro h
  have hmem : MeromorphicOn.divisor riemannXi ⊤ (i.1 : ℂ) ≠ 0 := by
    have := i.1.2; rwa [Function.mem_support] at this
  rw [show (i.1 : ℂ) = 0 from h, divisor_riemannXi_apply_zero] at hmem
  exact hmem rfl
private theorem untop₀_map_natCast (x : ℕ∞) :
    (ENat.map (Nat.cast : ℕ → ℤ) x).untop₀ = (x.toNat : ℤ) := by
  induction x using ENat.recTopCoe <;> simp
theorem divisor_eq_analyticOrderNatAt {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f ⊤) (z : ℂ) :
    MeromorphicOn.divisor f ⊤ z = (analyticOrderNatAt f z : ℤ) := by
  rw [MeromorphicOn.divisor_apply hf.meromorphicOn (Set.mem_univ _),
    (hf z (Set.mem_univ _)).meromorphicOrderAt_eq, untop₀_map_natCast]
  rfl
theorem ncard_setOf_riemannXiZeros_eq (z : ℂ) :
    {i | riemannXiZeros i = z}.ncard = (MeromorphicOn.divisor riemannXi ⊤ z).toNat := by
  by_cases hz : z ∈ (MeromorphicOn.divisor riemannXi ⊤).support
  · have hset : {i | riemannXiZeros i = z}
        = {i : RiemannXiZerosIndex | i.1 = ⟨z, hz⟩} := by
      ext i
      simp only [Set.mem_ofPred_eq, riemannXiZeros, Subtype.ext_iff]
    rw [hset]
    calc {i : RiemannXiZerosIndex |
            i.1 = (⟨z, hz⟩ : (MeromorphicOn.divisor riemannXi ⊤).support)}.ncard
        = Nat.card {i : RiemannXiZerosIndex //
            i.1 = (⟨z, hz⟩ : (MeromorphicOn.divisor riemannXi ⊤).support)} :=
          (Nat.card_coe_set_eq _).symm
      _ = Nat.card (Fin (MeromorphicOn.divisor riemannXi ⊤ z).toNat) :=
          Nat.card_congr (Equiv.sigmaSubtype
            (⟨z, hz⟩ : (MeromorphicOn.divisor riemannXi ⊤).support))
      _ = (MeromorphicOn.divisor riemannXi ⊤ z).toNat := by simp
  · have hempty : {i | riemannXiZeros i = z} = ∅ := by
      ext i
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, riemannXiZeros]
      intro h
      exact hz (h ▸ i.1.2)
    simp only [Function.mem_support, ne_eq, not_not] at hz
    rw [hempty, Set.ncard_empty, hz, Int.toNat_zero]
theorem divisor_riemannXiCanonicalProduct_riemannXiZeros_eq :
    MeromorphicOn.divisor (riemannXiCanonicalProduct riemannXiZeros) ⊤
      = MeromorphicOn.divisor riemannXi ⊤ := by
  have hsum : Summable (fun i ↦ ‖(riemannXiZeros i)⁻¹‖ ^ 2) :=
    summable_inv_norm_sq_riemannXiZeros
  have hPanalytic : AnalyticOnNhd ℂ (riemannXiCanonicalProduct riemannXiZeros) ⊤ :=
    (differentiable_riemannXiCanonicalProduct riemannXiZeros hsum).differentiableOn.analyticOnNhd
      isOpen_univ
  ext z
  have hξnn : 0 ≤ MeromorphicOn.divisor riemannXi ⊤ z := by
    rw [divisor_eq_analyticOrderNatAt analyticOnNhd_riemannXi z]; positivity
  rw [divisor_eq_analyticOrderNatAt hPanalytic z,
    analyticOrderNatAt_riemannXiCanonicalProduct riemannXiZeros hsum riemannXiZeros_ne_zero z,
    ncard_setOf_riemannXiZeros_eq z, Int.toNat_of_nonneg hξnn]
theorem differentiable_riemannXi_div_canonicalProduct :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ (∀ s, g s ≠ 0) ∧
      (∀ s, riemannXi s = g s * riemannXiCanonicalProduct riemannXiZeros s) ∧ g 0 = 1 / 2 := by
  set P := riemannXiCanonicalProduct riemannXiZeros with hP
  have hsum : Summable (fun i ↦ ‖(riemannXiZeros i)⁻¹‖ ^ 2) :=
    summable_inv_norm_sq_riemannXiZeros
  have hPdiff : Differentiable ℂ P := differentiable_riemannXiCanonicalProduct riemannXiZeros hsum
  have hPanalytic : AnalyticOnNhd ℂ P ⊤ := hPdiff.differentiableOn.analyticOnNhd isOpen_univ
  have hξanalytic : AnalyticOnNhd ℂ riemannXi ⊤ := analyticOnNhd_riemannXi
  have hPmero : MeromorphicOn P ⊤ := hPanalytic.meromorphicOn
  have hξmero : MeromorphicOn riemannXi ⊤ := hξanalytic.meromorphicOn
  have hP0 : P 0 = 1 := riemannXiCanonicalProduct_zero riemannXiZeros
  have hP0ne : P 0 ≠ 0 := by rw [hP0]; norm_num
  set F : ℂ → ℂ := fun s ↦ riemannXi s / P s with hF
  have hFmero : MeromorphicOn F ⊤ := hξmero.div hPmero
  have hmordne : ∀ (f : ℂ → ℂ) (x : ℂ), AnalyticOnNhd ℂ f ⊤ → f x ≠ 0 →
      ∀ z ∈ (⊤ : Set ℂ), meromorphicOrderAt f z ≠ ⊤ := fun f x hf hx z hz ↦
    meromorphicOrderAt_ne_top_of_isPreconnected hf.meromorphicOn isPreconnected_univ
      (Set.mem_univ x) hz (by
        rw [(hf x (Set.mem_univ _)).meromorphicOrderAt_eq,
          (hf x (Set.mem_univ _)).analyticOrderAt_eq_zero.mpr hx]; simp)
  have hξne := hmordne riemannXi 0 hξanalytic (by rw [riemannXi_zero]; norm_num)
  have hPne := hmordne P 0 hPanalytic hP0ne
  have hPinvne : ∀ z ∈ (⊤ : Set ℂ), meromorphicOrderAt P⁻¹ z ≠ ⊤ := by
    intro z hz
    rw [meromorphicOrderAt_inv]
    simpa using hPne z hz
  have hdivF : MeromorphicOn.divisor F ⊤ = 0 := by
    have hFeq : F = riemannXi * P⁻¹ := by
      funext s; simp only [hF, Pi.mul_apply, Pi.inv_apply, div_eq_mul_inv]
    rw [hFeq, MeromorphicOn.divisor_mul hξmero hPmero.inv hξne hPinvne,
      MeromorphicOn.divisor_inv, hP, divisor_riemannXiCanonicalProduct_riemannXiZeros_eq,
      add_neg_cancel]
  set g := toMeromorphicNFOn F ⊤ with hg
  have hgNF : MeromorphicNFOn g ⊤ := meromorphicNFOn_toMeromorphicNFOn F ⊤
  have hdivg0 : MeromorphicOn.divisor g ⊤ = 0 :=
    (MeromorphicOn.divisor_of_toMeromorphicNFOn hFmero).trans hdivF
  have hganalytic : AnalyticOnNhd ℂ g ⊤ :=
    hgNF.divisor_nonneg_iff_analyticOnNhd.mp (le_of_eq hdivg0.symm)
  have hgdiff : Differentiable ℂ g := fun s ↦ (hganalytic s (Set.mem_univ _)).differentiableAt
  have hFanalytic0 : AnalyticAt ℂ F 0 := by
    rw [hF]; exact (hξanalytic 0 (Set.mem_univ _)).div (hPanalytic 0 (Set.mem_univ _)) hP0ne
  have hF0 : F 0 = 1 / 2 := by
    rw [hF]; change riemannXi 0 / P 0 = 1 / 2; rw [riemannXi_zero, hP0]; norm_num
  have hg0 : g 0 = 1 / 2 := by
    have h1 := toMeromorphicNFOn_eq_toMeromorphicNFAt_on_nhds hFmero (Set.mem_univ (0 : ℂ))
    rw [toMeromorphicNFAt_eq_self.mpr hFanalytic0.meromorphicNFAt] at h1
    rw [hg, h1.eq_of_nhds, hF0]
  have hgne : ∀ s, g s ≠ 0 := fun s ↦ by
    rw [← (hgNF (Set.mem_univ s)).meromorphicOrderAt_eq_zero_iff]
    have hne : meromorphicOrderAt g s ≠ ⊤ :=
      hmordne g 0 hganalytic (by rw [hg0]; norm_num) s (Set.mem_univ _)
    have hdiv : (meromorphicOrderAt g s).untop₀ = 0 := by
      rw [← MeromorphicOn.divisor_apply hgNF.meromorphicOn (Set.mem_univ s), hdivg0]; rfl
    exact (WithTop.untop₀_eq_zero.mp hdiv).resolve_right hne
  have hFg : F =ᶠ[codiscreteWithin ⊤] g := toMeromorphicNFOn_eqOn_codiscrete hFmero
  have hPneSet : P ⁻¹' {0}ᶜ ∈ codiscreteWithin (⊤ : Set ℂ) :=
    hPanalytic.preimage_zero_mem_codiscreteWithin hP0ne (Set.mem_univ _) isConnected_univ
  have hgPeqξ : (fun s ↦ g s * P s) =ᶠ[codiscreteWithin ⊤] riemannXi := by
    have e1 : (fun s ↦ g s * P s) =ᶠ[codiscreteWithin ⊤] (fun s ↦ F s * P s) :=
      hFg.symm.mul (EventuallyEq.refl _ P)
    have e2 : (fun s ↦ F s * P s) =ᶠ[codiscreteWithin ⊤] riemannXi := by
      filter_upwards [hPneSet] with s hs
      have hsne : P s ≠ 0 := by
        simpa only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff] using hs
      simp only [hF]
      exact div_mul_cancel₀ (riemannXi s) hsne
    exact e1.trans e2
  have hgPanalytic : AnalyticOnNhd ℂ (fun s ↦ g s * P s) ⊤ :=
    fun z hz ↦ (hganalytic z hz).mul (hPanalytic z hz)
  have hle : 𝓝[≠] (0 : ℂ) ≤ codiscreteWithin (⊤ : Set ℂ) := by
    rw [Filter.codiscreteWithin]
    refine le_iSup₂_of_le (0 : ℂ) (Set.mem_univ _) (le_of_eq ?_)
    rw [Set.top_eq_univ, ← Set.compl_eq_univ_sdiff]
  have hfreq : ∃ᶠ z in 𝓝[≠] (0 : ℂ), (fun s ↦ g s * P s) z = riemannXi z :=
    (hgPeqξ.filter_mono hle).frequently
  exact ⟨g, hgdiff, hgne, fun s ↦ (hgPanalytic.eqOn_of_preconnected_of_frequently_eq hξanalytic
    isPreconnected_univ (Set.mem_univ 0) hfreq (Set.mem_univ s)).symm, hg0⟩
theorem exists_entire_log_riemannXi_div_canonicalProduct :
    ∃ h : ℂ → ℂ, Differentiable ℂ h ∧ h 0 = Complex.log (1 / 2) ∧
      (∀ s, riemannXi s = Complex.exp (h s) *
        riemannXiCanonicalProduct riemannXiZeros s) := by
  obtain ⟨g, hgdiff, hgne, hgP, hg0⟩ := differentiable_riemannXi_div_canonicalProduct
  set φ : ℂ → ℂ := fun s ↦ deriv g s / g s with hφ
  have hgana : AnalyticOnNhd ℂ g Set.univ := hgdiff.differentiableOn.analyticOnNhd isOpen_univ
  have hderivdiff : Differentiable ℂ (deriv g) :=
    fun x ↦ (hgana.deriv x (Set.mem_univ _)).differentiableAt
  have hφdiff : Differentiable ℂ φ := hderivdiff.div hgdiff hgne
  obtain ⟨H, hH0, hHderiv⟩ := hφdiff.isExactOn_univ.with_val_at 0 0
  have hHderiv' : ∀ x, HasDerivAt H (φ x) x := fun x ↦ hHderiv x (Set.mem_univ _)
  have hHdiff : Differentiable ℂ H := fun x ↦ (hHderiv' x).differentiableAt
  set k : ℂ → ℂ := fun s ↦ g s * Complex.exp (-H s) with hk
  have hkderiv : ∀ x, HasDerivAt k 0 x := by
    intro x
    have hg_deriv : HasDerivAt g (deriv g x) x := (hgdiff x).hasDerivAt
    have hexp_deriv := ((hHderiv' x).neg).cexp
    have hval : deriv g x * Complex.exp ((-H) x) +
        g x * (Complex.exp ((-H) x) * -φ x) = 0 := by
      simp only [hφ]
      field_simp [hgne x]
      ring
    exact hval ▸ hg_deriv.mul hexp_deriv
  have hkdiff : Differentiable ℂ k := fun x ↦ (hkderiv x).differentiableAt
  have hkconst : ∀ s, k s = k 0 :=
    fun s ↦ is_const_of_deriv_eq_zero hkdiff (fun x ↦ (hkderiv x).deriv) s 0
  have hk0 : k 0 = 1 / 2 := by
    simp only [hk, hH0, neg_zero, Complex.exp_zero, mul_one, hg0]
  refine ⟨fun s ↦ H s + Complex.log (1 / 2), hHdiff.add_const _, by simp [hH0], fun s ↦ ?_⟩
  have hk_eval : g s * Complex.exp (-H s) = 1 / 2 := by
    have := hkconst s; rw [hk0] at this; simpa only [hk] using this
  have hexp : Complex.exp (H s + Complex.log (1 / 2)) = g s := by
    rw [Complex.exp_add, Complex.exp_log (by norm_num : (1 / 2 : ℂ) ≠ 0), ← hk_eval,
      Complex.exp_neg, mul_comm (g s), ← mul_assoc,
      mul_inv_cancel₀ (Complex.exp_ne_zero _), one_mul]
  rw [hgP s, hexp]
end
end CountPort21
section CountPort22
section
open Complex Filter Topology MeasureTheory
theorem neg_le_log_norm_weierstrassE1 {w : ℂ} (hw : ‖w‖ ≤ 1 / 2) :
    -4 * ‖w‖ ^ 2 ≤ Real.log ‖weierstrassE1 w‖ := by
  set x : ℝ := 2 * ‖w‖ ^ 2 with hx
  have hx0 : 0 ≤ x := by positivity
  have hxle : x ≤ 1 / 2 := by rw [hx]; nlinarith [norm_nonneg w]
  have hpos : 0 < 1 - x := by linarith
  have hge : 1 - x ≤ ‖weierstrassE1 w‖ := by
    have h := norm_sub_norm_le (1 : ℂ) (weierstrassE1 w)
    rw [norm_one, norm_sub_rev] at h
    linarith [norm_weierstrassE1_sub_one_le hw]
  have hlog : -(2 * x) ≤ Real.log (1 - x) := by
    have h := Real.log_le_sub_one_of_pos (show 0 < (1 - x)⁻¹ by positivity)
    rw [Real.log_inv] at h
    nlinarith [mul_inv_cancel₀ hpos.ne', inv_nonneg.mpr hpos.le,
      mul_nonneg hx0 (show (0 : ℝ) ≤ 1 - 2 * x by linarith)]
  calc -4 * ‖w‖ ^ 2 = -(2 * x) := by rw [hx]; ring
    _ ≤ Real.log (1 - x) := hlog
    _ ≤ Real.log ‖weierstrassE1 w‖ := Real.log_le_log hpos hge
theorem Real.log_add_one_sq_le {R : ℝ} (hR : 1 ≤ R) :
    (Real.log R + 1) ^ 2 ≤ 16 * R ^ (1 / 2 : ℝ) := by
  have hR0 : (0 : ℝ) < R := by linarith
  have hnn : 0 ≤ Real.log R + 1 := by linarith [Real.log_nonneg hR]
  have hle : Real.log R + 1 ≤ 4 * R ^ (1 / 4 : ℝ) := by
    have h := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hR0 (1 / 4 : ℝ))
    rw [Real.log_rpow hR0] at h; linarith
  calc (Real.log R + 1) ^ 2 ≤ (4 * R ^ (1 / 4 : ℝ)) ^ 2 := by gcongr
    _ = 16 * R ^ (1 / 2 : ℝ) := by
        rw [mul_pow, ← Real.rpow_natCast (R ^ (1 / 4 : ℝ)) 2, ← Real.rpow_mul hR0.le]; norm_num
theorem finite_setOf_riemannXiZeros_eq (z : ℂ) :
    {i : RiemannXiZerosIndex | riemannXiZeros i = z}.Finite := by
  by_cases hz : z ∈ (MeromorphicOn.divisor riemannXi ⊤).support
  · have hset : {i : RiemannXiZerosIndex | riemannXiZeros i = z}
        = {i : RiemannXiZerosIndex | i.1 = ⟨z, hz⟩} := by
      ext i; simp only [Set.mem_ofPred_eq, riemannXiZeros, Subtype.ext_iff]
    rw [hset, ← Set.finite_coe_iff]
    exact Finite.of_equiv _ (Equiv.sigmaSubtype
      (⟨z, hz⟩ : (MeromorphicOn.divisor riemannXi ⊤).support)).symm
  · have hempty : {i : RiemannXiZerosIndex | riemannXiZeros i = z} = ∅ := by
      ext i
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, riemannXiZeros]
      intro h; exact hz (h ▸ i.1.2)
    rw [hempty]; exact Set.finite_empty
private def zerosInBall (t : ℝ) : Set ℂ :=
  {z | z ∈ (MeromorphicOn.divisor riemannXi ⊤).support ∧ ‖z‖ ≤ t}
private theorem finite_zerosInBall (t : ℝ) : (zerosInBall t).Finite := by
  refine ((MeromorphicOn.divisor riemannXi (Metric.closedBall 0 t)).finiteSupport
    (isCompact_closedBall 0 t)).subset fun z hz ↦ ?_
  obtain ⟨hzsupp, hzt⟩ := hz
  have hzb : z ∈ Metric.closedBall (0 : ℂ) t := by
    simpa only [Metric.mem_closedBall, dist_eq_norm, sub_zero] using hzt
  rw [Function.mem_support, divisor_riemannXi_closedBall_eq t hzb]
  rwa [Function.mem_support] at hzsupp
private theorem setOf_norm_le_eq_biUnion (t : ℝ) :
    {i : RiemannXiZerosIndex | ‖riemannXiZeros i‖ ≤ t}
      = ⋃ z ∈ zerosInBall t, {i : RiemannXiZerosIndex | riemannXiZeros i = z} := by
  ext i
  simp only [Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop]
  exact ⟨fun hi ↦ ⟨riemannXiZeros i, ⟨i.1.2, hi⟩, rfl⟩, fun ⟨_, ⟨_, hzt⟩, hz⟩ ↦ hz ▸ hzt⟩
theorem finite_setOf_norm_riemannXiZeros_le (t : ℝ) :
    {i : RiemannXiZerosIndex | ‖riemannXiZeros i‖ ≤ t}.Finite := by
  rw [setOf_norm_le_eq_biUnion]
  exact (finite_zerosInBall t).biUnion fun z _ ↦ finite_setOf_riemannXiZeros_eq z
theorem ncard_setOf_norm_riemannXiZeros_le_eq (t : ℝ) :
    (({i : RiemannXiZerosIndex | ‖riemannXiZeros i‖ ≤ t}.ncard : ℝ)) = riemannXiZeroCount t := by
  have hZfin := finite_zerosInBall t
  set Zf := hZfin.toFinset
  have hncard : {i : RiemannXiZerosIndex | ‖riemannXiZeros i‖ ≤ t}.ncard
      = ∑ z ∈ Zf, (MeromorphicOn.divisor riemannXi ⊤ z).toNat := by
    rw [setOf_norm_le_eq_biUnion,
      Set.Finite.ncard_biUnion hZfin (fun z _ ↦ finite_setOf_riemannXiZeros_eq z) ?_]
    · rw [← hZfin.coe_toFinset, finsum_mem_coe_finset]
      exact Finset.sum_congr rfl fun z _ ↦ ncard_setOf_riemannXiZeros_eq z
    · intro z₁ _ z₂ _ hne
      refine Set.disjoint_left.mpr fun i hi1 hi2 ↦ hne ?_
      simp only [Set.mem_ofPred_eq] at hi1 hi2
      rw [← hi1, ← hi2]
  have hcount : riemannXiZeroCount t
      = ∑ z ∈ Zf, ((MeromorphicOn.divisor riemannXi ⊤ z).toNat : ℝ) := by
    have hdef : riemannXiZeroCount t
        = ∑ᶠ z, ((MeromorphicOn.divisor riemannXi (Metric.closedBall 0 t) z : ℤ) : ℝ) := rfl
    rw [hdef, finsum_eq_finsetSum_of_support_subset _ (s := Zf) ?subset]
    · refine Finset.sum_congr rfl fun z hz ↦ ?_
      have hzb : z ∈ Metric.closedBall (0 : ℂ) t := by
        simpa [Metric.mem_closedBall, dist_eq_norm] using (hZfin.mem_toFinset.mp hz).2
      rw [divisor_riemannXi_closedBall_eq t hzb]
      exact (divisor_riemannXi_toNat_cast z).symm
    case subset =>
      intro z hz
      have hzint : MeromorphicOn.divisor riemannXi (Metric.closedBall 0 t) z ≠ 0 :=
        Int.cast_ne_zero.mp (Function.mem_support.mp hz)
      have hzb : z ∈ Metric.closedBall (0 : ℂ) t := by
        by_contra hb
        exact hzint (Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hb)
      rw [Finset.mem_coe, hZfin.mem_toFinset]
      refine ⟨Function.mem_support.mpr ?_, by
        simpa [Metric.mem_closedBall, dist_eq_norm] using hzb⟩
      rw [← divisor_riemannXi_closedBall_eq t hzb]; exact hzint
  rw [hncard, hcount, Nat.cast_sum]
theorem exists_card_riemannXiZeros_le :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 2 ≤ t →
      ({i : RiemannXiZerosIndex | ‖riemannXiZeros i‖ ≤ t}.ncard : ℝ) ≤ C * (t * Real.log t) := by
  obtain ⟨C, hC, hbound⟩ := riemannXiZeroCount_le
  exact ⟨C, hC, fun t ht ↦ by rw [ncard_setOf_norm_riemannXiZeros_le_eq t]; exact hbound t ht⟩
theorem exists_mem_Icc_forall_le_dist {S : Finset ℝ} {a b δ : ℝ} (hδ : 0 < δ)
    (hcard : 2 * δ * S.card < b - a) :
    ∃ r ∈ Set.Icc a b, ∀ t ∈ S, δ ≤ |r - t| := by
  classical
  set B : Set ℝ := ⋃ t ∈ S, Set.Ioo (t - δ) (t + δ) with hB
  have hlt : volume B < volume (Set.Icc a b) := by
    have hvolB : volume B ≤ ENNReal.ofReal (2 * δ * S.card) := by
      refine (measure_biUnion_finset_le S _).trans ?_
      rw [show ENNReal.ofReal (2 * δ * S.card) = ∑ _t ∈ S, ENNReal.ofReal (2 * δ) from by
        rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1; ring]
      exact Finset.sum_le_sum fun t _ ↦ le_of_eq (by rw [Real.volume_Ioo]; congr 1; ring)
    rw [Real.volume_Icc]
    exact hvolB.trans_lt ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)).mpr hcard)
  obtain ⟨r, hrIcc, hrB⟩ : (Set.Icc a b \ B).Nonempty :=
    nonempty_of_measure_ne_zero (μ := volume) fun hzero ↦ absurd
      ((measure_mono (Set.subset_sdiff_union (Set.Icc a b) B)).trans
        ((measure_union_le _ _).trans_eq (by rw [hzero, zero_add]))) (not_le.mpr hlt)
  refine ⟨r, hrIcc, fun t ht ↦ ?_⟩
  have hrt : r ∉ Set.Ioo (t - δ) (t + δ) := fun h ↦ hrB (by rw [hB]; exact Set.mem_biUnion ht h)
  rw [Set.mem_Ioo, not_and_or, not_lt, not_lt] at hrt
  rcases hrt with h | h
  · exact le_abs.mpr (.inr (by linarith))
  · exact le_abs.mpr (.inl (by linarith))
private lemma inv_rpow_mul_rpow {a : ℝ} (ha : 0 < a) (p q : ℝ) :
    a⁻¹ ^ p * a ^ q = a ^ (q - p) := by
  rw [Real.inv_rpow ha.le, ← Real.rpow_neg ha.le, ← Real.rpow_add ha]
  congr 1
  ring
theorem summable_inv_norm_rpow_riemannXiZeros {p : ℝ} (hp : 1 < p) :
    Summable (fun i : RiemannXiZerosIndex ↦ ‖(riemannXiZeros i)⁻¹‖ ^ p) := by
  rw [summable_sigma_of_nonneg fun _ ↦ by positivity]
  refine ⟨fun x ↦ (hasSum_fintype _).summable, ?_⟩
  have hbase := summable_riemannXiDivisor_norm_rpow hp
  refine (hbase.subtype (MeromorphicOn.divisor riemannXi ⊤).support).congr fun z ↦ ?_
  have hz0 : z.1 ≠ 0 := by
    intro h
    have hmem := Function.mem_support.mp z.2
    rw [h, divisor_riemannXi_apply_zero] at hmem
    exact hmem rfl
  rw [tsum_fintype]
  simp only [riemannXiZeros, Function.comp_apply, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  rw [show ‖z.1⁻¹‖ ^ p = ‖z.1‖ ^ (-p) from by
      rw [norm_inv, Real.inv_rpow (norm_nonneg _), ← Real.rpow_neg (norm_nonneg _)],
    divisor_riemannXi_toNat_cast z.1]
private noncomputable def holderSum : ℝ :=
  ∑' i : RiemannXiZerosIndex, ‖(riemannXiZeros i)⁻¹‖ ^ (3 / 2 : ℝ)
private theorem summable_inv_norm_rpow_three_halves :
    Summable (fun i : RiemannXiZerosIndex ↦ ‖(riemannXiZeros i)⁻¹‖ ^ (3 / 2 : ℝ)) :=
  summable_inv_norm_rpow_riemannXiZeros (by norm_num)
private theorem holderSum_nonneg : 0 ≤ holderSum := tsum_nonneg fun _ ↦ by positivity
private theorem tsum_subtype_le_of_le_mul {s : Set RiemannXiZerosIndex}
    {f : RiemannXiZerosIndex → ℝ} (hfs : Summable fun i : s ↦ f (i : RiemannXiZerosIndex))
    {e : ℝ} (he : 0 ≤ e)
    (hf : ∀ i ∈ s, f i ≤ e * ‖(riemannXiZeros i)⁻¹‖ ^ (3 / 2 : ℝ)) :
    ∑' i : s, f (i : RiemannXiZerosIndex) ≤ (holderSum + 1) * e :=
  calc ∑' i : s, f (i : RiemannXiZerosIndex)
      ≤ ∑' i : s, e * ‖(riemannXiZeros (i : RiemannXiZerosIndex))⁻¹‖ ^ (3 / 2 : ℝ) :=
        Summable.tsum_le_tsum (fun i ↦ hf i i.2) hfs
          ((summable_inv_norm_rpow_three_halves.subtype s).mul_left _)
    _ = e * ∑' i : s, ‖(riemannXiZeros (i : RiemannXiZerosIndex))⁻¹‖ ^ (3 / 2 : ℝ) := tsum_mul_left
    _ ≤ e * holderSum :=
        mul_le_mul_of_nonneg_left
          (summable_inv_norm_rpow_three_halves.tsum_subtype_le _ s fun _ ↦ by positivity) he
    _ ≤ (holderSum + 1) * e := by nlinarith [holderSum_nonneg]
theorem exists_sum_inv_norm_riemannXiZeros_le :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 ≤ t →
      ∑ i ∈ (finite_setOf_norm_riemannXiZeros_le t).toFinset, ‖(riemannXiZeros i)⁻¹‖
        ≤ C * t ^ (1 / 2 : ℝ) := by
  refine ⟨holderSum + 1, by linarith [holderSum_nonneg], fun t ht ↦ ?_⟩
  rw [← Finset.tsum_subtype (f := fun i ↦ ‖(riemannXiZeros i)⁻¹‖)]
  refine tsum_subtype_le_of_le_mul (f := fun i ↦ ‖(riemannXiZeros i)⁻¹‖)
    (e := t ^ (1 / 2 : ℝ)) Summable.of_finite (Real.rpow_nonneg ht _) fun i hi ↦ ?_
  rw [Finset.mem_coe, Set.Finite.mem_toFinset] at hi
  rw [norm_inv]
  set a := ‖riemannXiZeros i‖ with hadef
  have ha : (0 : ℝ) < a := norm_pos_iff.mpr (riemannXiZeros_ne_zero i)
  calc a⁻¹
      = a⁻¹ ^ (3 / 2 : ℝ) * a ^ (1 / 2 : ℝ) := by
        rw [inv_rpow_mul_rpow ha, show (1 / 2 - 3 / 2 : ℝ) = -1 by norm_num, Real.rpow_neg_one]
    _ ≤ a⁻¹ ^ (3 / 2 : ℝ) * t ^ (1 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow ha.le hi (by norm_num)) (by positivity)
    _ = t ^ (1 / 2 : ℝ) * a⁻¹ ^ (3 / 2 : ℝ) := by ring
theorem exists_sum_inv_norm_sq_riemannXiZeros_tail_le :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 < t →
      ∑' i : {i : RiemannXiZerosIndex // t < ‖riemannXiZeros i‖},
          ‖(riemannXiZeros (i : RiemannXiZerosIndex))⁻¹‖ ^ 2 ≤ C * t ^ (-(1 / 2) : ℝ) := by
  refine ⟨holderSum + 1, by linarith [holderSum_nonneg], fun t ht ↦ ?_⟩
  refine tsum_subtype_le_of_le_mul (s := {i | t < ‖riemannXiZeros i‖})
    (f := fun i ↦ ‖(riemannXiZeros i)⁻¹‖ ^ 2) (e := t ^ (-(1 / 2) : ℝ))
    (summable_inv_norm_sq_riemannXiZeros.subtype _) (Real.rpow_nonneg ht.le _) fun i hi ↦ ?_
  rw [norm_inv]
  set a := ‖riemannXiZeros i‖ with hadef
  have ha : (0 : ℝ) < a := lt_trans ht hi
  calc a⁻¹ ^ 2
      = a⁻¹ ^ (3 / 2 : ℝ) * a ^ (-(1 / 2) : ℝ) := by
        rw [inv_rpow_mul_rpow ha, show (-(1 / 2) - 3 / 2 : ℝ) = ((2 : ℕ) : ℝ) * (-1) by norm_num,
          Real.rpow_mul ha.le, Real.rpow_natCast, Real.rpow_neg_one, ← inv_pow]
    _ ≤ a⁻¹ ^ (3 / 2 : ℝ) * t ^ (-(1 / 2) : ℝ) :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_nonpos ht hi.le (by norm_num)) (by positivity)
    _ = t ^ (-(1 / 2) : ℝ) * a⁻¹ ^ (3 / 2 : ℝ) := by ring
private lemma self_mul_rpow_half {R : ℝ} (hR : 0 < R) :
    R * R ^ (1 / 2 : ℝ) = R ^ (3 / 2 : ℝ) := by
  rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hR, Real.rpow_one]
private lemma far_rpow_id {R : ℝ} (hR : 0 < R) :
    16 * R ^ 2 * (4 * R) ^ (-(1 / 2) : ℝ) = 8 * R ^ (3 / 2 : ℝ) := by
  have h4 : (4 : ℝ) ^ (-(1 / 2) : ℝ) = 1 / 2 := by
    rw [Real.rpow_neg (by norm_num), ← Real.sqrt_eq_rpow, show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]; norm_num
  have hRid : R ^ 2 * R ^ (-(1 / 2) : ℝ) = R ^ (3 / 2 : ℝ) := by
    have h2 : R ^ 2 = R ^ (2 : ℝ) := by rw [← Real.rpow_natCast R 2]; norm_num
    rw [h2, ← Real.rpow_add hR, show (2 : ℝ) + -(1 / 2) = 3 / 2 by norm_num]
  rw [Real.mul_rpow (by norm_num) hR.le, h4,
    show 16 * R ^ 2 * (1 / 2 * R ^ (-(1 / 2) : ℝ)) = 8 * (R ^ 2 * R ^ (-(1 / 2) : ℝ)) by ring, hRid]
private lemma near_rpow_id {R : ℝ} (hR : 0 < R) :
    2 * R * (4 * R) ^ (1 / 2 : ℝ) = 4 * R ^ (3 / 2 : ℝ) := by
  have h4 : (4 : ℝ) ^ (1 / 2 : ℝ) = 2 := by
    rw [← Real.sqrt_eq_rpow, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [Real.mul_rpow (by norm_num) hR.le, h4,
    show 2 * R * (2 * R ^ (1 / 2 : ℝ)) = 4 * (R * R ^ (1 / 2 : ℝ)) by ring, self_mul_rpow_half hR]
theorem exists_tsum_far_log_norm_weierstrassE1_ge :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 2 ≤ R → ∀ s : ℂ, ‖s‖ ≤ 2 * R →
      -(C * R ^ (3 / 2 : ℝ)) ≤
        ∑' i : {i : RiemannXiZerosIndex // 4 * R < ‖riemannXiZeros i‖},
          Real.log ‖weierstrassE1 (s / riemannXiZeros (i : RiemannXiZerosIndex))‖ := by
  obtain ⟨C2, hC2pos, hC2⟩ := exists_sum_inv_norm_sq_riemannXiZeros_tail_le
  refine ⟨8 * C2, by positivity, fun R hR s hs ↦ ?_⟩
  have hRpos : (0 : ℝ) < R := by linarith
  have h4R : (0 : ℝ) < 4 * R := by linarith
  have hsublog := (summable_log_norm_weierstrassE1 riemannXiZeros
    summable_inv_norm_sq_riemannXiZeros s).subtype {i | 4 * R < ‖riemannXiZeros i‖}
  have hsubinv := (summable_inv_norm_sq_riemannXiZeros.subtype
    {i | 4 * R < ‖riemannXiZeros i‖}).mul_left (-16 * R ^ 2)
  have hterm : ∀ i : {i : RiemannXiZerosIndex // 4 * R < ‖riemannXiZeros i‖},
      -16 * R ^ 2 * ‖(riemannXiZeros (i : RiemannXiZerosIndex))⁻¹‖ ^ 2
        ≤ Real.log ‖weierstrassE1 (s / riemannXiZeros (i : RiemannXiZerosIndex))‖ := by
    intro i
    set ρ := riemannXiZeros (i : RiemannXiZerosIndex) with hρ
    have hρpos : (0 : ℝ) < ‖ρ‖ := lt_trans h4R i.2
    refine le_trans ?_ (neg_le_log_norm_weierstrassE1
      (show ‖s / ρ‖ ≤ 1 / 2 by rw [norm_div, div_le_iff₀ hρpos]; linarith [i.2]))
    rw [show ‖s / ρ‖ ^ 2 = ‖s‖ ^ 2 * ‖ρ⁻¹‖ ^ 2 by rw [norm_div, norm_inv]; ring]
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ 16 * R ^ 2 - 4 * ‖s‖ ^ 2 by
      nlinarith [hs, norm_nonneg s, hRpos]) (sq_nonneg ‖ρ⁻¹‖)]
  refine le_trans ?_
    (Summable.tsum_le_tsum (L := SummationFilter.unconditional _) hterm hsubinv hsublog)
  rw [tsum_mul_left]
  calc -(8 * C2 * R ^ (3 / 2 : ℝ))
      = -16 * R ^ 2 * (C2 * (4 * R) ^ (-(1 / 2) : ℝ)) := by
        rw [show -16 * R ^ 2 * (C2 * (4 * R) ^ (-(1 / 2) : ℝ))
          = -(C2 * (16 * R ^ 2 * (4 * R) ^ (-(1 / 2) : ℝ))) by ring, far_rpow_id hRpos]; ring
    _ ≤ -16 * R ^ 2 * ∑' i : {i : RiemannXiZerosIndex // 4 * R < ‖riemannXiZeros i‖},
          ‖(riemannXiZeros (i : RiemannXiZerosIndex))⁻¹‖ ^ 2 :=
        mul_le_mul_of_nonpos_left (hC2 (4 * R) h4R) (by nlinarith [sq_nonneg R, hRpos])
theorem exists_finset_near_log_norm_weierstrassE1_ge :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 2 ≤ R → ∃ R' ∈ Set.Icc R (2 * R), ∀ s : ℂ, ‖s‖ = R' →
      (∀ i : RiemannXiZerosIndex, ‖riemannXiZeros i‖ ≤ 4 * R → s ≠ riemannXiZeros i) ∧
      -(C * R ^ (3 / 2 : ℝ)) ≤
        ∑ i ∈ (finite_setOf_norm_riemannXiZeros_le (4 * R)).toFinset,
          Real.log ‖weierstrassE1 (s / riemannXiZeros i)‖ := by
  obtain ⟨Cn, hCnpos, hCn⟩ := exists_card_riemannXiZeros_le
  obtain ⟨C1, hC1pos, hC1⟩ := exists_sum_inv_norm_riemannXiZeros_le
  set Clog : ℝ := Real.log (256 * Cn + 4) + 2 with hClog
  have hlogc : (0 : ℝ) ≤ Real.log (256 * Cn + 4) := Real.log_nonneg (by linarith)
  have hcc : (0 : ℝ) ≤ 12 * Cn * Clog := by rw [hClog]; nlinarith
  refine ⟨4 * C1 + 192 * Cn * Clog, by linarith, fun R hR ↦ ?_⟩
  have hRpos : (0 : ℝ) < R := by linarith
  have hR1 : (1 : ℝ) ≤ R := by linarith
  have hlogR : (0 : ℝ) ≤ Real.log R := Real.log_nonneg hR1
  set F := (finite_setOf_norm_riemannXiZeros_le (4 * R)).toFinset with hF
  set m := F.card with hm
  have hmnn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  set δ : ℝ := R / (4 * ((m : ℝ) + 1)) with hδ
  have hδpos : 0 < δ := div_pos hRpos (by positivity)
  have hδid : δ * (4 * ((m : ℝ) + 1)) = R := by rw [hδ]; field_simp
  have hmcard : (m : ℝ) ≤ Cn * (4 * R * Real.log (4 * R)) := by
    rw [hm, hF, ← Set.ncard_eq_toFinset_card _ (finite_setOf_norm_riemannXiZeros_le (4 * R))]
    exact hCn (4 * R) (by linarith)
  obtain ⟨R', hR'mem, hR'dist⟩ :=
    exists_mem_Icc_forall_le_dist (S := F.image fun i ↦ ‖riemannXiZeros i‖) (a := R) (b := 2 * R)
      hδpos (by
        have hci : ((F.image fun i ↦ ‖riemannXiZeros i‖).card : ℝ) ≤ (m : ℝ) := by
          rw [hm]; exact_mod_cast Finset.card_image_le
        nlinarith [mul_nonneg hδpos.le (sub_nonneg.mpr hci), mul_nonneg hδpos.le hmnn])
  refine ⟨R', hR'mem, fun s hs ↦ ?_⟩
  have hR'le : R' ≤ 2 * R := hR'mem.2
  have hdist : ∀ i ∈ F, δ ≤ ‖s - riemannXiZeros i‖ := fun i hiF ↦
    (hR'dist _ (Finset.mem_image_of_mem _ hiF)).trans <| by
      simpa only [hs] using abs_norm_sub_norm_le s (riemannXiZeros i)
  have hne : ∀ i ∈ F, s ≠ riemannXiZeros i := fun i hiF heq ↦ by
    have hd := hdist i hiF; rw [heq, sub_self, norm_zero] at hd; linarith
  refine ⟨fun i hi ↦ hne i (by rw [hF, Set.Finite.mem_toFinset]; exact hi), ?_⟩
  have hlogd : Real.log δ - Real.log (4 * R) = -Real.log (16 * ((m : ℝ) + 1)) := by
    rw [← Real.log_div hδpos.ne' (by positivity), ← Real.log_inv]
    congr 1
    rw [hδ]; field_simp; ring
  have hpt : ∀ i ∈ F, Real.log δ - Real.log (4 * R) - 2 * R * ‖(riemannXiZeros i)⁻¹‖
      ≤ Real.log ‖weierstrassE1 (s / riemannXiZeros i)‖ := by
    intro i hiF
    set ρ := riemannXiZeros i with hρ
    have hρne : ρ ≠ 0 := riemannXiZeros_ne_zero i
    have hi4R : ‖ρ‖ ≤ 4 * R := by have h := hiF; rw [hF, Set.Finite.mem_toFinset] at h; exact h
    have hρpos : 0 < ‖ρ‖ := norm_pos_iff.mpr hρne
    have hsne : s ≠ ρ := hne i hiF
    rw [log_norm_weierstrassE1 (fun h ↦ hsne ((div_eq_one_iff_eq hρne).mp h)),
      show ‖(1 : ℂ) - s / ρ‖ = ‖s - ρ‖ / ‖ρ‖ by
        rw [show (1 : ℂ) - s / ρ = (ρ - s) / ρ by rw [sub_div, div_self hρne], norm_div,
          norm_sub_rev],
      Real.log_div (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hsne)) hρpos.ne']
    have hb2 : ‖s / ρ‖ ≤ 2 * R * ‖ρ⁻¹‖ := by
      rw [norm_div, norm_inv, hs, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right hR'le (by positivity)
    linarith [Real.log_le_log hδpos (hdist i hiF), Real.log_le_log hρpos hi4R,
      (abs_le.mp (Complex.abs_re_le_norm (s / ρ))).1]
  refine le_trans ?_ (Finset.sum_le_sum hpt)
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum, hlogd, mul_neg]
  have h2Rsum : 2 * R * ∑ i ∈ F, ‖(riemannXiZeros i)⁻¹‖ ≤ 4 * C1 * R ^ (3 / 2 : ℝ) :=
    calc 2 * R * ∑ i ∈ F, ‖(riemannXiZeros i)⁻¹‖
        ≤ 2 * R * (C1 * (4 * R) ^ (1 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_left (by rw [hF]; exact hC1 (4 * R) (by linarith)) (by linarith)
      _ = C1 * (2 * R * (4 * R) ^ (1 / 2 : ℝ)) := by ring
      _ = 4 * C1 * R ^ (3 / 2 : ℝ) := by rw [near_rpow_id hRpos]; ring
  have hmlog : (m : ℝ) * Real.log (16 * ((m : ℝ) + 1)) ≤ 192 * Cn * Clog * R ^ (3 / 2 : ℝ) := by
    have hCn4R : (0 : ℝ) ≤ Cn * (4 * R) := by positivity
    have hm12 : (m : ℝ) ≤ 12 * Cn * R * (Real.log R + 1) := by
      have h : Real.log (4 * R) ≤ 3 * (Real.log R + 1) := by
        rw [Real.log_mul (by norm_num) hRpos.ne']
        linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num)]
      nlinarith [hmcard, mul_le_mul_of_nonneg_left h hCn4R]
    have hm16 : (m : ℝ) ≤ 16 * Cn * R ^ 2 := by
      have h : Real.log (4 * R) ≤ 4 * R :=
        by linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 * R by linarith)]
      nlinarith [hmcard, mul_le_mul_of_nonneg_left h hCn4R]
    have hlogm : Real.log (16 * ((m : ℝ) + 1)) ≤ Clog * (Real.log R + 1) := by
      have hmono := Real.log_le_log (show (0 : ℝ) < 16 * ((m : ℝ) + 1) by positivity)
        (show 16 * ((m : ℝ) + 1) ≤ (256 * Cn + 4) * R ^ 2 by nlinarith [hm16])
      rw [Real.log_mul (by positivity) (by positivity : (R : ℝ) ^ 2 ≠ 0), Real.log_pow] at hmono
      rw [hClog]
      push_cast at hmono ⊢
      nlinarith [mul_nonneg hlogc hlogR]
    have hRL2 : R * (Real.log R + 1) ^ 2 ≤ 16 * R ^ (3 / 2 : ℝ) := by
      rw [← self_mul_rpow_half hRpos]
      nlinarith [Real.log_add_one_sq_le hR1, hRpos]
    have hstep := mul_le_mul hm12 hlogm (Real.log_nonneg (by linarith))
      (by positivity : (0 : ℝ) ≤ 12 * Cn * R * (Real.log R + 1))
    nlinarith [mul_le_mul_of_nonneg_left hRL2 hcc]
  linarith only [hmlog, h2Rsum]
theorem exists_circle_log_norm_riemannXiCanonicalProduct_ge :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 2 ≤ R → ∃ R' ∈ Set.Icc R (2 * R), ∀ s : ℂ, ‖s‖ = R' →
      riemannXiCanonicalProduct riemannXiZeros s ≠ 0 ∧
        -(C * R ^ (3 / 2 : ℝ)) ≤ Real.log ‖riemannXiCanonicalProduct riemannXiZeros s‖ := by
  obtain ⟨CF, hCFpos, hCF⟩ := exists_tsum_far_log_norm_weierstrassE1_ge
  obtain ⟨CN, hCNpos, hCN⟩ := exists_finset_near_log_norm_weierstrassE1_ge
  refine ⟨CF + CN, by linarith, fun R hR ↦ ?_⟩
  obtain ⟨R', hR'mem, hR'⟩ := hCN R hR
  refine ⟨R', hR'mem, fun s hs ↦ ?_⟩
  obtain ⟨hne_near, hnear⟩ := hR' s hs
  have hs2R : ‖s‖ ≤ 2 * R := by rw [hs]; exact hR'mem.2
  have hsum := summable_inv_norm_sq_riemannXiZeros
  have hsumlog := summable_log_norm_weierstrassE1 riemannXiZeros hsum s
  have hsne : ∀ i, s ≠ riemannXiZeros i := by
    intro i
    rcases le_or_gt ‖riemannXiZeros i‖ (4 * R) with hle | hlt
    · exact hne_near i hle
    · intro heq
      rw [← heq, hs] at hlt
      linarith [hR'mem.2]
  refine ⟨riemannXiCanonicalProduct_ne_zero_of_forall_ne riemannXiZeros hsum hsne, ?_⟩
  set F := (finite_setOf_norm_riemannXiZeros_le (4 * R)).toFinset with hF
  have hfar : -(CF * R ^ (3 / 2 : ℝ))
      ≤ ∑' x : ↥((↑F : Set RiemannXiZerosIndex)ᶜ),
          Real.log ‖weierstrassE1 (s / riemannXiZeros (x : RiemannXiZerosIndex))‖ := by
    rw [show ((↑F : Set RiemannXiZerosIndex)ᶜ) = {i | 4 * R < ‖riemannXiZeros i‖} by
      rw [hF, Set.Finite.coe_toFinset]
      ext i; simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_le]]
    exact hCF R hR s hs2R
  rw [log_norm_riemannXiCanonicalProduct riemannXiZeros hsum hsne,
    ← hsumlog.sum_add_tsum_compl (s := F)]
  linarith [hnear, hfar]
end
end CountPort22
section CountPort23
section
lemma AnalyticOn.norm_le_of_norm_le_on_sphere {C r R : ℝ} {f : ℂ → ℂ} {w : ℂ}
    (hyp_r : r ≤ R)
    (analytic : AnalyticOn ℂ f (Metric.closedBall 0 R))
    (cond : ∀ z ∈ Metric.sphere 0 r, ‖f z‖ ≤ C)
    (wInS : w ∈ Metric.closedBall 0 r) :
    ‖f w‖ ≤ C := by
  apply Complex.norm_le_of_forall_mem_frontier_norm_le
    (U := Metric.closedBall 0 r) Metric.isBounded_closedBall
  · apply DifferentiableOn.diffContOnCl
    rw [Metric.closure_closedBall]
    exact AnalyticOn.differentiableOn
      (AnalyticOn.mono analytic
        (Metric.closedBall_subset_closedBall hyp_r))
  · rw [frontier_closedBall']
    exact cond
  · rw [Metric.closure_closedBall]
    exact wInS
noncomputable abbrev divRemovable_zero (f : ℂ → ℂ) : ℂ → ℂ :=
  Function.update (fun z ↦ f z / z) 0 (deriv f 0)
lemma divRemovable_zero_of_ne_zero {z : ℂ} (f : ℂ → ℂ)
    (z_ne_0 : z ≠ 0) :
    divRemovable_zero f z = f z / z := by
  apply Function.update_of_ne z_ne_0
lemma AnalyticOn_divRemovable_zero {f : ℂ → ℂ} {s : Set ℂ}
    (sInNhds0 : s ∈ nhds 0) (zero : f 0 = 0) (o : IsOpen s)
    (analytic : AnalyticOn ℂ f s) :
    AnalyticOn ℂ (divRemovable_zero f) s := by
  rw [Complex.analyticOn_iff_differentiableOn o,
    ← Complex.differentiableOn_compl_singleton_and_continuousAt_iff sInNhds0]
  constructor
  · have (x) (hx : x ∈ s \ {0}) : x ≠ 0 := by
      rw [Set.mem_sdiff, Set.mem_singleton_iff] at hx
      exact hx.right
    rw [differentiableOn_congr (fun x hyp_x => Function.update_of_ne (this x hyp_x) _ _)]
    exact
      (analytic.mono Set.sdiff_subset).differentiableOn.fun_div
      (differentiableOn_id.mono (Set.subset_univ (s \ {0})))
      this
  · have U :=
      HasDerivAt.continuousAt_div (c := 0) (a := deriv f 0)
        (f := f)
        (DifferentiableOn.hasDerivAt
          ((Complex.analyticOn_iff_differentiableOn o).mp analytic)
          sInNhds0)
    simpa [divRemovable_zero, zero] using U
lemma AnalyticOn_divRemovable_zero_closedBall {f : ℂ → ℂ}
    {R : ℝ} (Rpos : 0 < R)
    (analytic : AnalyticOn ℂ f (Metric.closedBall 0 R))
    (zero : f 0 = 0) :
    AnalyticOn ℂ (divRemovable_zero f) (Metric.closedBall 0 R) := by
  apply analyticOn_of_locally_analyticOn
  intro x x_hyp
  simp only [Metric.mem_closedBall, dist_zero_right] at x_hyp
  cases x_hyp.eq_or_lt with
  | inl h =>
    use Metric.ball x (R / 2)
    refine ⟨Metric.isOpen_ball, ?_, ?_⟩
    · simp [Rpos]
    · have (x₂) (hyp_x₂ : x₂ ∈ Metric.closedBall 0 R ∩ Metric.ball x (R / 2)) : x₂ ≠ 0 := by
        rw [ball_eq, Set.mem_inter_iff, Metric.mem_closedBall, dist_zero_right,
          Set.mem_ofPred_eq] at hyp_x₂
        rw [← norm_pos_iff]
        calc 0
          _ < R - ‖x₂ - x‖ := by
            obtain ⟨-, v⟩ := hyp_x₂
            linarith
          _ = ‖x‖ - ‖x - x₂‖ := by
            rw [h, norm_sub_rev]
          _ ≤ ‖x - (x - x₂)‖ := norm_sub_norm_le ..
          _ ≤ ‖x₂‖ := by rw [sub_sub_cancel]
      apply AnalyticOn.congr
      · exact (analytic.mono Set.inter_subset_left).div analyticOn_id this
      · intro x₃ hyp_x₃
        exact divRemovable_zero_of_ne_zero _ (this _ hyp_x₃)
  | inr h =>
    use Metric.ball 0 R
    refine ⟨Metric.isOpen_ball, ?_, ?_⟩
    · simp only [ball_eq, sub_zero, Set.mem_ofPred_eq, h]
    · have si : Metric.closedBall (0 : ℂ) R ∩ Metric.ball (0 : ℂ) R =
        Metric.ball (0 : ℂ) R := by
        apply Set.inter_eq_self_of_subset_right
        exact Metric.ball_subset_closedBall
      rw [si]
      exact AnalyticOn_divRemovable_zero
        (Metric.ball_mem_nhds 0 Rpos)
        zero Metric.isOpen_ball
        (analytic.mono Metric.ball_subset_closedBall)
noncomputable abbrev schwartzQuotient (f : ℂ → ℂ) (M : ℝ) :
    ℂ → ℂ :=
  fun z ↦ divRemovable_zero f z / (2 * M - f z)
lemma AnalyticOn.schwartzQuotient {f : ℂ → ℂ} {R : ℝ}
    (M : ℝ) (Rpos : 0 < R)
    (analytic : AnalyticOn ℂ f (Metric.closedBall 0 R))
    (nonzero : ∀ z ∈ Metric.closedBall 0 R, 2 * M - f z ≠ 0)
    (zero : f 0 = 0) :
    AnalyticOn ℂ (schwartzQuotient f M) (Metric.closedBall 0 R) :=
  AnalyticOn.div
    (AnalyticOn_divRemovable_zero_closedBall Rpos analytic zero)
    (AnalyticOn.sub analyticOn_const analytic) nonzero
lemma Complex.norm_le_norm_two_mul_sub_of_re_le {M : ℝ}
    {x : ℂ} (Mpos : 0 < M) (hyp_re_x : x.re ≤ M) :
    ‖x‖ ≤ ‖2 * M - x‖ := by
  rw [← sq_le_sq₀ (by positivity) (by positivity)]
  repeat rw [Complex.sq_norm, Complex.normSq_apply]
  rw [calc
    (2 * M - x).re * (2 * M - x).re +
        (2 * M - x).im * (2 * M - x).im =
      (2 * M - x.re) * (2 * M - x.re) +
        x.im * x.im := by simp
    _ = x.re * x.re +
        (x.im * x.im + 4 * M * (M - x.re)) := by ring]
  bound
theorem borelCaratheodory_closedBall {M R r : ℝ} {z : ℂ}
    {f : ℂ → ℂ} (Rpos : 0 < R)
    (analytic : AnalyticOn ℂ f (Metric.closedBall 0 R))
    (zeroAtZero : f 0 = 0) (Mpos : 0 < M)
    (realPartBounded : ∀ z ∈ Metric.closedBall 0 R, (f z).re ≤ M)
    (hyp_r : r < R)
    (hyp_z : z ∈ Metric.closedBall 0 r) :
    ‖f z‖ ≤ (2 * M * r) / (R - r) := by
  have zInSFunc :
      ∀ r ≤ R, ∀ z ∈ Metric.sphere (0 : ℂ) r,
      z ∈ Metric.closedBall (0 : ℂ) R := by
    intro r hyp_r z hyp_z
    exact Set.mem_of_mem_of_subset hyp_z <|
      (Metric.sphere_subset_closedBall).trans
        (Metric.closedBall_subset_closedBall hyp_r)
  have fPosAll :
      ∀ z ∈ Metric.closedBall 0 R, 2 * M - f z ≠ 0 := by
    intro z zInS
    exact Complex.ne_zero_of_re_pos (by
      rw [Complex.sub_re, Complex.mul_re, Complex.re_ofNat, Complex.ofReal_re,
        Complex.im_ofNat, Complex.ofReal_im, mul_zero, sub_zero, sub_pos]
      linarith [realPartBounded z zInS])
  have schwartzQuotientBounded :
      ∀ z ∈ Metric.sphere 0 R,
      ‖schwartzQuotient f M z‖ ≤ 1 / R := by
    intro z hyp_z
    have zNe0 : z ≠ 0 := by
      rw [mem_sphere_zero_iff_norm] at hyp_z
      exact ne_zero_of_norm_ne_zero (by linarith)
    have zInS : z ∈ Metric.closedBall 0 R :=
      zInSFunc R le_rfl z hyp_z
    rw [mem_sphere_iff_norm, sub_zero] at hyp_z
    calc ‖schwartzQuotient f M z‖
      _ = (‖f z‖ / ‖z‖) / ‖2 * M - f z‖ := by
        simp only [Complex.norm_div, divRemovable_zero_of_ne_zero f zNe0]
      _ ≤ (‖f z‖ / ‖z‖) / ‖f z‖ := by
        by_cases h : ‖f z‖ = 0
        · simp only [h, zero_div, div_zero, le_refl]
        · exact div_le_div_of_nonneg_left
            (by positivity) (by positivity)
            (Complex.norm_le_norm_two_mul_sub_of_re_le
              Mpos (realPartBounded z zInS))
      _ ≤ 1 / ‖z‖ := by
        rw [div_right_comm]
        exact div_le_div_of_nonneg_right (div_self_le_one _) (norm_nonneg _)
      _ = 1 / R := by rw [hyp_z]
  have maxMod (z) (hz : z ∈ Metric.closedBall 0 R) : ‖schwartzQuotient f M z‖ ≤ 1 / R :=
    AnalyticOn.norm_le_of_norm_le_on_sphere le_rfl
      (AnalyticOn.schwartzQuotient M Rpos analytic fPosAll zeroAtZero)
      schwartzQuotientBounded hz
  have boundForF :
      ∀ r < R, 0 < r →
      ∀ z ∈ Metric.sphere 0 r,
      ‖f z‖ ≤ 2 * M * r / (R - r) := by
    intro r hyp_r r_pos z zOnR
    have zInS : z ∈ Metric.closedBall 0 R :=
      zInSFunc r hyp_r.le z zOnR
    rw [mem_sphere_zero_iff_norm] at zOnR
    have := maxMod z zInS
    unfold schwartzQuotient at this
    have U : z ≠ 0 := by
      rwa [← norm_pos_iff, zOnR]
    simp only [divRemovable_zero_of_ne_zero f U, Complex.norm_div, one_div] at this
    have U : 0 < r * ‖2 * M - f z‖ := by
      simp only [r_pos, mul_pos_iff_of_pos_left, norm_pos_iff, ne_eq, fPosAll z zInS,
        not_false_eq_true]
    rw [zOnR, div_div, div_le_iff₀' U] at this
    have U0 :
        ‖f z‖ ≤ 2 * M * r / R + (r / R) * ‖f z‖ := by
      calc ‖f z‖
        _ ≤ r * ‖2 * M - f z‖ * R⁻¹ := this
        _ ≤ r * (‖(2 : ℂ) * M‖ + ‖f z‖) * R⁻¹ := by
          grw [norm_sub_le]
        _ = r * (2 * M + ‖f z‖) * R⁻¹ := by
          simp [Mpos.le]
        _ = 2 * M * r / R + (r / R) * ‖f z‖ := by
          ring_nf
    rw [← tsub_le_iff_right, ← one_sub_mul, ← le_div_iff₀'] at U0
    · have hR : (R : ℝ) ≠ 0 := Rpos.ne'
      have hRr : R - r ≠ 0 := sub_ne_zero.mpr (ne_of_lt hyp_r).symm
      have heq : 2 * M * r / (R - r) = 2 * M * r / R / (1 - r / R) := by
        rw [one_sub_div hR]; field_simp
      rw [heq]
      exact U0
    · rwa [sub_pos, div_lt_one₀ Rpos]
  have maxBoundForF
      (r) (hyp_r : r < R) (pos_r : 0 < r)
      (z) (hz : z ∈ Metric.closedBall 0 r) :
      ‖f z‖ ≤ 2 * M * r / (R - r) :=
    AnalyticOn.norm_le_of_norm_le_on_sphere hyp_r.le analytic (boundForF r hyp_r pos_r) hz
  have U : 0 ≤ r := by
    rw [mem_closedBall_iff_norm, sub_zero] at hyp_z
    exact (norm_nonneg z).trans hyp_z
  cases U.eq_or_lt' with
  | inl pos_r =>
    obtain rfl : z = 0 := by
      rwa [pos_r, Metric.closedBall_zero, Set.mem_singleton_iff] at hyp_z
    rwa [pos_r, mul_zero, sub_zero, zero_div, norm_le_zero_iff]
  | inr pos_r =>
    exact maxBoundForF r hyp_r pos_r z hyp_z
end
end CountPort23
section CountPort24
section
open Complex Filter Topology Set Metric
theorem re_log_riemannXi_div_canonicalProduct_le {h : ℂ → ℂ}
    (hrep : ∀ s, riemannXi s =
      Complex.exp (h s) * riemannXiCanonicalProduct riemannXiZeros s) :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 2 ≤ R → ∃ R' ∈ Set.Icc R (2 * R), ∀ s : ℂ, ‖s‖ = R' →
      (h s).re ≤ C * R ^ (3 / 2 : ℝ) := by
  obtain ⟨Cξ, hCξ, hξ⟩ := norm_riemannXi_le_exp
  obtain ⟨CP, hCP, hP⟩ := exists_circle_log_norm_riemannXiCanonicalProduct_ge
  refine ⟨Cξ * (2 * (2 : ℝ) ^ (3 / 2 : ℝ)) + CP, by positivity, fun R hR ↦ ?_⟩
  obtain ⟨R', hR'mem, hR'⟩ := hP R hR
  refine ⟨R', hR'mem, fun s hs ↦ ?_⟩
  obtain ⟨hPne, hlogP⟩ := hR' s hs
  set P := riemannXiCanonicalProduct riemannXiZeros
  have hR0 : (0 : ℝ) ≤ R := by linarith
  have hs2 : (2 : ℝ) ≤ ‖s‖ := hs ▸ hR.trans hR'mem.1
  have hPpos : 0 < ‖P s‖ := norm_pos_iff.mpr hPne
  have hnormξ : ‖riemannXi s‖ = Real.exp ((h s).re) * ‖P s‖ := by
    rw [hrep s, norm_mul, Complex.norm_exp]
  have hξpos : 0 < ‖riemannXi s‖ := by rw [hnormξ]; positivity
  have hre_eq : (h s).re = Real.log ‖riemannXi s‖ - Real.log ‖P s‖ := by
    rw [hnormξ, Real.log_mul (Real.exp_pos _).ne' hPpos.ne', Real.log_exp, add_sub_cancel_right]
  have hlogξ : Real.log ‖riemannXi s‖ ≤ Cξ * (‖s‖ * Real.log ‖s‖) :=
    (Real.log_le_iff_le_exp hξpos).2 (hξ s hs2)
  have hsl : ‖s‖ * Real.log ‖s‖ ≤ 2 * ((2 : ℝ) ^ (3 / 2 : ℝ) * R ^ (3 / 2 : ℝ)) := by
    rw [← Real.mul_rpow (by norm_num) hR0]
    have hlog : Real.log ‖s‖ ≤ 2 * ‖s‖ ^ (1 / 2 : ℝ) := by
      have := Real.log_le_rpow_div (norm_nonneg s) (by norm_num : (0 : ℝ) < 1 / 2)
      linarith
    have hmul : ‖s‖ * ‖s‖ ^ (1 / 2 : ℝ) = ‖s‖ ^ (3 / 2 : ℝ) := by
      rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add (by linarith), Real.rpow_one]
    have hpow : ‖s‖ ^ (3 / 2 : ℝ) ≤ (2 * R) ^ (3 / 2 : ℝ) :=
      Real.rpow_le_rpow (norm_nonneg s) (hs ▸ hR'mem.2) (by norm_num)
    nlinarith [mul_le_mul_of_nonneg_left hlog (norm_nonneg s)]
  calc (h s).re = Real.log ‖riemannXi s‖ - Real.log ‖P s‖ := hre_eq
    _ ≤ Cξ * (‖s‖ * Real.log ‖s‖) + CP * R ^ (3 / 2 : ℝ) := by linarith
    _ ≤ Cξ * (2 * ((2 : ℝ) ^ (3 / 2 : ℝ) * R ^ (3 / 2 : ℝ))) + CP * R ^ (3 / 2 : ℝ) := by
        linarith [mul_le_mul_of_nonneg_left hsl hCξ.le]
    _ = (Cξ * (2 * (2 : ℝ) ^ (3 / 2 : ℝ)) + CP) * R ^ (3 / 2 : ℝ) := by ring
end
end CountPort24
section CountPort25
section
open Complex Filter Topology Set Metric
theorem exists_affine_log_riemannXi_div_canonicalProduct {h : ℂ → ℂ}
    (hdiff : Differentiable ℂ h)
    (hrep : ∀ s, riemannXi s =
      Complex.exp (h s) * riemannXiCanonicalProduct riemannXiZeros s) :
    ∃ A B : ℂ, ∀ s, h s = A + B * s := by
  obtain ⟨C, hCpos, hgrow⟩ := re_log_riemannXi_div_canonicalProduct_le hrep
  have hderivdiff : Differentiable ℂ (deriv h) := fun x ↦
    ((analyticOnNhd_univ_iff_differentiable.mpr hdiff).deriv x (mem_univ x)).differentiableAt
  set C₀ : ℝ := 2 * C + 3 * ‖h 0‖ + 2 with hC₀def
  have claimA : ∀ R : ℝ, 2 ≤ R → ∀ z : ℂ, ‖z‖ ≤ R / 2 → ‖h z‖ ≤ C₀ * R ^ (3 / 2 : ℝ) := by
    intro R hR z hz
    obtain ⟨R', hR'mem, hR'⟩ := hgrow R hR
    have hR'pos : 0 < R' := by linarith [hR'mem.1]
    have hRpow1 : (1 : ℝ) ≤ R ^ (3 / 2 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
    have hCR : 0 ≤ C * R ^ (3 / 2 : ℝ) :=
      mul_nonneg hCpos.le (Real.rpow_nonneg (by linarith) _)
    have hmax : ∀ w : ℂ, ‖w‖ ≤ R' → (h w).re ≤ C * R ^ (3 / 2 : ℝ) := by
      intro w hw
      have hfront : ∀ ζ ∈ frontier (ball (0 : ℂ) R'),
          ‖Complex.exp (h ζ)‖ ≤ Real.exp (C * R ^ (3 / 2 : ℝ)) := fun ζ hζ ↦ by
        rw [frontier_ball 0 hR'pos.ne'] at hζ
        rw [Complex.norm_exp]
        exact Real.exp_le_exp.mpr (hR' ζ (by simpa using mem_sphere_iff_norm.mp hζ))
      have hle := Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball
        hdiff.cexp.diffContOnCl hfront
        (by rw [closure_ball 0 hR'pos.ne']; simpa [mem_closedBall, dist_eq_norm] using hw)
      rw [Complex.norm_exp] at hle
      exact Real.exp_le_exp.mp hle
    have hbc := borelCaratheodory_closedBall (f := fun s ↦ h s - h 0) (z := z) (r := R' / 2)
      (M := C * R ^ (3 / 2 : ℝ) + ‖h 0‖ + 1) hR'pos
      ((analyticOn_univ_iff_differentiable.mpr (hdiff.sub_const (h 0))).mono (subset_univ _))
      (by simp) (by linarith [norm_nonneg (h 0)])
      (fun ζ hζ ↦ by
        rw [mem_closedBall, dist_eq_norm, sub_zero] at hζ
        simp only [Complex.sub_re]
        linarith [hmax ζ hζ, (neg_le_abs (h 0).re).trans (abs_re_le_norm (h 0))])
      (by linarith) (by simp only [mem_closedBall, dist_eq_norm, sub_zero]; linarith [hR'mem.1])
    rw [show R' - R' / 2 = R' / 2 by ring, mul_div_assoc, div_self (half_pos hR'pos).ne',
      mul_one] at hbc
    rw [hC₀def]
    nlinarith [hbc, norm_sub_norm_le (h z) (h 0), norm_nonneg (h 0),
      mul_nonneg (norm_nonneg (h 0)) (sub_nonneg.mpr hRpow1)]
  have claimB : ∀ c : ℂ, iteratedDeriv 2 h c = 0 := by
    intro c
    have htend : Tendsto (fun R : ℝ ↦ 32 * C₀ * R ^ (-(1 / 2) : ℝ)) atTop (𝓝 0) := by
      simpa using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).const_mul (32 * C₀)
    refine norm_le_zero_iff.mp <| ge_of_tendsto htend ?_
    filter_upwards [eventually_ge_atTop (4 * ‖c‖ + 2)] with R hR
    have hR2 : 2 ≤ R := by linarith [norm_nonneg c]
    have hRpos : 0 < R := by linarith
    set ρ : ℝ := R / 2 - ‖c‖ with hρdef
    have hρ4 : R / 4 ≤ ρ := by rw [hρdef]; linarith
    have hρpos : 0 < ρ := by linarith
    have hcauchy := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le 2 hρpos
      hdiff.diffContOnCl (fun z hz ↦ claimA R hR2 z (by
        have hzc := norm_sub_norm_le z c
        rw [mem_sphere_iff_norm.mp hz, hρdef] at hzc
        linarith))
    rw [show ((Nat.factorial 2 : ℕ) : ℝ) = 2 from by norm_num [Nat.factorial]] at hcauchy
    have hpowid : R ^ (3 / 2 : ℝ) / R ^ 2 = R ^ (-(1 / 2) : ℝ) := by
      rw [← Real.rpow_natCast R 2, ← Real.rpow_sub hRpos]; norm_num
    calc ‖iteratedDeriv 2 h c‖ ≤ 2 * (C₀ * R ^ (3 / 2 : ℝ)) / ρ ^ 2 := hcauchy
      _ ≤ 2 * (C₀ * R ^ (3 / 2 : ℝ)) / (R ^ 2 / 16) := by
          gcongr; nlinarith [hρ4, hρpos]
      _ = 32 * C₀ * (R ^ (3 / 2 : ℝ) / R ^ 2) := by ring
      _ = 32 * C₀ * R ^ (-(1 / 2) : ℝ) := by rw [hpowid]
  have hderivconst : ∀ x : ℂ, deriv h x = deriv h 0 := fun x ↦
    is_const_of_deriv_eq_zero hderivdiff
      (fun y ↦ by simpa [iteratedDeriv_succ, iteratedDeriv_one] using claimB y) x 0
  refine ⟨h 0, deriv h 0, fun s ↦ ?_⟩
  have key : h s - deriv h 0 * s = h 0 := by
    simpa using is_const_of_deriv_eq_zero (f := fun y : ℂ ↦ h y - deriv h 0 * y)
      (hdiff.sub (differentiable_id.const_mul _))
      (fun x ↦ by
        have hd : HasDerivAt (fun y : ℂ ↦ h y - deriv h 0 * y) (deriv h x - deriv h 0) x :=
          (hdiff x).hasDerivAt.sub (by simpa using (hasDerivAt_id x).const_mul (deriv h 0))
        rw [hd.deriv, hderivconst x]; ring) s 0
  linear_combination key
end
end CountPort25
section CountPort26
section
open Complex Filter Topology Set
open scoped ComplexConjugate
theorem logDeriv_riemannXiCanonicalProduct_riemannXiZeros_zero :
    logDeriv (riemannXiCanonicalProduct riemannXiZeros) 0 = 0 := by
  set ρ := riemannXiZeros
  set f : RiemannXiZerosIndex → ℂ → ℂ := fun i s ↦ weierstrassE1 (s / ρ i) with hf
  have hd : ∀ i, DifferentiableOn ℂ (f i) Set.univ := fun i ↦
    (differentiable_weierstrassE1.comp (differentiable_id.div_const (ρ i))).differentiableOn
  have hf0 : ∀ i, f i 0 = 1 := fun i ↦ by simp [hf]
  have hlog0 : ∀ i, logDeriv (f i) 0 = 0 := fun i ↦ by
    have hu : HasDerivAt (fun s : ℂ ↦ s / ρ i) (ρ i)⁻¹ 0 := by
      simpa [div_eq_mul_inv] using (hasDerivAt_id (0 : ℂ)).div_const (ρ i)
    have hde : HasDerivAt (f i) 0 0 := by
      simpa [hf, Function.comp_def] using (hasDerivAt_weierstrassE1 ((0 : ℂ) / ρ i)).comp 0 hu
    rw [logDeriv_apply, hde.deriv, hf0 i, zero_div]
  have hkey := logDeriv_tprod_eq_tsum (s := Set.univ) isOpen_univ (Set.mem_univ (0 : ℂ))
    (fun i ↦ by rw [hf0 i]; norm_num) hd (by simp only [hlog0]; exact summable_zero)
    ((hasProdLocallyUniformlyOn_riemannXiCanonicalProduct ρ
      summable_inv_norm_sq_riemannXiZeros).multipliableLocallyUniformlyOn)
    (by simp only [hf0, tprod_one]; norm_num)
  simp only [hlog0, tsum_zero] at hkey
  exact hkey
theorem logDeriv_riemannXi_zero_eq_deriv {h : ℂ → ℂ} (hdiff : Differentiable ℂ h)
    (hrep : ∀ s, riemannXi s =
      Complex.exp (h s) * riemannXiCanonicalProduct riemannXiZeros s) :
    logDeriv riemannXi 0 = deriv h 0 := by
  have hP0ne : riemannXiCanonicalProduct riemannXiZeros 0 ≠ 0 := by
    rw [riemannXiCanonicalProduct_zero]; norm_num
  rw [funext hrep, logDeriv_mul (f := fun s ↦ Complex.exp (h s))
      (g := riemannXiCanonicalProduct riemannXiZeros) 0 (Complex.exp_ne_zero _) hP0ne
      (hdiff 0).hasDerivAt.cexp.differentiableAt
      (differentiable_riemannXiCanonicalProduct riemannXiZeros
        summable_inv_norm_sq_riemannXiZeros 0),
    show (fun s ↦ Complex.exp (h s)) = Complex.exp ∘ h from rfl,
    logDeriv_comp (Complex.differentiable_exp (h 0)) (hdiff 0), Complex.logDeriv_exp,
    logDeriv_riemannXiCanonicalProduct_riemannXiZeros_zero]
  simp
theorem log_riemannXi_div_canonicalProduct_const_eq {h : ℂ → ℂ} {A B : ℂ}
    (hdiff : Differentiable ℂ h)
    (hrep : ∀ s, riemannXi s =
      Complex.exp (h s) * riemannXiCanonicalProduct riemannXiZeros s)
    (haffine : ∀ s, h s = A + B * s) :
    Complex.exp A = 1 / 2 ∧ B = logDeriv riemannXi 0 ∧ conj B = B := by
  have hexpA : Complex.exp A = 1 / 2 := by
    have h0 := hrep 0
    rw [riemannXi_zero, riemannXiCanonicalProduct_zero, mul_one, haffine 0, mul_zero,
      add_zero] at h0
    exact h0.symm
  have hBeq : B = logDeriv riemannXi 0 := by
    rw [logDeriv_riemannXi_zero_eq_deriv hdiff hrep, funext haffine]; simp
  have hsym : conj ∘ riemannXi ∘ conj = riemannXi := by
    funext s; simp only [Function.comp_apply, riemannXi_conj, Complex.conj_conj]
  have hreal : conj (deriv riemannXi 0) = deriv riemannXi 0 := by
    simpa using congrFun (by rw [← deriv_conj_conj, hsym] :
      conj ∘ deriv riemannXi ∘ conj = deriv riemannXi) 0
  refine ⟨hexpA, hBeq, ?_⟩
  rw [hBeq, logDeriv_apply, map_div₀, hreal, riemannXi_zero, map_div₀, map_one, map_ofNat]
theorem riemannXi_eq_hadamard_product :
    ∃ B : ℝ, ∀ s, riemannXi s =
      1 / 2 * Complex.exp (B * s) * riemannXiCanonicalProduct riemannXiZeros s := by
  obtain ⟨h, hdiff, _, hrep⟩ := exists_entire_log_riemannXi_div_canonicalProduct
  obtain ⟨A, B, haffine⟩ := exists_affine_log_riemannXi_div_canonicalProduct hdiff hrep
  obtain ⟨hexpA, _, hBreal⟩ := log_riemannXi_div_canonicalProduct_const_eq hdiff hrep haffine
  refine ⟨B.re, fun s ↦ ?_⟩
  have hBre : (B.re : ℂ) = B := Complex.conj_eq_iff_re.mp hBreal
  rw [hrep s, haffine s, Complex.exp_add, hexpA, hBre]
end
end CountPort26
section CountPort27
section
open Complex Filter Topology Set
open scoped Real
private lemma logDeriv_weierstrassE1_div {ρ : ℂ} (hρ : ρ ≠ 0) {s : ℂ} (hs : s ≠ ρ) :
    logDeriv (fun z ↦ weierstrassE1 (z / ρ)) s = 1 / (s - ρ) + 1 / ρ := by
  have hsρ : s - ρ ≠ 0 := sub_ne_zero.mpr hs
  have hne1 : s / ρ ≠ 1 := fun h ↦ hs ((div_eq_one_iff_eq hρ).mp h)
  have h1ρ : (1 : ℂ) - s / ρ ≠ 0 := sub_ne_zero.mpr (Ne.symm hne1)
  have hu : HasDerivAt (fun z : ℂ ↦ z / ρ) (1 / ρ) s := by
    simpa using (hasDerivAt_id s).div_const ρ
  have hc : HasDerivAt (fun z ↦ weierstrassE1 (z / ρ))
      (-(s / ρ) * Complex.exp (s / ρ) * (1 / ρ)) s := by
    have h := (hasDerivAt_weierstrassE1 (s / ρ)).comp s hu
    simpa [Function.comp_def] using h
  rw [logDeriv_apply, hc.deriv]
  simp only [weierstrassE1]
  rw [show -(s / ρ) * Complex.exp (s / ρ) * (1 / ρ)
        = (-(s / ρ) * (1 / ρ)) * Complex.exp (s / ρ) by ring,
      mul_div_mul_right _ _ (Complex.exp_ne_zero _), div_eq_iff h1ρ]
  field_simp
  ring
theorem summable_partial_fraction {s : ℂ} (hs : ∀ i, s ≠ riemannXiZeros i) :
    Summable (fun i ↦ 1 / (s - riemannXiZeros i) + 1 / riemannXiZeros i) := by
  set ρ := riemannXiZeros
  have hsum : Summable (fun i ↦ ‖(ρ i)⁻¹‖ ^ 2) := summable_inv_norm_sq_riemannXiZeros
  have hu : Summable (fun i ↦ 2 * ‖s‖ * ‖(ρ i)⁻¹‖ ^ 2) := hsum.mul_left _
  have htail : ∀ᶠ i in Filter.cofinite, ‖(ρ i)⁻¹‖ ≤ 1 / (2 * (‖s‖ + 1)) := by
    have hlt : (0 : ℝ) < (1 / (2 * (‖s‖ + 1))) ^ 2 := by positivity
    filter_upwards [hsum.tendsto_cofinite_zero.eventually (eventually_lt_nhds hlt)] with i hi
    exact (lt_of_pow_lt_pow_left₀ 2 (by positivity) hi).le
  refine Summable.of_norm_bounded_eventually hu ?_
  filter_upwards [htail] with i hi
  have hρpos : 0 < ‖ρ i‖ := norm_pos_iff.mpr (riemannXiZeros_ne_zero i)
  have hsρpos : 0 < ‖s - ρ i‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (hs i))
  have hbig : 2 * (‖s‖ + 1) ≤ ‖ρ i‖ := by
    rw [norm_inv, one_div] at hi
    exact (inv_le_inv₀ hρpos (by positivity)).mp hi
  have hge : ‖ρ i‖ / 2 ≤ ‖s - ρ i‖ := by
    have h1 : ‖ρ i‖ - ‖s‖ ≤ ‖s - ρ i‖ := by
      rw [norm_sub_rev]; exact norm_sub_norm_le _ _
    nlinarith [norm_nonneg s]
  have hinv : ‖(s - ρ i)⁻¹‖ ≤ 2 * ‖(ρ i)⁻¹‖ := by
    rw [norm_inv, norm_inv]
    rw [show 2 * ‖ρ i‖⁻¹ = (‖ρ i‖ / 2)⁻¹ by rw [inv_div]; ring]
    exact inv_anti₀ (by positivity) hge
  have hρi : ρ i ≠ 0 := riemannXiZeros_ne_zero i
  have hsρi : s - ρ i ≠ 0 := sub_ne_zero.mpr (hs i)
  have hterm : 1 / (s - ρ i) + 1 / ρ i = s * (ρ i)⁻¹ * (s - ρ i)⁻¹ := by
    field_simp
    ring
  calc ‖1 / (s - ρ i) + 1 / ρ i‖
      = ‖s‖ * ‖(ρ i)⁻¹‖ * ‖(s - ρ i)⁻¹‖ := by rw [hterm, norm_mul, norm_mul]
    _ ≤ ‖s‖ * ‖(ρ i)⁻¹‖ * (2 * ‖(ρ i)⁻¹‖) := by gcongr
    _ = 2 * ‖s‖ * ‖(ρ i)⁻¹‖ ^ 2 := by ring
theorem logDeriv_riemannXiCanonicalProduct_eq {s : ℂ}
    (hs : ∀ i, s ≠ riemannXiZeros i) :
    logDeriv (riemannXiCanonicalProduct riemannXiZeros) s
      = ∑' i, (1 / (s - riemannXiZeros i) + 1 / riemannXiZeros i) := by
  set ρ := riemannXiZeros
  have hsum : Summable (fun i ↦ ‖(ρ i)⁻¹‖ ^ 2) := summable_inv_norm_sq_riemannXiZeros
  set f : RiemannXiZerosIndex → ℂ → ℂ := fun i s ↦ weierstrassE1 (s / ρ i)
  have hd : ∀ i, DifferentiableOn ℂ (f i) Set.univ := fun i ↦
    (differentiable_weierstrassE1.comp (differentiable_id.div_const (ρ i))).differentiableOn
  have hfne : ∀ i, f i s ≠ 0 := fun i ↦
    weierstrassE1_ne_zero (fun h ↦ hs i ((div_eq_one_iff_eq (riemannXiZeros_ne_zero i)).mp h))
  have hlog : ∀ i, logDeriv (f i) s = 1 / (s - ρ i) + 1 / ρ i := fun i ↦
    logDeriv_weierstrassE1_div (riemannXiZeros_ne_zero i) (hs i)
  have hmsum : Summable (fun i ↦ logDeriv (f i) s) := by
    simp only [hlog]; exact summable_partial_fraction hs
  have htend : MultipliableLocallyUniformlyOn f Set.univ :=
    (hasProdLocallyUniformlyOn_riemannXiCanonicalProduct ρ hsum).multipliableLocallyUniformlyOn
  have hnez : ∏' i, f i s ≠ 0 :=
    riemannXiCanonicalProduct_ne_zero_of_forall_ne ρ hsum hs
  have hkey := logDeriv_tprod_eq_tsum (s := Set.univ) isOpen_univ (Set.mem_univ s)
    hfne hd hmsum htend hnez
  exact hkey.trans (tsum_congr hlog)
theorem riemannXi_ne_zero_of_forall_ne {s : ℂ} (hs : ∀ i, s ≠ riemannXiZeros i) :
    riemannXi s ≠ 0 := by
  obtain ⟨B, hB⟩ := riemannXi_eq_hadamard_product
  rw [hB s]
  exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.exp_ne_zero _))
    (riemannXiCanonicalProduct_ne_zero_of_forall_ne riemannXiZeros
      summable_inv_norm_sq_riemannXiZeros hs)
theorem logDeriv_riemannXi_eq {s : ℂ} (hs : ∀ i, s ≠ riemannXiZeros i) :
    logDeriv riemannXi s = logDeriv riemannXi 0
      + ∑' i, (1 / (s - riemannXiZeros i) + 1 / riemannXiZeros i) := by
  obtain ⟨B, hB⟩ := riemannXi_eq_hadamard_product
  have key : ∀ z : ℂ, (∀ i, z ≠ riemannXiZeros i) →
      logDeriv riemannXi z = B + ∑' i, (1 / (z - riemannXiZeros i) + 1 / riemannXiZeros i) := by
    intro z hz
    have hPne : riemannXiCanonicalProduct riemannXiZeros z ≠ 0 :=
      riemannXiCanonicalProduct_ne_zero_of_forall_ne _ summable_inv_norm_sq_riemannXiZeros hz
    have hξfun : riemannXi =
        fun w ↦ (1 / 2 * Complex.exp (B * w)) * riemannXiCanonicalProduct riemannXiZeros w := by
      funext w; rw [hB w]
    have hpre : (1 / 2 * Complex.exp (B * z) : ℂ) ≠ 0 :=
      mul_ne_zero (by norm_num) (Complex.exp_ne_zero _)
    have hdpre : DifferentiableAt ℂ (fun w : ℂ ↦ 1 / 2 * Complex.exp (B * w)) z := by
      fun_prop
    have hdP : DifferentiableAt ℂ (riemannXiCanonicalProduct riemannXiZeros) z :=
      differentiable_riemannXiCanonicalProduct _ summable_inv_norm_sq_riemannXiZeros z
    rw [hξfun, logDeriv_mul z hpre hPne hdpre hdP,
      logDeriv_riemannXiCanonicalProduct_eq hz]
    congr 1
    rw [logDeriv_const_mul z _ (by norm_num)]
    have hde : HasDerivAt (fun w : ℂ ↦ Complex.exp (B * w)) (Complex.exp (B * z) * B) z := by
      simpa using ((hasDerivAt_id z).const_mul (B : ℂ)).cexp
    rw [logDeriv_apply, hde.deriv, mul_comm, mul_div_assoc, div_self (Complex.exp_ne_zero _),
      mul_one]
  have h0 : ∀ i, (0 : ℂ) ≠ riemannXiZeros i := fun i ↦ (riemannXiZeros_ne_zero i).symm
  have htsum0 : ∑' i, (1 / ((0 : ℂ) - riemannXiZeros i) + 1 / riemannXiZeros i) = 0 := by
    simp only [zero_sub, one_div, inv_neg, neg_add_cancel, tsum_zero]
  have hkey0 := key 0 h0
  rw [htsum0, add_zero] at hkey0
  rw [key s hs, hkey0]
theorem logDeriv_riemannZeta_eq {s : ℂ} (hre : 0 < s.re) (hs1 : s ≠ 1)
    (hs : ∀ i, s ≠ riemannXiZeros i) :
    logDeriv riemannZeta s = logDeriv riemannXi 0 - 1 / s - 1 / (s - 1)
      + 1 / 2 * (Real.log π : ℂ) - 1 / 2 * Complex.digamma (s / 2)
      + ∑' i, (1 / (s - riemannXiZeros i) + 1 / riemannXiZeros i) := by
  have hs0 : s ≠ 0 := by rintro rfl; simp at hre
  have hsm1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hΓℝ : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos hre
  have hsdiv : 0 < (s / 2).re := by rw [Complex.div_ofNat_re]; linarith
  have hΓne : Complex.Gamma (s / 2) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hsdiv
  have hnp : ∀ m : ℕ, s / 2 ≠ -↑m := ne_neg_natCast_of_re_pos hsdiv
  have hdΓ : DifferentiableAt ℂ Complex.Gamma (s / 2) := differentiableAt_Gamma_of_re_pos hsdiv
  have hζne : riemannZeta s ≠ 0 := by
    intro h
    exact (riemannXi_ne_zero_of_forall_ne hs)
      (by rw [riemannXi_eq_prefactor_mul hs0 hs1 hΓℝ, h, mul_zero])
  have hcpowne : (π : ℂ) ^ (-s / 2) ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero hπ]; exact Complex.exp_ne_zero _
  have hf : HasDerivAt (fun w : ℂ ↦ -w / 2) (-1 / 2 : ℂ) s := by
    simpa using ((hasDerivAt_id s).neg).div_const 2
  have hcp : HasDerivAt (fun w : ℂ ↦ (π : ℂ) ^ (-w / 2))
      ((π : ℂ) ^ (-s / 2) * Complex.log π * (-1 / 2)) s := hf.const_cpow (Or.inl hπ)
  have hlcpow : logDeriv (fun w : ℂ ↦ (π : ℂ) ^ (-w / 2)) s
      = -(1 / 2 : ℂ) * (Real.log π : ℂ) := by
    rw [logDeriv_apply, hcp.deriv,
      show (π : ℂ) ^ (-s / 2) * Complex.log π * (-1 / 2)
        = (Complex.log π * (-1 / 2)) * (π : ℂ) ^ (-s / 2) by ring,
      mul_div_assoc, div_self hcpowne, mul_one, ← Complex.ofReal_log Real.pi_pos.le]
    ring
  have hu : HasDerivAt (fun w : ℂ ↦ w / 2) (1 / 2 : ℂ) s := by
    simpa using (hasDerivAt_id s).div_const 2
  have hdΓfun : DifferentiableAt ℂ (fun w : ℂ ↦ Complex.Gamma (w / 2)) s :=
    hdΓ.comp s hu.differentiableAt
  have hcomp : logDeriv (Complex.Gamma ∘ fun w : ℂ ↦ w / 2) s
      = logDeriv Complex.Gamma (s / 2) * deriv (fun w : ℂ ↦ w / 2) s :=
    logDeriv_comp hdΓ hu.differentiableAt
  have hlΓ : logDeriv (fun w : ℂ ↦ Complex.Gamma (w / 2)) s
      = (1 / 2 : ℂ) * Complex.digamma (s / 2) := by
    rw [show (fun w : ℂ ↦ Complex.Gamma (w / 2)) = Complex.Gamma ∘ fun w ↦ w / 2 from rfl,
      hcomp, hu.deriv, ← Complex.digamma_def]
    ring
  have hdcpow : DifferentiableAt ℂ (fun w : ℂ ↦ (π : ℂ) ^ (-w / 2)) s := hcp.differentiableAt
  have hB' : logDeriv Gammaℝ s
      = -(1 / 2 : ℂ) * (Real.log π : ℂ) + 1 / 2 * Complex.digamma (s / 2) := by
    rw [show (Gammaℝ : ℂ → ℂ) = fun w ↦ (π : ℂ) ^ (-w / 2) * Complex.Gamma (w / 2) from rfl,
      logDeriv_mul s hcpowne hΓne hdcpow hdΓfun, hlcpow, hlΓ]
  have hA : logDeriv (fun w : ℂ ↦ 1 / 2 * (w * (w - 1))) s = 1 / s + 1 / (s - 1) := by
    have hda : HasDerivAt (fun w : ℂ ↦ 1 / 2 * (w * (w - 1))) (1 / 2 * (1 * (s - 1) + s * 1)) s :=
      ((hasDerivAt_id s).mul ((hasDerivAt_id s).sub_const 1)).const_mul (1 / 2)
    rw [logDeriv_apply, hda.deriv]
    field_simp
  have hdΓℝ : DifferentiableAt ℂ Gammaℝ s := (Complex.analyticAt_Gammaℝ hre).differentiableAt
  have hdA' : DifferentiableAt ℂ (fun w : ℂ ↦ 1 / 2 * (w * (w - 1))) s := by fun_prop
  have hdf1 : DifferentiableAt ℂ (fun w : ℂ ↦ 1 / 2 * (w * (w - 1)) * Gammaℝ w) s := hdA'.mul hdΓℝ
  have hdζ : DifferentiableAt ℂ riemannZeta s := differentiableAt_riemannZeta hs1
  have hAne : (1 / 2 * (s * (s - 1)) : ℂ) ≠ 0 := mul_ne_zero (by norm_num) (mul_ne_zero hs0 hsm1)
  have hf1ne : (1 / 2 * (s * (s - 1)) * Gammaℝ s : ℂ) ≠ 0 := mul_ne_zero hAne hΓℝ
  have hEq : riemannXi =ᶠ[nhds s]
      fun w ↦ 1 / 2 * (w * (w - 1)) * Gammaℝ w * riemannZeta w := by
    have hV : IsOpen ({w : ℂ | 0 < w.re} ∩ {w : ℂ | w ≠ 1}) :=
      (Complex.isOpen_re_gt 0).inter isOpen_ne
    filter_upwards [hV.mem_nhds ⟨hre, hs1⟩] with w hw
    obtain ⟨hw0, hw1⟩ := hw
    have hw0' : w ≠ 0 := by rintro rfl; simp at hw0
    exact riemannXi_eq_prefactor_mul hw0' hw1 (Gammaℝ_ne_zero_of_re_pos hw0)
  have hlogeq : logDeriv riemannXi s
      = logDeriv (fun w ↦ 1 / 2 * (w * (w - 1)) * Gammaℝ w * riemannZeta w) s := by
    rw [logDeriv_apply, logDeriv_apply, hEq.deriv_eq, hEq.self_of_nhds]
  have hxi1 : logDeriv riemannXi s = logDeriv riemannXi 0
      + ∑' i, (1 / (s - riemannXiZeros i) + 1 / riemannXiZeros i) := logDeriv_riemannXi_eq hs
  have hxi2 : logDeriv riemannXi s = 1 / s + 1 / (s - 1)
      + (-(1 / 2 : ℂ) * (Real.log π : ℂ) + 1 / 2 * Complex.digamma (s / 2))
      + logDeriv riemannZeta s := by
    rw [hlogeq, logDeriv_mul s hf1ne hζne hdf1 hdζ, logDeriv_mul s hAne hΓℝ hdA' hdΓℝ, hA, hB']
  have heq := hxi2.symm.trans hxi1
  linear_combination heq
end
end CountPort27
section CountPort28
section
def bookerKernelDenom (m v τ : ℝ) : ℝ := (m ^ 2 - v ^ 2 - τ ^ 2) ^ 2 + 4 * m ^ 2 * v ^ 2
noncomputable def bookerRemainder (m v : ℝ) : ℝ :=
  ∫ τ in (0 : ℝ)..1, 2 * τ ^ 2 * (1 - τ) * (m ^ 2 - 3 * v ^ 2 - τ ^ 2) / bookerKernelDenom m v τ
lemma bookerKernelDenom_pos {m v : ℝ} (τ : ℝ) (hm : 0 < m) (hv : v ≠ 0) :
    0 < bookerKernelDenom m v τ :=
  add_pos_of_nonneg_of_pos (sq_nonneg _) (by positivity)
lemma bookerRemainder_nonpos_of_dispersive {m v : ℝ} (hm : 0 < m) (hmv : m ^ 2 ≤ 3 * v ^ 2) :
    bookerRemainder m v ≤ 0 := by
  have hv : v ≠ 0 := by rintro rfl; nlinarith [mul_pos hm hm]
  rw [bookerRemainder, ← neg_nonneg, ← intervalIntegral.integral_neg]
  apply intervalIntegral.integral_nonneg (by norm_num)
  rintro u ⟨_, hu1⟩
  rw [← neg_div]
  exact div_nonneg (neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos
    (mul_nonneg (by positivity) (by linarith)) (by nlinarith [sq_nonneg u])))
    (bookerKernelDenom_pos u hm hv).le
lemma bookerRemainder_le_of_dispersive {m v : ℝ} (hm : 0 < m) (hmv : m ^ 2 ≤ 3 * v ^ 2) :
    bookerRemainder m v ≤ 1 / 2 :=
  (bookerRemainder_nonpos_of_dispersive hm hmv).trans (by norm_num)
lemma bookerKernelDenom_eq_mul (m v τ : ℝ) :
    bookerKernelDenom m v τ = ((m - τ) ^ 2 + v ^ 2) * ((m + τ) ^ 2 + v ^ 2) := by
  unfold bookerKernelDenom; ring
lemma bookerKernelDenom_partialFraction {m v : ℝ} (τ : ℝ) (hm : 0 < m) (hv : v ≠ 0) :
    (m + τ) / ((m + τ) ^ 2 + v ^ 2) + (m - τ) / ((m - τ) ^ 2 + v ^ 2)
      = 2 * m / (m ^ 2 + v ^ 2)
        + 2 * τ ^ 2 * m * (m ^ 2 - 3 * v ^ 2 - τ ^ 2)
            / ((m ^ 2 + v ^ 2) * bookerKernelDenom m v τ) := by
  have hA : ((m - τ) ^ 2 + v ^ 2) ≠ 0 := by positivity
  have hB : ((m + τ) ^ 2 + v ^ 2) ≠ 0 := by positivity
  have hmv : (0 : ℝ) < m ^ 2 + v ^ 2 := by positivity
  have hD : bookerKernelDenom m v τ ≠ 0 := (bookerKernelDenom_pos τ hm hv).ne'
  rw [bookerKernelDenom_eq_mul]
  field_simp
  ring
noncomputable def bookerSinglePole (m v : ℝ) : ℝ :=
  ∫ τ in (0 : ℝ)..1, (1 - τ) *
    ((m + τ) / ((m + τ) ^ 2 + v ^ 2) + (m - τ) / ((m - τ) ^ 2 + v ^ 2))
lemma bookerSinglePole_eq {m v : ℝ} (hm : 0 < m) (hv : v ≠ 0) :
    bookerSinglePole m v = m / (m ^ 2 + v ^ 2) * (1 + bookerRemainder m v) := by
  have hint1 : IntervalIntegrable (fun τ : ℝ ↦ 2 * (1 - τ)) MeasureTheory.volume 0 1 :=
    (by fun_prop : Continuous fun τ : ℝ ↦ 2 * (1 - τ)).intervalIntegrable 0 1
  have hint2 : IntervalIntegrable (fun τ : ℝ ↦
      2 * τ ^ 2 * (1 - τ) * (m ^ 2 - 3 * v ^ 2 - τ ^ 2) / bookerKernelDenom m v τ)
      MeasureTheory.volume 0 1 := by
    apply Continuous.intervalIntegrable
    apply Continuous.div (by fun_prop) (by unfold bookerKernelDenom; fun_prop)
    exact fun τ ↦ (bookerKernelDenom_pos τ hm hv).ne'
  have hpt : Set.EqOn
      (fun τ : ℝ ↦ (1 - τ) *
        ((m + τ) / ((m + τ) ^ 2 + v ^ 2) + (m - τ) / ((m - τ) ^ 2 + v ^ 2)))
      (fun τ : ℝ ↦ m / (m ^ 2 + v ^ 2) *
        (2 * (1 - τ) + 2 * τ ^ 2 * (1 - τ) * (m ^ 2 - 3 * v ^ 2 - τ ^ 2)
          / bookerKernelDenom m v τ))
      (Set.uIcc 0 1) := by
    intro τ _
    dsimp only
    have hmv : (0 : ℝ) < m ^ 2 + v ^ 2 := by positivity
    have hD : bookerKernelDenom m v τ ≠ 0 := (bookerKernelDenom_pos τ hm hv).ne'
    rw [bookerKernelDenom_partialFraction τ hm hv]
    field_simp
  have h1 : ∫ τ in (0 : ℝ)..1, (2 : ℝ) * (1 - τ) = 1 := by
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub
      intervalIntegrable_const intervalIntegral.intervalIntegrable_id]
    norm_num
  unfold bookerSinglePole bookerRemainder
  rw [intervalIntegral.integral_congr hpt, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add hint1 hint2, h1]
lemma bookerSinglePole_le_of_dispersive {m v : ℝ} (hm : 0 < m) (hmv : m ^ 2 ≤ 3 * v ^ 2) :
    bookerSinglePole m v ≤ 3 / 2 * (m / (m ^ 2 + v ^ 2)) := by
  have hv : v ≠ 0 := by rintro rfl; nlinarith [mul_pos hm hm]
  rw [bookerSinglePole_eq hm hv]
  nlinarith [mul_le_mul_of_nonneg_left (bookerRemainder_le_of_dispersive hm hmv)
    (by positivity : (0 : ℝ) ≤ m / (m ^ 2 + v ^ 2))]
private lemma intervalIntegrable_log_add_left (m : ℝ) :
    IntervalIntegrable (fun τ : ℝ ↦ Real.log (m + τ)) MeasureTheory.volume 0 1 := by
  have h := (intervalIntegral.intervalIntegrable_log' (a := m) (b := m + 1)).comp_add_left m
  rwa [show m - m = (0 : ℝ) by ring, show m + 1 - m = (1 : ℝ) by ring] at h
private lemma intervalIntegrable_log_sub_left (m : ℝ) :
    IntervalIntegrable (fun τ : ℝ ↦ Real.log (m - τ)) MeasureTheory.volume 0 1 := by
  have h := (intervalIntegral.intervalIntegrable_log' (a := m - 1) (b := m)).comp_sub_left m
  rw [show m - (m - 1) = (1 : ℝ) by ring, show m - m = (0 : ℝ) by ring] at h
  exact h.symm
noncomputable def bookerSlice (m : ℝ) : ℝ :=
  (m + 1) * Real.log (m + 1) + (m - 1) * Real.log |m - 1| - 2 * m * Real.log m
lemma bookerSlice_eq_integral (m : ℝ) :
    bookerSlice m = ∫ τ in (0 : ℝ)..1, (Real.log (m + τ) - Real.log (m - τ)) := by
  rw [intervalIntegral.integral_sub (intervalIntegrable_log_add_left m)
    (intervalIntegrable_log_sub_left m)]
  have e1 : (∫ τ in (0 : ℝ)..1, Real.log (m + τ))
      = (m + 1) * Real.log (m + 1) - m * Real.log m - 1 := by
    rw [intervalIntegral.integral_comp_add_left Real.log m, add_zero, integral_log]; ring
  have e2 : (∫ τ in (0 : ℝ)..1, Real.log (m - τ))
      = m * Real.log m - (m - 1) * Real.log (m - 1) - 1 := by
    rw [intervalIntegral.integral_comp_sub_left Real.log m, sub_zero, integral_log]; ring
  rw [e1, e2, bookerSlice, Real.log_abs]; ring
lemma bookerSinglePole_eq_half_integral_log {m v : ℝ} (hv : v ≠ 0) :
    bookerSinglePole m v = ∫ τ in (0 : ℝ)..1,
      1 / 2 * (Real.log ((m + τ) ^ 2 + v ^ 2) - Real.log ((m - τ) ^ 2 + v ^ 2)) := by
  set V : ℝ → ℝ :=
    fun τ ↦ 1 / 2 * (Real.log ((m + τ) ^ 2 + v ^ 2) - Real.log ((m - τ) ^ 2 + v ^ 2)) with hVdef
  have hVderiv : ∀ τ : ℝ,
      HasDerivAt V ((m + τ) / ((m + τ) ^ 2 + v ^ 2) + (m - τ) / ((m - τ) ^ 2 + v ^ 2)) τ := by
    intro τ
    have hp : (m + τ) ^ 2 + v ^ 2 ≠ 0 := by positivity
    have hq : (m - τ) ^ 2 + v ^ 2 ≠ 0 := by positivity
    have hin1 : HasDerivAt (fun τ : ℝ ↦ (m + τ) ^ 2 + v ^ 2) (2 * (m + τ)) τ := by
      simpa using (((hasDerivAt_id τ).const_add m).pow 2).add_const (v ^ 2)
    have hin2 : HasDerivAt (fun τ : ℝ ↦ (m - τ) ^ 2 + v ^ 2) (2 * (m - τ) * (-1)) τ := by
      simpa using (((hasDerivAt_id τ).const_sub m).pow 2).add_const (v ^ 2)
    exact (HasDerivAt.const_mul (1 / 2) ((hin1.log hp).sub (hin2.log hq))).congr_deriv
      (by field_simp; ring)
  have hcont : Continuous
      (fun τ : ℝ ↦ (m + τ) / ((m + τ) ^ 2 + v ^ 2) + (m - τ) / ((m - τ) ^ 2 + v ^ 2)) :=
    (Continuous.div (by fun_prop) (by fun_prop) (fun τ ↦ by positivity)).add
      (Continuous.div (by fun_prop) (by fun_prop) (fun τ ↦ by positivity))
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := fun s : ℝ ↦ 1 - s) (v := V) (u' := fun _ : ℝ ↦ (-1 : ℝ))
    (v' := fun τ : ℝ ↦ (m + τ) / ((m + τ) ^ 2 + v ^ 2) + (m - τ) / ((m - τ) ^ 2 + v ^ 2))
    (fun x _ ↦ by simpa using (hasDerivAt_id x).const_sub 1) (fun x _ ↦ hVderiv x)
    (continuous_const.intervalIntegrable 0 1) (hcont.intervalIntegrable 0 1)
  have hV0 : V 0 = 0 := by simp [hVdef]
  rw [bookerSinglePole, hibp, intervalIntegral.integral_const_mul, hV0]
  ring
lemma bookerSinglePole_le_bookerSlice {m v : ℝ} (hm : 0 < m) (hv : v ≠ 0) :
    bookerSinglePole m v ≤ bookerSlice m := by
  rw [bookerSinglePole_eq_half_integral_log hv, bookerSlice_eq_integral m]
  set V : ℝ → ℝ :=
    fun τ ↦ 1 / 2 * (Real.log ((m + τ) ^ 2 + v ^ 2) - Real.log ((m - τ) ^ 2 + v ^ 2)) with hVdef
  have hVcont : Continuous V := by
    rw [hVdef]
    exact ((Continuous.log (by fun_prop) fun τ ↦ by positivity).sub
      (Continuous.log (by fun_prop) fun τ ↦ by positivity)).const_mul _
  refine intervalIntegral.integral_mono_ae_restrict (by norm_num)
    (hVcont.intervalIntegrable 0 1)
    ((intervalIntegrable_log_add_left m).sub (intervalIntegrable_log_sub_left m)) ?_
  refine (MeasureTheory.ae_restrict_iff' measurableSet_Icc).mpr ?_
  filter_upwards [MeasureTheory.Measure.ae_ne (MeasureTheory.volume : MeasureTheory.Measure ℝ) m]
    with τ hτm hτmem
  obtain ⟨hτ0, hτ1⟩ := hτmem
  have hmt : (0 : ℝ) < m + τ := by linarith
  have hmtne : m - τ ≠ 0 := sub_ne_zero.mpr fun h ↦ hτm h.symm
  have hA : (0 : ℝ) < (m + τ) ^ 2 := by positivity
  have hB : (0 : ℝ) < (m - τ) ^ 2 := by positivity
  have hAB : (m - τ) ^ 2 ≤ (m + τ) ^ 2 := by nlinarith [mul_nonneg hm.le hτ0]
  have hfrac : ((m + τ) ^ 2 + v ^ 2) / (m + τ) ^ 2 ≤ ((m - τ) ^ 2 + v ^ 2) / (m - τ) ^ 2 := by
    rw [div_le_div_iff₀ hA hB]; nlinarith [mul_le_mul_of_nonneg_left hAB (sq_nonneg v)]
  have hlog := Real.log_le_log (by positivity) hfrac
  rw [Real.log_div (by positivity) hA.ne', Real.log_div (by positivity) hB.ne',
    Real.log_pow, Real.log_pow] at hlog
  push_cast at hlog
  linarith [hlog]
noncomputable def bookerSinglePoleIntegral (a v : ℝ) : ℝ :=
  ∫ ρ in (0 : ℝ)..2, (1 - |1 - ρ|) * ((ρ - a) / ((ρ - a) ^ 2 + v ^ 2))
lemma bookerSinglePoleIntegral_eq {a v : ℝ} (hv : v ≠ 0) :
    bookerSinglePoleIntegral a v = bookerSinglePole (1 - a) v := by
  unfold bookerSinglePoleIntegral bookerSinglePole
  set f : ℝ → ℝ := fun ρ ↦ (1 - |1 - ρ|) * ((ρ - a) / ((ρ - a) ^ 2 + v ^ 2)) with hf
  set h : ℝ → ℝ := fun τ ↦ (1 - |τ|) * ((1 - a + τ) / ((1 - a + τ) ^ 2 + v ^ 2)) with hh
  have hch : Continuous h := by
    rw [hh]
    exact Continuous.mul (by fun_prop)
      (Continuous.div (by fun_prop) (by fun_prop) fun x ↦ by positivity)
  have hcn : Continuous (fun τ ↦ h (-τ)) := hch.comp continuous_neg
  have hstep : (∫ τ in (-1 : ℝ)..1, f (τ + 1)) = ∫ ρ in (0 : ℝ)..2, f ρ := by
    rw [intervalIntegral.integral_comp_add_right f 1]; norm_num
  have hcongr : (∫ τ in (-1 : ℝ)..1, f (τ + 1)) = ∫ τ in (-1 : ℝ)..1, h τ :=
    intervalIntegral.integral_congr (fun τ _ ↦ by
      simp only [hf, hh]
      rw [show (1 : ℝ) - (τ + 1) = -τ by ring, abs_neg]; ring)
  rw [← hstep, hcongr]
  have hneg : (∫ τ in (-1 : ℝ)..0, h τ) = ∫ τ in (0 : ℝ)..1, h (-τ) := by
    rw [intervalIntegral.integral_comp_neg h]; norm_num
  rw [← intervalIntegral.integral_add_adjacent_intervals
        (hch.intervalIntegrable (-1) 0) (hch.intervalIntegrable 0 1), hneg,
      ← intervalIntegral.integral_add (hcn.intervalIntegrable 0 1) (hch.intervalIntegrable 0 1)]
  refine intervalIntegral.integral_congr (fun τ hτ ↦ ?_)
  rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hτ
  obtain ⟨hτ0, _⟩ := hτ
  simp only [hh, abs_neg, abs_of_nonneg hτ0]
  ring
open intervalIntegral MeasureTheory Topology in
lemma intervalIntegral.integral_integral_add_eq_tent {f : ℝ → ℝ} (hf : Continuous f) :
    (∫ σ in (0 : ℝ)..1, ∫ r in (0 : ℝ)..1, f (r + σ))
      = ∫ ρ in (0 : ℝ)..2, (1 - |1 - ρ|) * f ρ := by
  set F : ℝ → ℝ := fun x ↦ ∫ t in (0 : ℝ)..x, f t with hF_def
  have hFderiv : ∀ x : ℝ, HasDerivAt F (f x) x := fun x ↦
    integral_hasDerivAt_right (hf.intervalIntegrable 0 x)
      (hf.stronglyMeasurableAtFilter volume (𝓝 x)) hf.continuousAt
  have hFcont : Continuous F := Differentiable.continuous fun x ↦ (hFderiv x).differentiableAt
  set G : ℝ → ℝ := fun x ↦ ∫ t in (0 : ℝ)..x, F t with hG_def
  have e0 : (∫ σ in (0 : ℝ)..1, F σ) = G 1 := by simp only [hG_def]
  have hFG2 : (∫ ρ in (1 : ℝ)..2, F ρ) = G 2 - G 1 := by
    simp only [hG_def]
    linarith [integral_add_adjacent_intervals (hFcont.intervalIntegrable (μ := volume) 0 1)
      (hFcont.intervalIntegrable 1 2)]
  have hinner : ∀ σ : ℝ, (∫ r in (0 : ℝ)..1, f (r + σ)) = F (1 + σ) - F σ := fun σ ↦ by
    rw [integral_comp_add_right f σ, zero_add]
    simp only [hF_def]
    linarith [integral_add_adjacent_intervals (hf.intervalIntegrable (μ := volume) 0 σ)
      (hf.intervalIntegrable σ (1 + σ))]
  have e1 : (∫ σ in (0 : ℝ)..1, F (1 + σ)) = G 2 - G 1 := by
    rw [integral_congr (g := fun σ ↦ F (σ + 1)) fun σ _ ↦ by rw [add_comm],
      integral_comp_add_right F 1, zero_add, (by norm_num : (1 : ℝ) + 1 = 2), hFG2]
  have hc1 : IntervalIntegrable (fun σ : ℝ ↦ F (1 + σ)) volume 0 1 :=
    (hFcont.comp (continuous_const.add continuous_id)).intervalIntegrable 0 1
  have hLHS : (∫ σ in (0 : ℝ)..1, ∫ r in (0 : ℝ)..1, f (r + σ)) = G 2 - 2 * G 1 := by
    rw [integral_congr (fun σ _ ↦ hinner σ),
      integral_sub hc1 (hFcont.intervalIntegrable 0 1), e1, e0]
    ring
  have htent : Continuous (fun ρ : ℝ ↦ (1 - |1 - ρ|) * f ρ) := by fun_prop
  have hsplit : (∫ ρ in (0 : ℝ)..2, (1 - |1 - ρ|) * f ρ)
      = (∫ ρ in (0 : ℝ)..1, ρ * f ρ) + ∫ ρ in (1 : ℝ)..2, (2 - ρ) * f ρ := by
    rw [← integral_add_adjacent_intervals (htent.intervalIntegrable 0 1)
      (htent.intervalIntegrable 1 2)]
    congr 1
    · refine integral_congr fun ρ hρ ↦ ?_
      rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hρ
      rw [abs_of_nonneg (by linarith [hρ.2] : (0 : ℝ) ≤ 1 - ρ)]; ring
    · refine integral_congr fun ρ hρ ↦ ?_
      rw [Set.uIcc_of_le (by norm_num : (1 : ℝ) ≤ 2)] at hρ
      rw [abs_of_nonpos (by linarith [hρ.1] : 1 - ρ ≤ 0)]; ring
  have hIBP1 : (∫ ρ in (0 : ℝ)..1, ρ * f ρ) = F 1 - G 1 := by
    have h := integral_mul_deriv_eq_deriv_mul (a := (0 : ℝ)) (b := 1)
      (u := fun ρ ↦ ρ) (v := F) (u' := fun _ ↦ (1 : ℝ)) (v' := f)
      (fun x _ ↦ hasDerivAt_id x) (fun x _ ↦ hFderiv x)
      (continuous_const.intervalIntegrable 0 1) (hf.intervalIntegrable 0 1)
    simp only [one_mul, zero_mul, sub_zero] at h ⊢
    rw [h, e0]
  have hIBP2 : (∫ ρ in (1 : ℝ)..2, (2 - ρ) * f ρ) = -F 1 + (G 2 - G 1) := by
    have h := integral_mul_deriv_eq_deriv_mul (a := (1 : ℝ)) (b := 2)
      (u := fun ρ ↦ 2 - ρ) (v := F) (u' := fun _ ↦ (-1 : ℝ)) (v' := f)
      (fun x _ ↦ (hasDerivAt_id x).const_sub 2) (fun x _ ↦ hFderiv x)
      (continuous_const.intervalIntegrable 1 2) (hf.intervalIntegrable 1 2)
    beta_reduce at h
    rw [h, show (∫ x in (1 : ℝ)..2, (-1 : ℝ) * F x) = -(G 2 - G 1) from by
      rw [intervalIntegral.integral_const_mul, hFG2]; ring]
    ring
  rw [hLHS, hsplit, hIBP1, hIBP2]
  ring
open intervalIntegral MeasureTheory in
lemma integral_integral_eq_bookerSinglePoleIntegral_add {u v : ℝ} (hv : v ≠ 0) :
    (∫ σ in (0 : ℝ)..1, ∫ r in (0 : ℝ)..1,
        (r + σ + u) / ((r + σ + u) ^ 2 + v ^ 2) + (r + σ - u) / ((r + σ - u) ^ 2 + v ^ 2))
      = bookerSinglePoleIntegral (-u) v + bookerSinglePoleIntegral u v := by
  have habs : Continuous (fun ρ : ℝ ↦ 1 - |1 - ρ|) := by fun_prop
  have hcont : Continuous (fun s : ℝ ↦
      (s + u) / ((s + u) ^ 2 + v ^ 2) + (s - u) / ((s - u) ^ 2 + v ^ 2)) :=
    (Continuous.div (by fun_prop) (by fun_prop) (fun s ↦ by positivity)).add
      (Continuous.div (by fun_prop) (by fun_prop) (fun s ↦ by positivity))
  have hk1 : Continuous (fun ρ : ℝ ↦ (1 - |1 - ρ|) * ((ρ - -u) / ((ρ - -u) ^ 2 + v ^ 2))) :=
    habs.mul (Continuous.div (by fun_prop) (by fun_prop) (fun ρ ↦ by positivity))
  have hk2 : Continuous (fun ρ : ℝ ↦ (1 - |1 - ρ|) * ((ρ - u) / ((ρ - u) ^ 2 + v ^ 2))) :=
    habs.mul (Continuous.div (by fun_prop) (by fun_prop) (fun ρ ↦ by positivity))
  calc (∫ σ in (0 : ℝ)..1, ∫ r in (0 : ℝ)..1,
          (r + σ + u) / ((r + σ + u) ^ 2 + v ^ 2) + (r + σ - u) / ((r + σ - u) ^ 2 + v ^ 2))
      = ∫ ρ in (0 : ℝ)..2, (1 - |1 - ρ|) *
          ((ρ + u) / ((ρ + u) ^ 2 + v ^ 2) + (ρ - u) / ((ρ - u) ^ 2 + v ^ 2)) :=
        intervalIntegral.integral_integral_add_eq_tent hcont
    _ = bookerSinglePoleIntegral (-u) v + bookerSinglePoleIntegral u v := by
        unfold bookerSinglePoleIntegral
        rw [← integral_add (hk1.intervalIntegrable 0 2) (hk2.intervalIntegrable 0 2)]
        refine integral_congr (fun ρ _ ↦ ?_)
        ring
noncomputable def bookerSliceReciprocal (x : ℝ) : ℝ :=
  (x + 1) * Real.log (x + 1) - (x - 1) * Real.log |x - 1|
lemma bookerSliceReciprocal_eq_sub (x : ℝ) :
    bookerSliceReciprocal x = (x + 1) * Real.log (x + 1) - (x - 1) * Real.log (x - 1) := by
  rw [bookerSliceReciprocal, Real.log_abs]
private lemma hasDerivAt_log_add_one {x : ℝ} (h : x + 1 ≠ 0) :
    HasDerivAt (fun y : ℝ ↦ Real.log (y + 1)) (x + 1)⁻¹ x := by
  simpa [Function.comp_def] using (Real.hasDerivAt_log h).comp x ((hasDerivAt_id x).add_const 1)
private lemma hasDerivAt_log_sub_one {x : ℝ} (h : x - 1 ≠ 0) :
    HasDerivAt (fun y : ℝ ↦ Real.log (y - 1)) (x - 1)⁻¹ x := by
  simpa [Function.comp_def] using (Real.hasDerivAt_log h).comp x ((hasDerivAt_id x).sub_const 1)
private lemma hasDerivAt_bookerSliceReciprocal {x : ℝ} (h1 : x + 1 ≠ 0) (h2 : x - 1 ≠ 0) :
    HasDerivAt bookerSliceReciprocal (Real.log (x + 1) - Real.log (x - 1)) x := by
  rw [funext bookerSliceReciprocal_eq_sub]
  have d1 : HasDerivAt (fun x : ℝ ↦ x + 1) 1 x := (hasDerivAt_id x).add_const 1
  have d2 : HasDerivAt (fun x : ℝ ↦ x - 1) 1 x := (hasDerivAt_id x).sub_const 1
  exact ((d1.mul (hasDerivAt_log_add_one h1)).sub (d2.mul (hasDerivAt_log_sub_one h2))).congr_deriv
    (by rw [mul_inv_cancel₀ h1, mul_inv_cancel₀ h2]; ring)
private lemma deriv_bookerSliceReciprocal_eqOn {U : Set ℝ} (hU : IsOpen U)
    (hUmem : ∀ y ∈ U, y + 1 ≠ 0 ∧ y - 1 ≠ 0) {x : ℝ} (hx : x ∈ U) :
    deriv bookerSliceReciprocal =ᶠ[nhds x] fun y ↦ Real.log (y + 1) - Real.log (y - 1) :=
  Filter.eventuallyEq_of_mem (hU.mem_nhds hx) fun y hy ↦
    (hasDerivAt_bookerSliceReciprocal (hUmem y hy).1 (hUmem y hy).2).deriv
private lemma hasDerivAt_deriv_bookerSliceReciprocal {U : Set ℝ} (hU : IsOpen U)
    (hUmem : ∀ y ∈ U, y + 1 ≠ 0 ∧ y - 1 ≠ 0) {x : ℝ} (hx : x ∈ U) :
    HasDerivAt (deriv bookerSliceReciprocal) ((x + 1)⁻¹ - (x - 1)⁻¹) x := by
  have heq := deriv_bookerSliceReciprocal_eqOn hU hUmem hx
  exact (((hasDerivAt_log_add_one (hUmem x hx).1).sub
    (hasDerivAt_log_sub_one (hUmem x hx).2)).congr_of_eventuallyEq heq)
private lemma deriv2_bookerSliceReciprocal {U : Set ℝ} (hU : IsOpen U)
    (hUmem : ∀ y ∈ U, y + 1 ≠ 0 ∧ y - 1 ≠ 0) {x : ℝ} (hx : x ∈ U) :
    deriv^[2] bookerSliceReciprocal x = (x + 1)⁻¹ - (x - 1)⁻¹ := by
  change deriv (deriv bookerSliceReciprocal) x = _
  exact (hasDerivAt_deriv_bookerSliceReciprocal hU hUmem hx).deriv
private lemma continuous_bookerSliceReciprocal_form :
    Continuous fun x : ℝ ↦ (x + 1) * Real.log (x + 1) - (x - 1) * Real.log (x - 1) :=
  (Real.continuous_mul_log.comp (by fun_prop : Continuous fun x : ℝ ↦ x + 1)).sub
    (Real.continuous_mul_log.comp (by fun_prop : Continuous fun x : ℝ ↦ x - 1))
private lemma continuousOn_bookerSliceReciprocal (S : Set ℝ) :
    ContinuousOn bookerSliceReciprocal S :=
  continuous_bookerSliceReciprocal_form.continuousOn.congr fun x _ ↦
    bookerSliceReciprocal_eq_sub x
private lemma convexOn_bookerSliceReciprocal :
    ConvexOn ℝ (Set.Icc (1 / 2 : ℝ) 1) bookerSliceReciprocal := by
  have hUmem : ∀ y ∈ Set.Ioo (1 / 2 : ℝ) 1, y + 1 ≠ 0 ∧ y - 1 ≠ 0 := fun y hy ↦
    ⟨ne_of_gt (by linarith [hy.1]), ne_of_lt (by linarith [hy.2])⟩
  apply convexOn_of_deriv2_nonneg (convex_Icc _ _) (continuousOn_bookerSliceReciprocal _)
  · rw [interior_Icc]; intro x hx
    exact (hasDerivAt_bookerSliceReciprocal (hUmem x hx).1
      (hUmem x hx).2).differentiableAt.differentiableWithinAt
  · rw [interior_Icc]; intro x hx
    exact (hasDerivAt_deriv_bookerSliceReciprocal isOpen_Ioo hUmem
      hx).differentiableAt.differentiableWithinAt
  · rw [interior_Icc]; intro x hx
    rw [deriv2_bookerSliceReciprocal isOpen_Ioo hUmem hx]
    have hna : (x - 1)⁻¹ < 0 := inv_lt_zero.mpr (by linarith [hx.2])
    have hpb : (0 : ℝ) < (x + 1)⁻¹ := inv_pos.mpr (by linarith [hx.1])
    linarith
private lemma concaveOn_bookerSliceReciprocal :
    ConcaveOn ℝ (Set.Ici (1 : ℝ)) bookerSliceReciprocal := by
  have hUmem : ∀ y ∈ Set.Ioi (1 : ℝ), y + 1 ≠ 0 ∧ y - 1 ≠ 0 := fun y hy ↦
    ⟨ne_of_gt (by simp only [Set.mem_Ioi] at hy; linarith),
      ne_of_gt (by simp only [Set.mem_Ioi] at hy; linarith)⟩
  apply concaveOn_of_deriv2_nonpos (convex_Ici _) (continuousOn_bookerSliceReciprocal _)
  · rw [interior_Ici]; intro x hx
    exact (hasDerivAt_bookerSliceReciprocal (hUmem x hx).1
      (hUmem x hx).2).differentiableAt.differentiableWithinAt
  · rw [interior_Ici]; intro x hx
    exact (hasDerivAt_deriv_bookerSliceReciprocal isOpen_Ioi hUmem
      hx).differentiableAt.differentiableWithinAt
  · rw [interior_Ici]; intro x hx
    rw [deriv2_bookerSliceReciprocal isOpen_Ioi hUmem hx, sub_nonpos]
    simp only [Set.mem_Ioi] at hx
    have ha : 0 < x - 1 := by linarith
    exact inv_anti₀ ha (by linarith)
private lemma le_add_deriv_mul_of_concaveOn {f : ℝ → ℝ} {S : Set ℝ} {x x₀ f' : ℝ}
    (hf : ConcaveOn ℝ S f) (hx : x ∈ S) (hx₀ : x₀ ∈ S) (hd : HasDerivAt f f' x₀) :
    f x ≤ f x₀ + f' * (x - x₀) := by
  rcases lt_trichotomy x x₀ with hlt | heq | hgt
  · have hslope := hf.le_slope_of_hasDerivAt hx hx₀ hlt hd
    rw [slope_def_field, le_div_iff₀ (by linarith : (0 : ℝ) < x₀ - x)] at hslope
    nlinarith [hslope]
  · rw [heq]; simp
  · have hslope := hf.slope_le_of_hasDerivAt hx₀ hx hgt hd
    rw [slope_def_field, div_le_iff₀ (by linarith : (0 : ℝ) < x - x₀)] at hslope
    nlinarith [hslope]
lemma bookerSliceReciprocal_le {x : ℝ} (hx : 1 / 2 ≤ x) :
    bookerSliceReciprocal x ≤ 3 / 2 * x ^ 2 := by
  have hl2l := Real.log_two_gt_d9
  have hl2u := Real.log_two_lt_d9
  have hl3l := Real.log_three_gt_d9
  have hl3u := Real.log_three_lt_d9
  have hl5l := Real.log_five_gt_d9
  have hl5u := Real.log_five_lt_d9
  rcases le_total x 1 with hx1 | hx1
  ·
    have hmem_half : (1 / 2 : ℝ) ∈ Set.Icc (1 / 2 : ℝ) 1 := by constructor <;> norm_num
    have hmem_one : (1 : ℝ) ∈ Set.Icc (1 / 2 : ℝ) 1 := by constructor <;> norm_num
    have ha : (0 : ℝ) ≤ 2 * (1 - x) := by linarith
    have hb : (0 : ℝ) ≤ 2 * x - 1 := by linarith
    have hab : 2 * (1 - x) + (2 * x - 1) = 1 := by ring
    have hchord := convexOn_bookerSliceReciprocal.2 hmem_half hmem_one ha hb hab
    simp only [smul_eq_mul] at hchord
    rw [show 2 * (1 - x) * (1 / 2) + (2 * x - 1) * 1 = x by ring] at hchord
    have e_half : bookerSliceReciprocal (1 / 2) = 3 / 2 * Real.log 3 - 2 * Real.log 2 := by
      rw [bookerSliceReciprocal, show |(1 : ℝ) / 2 - 1| = 1 / 2 by
          rw [show (1 : ℝ) / 2 - 1 = -(1 / 2) by norm_num, abs_neg]; norm_num,
        show (1 : ℝ) / 2 + 1 = 3 / 2 by norm_num,
        Real.log_div (by norm_num) (by norm_num), Real.log_div (by norm_num) (by norm_num),
        Real.log_one]
      ring
    have e_one : bookerSliceReciprocal 1 = 2 * Real.log 2 := by
      rw [bookerSliceReciprocal, show (1 : ℝ) + 1 = 2 by norm_num, show (1 : ℝ) - 1 = 0 by norm_num]
      simp only [abs_zero, Real.log_zero, mul_zero, sub_zero]
    rw [e_half, e_one] at hchord
    nlinarith [hchord, sq_nonneg (x - (8 * Real.log 2 - 3 * Real.log 3) / 3),
      hl2l, hl2u, hl3l, hl3u,
      mul_nonneg (by linarith : (0 : ℝ) ≤ Real.log 3 - 1.0986122885)
        (by linarith : (0 : ℝ) ≤ (0.6931471808 : ℝ) - Real.log 2),
      mul_nonneg (by linarith : (0 : ℝ) ≤ Real.log 2 - 0.6931471803)
        (by linarith : (0 : ℝ) ≤ (1.0986122888 : ℝ) - Real.log 3)]
  ·
    have hx0mem : (13 / 12 : ℝ) ∈ Set.Ici (1 : ℝ) := by norm_num
    have hxmem : x ∈ Set.Ici (1 : ℝ) := hx1
    have hderiv : HasDerivAt bookerSliceReciprocal
        (Real.log (13 / 12 + 1) - Real.log (13 / 12 - 1)) (13 / 12) :=
      hasDerivAt_bookerSliceReciprocal (by norm_num) (by norm_num)
    have eL' : Real.log (13 / 12 + 1) - Real.log (13 / 12 - 1) = 2 * Real.log 5 := by
      rw [show (13 : ℝ) / 12 + 1 = 25 / 12 by norm_num, show (13 : ℝ) / 12 - 1 = 1 / 12 by norm_num,
        ← Real.log_div (by norm_num) (by norm_num),
        show (25 : ℝ) / 12 / (1 / 12) = 25 by norm_num, show (25 : ℝ) = 5 ^ 2 by norm_num,
        Real.log_pow]
      push_cast; ring
    have eL0 : bookerSliceReciprocal (13 / 12)
        = 25 / 6 * Real.log 5 - 4 * Real.log 2 - 2 * Real.log 3 := by
      rw [bookerSliceReciprocal_eq_sub, show (13 : ℝ) / 12 + 1 = 25 / 12 by norm_num,
        show (13 : ℝ) / 12 - 1 = 1 / 12 by norm_num,
        Real.log_div (by norm_num) (by norm_num), Real.log_div (by norm_num) (by norm_num),
        Real.log_one, show (25 : ℝ) = 5 ^ 2 by norm_num, show (12 : ℝ) = 2 ^ 2 * 3 by norm_num,
        Real.log_pow, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
      push_cast; ring
    rw [eL'] at hderiv
    have htan : bookerSliceReciprocal x
        ≤ bookerSliceReciprocal (13 / 12) + 2 * Real.log 5 * (x - 13 / 12) :=
      le_add_deriv_mul_of_concaveOn concaveOn_bookerSliceReciprocal hxmem hx0mem hderiv
    rw [eL0] at htan
    nlinarith [htan, sq_nonneg (x - 2 * Real.log 5 / 3), hl2l, hl2u, hl3l, hl5l, hl5u,
      mul_nonneg (by linarith : (0 : ℝ) ≤ Real.log 5 - 1.6094379123)
        (by linarith : (0 : ℝ) ≤ (1.6094379126 : ℝ) - Real.log 5)]
lemma bookerSlice_eq_mul_bookerSliceReciprocal {m : ℝ} (hm : 0 < m) :
    bookerSlice m = m * bookerSliceReciprocal (1 / m) := by
  have hm0 : m ≠ 0 := hm.ne'
  rcases eq_or_ne m 1 with rfl | hm1
  · norm_num [bookerSlice, bookerSliceReciprocal]
  · have hlm : Real.log (1 / m + 1) = Real.log (m + 1) - Real.log m := by
      rw [show (1 : ℝ) / m + 1 = (m + 1) / m by field_simp; ring, Real.log_div (by positivity) hm0]
    have habs : |m - 1| ≠ 0 := abs_ne_zero.mpr (sub_ne_zero.mpr hm1)
    have hlm2 : Real.log |1 / m - 1| = Real.log |m - 1| - Real.log m := by
      rw [show |(1 : ℝ) / m - 1| = |m - 1| / m by
            rw [show (1 : ℝ) / m - 1 = (1 - m) / m by field_simp, abs_div, abs_of_pos hm,
              abs_sub_comm],
        Real.log_div habs hm0]
    rw [bookerSlice, bookerSliceReciprocal, hlm, hlm2]
    field_simp
    ring
lemma mul_bookerSlice_le {m : ℝ} (hm0 : 0 < m) (hm2 : m ≤ 2) :
    m * bookerSlice m ≤ 3 / 2 := by
  have hx : (1 : ℝ) / 2 ≤ 1 / m := by rw [le_div_iff₀ hm0]; linarith
  rw [bookerSlice_eq_mul_bookerSliceReciprocal hm0]
  nlinarith [mul_le_mul_of_nonneg_left (bookerSliceReciprocal_le hx) (sq_nonneg m),
    (by field_simp : m ^ 2 * (1 / m) ^ 2 = 1)]
lemma bookerSinglePole_le_of {m v : ℝ} (hm0 : 0 ≤ m) (hm2 : m ≤ 2) (hv : v ≠ 0)
    {c : ℝ} (hc : 2 ≤ c) :
    bookerSinglePole m v ≤ c * (m / (m ^ 2 + v ^ 2)) := by
  rcases hm0.lt_or_eq with hm | rfl
  · rcases le_or_gt (m ^ 2) (3 * v ^ 2) with hd | hconc
    ·
      have hdisp := bookerSinglePole_le_of_dispersive hm hd
      have hpos : (0 : ℝ) ≤ m / (m ^ 2 + v ^ 2) := by positivity
      exact le_trans hdisp (mul_le_mul_of_nonneg_right (by linarith) hpos)
    ·
      have hP : bookerSinglePole m v ≤ bookerSlice m := bookerSinglePole_le_bookerSlice hm hv
      have hΦ : m * bookerSlice m ≤ 3 / 2 := mul_bookerSlice_le hm hm2
      have hmv2 : (0 : ℝ) < m ^ 2 + v ^ 2 := by positivity
      have hB : bookerSlice m ≤ 3 / (2 * m) := by
        rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * m)]; nlinarith [hΦ]
      have hD : (3 : ℝ) / (2 * m) ≤ c * (m / (m ^ 2 + v ^ 2)) := by
        rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * m),
          show c * (m / (m ^ 2 + v ^ 2)) * (2 * m) = 2 * c * m ^ 2 / (m ^ 2 + v ^ 2) by ring,
          le_div_iff₀ hmv2]
        nlinarith [hconc.le, mul_nonneg (show (0 : ℝ) ≤ c - 2 by linarith) (mul_pos hm hm).le]
      exact le_trans (le_trans hP hB) hD
  ·
    have h0 : bookerSinglePole 0 v = 0 := by
      rw [bookerSinglePole, intervalIntegral.integral_congr (g := fun _ : ℝ ↦ (0 : ℝ))
        (fun τ _ ↦ by
          rw [show (0 : ℝ) + τ = τ by ring, show (0 : ℝ) - τ = -τ by ring, neg_sq]; ring),
        intervalIntegral.integral_zero]
    rw [h0]
    simp
theorem bookerSinglePoleIntegral_le_of {a v : ℝ} (ha1 : -1 ≤ a) (ha2 : a ≤ 1) (hv : v ≠ 0)
    {c : ℝ} (hc : 2 ≤ c) :
    bookerSinglePoleIntegral a v ≤ c * ((1 - a) / ((1 - a) ^ 2 + v ^ 2)) := by
  rw [bookerSinglePoleIntegral_eq hv]
  exact bookerSinglePole_le_of (by linarith) (by linarith) hv hc
noncomputable def bookerPairKernel (u v s : ℝ) : ℝ :=
  (s + u) / ((s + u) ^ 2 + v ^ 2) + (s - u) / ((s - u) ^ 2 + v ^ 2)
noncomputable def bookerPairIntegral (d : ℝ) (w : ℂ) : ℝ :=
  ∫ x in (0 : ℝ)..d, Real.log ‖((x : ℂ) + (d : ℂ) + w) *
    ((x : ℂ) + (d : ℂ) - (starRingEnd ℂ) w) /
    (((x : ℂ) + w) * ((x : ℂ) - (starRingEnd ℂ) w))‖
theorem bookerPairKernel_integral_le_of {u v : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv : v ≠ 0)
    {c : ℝ} (hc : 2 ≤ c) :
    (∫ σ in (0 : ℝ)..1, ∫ r in (0 : ℝ)..1, bookerPairKernel u v (r + σ))
      ≤ c * bookerPairKernel u v 1 := by
  unfold bookerPairKernel
  rw [integral_integral_eq_bookerSinglePoleIntegral_add hv]
  have h1 := bookerSinglePoleIntegral_le_of (a := -u) (v := v) (by linarith) (by linarith) hv hc
  have h2 := bookerSinglePoleIntegral_le_of (a := u) (v := v) (by linarith) (by linarith) hv hc
  simp only [sub_neg_eq_add] at h1
  rw [mul_add]
  linarith
private lemma bookerPairKernel_abs (u v s : ℝ) :
    bookerPairKernel u v s = bookerPairKernel |u| v s := by
  unfold bookerPairKernel
  rcases abs_choice u with h | h
  · rw [h]
  · rw [h]; ring
private lemma bookerPairKernel_scale (u v s d : ℝ) (hd : d ≠ 0) (hv : v ≠ 0) :
    bookerPairKernel u v (d * s) = 1 / d * bookerPairKernel (u / d) (v / d) s := by
  have h1 : (d * s + u) ^ 2 + v ^ 2 ≠ 0 := by positivity
  have h2 : (d * s - u) ^ 2 + v ^ 2 ≠ 0 := by positivity
  have h3 : (s + u / d) ^ 2 + (v / d) ^ 2 ≠ 0 := by positivity
  have h4 : (s - u / d) ^ 2 + (v / d) ^ 2 ≠ 0 := by positivity
  unfold bookerPairKernel
  rw [show d * s + u = d * (s + u / d) by field_simp,
    show d * s - u = d * (s - u / d) by field_simp]
  field_simp
private lemma Complex.log_norm_eq_half_log (z : ℂ) :
    Real.log ‖z‖ = 1 / 2 * Real.log (z.re ^ 2 + z.im ^ 2) := by
  rw [Complex.norm_def, Real.log_sqrt (Complex.normSq_nonneg _), Complex.normSq_apply, ← sq, ← sq]
  ring
private lemma integral_pole_add (x d v b : ℝ) (hv : v ≠ 0) :
    (∫ σ in (0 : ℝ)..d, (x + σ + b) / ((x + σ + b) ^ 2 + v ^ 2))
      = 1 / 2 * Real.log ((x + d + b) ^ 2 + v ^ 2) - 1 / 2 * Real.log ((x + b) ^ 2 + v ^ 2) := by
  have hpos : ∀ s : ℝ, (0 : ℝ) < (x + s + b) ^ 2 + v ^ 2 := fun s ↦ by positivity
  have hF : ∀ s ∈ Set.uIcc (0 : ℝ) d,
      HasDerivAt (fun y ↦ 1 / 2 * Real.log ((x + y + b) ^ 2 + v ^ 2))
        ((x + s + b) / ((x + s + b) ^ 2 + v ^ 2)) s := by
    intro s _
    have hlin : HasDerivAt (fun y ↦ x + y + b) 1 s := by
      simpa using ((hasDerivAt_id s).const_add x).add_const b
    have hsq : HasDerivAt (fun y ↦ (x + y + b) ^ 2 + v ^ 2) (2 * (x + s + b)) s := by
      simpa using (hlin.pow 2).add_const (v ^ 2)
    exact ((hsq.log (hpos s).ne').const_mul (1 / 2)).congr_deriv (by ring)
  have hcont : Continuous (fun s ↦ (x + s + b) / ((x + s + b) ^ 2 + v ^ 2)) :=
    Continuous.div (by fun_prop) (by fun_prop) (fun s ↦ ne_of_gt (hpos s))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF (hcont.intervalIntegrable _ _)]; norm_num
private lemma integral_pole_sub (x d v a : ℝ) (hv : v ≠ 0) :
    (∫ σ in (0 : ℝ)..d, (x + σ - a) / ((x + σ - a) ^ 2 + v ^ 2))
      = 1 / 2 * Real.log ((x + d - a) ^ 2 + v ^ 2) - 1 / 2 * Real.log ((x - a) ^ 2 + v ^ 2) := by
  rw [show (∫ σ in (0 : ℝ)..d, (x + σ - a) / ((x + σ - a) ^ 2 + v ^ 2))
        = ∫ σ in (0 : ℝ)..d, (x + σ + (-a)) / ((x + σ + (-a)) ^ 2 + v ^ 2) from
      intervalIntegral.integral_congr (fun σ _ ↦ by ring_nf), integral_pole_add x d v (-a) hv]
  ring_nf
private lemma double_integral_bookerPairKernel_scale {d u v : ℝ} (hd : 0 < d) (hv : v ≠ 0) :
    (∫ x in (0 : ℝ)..d, ∫ σ in (0 : ℝ)..d, bookerPairKernel u v (x + σ))
      = d * ∫ x in (0 : ℝ)..1, ∫ σ in (0 : ℝ)..1, bookerPairKernel (u / d) (v / d) (x + σ) := by
  have subst : ∀ (f : ℝ → ℝ), (∫ y in (0 : ℝ)..d, f y) = d * ∫ y in (0 : ℝ)..1, f (d * y) := by
    intro f
    rw [intervalIntegral.integral_comp_mul_left f hd.ne', mul_zero, mul_one, smul_eq_mul,
        ← mul_assoc, mul_inv_cancel₀ hd.ne', one_mul]
  rw [subst (fun x ↦ ∫ σ in (0 : ℝ)..d, bookerPairKernel u v (x + σ))]
  rw [intervalIntegral.integral_congr
        (g := fun y ↦ d * ∫ σ in (0 : ℝ)..1, bookerPairKernel u v (d * y + d * σ))
        (fun y _ ↦ subst (fun σ ↦ bookerPairKernel u v (d * y + σ)))]
  rw [intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_congr
        (g := fun y ↦ 1 / d * ∫ σ in (0 : ℝ)..1, bookerPairKernel (u / d) (v / d) (y + σ))
        (fun y _ ↦ ?_)]
  · rw [intervalIntegral.integral_const_mul]; field_simp
  · change (∫ σ in (0 : ℝ)..1, bookerPairKernel u v (d * y + d * σ))
        = 1 / d * ∫ σ in (0 : ℝ)..1, bookerPairKernel (u / d) (v / d) (y + σ)
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun σ _ ↦ ?_)
    rw [show d * y + d * σ = d * (y + σ) by ring, bookerPairKernel_scale u v (y + σ) d hd.ne' hv]
private lemma bookerPairKernel_integral_le_of_abs_le {u v : ℝ} (hu : |u| ≤ 1) (hv : v ≠ 0)
    {c : ℝ} (hc : 2 ≤ c) :
    (∫ σ in (0 : ℝ)..1, ∫ r in (0 : ℝ)..1, bookerPairKernel u v (σ + r))
      ≤ c * bookerPairKernel u v 1 := by
  have key := bookerPairKernel_integral_le_of (abs_nonneg u) hu hv hc
  rw [show (∫ σ in (0 : ℝ)..1, ∫ r in (0 : ℝ)..1, bookerPairKernel u v (σ + r))
        = ∫ σ in (0 : ℝ)..1, ∫ r in (0 : ℝ)..1, bookerPairKernel |u| v (r + σ) from
      intervalIntegral.integral_congr (fun σ _ ↦
        intervalIntegral.integral_congr (fun r _ ↦ by
          rw [bookerPairKernel_abs u v (σ + r), add_comm σ r]))]
  rw [bookerPairKernel_abs u v 1]
  exact key
theorem bookerPairIntegral_le_of {d : ℝ} (hd1 : 1 / 2 < d) {w : ℂ}
    (hw : |w.re| ≤ 1 / 2) (hwim : w.im ≠ 0) {c : ℝ} (hc : 2 ≤ c) :
    bookerPairIntegral d w
      ≤ c * d ^ 2 * (1 / ((d : ℂ) + w) + 1 / ((d : ℂ) - (starRingEnd ℂ) w)).re := by
  unfold bookerPairIntegral
  have hd0 : 0 < d := by linarith
  have hre : (1 / ((d : ℂ) + w) + 1 / ((d : ℂ) - (starRingEnd ℂ) w)).re
      = bookerPairKernel w.re w.im d := by
    unfold bookerPairKernel
    simp only [Complex.add_re, Complex.inv_re, Complex.normSq_apply, Complex.add_im,
      Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re,
      Complex.conj_im, one_div]
    ring
  have hint : ∀ x : ℝ,
      Real.log ‖((x : ℂ) + (d : ℂ) + w) * ((x : ℂ) + (d : ℂ) - (starRingEnd ℂ) w) /
        (((x : ℂ) + w) * ((x : ℂ) - (starRingEnd ℂ) w))‖
        = ∫ σ in (0 : ℝ)..d, bookerPairKernel w.re w.im (x + σ) := by
    intro x
    have hz : ∀ z : ℂ, z.im ≠ 0 → z ≠ 0 := fun z hz h ↦ hz (by rw [h]; simp)
    have hA : ((x : ℂ) + (d : ℂ) + w) ≠ 0 := hz _ (by simpa using hwim)
    have hB : ((x : ℂ) + (d : ℂ) - (starRingEnd ℂ) w) ≠ 0 := hz _ (by simpa using hwim)
    have hC : ((x : ℂ) + w) ≠ 0 := hz _ (by simpa using hwim)
    have hD : ((x : ℂ) - (starRingEnd ℂ) w) ≠ 0 := hz _ (by simpa using hwim)
    rw [norm_div, norm_mul, norm_mul,
        Real.log_div (mul_ne_zero (norm_ne_zero_iff.mpr hA) (norm_ne_zero_iff.mpr hB))
                     (mul_ne_zero (norm_ne_zero_iff.mpr hC) (norm_ne_zero_iff.mpr hD)),
        Real.log_mul (norm_ne_zero_iff.mpr hA) (norm_ne_zero_iff.mpr hB),
        Real.log_mul (norm_ne_zero_iff.mpr hC) (norm_ne_zero_iff.mpr hD),
        Complex.log_norm_eq_half_log, Complex.log_norm_eq_half_log,
        Complex.log_norm_eq_half_log, Complex.log_norm_eq_half_log]
    simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im]
    unfold bookerPairKernel
    rw [intervalIntegral.integral_add, integral_pole_add x d w.im w.re hwim,
        integral_pole_sub x d w.im w.re hwim]
    · ring_nf
    · exact (Continuous.div (by fun_prop) (by fun_prop)
        (fun s ↦ by positivity)).intervalIntegrable _ _
    · exact (Continuous.div (by fun_prop) (by fun_prop)
        (fun s ↦ by positivity)).intervalIntegrable _ _
  rw [hre, intervalIntegral.integral_congr (fun x _ ↦ hint x),
      double_integral_bookerPairKernel_scale hd0 hwim]
  have hRHS : c * d ^ 2 * bookerPairKernel w.re w.im d
      = d * (c * bookerPairKernel (w.re / d) (w.im / d) 1) := by
    have hs := bookerPairKernel_scale w.re w.im 1 d hd0.ne' hwim
    rw [mul_one] at hs
    rw [hs]; field_simp
  rw [hRHS]
  apply mul_le_mul_of_nonneg_left _ hd0.le
  refine bookerPairKernel_integral_le_of_abs_le ?_ ?_ hc
  · rw [abs_div, abs_of_pos hd0, div_le_one hd0]; linarith
  · exact div_ne_zero hwim hd0.ne'
end
end CountPort28


