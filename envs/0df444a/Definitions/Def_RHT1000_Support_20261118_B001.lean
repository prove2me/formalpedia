-- Prove2me | Definitions.Def_RHT1000_Support_20261118_B001
-- name    : RHT1000_Support_20261118_B001
-- status  : Definition
-- author  : @bueno_ricardo
-- created : 2026-11-18T16:19:12.499658+00:00
-- url     : https://prove2.me/theorems/650514fd-4e0b-440a-a544-a2e66a65369c
-- title:
--   Suporte completo para T1000 — bloco 1 de 10
-- statement:
--   Definições e lemas auxiliares completos para a prova finita T1000. Este bloco não afirma sozinho a conclusão T1000 nem RH. A divisão reduz o tempo de compilação sem substituir demonstrações por hipóteses.
-- source:
--   Código adaptado de Salvatore Mercuri e Bhavik Mehta, smmercuri/zeta, tag v1-1e8 (3dab648), com dependências e avisos de autoria preservados. Fonte histórica integral T1000: https://axle.axiommath.ai/check#r=d2dcb520-c50a-44dc-a527-de0f7a51b892 . Reorganização em módulos ordinários para compatibilidade com Prove2Me; atribuição da adaptação: projeto Desenvolvimento RH, Ricardo Marangoni Brandão Bueno.

import Mathlib
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
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
/-
Copyright (c) 2026 Salvatore Mercuri, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri, Bhavik Mehta
-/
section CertificatePort0
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
end CertificatePort0

section CertificatePort1
section
open scoped Real
namespace Real
theorem arctan_le_self {x : ℝ} (hx : 0 ≤ x) : arctan x ≤ x := by
  rcases hx.eq_or_lt with h | h
  · simp [← h]
  · have hlt := lt_tan (arctan_pos.2 h) (arctan_lt_pi_div_two x)
    rw [tan_arctan] at hlt
    exact hlt.le
theorem div_one_add_sq_le_arctan {x : ℝ} (hx : 0 ≤ x) : x / (1 + x ^ 2) ≤ arctan x := by
  have hpos : (0 : ℝ) < 1 + x ^ 2 := by positivity
  have hsq : √(1 + x ^ 2) * √(1 + x ^ 2) = 1 + x ^ 2 := mul_self_sqrt hpos.le
  have hsin : sin (2 * arctan x) = 2 * (x / (1 + x ^ 2)) := by
    rw [sin_two_mul, sin_arctan, cos_arctan, mul_assoc, div_mul_div_comm, mul_one, hsq]
  have hle : sin (2 * arctan x) ≤ 2 * arctan x := sin_le (by positivity)
  rw [hsin] at hle
  linarith
end Real
end
end CertificatePort1

section CertificatePort2
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
end CertificatePort2

section CertificatePort3
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
end CertificatePort3

section CertificatePort4
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
end CertificatePort4

section CertificatePort5
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
end CertificatePort5

section CertificatePort6
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
end CertificatePort6

section CertificatePort7
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
end CertificatePort7

section CertificatePort8
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
end CertificatePort8

section CertificatePort9
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
end CertificatePort9

section CertificatePort10
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
end CertificatePort10

section CertificatePort11
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
noncomputable def scale (g : CS n E) (R : ℝ) : CS n E := by
  by_cases h : R = 0
  · exact ⟨0, contDiff_const, by simp [HasCompactSupport, tsupport]⟩
  · refine ⟨fun x => funscale g R x, ?_, ?_⟩
    · exact g.h1.comp (contDiff_const_smul R⁻¹)
    · exact g.h2.comp_smul (inv_ne_zero h)
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
end CertificatePort11

section CertificatePort12
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
end
end CertificatePort12

section CertificatePort13
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
end CertificatePort13

section CertificatePort14
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
def Square (p : ℂ) (c : ℝ) : Set ℂ := Rectangle (-c - c * I + p) (c + c * I + p)
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
end CertificatePort14


