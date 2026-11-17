-- Prove2me | Definitions.Def_RHCount_ZeroCounting_20261116_v1
-- name    : RHCount_ZeroCounting_20261116_v1
-- status  : Definition
-- author  : @bueno_ricardo
-- created : 2026-11-16T18:25:49.794246+00:00
-- url     : https://prove2.me/theorems/1f30500c-1869-440f-8e52-f80474e329e7
-- title:
--   Argument variation and exact zeta zero counting
-- statement:
--   A support module defining continuous argument variation, the Riemann-Siegel phase and the multiplicity-weighted zeta zero counter. It includes the proved argument-principle infrastructure and exact Riemann-von Mangoldt relation used by the subsequent counting estimates. It imports the xi-product support module; all proofs are complete.
-- source:
--   Desenvolvimento RH — Ricardo Marangoni Brandão Bueno. Analytic sources smmercuri/zeta commit 3dab6480a82f1bfc5de0a59550e279cf50490033; PrimeNumberTheoremAnd commit 0a2c672d7533437e50f7a72596cb0ecd17352fbe. Partition of the completely checked actual_count_submission.lean into closed source sections. Complete sources, Apache-2.0 licenses and exact source manifest accompany the reproducibility archive. No novelty claim.

import Definitions.Def_RHCount_XiProduct_20261116_v1
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
section CountPort29
section
open scoped Topology
variable {a b : ℝ}
def IsContLog (a b : ℝ) (φ g : ℝ → ℂ) : Prop :=
  ContinuousOn g (Set.Icc a b) ∧ ∀ u ∈ Set.Icc a b, Complex.exp (g u) = φ u
namespace IsContLog
theorem continuousOn {φ g : ℝ → ℂ} (hg : IsContLog a b φ g) :
    ContinuousOn φ (Set.Icc a b) :=
  (Complex.continuous_exp.comp_continuousOn hg.1).congr fun u hu => (hg.2 u hu).symm
theorem ne_zero {φ g : ℝ → ℂ} (hg : IsContLog a b φ g) {u : ℝ} (hu : u ∈ Set.Icc a b) :
    φ u ≠ 0 := by
  rw [← hg.2 u hu]; exact Complex.exp_ne_zero _
end IsContLog
theorem simplyConnectedSpace_Icc (hab : a ≤ b) :
    SimplyConnectedSpace ↥(Set.Icc a b) := by
  have : ContractibleSpace ↥(Set.Icc a b) :=
    (convex_Icc a b).contractibleSpace ⟨a, Set.left_mem_Icc.mpr hab⟩
  infer_instance
instance instLocallyPathConnectedSpaceIcc :
    LocallyPathConnectedSpace ↥(Set.Icc a b) :=
  (convex_Icc a b).locallyPathConnectedSpace
theorem exists_isContLog (hab : a ≤ b) {φ : ℝ → ℂ}
    (hφ : ContinuousOn φ (Set.Icc a b)) (h0 : ∀ u ∈ Set.Icc a b, φ u ≠ 0)
    {c : ℂ} (hc : Complex.exp c = φ a) :
    ∃ g : ℝ → ℂ, IsContLog a b φ g ∧ g a = c := by
  have := simplyConnectedSpace_Icc hab
  let f : C(↥(Set.Icc a b), ℂ) := ⟨(Set.Icc a b).domRestrict φ, hφ.domRestrict⟩
  have hs : ∀ x : ↥(Set.Icc a b), f x ∈ ({0}ᶜ : Set ℂ) := fun x =>
    Set.mem_compl_singleton_iff.mpr (h0 x.1 x.2)
  have he : Complex.exp c = f ⟨a, Set.left_mem_Icc.mpr hab⟩ := hc
  obtain ⟨F, ⟨hFa, hFp⟩, -⟩ :=
    Complex.isCoveringMapOn_exp.existsUnique_continuousMap_lifts f he hs
  refine ⟨fun u => F (Set.projIcc a b hab u), ⟨?_, ?_⟩, ?_⟩
  · exact (F.continuous.comp continuous_projIcc).continuousOn
  · intro u hu
    change Complex.exp (F (Set.projIcc a b hab u)) = φ u
    have hcong := congrFun hFp (Set.projIcc a b hab u)
    simp only [Function.comp_apply] at hcong
    rw [hcong, Set.projIcc_of_mem hab hu]
    rfl
  · change F (Set.projIcc a b hab a) = c
    rw [Set.projIcc_of_mem hab (Set.left_mem_Icc.mpr hab)]
    exact hFa
theorem exists_isContLog_of_ne_zero (hab : a ≤ b) {φ : ℝ → ℂ}
    (hφ : ContinuousOn φ (Set.Icc a b)) (h0 : ∀ u ∈ Set.Icc a b, φ u ≠ 0) :
    ∃ g, IsContLog a b φ g :=
  let ⟨g, hg, _⟩ := exists_isContLog hab hφ h0 (Complex.exp_log (h0 a (Set.left_mem_Icc.mpr hab)))
  ⟨g, hg⟩
theorem IsContLog.sub_const (hab : a ≤ b) {φ g₁ g₂ : ℝ → ℂ}
    (h1 : IsContLog a b φ g₁) (h2 : IsContLog a b φ g₂) :
    ∀ u ∈ Set.Icc a b, g₁ u - g₂ u = g₁ a - g₂ a := by
  have := simplyConnectedSpace_Icc hab
  have hamem : a ∈ Set.Icc a b := Set.left_mem_Icc.mpr hab
  set k : ℂ := g₁ a - g₂ a with hk
  let f : C(↥(Set.Icc a b), ℂ) := ⟨(Set.Icc a b).domRestrict φ, h1.continuousOn.domRestrict⟩
  let F₁ : C(↥(Set.Icc a b), ℂ) := ⟨(Set.Icc a b).domRestrict g₁, h1.1.domRestrict⟩
  let F₂ : C(↥(Set.Icc a b), ℂ) :=
    ⟨fun x => (Set.Icc a b).domRestrict g₂ x + k, (h2.1.domRestrict).add continuous_const⟩
  have hexpk : Complex.exp k = 1 := by
    rw [hk, Complex.exp_sub, h1.2 a hamem, h2.2 a hamem, div_self (h1.ne_zero hamem)]
  have hP1 : F₁ ⟨a, hamem⟩ = g₁ a ∧ Complex.exp ∘ ⇑F₁ = ⇑f := by
    refine ⟨rfl, funext fun x => ?_⟩
    simpa [F₁, f] using h1.2 x.1 x.2
  have hP2 : F₂ ⟨a, hamem⟩ = g₁ a ∧ Complex.exp ∘ ⇑F₂ = ⇑f := by
    refine ⟨by simp only [F₂, ContinuousMap.coe_mk, Set.domRestrict_apply, hk]; ring,
      funext fun x => ?_⟩
    simp only [F₂, f, Function.comp_apply, ContinuousMap.coe_mk, Set.domRestrict_apply,
      Complex.exp_add, hexpk, mul_one]
    exact h2.2 x.1 x.2
  have huniq := Complex.isCoveringMapOn_exp.existsUnique_continuousMap_lifts f
    (e₀ := g₁ a) (a₀ := ⟨a, hamem⟩) (h1.2 a hamem)
    (fun x => Set.mem_compl_singleton_iff.mpr (h1.ne_zero x.2))
  have hF : F₁ = F₂ := huniq.unique hP1 hP2
  intro u hu
  have := DFunLike.congr_fun hF ⟨u, hu⟩
  simp only [F₁, F₂, ContinuousMap.coe_mk, Set.domRestrict_apply] at this
  rw [this]; ring
theorem IsContLog.im_sub_eq (hab : a ≤ b) {φ g₁ g₂ : ℝ → ℂ}
    (h1 : IsContLog a b φ g₁) (h2 : IsContLog a b φ g₂) :
    (g₁ b).im - (g₁ a).im = (g₂ b).im - (g₂ a).im := by
  have key := h1.sub_const hab h2 b (Set.right_mem_Icc.mpr hab)
  have hsub : (g₁ b - g₂ b).im = (g₁ a - g₂ a).im := by rw [key]
  simp only [Complex.sub_im] at hsub
  linarith
open Classical in
noncomputable def argVariation (a b : ℝ) (φ : ℝ → ℂ) : ℝ :=
  if h : ∃ g, IsContLog a b φ g then (h.choose b).im - (h.choose a).im else 0
theorem argVariation_eq_of_isContLog (hab : a ≤ b) {φ g : ℝ → ℂ}
    (hg : IsContLog a b φ g) : argVariation a b φ = (g b).im - (g a).im := by
  have hex : ∃ g, IsContLog a b φ g := ⟨g, hg⟩
  rw [argVariation, dif_pos hex]
  exact IsContLog.im_sub_eq hab hex.choose_spec hg
theorem argVariation_congr (hab : a ≤ b) {φ ψ : ℝ → ℂ}
    (h : Set.EqOn φ ψ (Set.Icc a b)) : argVariation a b φ = argVariation a b ψ := by
  by_cases hex : ∃ g, IsContLog a b φ g
  · obtain ⟨g, hg⟩ := hex
    have hg' : IsContLog a b ψ g := ⟨hg.1, fun u hu => (hg.2 u hu).trans (h hu)⟩
    rw [argVariation_eq_of_isContLog hab hg, argVariation_eq_of_isContLog hab hg']
  · have hex' : ¬ ∃ g, IsContLog a b ψ g := fun ⟨g, hg⟩ =>
      hex ⟨g, hg.1, fun u hu => (hg.2 u hu).trans (h hu).symm⟩
    unfold argVariation
    rw [dif_neg hex, dif_neg hex']
theorem argVariation_mul (hab : a ≤ b) {φ ψ : ℝ → ℂ}
    (hφ : ContinuousOn φ (Set.Icc a b)) (h0φ : ∀ u ∈ Set.Icc a b, φ u ≠ 0)
    (hψ : ContinuousOn ψ (Set.Icc a b)) (h0ψ : ∀ u ∈ Set.Icc a b, ψ u ≠ 0) :
    argVariation a b (φ * ψ) = argVariation a b φ + argVariation a b ψ := by
  obtain ⟨g, hg⟩ := exists_isContLog_of_ne_zero hab hφ h0φ
  obtain ⟨h, hh⟩ := exists_isContLog_of_ne_zero hab hψ h0ψ
  have hgh : IsContLog a b (φ * ψ) (g + h) := by
    refine ⟨hg.1.add hh.1, fun u hu => ?_⟩
    simp only [Pi.add_apply, Complex.exp_add, hg.2 u hu, hh.2 u hu, Pi.mul_apply]
  rw [argVariation_eq_of_isContLog hab hgh, argVariation_eq_of_isContLog hab hg,
    argVariation_eq_of_isContLog hab hh]
  simp only [Pi.add_apply, Complex.add_im]
  ring
theorem argVariation_trans {m : ℝ} (ham : a ≤ m) (hmb : m ≤ b) {φ : ℝ → ℂ}
    (hφ : ContinuousOn φ (Set.Icc a b)) (h0 : ∀ u ∈ Set.Icc a b, φ u ≠ 0) :
    argVariation a b φ = argVariation a m φ + argVariation m b φ := by
  have hab : a ≤ b := ham.trans hmb
  obtain ⟨g, hg⟩ := exists_isContLog_of_ne_zero hab hφ h0
  have hsub_am : Set.Icc a m ⊆ Set.Icc a b := Set.Icc_subset_Icc le_rfl hmb
  have hsub_mb : Set.Icc m b ⊆ Set.Icc a b := Set.Icc_subset_Icc ham le_rfl
  have hg_am : IsContLog a m φ g := ⟨hg.1.mono hsub_am, fun u hu => hg.2 u (hsub_am hu)⟩
  have hg_mb : IsContLog m b φ g := ⟨hg.1.mono hsub_mb, fun u hu => hg.2 u (hsub_mb hu)⟩
  rw [argVariation_eq_of_isContLog hab hg, argVariation_eq_of_isContLog ham hg_am,
    argVariation_eq_of_isContLog hmb hg_mb]
  ring
theorem argVariation_reverse (hab : a ≤ b) {φ : ℝ → ℂ}
    (hφ : ContinuousOn φ (Set.Icc a b)) (h0 : ∀ u ∈ Set.Icc a b, φ u ≠ 0) :
    argVariation a b (fun u => φ (a + b - u)) = - argVariation a b φ := by
  obtain ⟨g, hg⟩ := exists_isContLog_of_ne_zero hab hφ h0
  have hmap : Set.MapsTo (fun u : ℝ => a + b - u) (Set.Icc a b) (Set.Icc a b) := by
    intro u hu
    simp only [Set.mem_Icc] at hu ⊢
    constructor <;> linarith [hu.1, hu.2]
  have hcont : Continuous (fun u : ℝ => a + b - u) := by fun_prop
  have hg' : IsContLog a b (fun u => φ (a + b - u)) (fun u => g (a + b - u)) := by
    refine ⟨hg.1.comp hcont.continuousOn hmap, fun u hu => hg.2 (a + b - u) (hmap hu)⟩
  rw [argVariation_eq_of_isContLog hab hg', argVariation_eq_of_isContLog hab hg]
  rw [show a + b - b = a by ring, show a + b - a = b by ring]
  ring
theorem argVariation_comp {a' b' : ℝ} (hab : a ≤ b) (hab' : a' ≤ b')
    {σ : ℝ → ℝ} (hσc : ContinuousOn σ (Set.Icc a' b'))
    (hσmap : Set.MapsTo σ (Set.Icc a' b') (Set.Icc a b))
    (hσa : σ a' = a) (hσb : σ b' = b) {φ : ℝ → ℂ}
    (hφ : ContinuousOn φ (Set.Icc a b)) (h0 : ∀ u ∈ Set.Icc a b, φ u ≠ 0) :
    argVariation a' b' (fun v => φ (σ v)) = argVariation a b φ := by
  obtain ⟨g, hg⟩ := exists_isContLog_of_ne_zero hab hφ h0
  have hg' : IsContLog a' b' (fun v => φ (σ v)) (fun v => g (σ v)) :=
    ⟨hg.1.comp hσc hσmap, fun v hv => hg.2 (σ v) (hσmap hv)⟩
  rw [argVariation_eq_of_isContLog hab' hg', argVariation_eq_of_isContLog hab hg, hσa, hσb]
theorem argVariation_eq_arg_sub_arg (hab : a ≤ b) {φ : ℝ → ℂ}
    (hφ : ContinuousOn φ (Set.Icc a b)) (hsp : ∀ u ∈ Set.Icc a b, φ u ∈ Complex.slitPlane) :
    argVariation a b φ = (φ b).arg - (φ a).arg := by
  have hlog : IsContLog a b φ (fun u => Complex.log (φ u)) :=
    ⟨hφ.clog hsp, fun u hu => Complex.exp_log (Complex.slitPlane_ne_zero (hsp u hu))⟩
  rw [argVariation_eq_of_isContLog hab hlog, Complex.log_im, Complex.log_im]
private theorem injOn_exp_ball (z₀ : ℂ) :
    Set.InjOn Complex.exp (Metric.ball z₀ Real.pi) := by
  intro z hz w hw hzw
  have h1 : Complex.exp (z - w) = 1 := by
    rw [Complex.exp_sub, hzw, div_self (Complex.exp_ne_zero _)]
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h1
  have hd : ‖z - w‖ < 2 * Real.pi := by
    calc ‖z - w‖ = ‖(z - z₀) - (w - z₀)‖ := by ring_nf
      _ ≤ ‖z - z₀‖ + ‖w - z₀‖ := norm_sub_le _ _
      _ < Real.pi + Real.pi := by
          rw [mem_ball_iff_norm] at hz hw; exact add_lt_add hz hw
      _ = 2 * Real.pi := by ring
  have him : (z - w).im = 2 * Real.pi * n := by
    rw [hn]; simp only [Complex.mul_im, Complex.mul_re, Complex.intCast_re, Complex.intCast_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.re_ofNat,
      Complex.im_ofNat]; ring
  have hbound : |2 * Real.pi * (n : ℝ)| ≤ ‖z - w‖ := him ▸ Complex.abs_im_le_norm _
  have hn0 : n = 0 := by
    rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)] at hbound
    have : |n| < 1 := by exact_mod_cast (by nlinarith [Real.pi_pos] : |(n : ℝ)| < 1)
    have := abs_lt.mp this; omega
  rw [hn0] at hn
  simp only [Int.cast_zero, zero_mul] at hn
  exact sub_eq_zero.mp hn
theorem IsContLog.hasDerivAt {φ g : ℝ → ℂ} (hg : IsContLog a b φ g)
    {u₀ : ℝ} (hu₀ : u₀ ∈ Set.Ioo a b) {φ' : ℂ} (hφ' : HasDerivAt φ φ' u₀) :
    HasDerivAt g (φ' / φ u₀) u₀ := by
  have hu₀I : u₀ ∈ Set.Icc a b := Set.Ioo_subset_Icc_self hu₀
  have hw₀ : φ u₀ ≠ 0 := hg.ne_zero hu₀I
  obtain ⟨r, hr0, hrsp⟩ : ∃ r : ℂ, r ≠ 0 ∧ r * φ u₀ ∈ Complex.slitPlane := by
    rcases Complex.mem_slitPlane_or_neg_mem_slitPlane hw₀ with h | h
    · exact ⟨1, one_ne_zero, by simpa using h⟩
    · exact ⟨-1, by norm_num, by simpa using h⟩
  set L : ℝ → ℂ := fun u => Complex.log (r * φ u) - Complex.log r with hL_def
  have hL : HasDerivAt L (φ' / φ u₀) u₀ := by
    have h3 := ((Complex.hasDerivAt_log hrsp).comp u₀ (hφ'.const_mul r)).sub_const (Complex.log r)
    rw [inv_mul_eq_div, mul_div_mul_left _ _ hr0] at h3
    exact h3
  have hLexp : ∀ u, r * φ u ∈ Complex.slitPlane → Complex.exp (L u) = φ u := by
    intro u hu
    rw [hL_def, Complex.exp_sub, Complex.exp_log (Complex.slitPlane_ne_zero hu),
      Complex.exp_log hr0, mul_comm, mul_div_assoc, div_self hr0, mul_one]
  have hφc : ContinuousAt φ u₀ := hφ'.continuousAt
  have hIccnhds : Set.Icc a b ∈ 𝓝 u₀ :=
    Filter.mem_of_superset (isOpen_Ioo.mem_nhds hu₀) Set.Ioo_subset_Icc_self
  have hgc : ContinuousAt g u₀ := hg.1.continuousAt hIccnhds
  have hsp_nhds : ∀ᶠ u in 𝓝 u₀, r * φ u ∈ Complex.slitPlane :=
    (hφc.const_mul r).eventually_mem (Complex.isOpen_slitPlane.mem_nhds hrsp)
  set k₀ : ℂ := g u₀ - L u₀ with hk₀
  have hLkval : L u₀ + k₀ = g u₀ := by rw [hk₀]; ring
  have hLkc : ContinuousAt (fun u => L u + k₀) u₀ := hL.continuousAt.add continuousAt_const
  have hg_ball : ∀ᶠ u in 𝓝 u₀, g u ∈ Metric.ball (g u₀) Real.pi :=
    hgc.eventually_mem (Metric.ball_mem_nhds _ Real.pi_pos)
  have hLk_ball : ∀ᶠ u in 𝓝 u₀, (fun u => L u + k₀) u ∈ Metric.ball (g u₀) Real.pi := by
    apply hLkc.eventually_mem
    apply Metric.isOpen_ball.mem_nhds
    show L u₀ + k₀ ∈ Metric.ball (g u₀) Real.pi
    rw [hLkval]; exact Metric.mem_ball_self Real.pi_pos
  have hg_exp : ∀ᶠ u in 𝓝 u₀, Complex.exp (g u) = φ u := by
    filter_upwards [hIccnhds] with u hu using hg.2 u hu
  have hexpk : Complex.exp k₀ = 1 := by
    rw [hk₀, Complex.exp_sub, hg.2 u₀ hu₀I, hLexp u₀ hrsp, div_self hw₀]
  have hev : g =ᶠ[𝓝 u₀] (fun u => L u + k₀) := by
    filter_upwards [hg_ball, hLk_ball, hg_exp, hsp_nhds] with u hu1 hu2 hu3 hu4
    apply injOn_exp_ball (g u₀) hu1 hu2
    rw [hu3]
    simp only [Complex.exp_add, hLexp u hu4, hexpk, mul_one]
  exact (hL.add_const k₀).congr_of_eventuallyEq hev
theorem argVariation_eq_im_integral (hab : a ≤ b) {φ φ' : ℝ → ℂ}
    (hφ : ContinuousOn φ (Set.Icc a b)) (h0 : ∀ u ∈ Set.Icc a b, φ u ≠ 0)
    (hderiv : ∀ u ∈ Set.Ioo a b, HasDerivAt φ (φ' u) u)
    (hint : ContinuousOn (fun u => φ' u / φ u) (Set.Icc a b)) :
    argVariation a b φ = (∫ u in a..b, φ' u / φ u).im := by
  obtain ⟨g, hg⟩ := exists_isContLog_of_ne_zero hab hφ h0
  have hgderiv : ∀ u ∈ Set.Ioo a b, HasDerivAt g (φ' u / φ u) u :=
    fun u hu => hg.hasDerivAt hu (hderiv u hu)
  have hftc : ∫ u in a..b, φ' u / φ u = g b - g a :=
    intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hab hg.1
      (fun u hu => (hgderiv u hu).hasDerivWithinAt) (hint.intervalIntegrable_of_Icc hab)
  rw [argVariation_eq_of_isContLog hab hg, hftc, Complex.sub_im]
noncomputable def lineSeg (z₀ z₁ : ℂ) (u : ℝ) : ℂ := z₀ + (u : ℂ) * (z₁ - z₀)
@[simp] theorem lineSeg_zero (z₀ z₁ : ℂ) : lineSeg z₀ z₁ 0 = z₀ := by simp [lineSeg]
@[simp] theorem lineSeg_one (z₀ z₁ : ℂ) : lineSeg z₀ z₁ 1 = z₁ := by
  simp only [lineSeg, Complex.ofReal_one, one_mul]; ring
theorem lineSeg_re (z₀ z₁ : ℂ) (u : ℝ) :
    (lineSeg z₀ z₁ u).re = z₀.re + u * (z₁.re - z₀.re) := by
  simp [lineSeg, Complex.add_re, Complex.mul_re, Complex.sub_re]
theorem lineSeg_im (z₀ z₁ : ℂ) (u : ℝ) :
    (lineSeg z₀ z₁ u).im = z₀.im + u * (z₁.im - z₀.im) := by
  simp [lineSeg, Complex.add_im, Complex.mul_im, Complex.sub_im]
theorem continuous_lineSeg (z₀ z₁ : ℂ) : Continuous (lineSeg z₀ z₁) := by
  unfold lineSeg; fun_prop
theorem lineSeg_sub_const (z₀ z₁ c : ℂ) :
    (fun u => lineSeg z₀ z₁ u - c) = lineSeg (z₀ - c) (z₁ - c) := by
  funext u; simp only [lineSeg]; ring
end
end CountPort29
section CountPort30
section
open Complex
namespace Complex
theorem arg_add_arg_neg_conj {z : ℂ} (hz : 0 < z.im) :
    z.arg + (-(starRingEnd ℂ z)).arg = Real.pi := by
  have hpi : z.arg ≠ Real.pi := fun h ↦ hz.ne' (Complex.arg_eq_pi_iff.mp h).2
  rw [Complex.arg_neg_eq_arg_add_pi_of_im_neg (by simpa using hz), Complex.arg_conj, if_neg hpi]
  ring
end Complex
variable {a b : ℝ}
theorem argVariation_const (hab : a ≤ b) {c : ℂ} (hc : c ≠ 0) :
    argVariation a b (fun _ ↦ c) = 0 := by
  rw [argVariation_eq_of_isContLog hab
    (g := fun _ ↦ Complex.log c) ⟨continuousOn_const, fun _ _ ↦ Complex.exp_log hc⟩]
  ring
theorem argVariation_lineSeg {z₀ z₁ : ℂ}
    (h : ∀ u ∈ Set.Icc (0 : ℝ) 1, lineSeg z₀ z₁ u ∈ Complex.slitPlane) :
    argVariation 0 1 (lineSeg z₀ z₁) = z₁.arg - z₀.arg := by
  simpa using
    argVariation_eq_arg_sub_arg zero_le_one (continuous_lineSeg z₀ z₁).continuousOn h
noncomputable def argVariationContourL (f : ℂ → ℂ) (T : ℝ) : ℝ :=
  argVariation 0 1 (fun u ↦ f (lineSeg 2 (2 + Complex.I * T) u)) +
    argVariation 0 1 (fun u ↦ f (lineSeg (2 + Complex.I * T) (1 / 2 + Complex.I * T) u))
noncomputable def riemannSiegelTheta (T : ℝ) : ℝ :=
  argVariation 0 T (fun u ↦ Complex.Gamma (1 / 4 + Complex.I * (u / 2))) -
    (T / 2) * Real.log Real.pi
noncomputable def argZeta (T : ℝ) : ℝ := (1 / Real.pi) * argVariationContourL riemannZeta T
theorem argVariation_poly_seg {z₀ z₁ : ℂ}
    (hs : ∀ u ∈ Set.Icc (0 : ℝ) 1, lineSeg z₀ z₁ u ∈ Complex.slitPlane)
    (hs1 : ∀ u ∈ Set.Icc (0 : ℝ) 1, lineSeg (z₀ - 1) (z₁ - 1) u ∈ Complex.slitPlane) :
    argVariation 0 1 (fun u ↦ (1 / 2) * (lineSeg z₀ z₁ u * (lineSeg z₀ z₁ u - 1)))
      = (z₁.arg - z₀.arg) + ((z₁ - 1).arg - (z₀ - 1).arg) := by
  have hc2 : (1 / 2 : ℂ) ≠ 0 := one_div_ne_zero two_ne_zero
  have hsub : (fun u ↦ lineSeg z₀ z₁ u - 1) = lineSeg (z₀ - 1) (z₁ - 1) :=
    lineSeg_sub_const z₀ z₁ 1
  have hcont : ContinuousOn (lineSeg z₀ z₁) (Set.Icc (0 : ℝ) 1) :=
    (continuous_lineSeg z₀ z₁).continuousOn
  have hcont1 : ContinuousOn (fun u ↦ lineSeg z₀ z₁ u - 1) (Set.Icc (0 : ℝ) 1) :=
    ((continuous_lineSeg z₀ z₁).sub continuous_const).continuousOn
  have h0 : ∀ u ∈ Set.Icc (0 : ℝ) 1, lineSeg z₀ z₁ u ≠ 0 :=
    fun u hu ↦ Complex.slitPlane_ne_zero (hs u hu)
  have h1 : ∀ u ∈ Set.Icc (0 : ℝ) 1, lineSeg z₀ z₁ u - 1 ≠ 0 := fun u hu ↦ by
    rw [congrFun hsub u]; exact Complex.slitPlane_ne_zero (hs1 u hu)
  change argVariation 0 1
    ((fun _ ↦ (1 / 2 : ℂ)) * (lineSeg z₀ z₁ * fun u ↦ lineSeg z₀ z₁ u - 1)) = _
  rw [argVariation_mul zero_le_one continuousOn_const (fun _ _ ↦ hc2) (hcont.mul hcont1)
        (fun u hu ↦ mul_ne_zero (h0 u hu) (h1 u hu)),
    argVariation_const zero_le_one hc2, zero_add,
    argVariation_mul zero_le_one hcont h0 hcont1 h1,
    argVariation_lineSeg hs, hsub, argVariation_lineSeg hs1]
theorem argVariation_poly_L {T : ℝ} (hT : 0 < T) :
    argVariationContourL (fun s ↦ (1 / 2) * (s * (s - 1))) T = Real.pi := by
  have memRe : ∀ {z₀ z₁ : ℂ} {r : ℝ}, 0 < r → z₀.re = r → z₁.re = r →
      ∀ u ∈ Set.Icc (0 : ℝ) 1, lineSeg z₀ z₁ u ∈ Complex.slitPlane :=
    fun hr h0 h1 u _ ↦ Complex.mem_slitPlane_iff.2 <| .inl <| by
      rw [lineSeg_re, h0, h1]; simpa using hr
  have memIm : ∀ {z₀ z₁ : ℂ} {y : ℝ}, y ≠ 0 → z₀.im = y → z₁.im = y →
      ∀ u ∈ Set.Icc (0 : ℝ) 1, lineSeg z₀ z₁ u ∈ Complex.slitPlane :=
    fun hy h0 h1 u _ ↦ Complex.mem_slitPlane_iff.2 <| .inr <| by
      rw [lineSeg_im, h0, h1]; simpa using hy
  simp only [argVariationContourL]
  rw [argVariation_poly_seg (memRe (r := 2) two_pos (by norm_num) (by simp))
        (memRe (r := 1) one_pos (by norm_num) (by norm_num)),
      argVariation_poly_seg (memIm (y := T) hT.ne' (by simp) (by simp))
        (memIm (y := T) hT.ne' (by simp) (by simp))]
  have hzsub : (1 / 2 + Complex.I * (T : ℂ)) - 1 =
      -(starRingEnd ℂ (1 / 2 + Complex.I * (T : ℂ))) := by
    norm_num [Complex.ext_iff]
  have hz_im : (0 : ℝ) < (1 / 2 + Complex.I * (T : ℂ)).im := by simpa using hT
  rw [hzsub, Complex.ofNat_arg, show (2 : ℂ) - 1 = 1 by norm_num, Complex.arg_one]
  linarith [arg_add_arg_neg_conj hz_im]
end
end CountPort30
section CountPort31
section
open Complex Filter Topology Asymptotics
private theorem analyticAt_logDeriv {f : ℂ → ℂ} {x : ℂ} (hf : AnalyticAt ℂ f x) (h0 : f x ≠ 0) :
    AnalyticAt ℂ (logDeriv f) x :=
  show AnalyticAt ℂ (fun z ↦ deriv f z / f z) x from hf.deriv.div hf h0
private theorem holomorphicOn_logDeriv {f : ℂ → ℂ} {U S : Set ℂ} (hf : AnalyticOnNhd ℂ f U)
    (hSU : S ⊆ U) (h0 : ∀ x ∈ S, f x ≠ 0) : HolomorphicOn (logDeriv f) S := fun x hx ↦
  (analyticAt_logDeriv (hf x (hSU hx)) (h0 x hx)).differentiableAt.differentiableWithinAt
theorem meromorphicOrderAt_eq_residue_logDeriv {f : ℂ → ℂ} {z₀ : ℂ}
    (hf : AnalyticAt ℂ f z₀) (hf0 : ¬ ∀ᶠ z in 𝓝 z₀, f z = 0) :
    ∃ (n : ℕ) (g : ℂ → ℂ), AnalyticAt ℂ g z₀ ∧ g z₀ ≠ 0 ∧
      meromorphicOrderAt f z₀ = (n : ℤ) ∧
      AnalyticAt ℂ (logDeriv g) z₀ ∧
      logDeriv f =ᶠ[𝓝[≠] z₀] fun z ↦ (n : ℂ) / (z - z₀) + logDeriv g z := by
  obtain ⟨n, g, hg_an, hg_ne, hfg⟩ := hf.exists_eventuallyEq_pow_smul_nonzero_iff.mpr hf0
  have hord : meromorphicOrderAt f z₀ = (n : ℤ) := by
    rw [hf.meromorphicOrderAt_eq, hf.analyticOrderAt_eq_natCast.mpr ⟨g, hg_an, hg_ne, hfg⟩]; rfl
  refine ⟨n, g, hg_an, hg_ne, hord, analyticAt_logDeriv hg_an hg_ne, ?_⟩
  have hfg' : f =ᶠ[𝓝 z₀] fun z ↦ (z - z₀) ^ n • g z := hfg
  refine ((hfg'.deriv.div hfg').filter_mono nhdsWithin_le_nhds).trans ?_
  filter_upwards [self_mem_nhdsWithin,
    (hg_an.continuousAt.eventually_ne hg_ne).filter_mono nhdsWithin_le_nhds,
    hg_an.eventually_analyticAt.filter_mono nhdsWithin_le_nhds] with z hz hgz hgan
  have hpow : (z - z₀) ^ n ≠ 0 :=
    pow_ne_zero n (sub_ne_zero.mpr (Set.mem_compl_singleton_iff.mp hz))
  have key : deriv (fun w ↦ (w - z₀) ^ n • g w) z / ((z - z₀) ^ n • g z)
      = logDeriv (fun w ↦ (w - z₀) ^ n * g w) z := by simp only [smul_eq_mul, logDeriv_apply]
  have hpow_log := logDeriv_fun_pow (f := fun w : ℂ ↦ w - z₀) (x := z) (by fun_prop) n
  simp only [Pi.div_apply]
  rw [key, logDeriv_mul z hpow hgz (by fun_prop) hgan.differentiableAt, hpow_log, logDeriv_apply]
  simp [div_eq_mul_inv]
theorem finite_rectangle_inter_setOf_eq_zero {f : ℂ → ℂ} {U : Set ℂ} {z w z₀ : ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hU : IsConnected U) (hsub : Rectangle z w ⊆ U)
    (hz₀U : z₀ ∈ U) (hz₀ : f z₀ ≠ 0) :
    (Rectangle z w ∩ {ρ | f ρ = 0}).Finite := by
  have hcompact : IsCompact (Rectangle z w) := isCompact_uIcc.reProdIm isCompact_uIcc
  refine IsCompact.finite ?_ ?_
  ·
    exact hcompact.of_isClosed_subset ((hf.continuousOn.mono hsub).preimage_isClosed_of_isClosed
      (t := {0}) hcompact.isClosed isClosed_singleton) Set.inter_subset_left
  ·
    rw [Set.inter_comm]
    exact IsDiscrete.mono (isDiscrete_of_codiscreteWithin
      (hf.preimage_zero_mem_codiscreteWithin hz₀ hz₀U hU))
      (Set.inter_subset_inter_right _ hsub)
theorem rectangle_mem_nhds_of_not_mem_rectangleBorder {z w ρ : ℂ}
    (hzw_re : z.re ≤ w.re) (hzw_im : z.im ≤ w.im)
    (hρRect : ρ ∈ Rectangle z w) (hρ : ρ ∉ RectangleBorder z w) :
    Rectangle z w ∈ 𝓝 ρ := by
  rw [rectangle_mem_nhds_iff, Complex.mem_reProdIm, Set.uIoo_of_le hzw_re,
    Set.uIoo_of_le hzw_im, Set.mem_Ioo, Set.mem_Ioo]
  obtain ⟨hr1, hr2, hi1, hi2⟩ := (mem_Rect hzw_re hzw_im ρ).mp hρRect
  have hreIcc : ρ.re ∈ Set.uIcc z.re w.re := by rw [Set.uIcc_of_le hzw_re]; exact ⟨hr1, hr2⟩
  have himIcc : ρ.im ∈ Set.uIcc z.im w.im := by rw [Set.uIcc_of_le hzw_im]; exact ⟨hi1, hi2⟩
  refine ⟨⟨hr1.lt_of_ne ?_, hr2.lt_of_ne ?_⟩, hi1.lt_of_ne ?_, hi2.lt_of_ne ?_⟩
  · exact fun h ↦ hρ (Or.inl (Or.inl (Or.inr (Complex.mem_reProdIm.mpr ⟨h.symm, himIcc⟩))))
  · exact fun h ↦ hρ (Or.inr (Complex.mem_reProdIm.mpr ⟨h, himIcc⟩))
  · exact fun h ↦ hρ (Or.inl (Or.inl (Or.inl (Complex.mem_reProdIm.mpr ⟨hreIcc, h.symm⟩))))
  · exact fun h ↦ hρ (Or.inl (Or.inr (Complex.mem_reProdIm.mpr ⟨hreIcc, h⟩)))
theorem rectangleIntegral_logDeriv_eq_two_pi_I_of_subsingleton {f : ℂ → ℂ} {U : Set ℂ} {z w : ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hsub : Rectangle z w ⊆ U)
    (hzw_re : z.re ≤ w.re) (hzw_im : z.im ≤ w.im)
    (hbd : ∀ ρ ∈ RectangleBorder z w, f ρ ≠ 0)
    (hfin : (Rectangle z w ∩ {ρ | f ρ = 0}).Finite)
    (hss : (Rectangle z w ∩ {ρ | f ρ = 0}).Subsingleton) :
    RectangleIntegral (logDeriv f) z w
      = 2 * (Real.pi : ℂ) * I * ∑ ρ ∈ hfin.toFinset,
          (((meromorphicOrderAt f ρ).untopD 0 : ℤ) : ℂ) := by
  rcases hss.eq_empty_or_singleton with hZ | ⟨ρ, hZ⟩
  ·
    rw [Set.Finite.toFinset_eq_empty.mpr hZ, Finset.sum_empty, mul_zero]
    exact (holomorphicOn_logDeriv hf hsub fun x hx h0 ↦ Set.notMem_empty x
      (hZ ▸ (⟨hx, h0⟩ : x ∈ Rectangle z w ∩ {ρ | f ρ = 0}))).vanishesOnRectangle (subset_refl _)
  ·
    have hρZ : ρ ∈ Rectangle z w ∩ {ρ | f ρ = 0} := hZ ▸ Set.mem_singleton ρ
    have hρnhds : Rectangle z w ∈ 𝓝 ρ :=
      rectangle_mem_nhds_of_not_mem_rectangleBorder hzw_re hzw_im hρZ.1 fun h ↦ hbd ρ h hρZ.2
    have hfne : ∀ x ∈ Rectangle z w \ {ρ}, f x ≠ 0 := fun x hx h0 ↦
      hx.2 (hZ ▸ (⟨hx.1, h0⟩ : x ∈ Rectangle z w ∩ {ρ | f ρ = 0}))
    have hne : ¬ ∀ᶠ x in 𝓝 ρ, f x = 0 := fun hev ↦ by
      have h2 : ∀ᶠ x in 𝓝[≠] ρ, f x ≠ 0 := by
        filter_upwards [mem_nhdsWithin_of_mem_nhds hρnhds, self_mem_nhdsWithin] with x hx hx'
          using hfne x ⟨hx, hx'⟩
      obtain ⟨x, hx0, hxne⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and h2).exists
      exact hxne hx0
    obtain ⟨n, g, -, -, hord, hlogg, heq⟩ :=
      meromorphicOrderAt_eq_residue_logDeriv (hf ρ (hsub hρZ.1)) hne
    have near_p : (logDeriv f - fun s ↦ (n : ℂ) / (s - ρ)) =O[𝓝[≠] ρ] (1 : ℂ → ℂ) :=
      Filter.EventuallyEq.trans_isBigO
        (by filter_upwards [heq] with x hx; simp only [Pi.sub_apply]; rw [hx]; ring)
        ((Filter.Tendsto.isBigO_one ℂ hlogg.continuousAt).mono nhdsWithin_le_nhds)
    have hres : RectangleIntegral' (logDeriv f) z w = (n : ℂ) :=
      ResidueTheoremOnRectangleWithSimplePole' hzw_re hzw_im hρnhds
        (holomorphicOn_logDeriv hf (Set.sdiff_subset.trans hsub) hfne) near_p
    have htf : hfin.toFinset = {ρ} := by ext x; simp [hZ]
    rw [RectangleIntegral', smul_eq_mul] at hres
    field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero, Complex.I_ne_zero] at hres
    rw [htf, Finset.sum_singleton, hord, WithTop.untopD_coe]
    push_cast; linear_combination hres
private theorem exists_mem_Ioo_not_mem_finset {S : Finset ℝ} {r₁ r₂ : ℝ} (h : r₁ ≠ r₂) :
    ∃ a : ℝ, min r₁ r₂ < a ∧ a < max r₁ r₂ ∧ a ∉ S := by
  obtain ⟨a, ha, haS⟩ :=
    ((Set.Ioo_infinite (min_lt_max.mpr h)).sdiff S.finite_toSet).nonempty
  exact ⟨a, ha.1, ha.2, by simpa using haS⟩
private theorem ofReal_add_mul_I_re (x y : ℝ) : ((x : ℂ) + (y : ℂ) * I).re = x := by simp
private theorem ofReal_add_mul_I_im (x y : ℝ) : ((x : ℂ) + (y : ℂ) * I).im = y := by simp
private theorem rectangleBorder_vcut {z w : ℂ} {a : ℝ} (hza : z.re ≤ a) (haw : a ≤ w.re) :
    RectangleBorder z (↑a + ↑w.im * I) ⊆ {ρ : ℂ | ρ.re = a} ∪ RectangleBorder z w ∧
      RectangleBorder (↑a + ↑z.im * I) w ⊆ {ρ : ℂ | ρ.re = a} ∪ RectangleBorder z w := by
  have ha : a ∈ Set.uIcc z.re w.re := Set.mem_uIcc.mpr (Or.inl ⟨hza, haw⟩)
  refine ⟨fun ρ hρ ↦ ?_, fun ρ hρ ↦ ?_⟩ <;>
    have h₁ : ρ.re ∈ Set.uIcc z.re a → ρ.re ∈ Set.uIcc z.re w.re :=
      (Set.uIcc_subset_uIcc Set.left_mem_uIcc ha ·) <;>
    have h₂ : ρ.re ∈ Set.uIcc a w.re → ρ.re ∈ Set.uIcc z.re w.re :=
      (Set.uIcc_subset_uIcc ha Set.right_mem_uIcc ·) <;>
    simp only [RectangleBorder, ofReal_add_mul_I_re, ofReal_add_mul_I_im, Set.mem_union,
      Complex.mem_reProdIm, Set.mem_singleton_iff, Set.mem_ofPred_eq] at hρ ⊢ <;>
    tauto
private theorem rectangleBorder_hcut {z w : ℂ} {b : ℝ} (hzb : z.im ≤ b) (hbw : b ≤ w.im) :
    RectangleBorder z (↑w.re + ↑b * I) ⊆ {ρ : ℂ | ρ.im = b} ∪ RectangleBorder z w ∧
      RectangleBorder (↑z.re + ↑b * I) w ⊆ {ρ : ℂ | ρ.im = b} ∪ RectangleBorder z w := by
  have hb : b ∈ Set.uIcc z.im w.im := Set.mem_uIcc.mpr (Or.inl ⟨hzb, hbw⟩)
  refine ⟨fun ρ hρ ↦ ?_, fun ρ hρ ↦ ?_⟩ <;>
    have h₁ : ρ.im ∈ Set.uIcc z.im b → ρ.im ∈ Set.uIcc z.im w.im :=
      (Set.uIcc_subset_uIcc Set.left_mem_uIcc hb ·) <;>
    have h₂ : ρ.im ∈ Set.uIcc b w.im → ρ.im ∈ Set.uIcc z.im w.im :=
      (Set.uIcc_subset_uIcc hb Set.right_mem_uIcc ·) <;>
    simp only [RectangleBorder, ofReal_add_mul_I_re, ofReal_add_mul_I_im, Set.mem_union,
      Complex.mem_reProdIm, Set.mem_singleton_iff, Set.mem_ofPred_eq] at hρ ⊢ <;>
    tauto
private theorem toFinset_sub_eq_filter {f : ℂ → ℂ} {z w P Q : ℂ}
    (hfin : (Rectangle z w ∩ {ρ | f ρ = 0}).Finite)
    (hfinP : (Rectangle P Q ∩ {ρ | f ρ = 0}).Finite)
    (hPQ : Rectangle P Q ⊆ Rectangle z w) (p : ℂ → Prop) [DecidablePred p]
    (h : ∀ ρ ∈ Rectangle z w, f ρ = 0 → (ρ ∈ Rectangle P Q ↔ p ρ)) :
    hfinP.toFinset = hfin.toFinset.filter p := by
  ext ρ
  simp only [Set.Finite.mem_toFinset, Finset.mem_filter, Set.mem_inter_iff, Set.mem_ofPred_eq]
  exact ⟨fun ⟨hρP, hf0⟩ ↦ ⟨⟨hPQ hρP, hf0⟩, (h ρ (hPQ hρP) hf0).mp hρP⟩,
    fun ⟨⟨hρR, hf0⟩, hp⟩ ↦ ⟨(h ρ hρR hf0).mpr hp, hf0⟩⟩
private theorem rectangleIntegral_logDeriv_subdivide {f : ℂ → ℂ} {U : Set ℂ} {z₀ : ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hU : IsConnected U) (hz₀U : z₀ ∈ U) (hz₀ : f z₀ ≠ 0)
    {N : ℕ} {z w Q₁ P₂ ρ₁ ρ₂ : ℂ} {c : ℂ → ℝ} {a : ℝ}
    (ih : ∀ {z w : ℂ}, Rectangle z w ⊆ U → z.re ≤ w.re → z.im ≤ w.im →
      (∀ ρ ∈ RectangleBorder z w, f ρ ≠ 0) →
      ∀ (hfin : (Rectangle z w ∩ {ρ | f ρ = 0}).Finite), hfin.toFinset.card ≤ N →
        RectangleIntegral (logDeriv f) z w
          = 2 * (Real.pi : ℂ) * I * ∑ ρ ∈ hfin.toFinset,
              (((meromorphicOrderAt f ρ).untopD 0 : ℤ) : ℂ))
    (hsub : Rectangle z w ⊆ U) (hbd : ∀ ρ ∈ RectangleBorder z w, f ρ ≠ 0)
    (hfin : (Rectangle z w ∩ {ρ | f ρ = 0}).Finite)
    (hcard : hfin.toFinset.card ≤ N + 1)
    (hρ₁ : ρ₁ ∈ hfin.toFinset) (hρ₂ : ρ₂ ∈ hfin.toFinset)
    (ha1 : min (c ρ₁) (c ρ₂) < a) (ha2 : a < max (c ρ₁) (c ρ₂))
    (hane : ∀ ρ ∈ hfin.toFinset, c ρ ≠ a)
    (hsubR₁R : Rectangle z Q₁ ⊆ Rectangle z w) (hsubR₂R : Rectangle P₂ w ⊆ Rectangle z w)
    (hre1 : z.re ≤ Q₁.re) (him1 : z.im ≤ Q₁.im) (hre2 : P₂.re ≤ w.re) (him2 : P₂.im ≤ w.im)
    (hborder₁ : RectangleBorder z Q₁ ⊆ {ρ : ℂ | c ρ = a} ∪ RectangleBorder z w)
    (hborder₂ : RectangleBorder P₂ w ⊆ {ρ : ℂ | c ρ = a} ∪ RectangleBorder z w)
    (hmem₁ : ∀ ρ ∈ Rectangle z w, (ρ ∈ Rectangle z Q₁ ↔ c ρ ≤ a))
    (hmem₂ : ∀ ρ ∈ Rectangle z w, (ρ ∈ Rectangle P₂ w ↔ a ≤ c ρ))
    (hsplit : RectangleIntegral (logDeriv f) z w
        = RectangleIntegral (logDeriv f) z Q₁ + RectangleIntegral (logDeriv f) P₂ w) :
    RectangleIntegral (logDeriv f) z w
      = 2 * (Real.pi : ℂ) * I * ∑ ρ ∈ hfin.toFinset,
          (((meromorphicOrderAt f ρ).untopD 0 : ℤ) : ℂ) := by
  have hcut : ∀ ρ ∈ Rectangle z w, c ρ = a → f ρ ≠ 0 := fun ρ hρ ha hf0 ↦
    hane ρ (hfin.mem_toFinset.mpr ⟨hρ, hf0⟩) ha
  have hbd₁ : ∀ ρ ∈ RectangleBorder z Q₁, f ρ ≠ 0 := fun ρ hρ ↦
    (hborder₁ hρ).elim (hcut ρ (hsubR₁R (rectangleBorder_subset_rectangle _ _ hρ))) (hbd ρ)
  have hbd₂ : ∀ ρ ∈ RectangleBorder P₂ w, f ρ ≠ 0 := fun ρ hρ ↦
    (hborder₂ hρ).elim (hcut ρ (hsubR₂R (rectangleBorder_subset_rectangle _ _ hρ))) (hbd ρ)
  have hfin₁ := finite_rectangle_inter_setOf_eq_zero hf hU (hsubR₁R.trans hsub) hz₀U hz₀
  have hfin₂ := finite_rectangle_inter_setOf_eq_zero hf hU (hsubR₂R.trans hsub) hz₀U hz₀
  have hfeq1 : hfin₁.toFinset = hfin.toFinset.filter (fun ρ ↦ c ρ < a) :=
    toFinset_sub_eq_filter hfin hfin₁ hsubR₁R _ fun ρ hρ hf0 ↦
      (hmem₁ ρ hρ).trans (hane ρ (hfin.mem_toFinset.mpr ⟨hρ, hf0⟩)).le_iff_lt
  have hfeq2 : hfin₂.toFinset = hfin.toFinset.filter (fun ρ ↦ ¬ c ρ < a) :=
    toFinset_sub_eq_filter hfin hfin₂ hsubR₂R _ fun ρ hρ _ ↦ (hmem₂ ρ hρ).trans not_lt.symm
  have hpart : (hfin.toFinset.filter (fun ρ ↦ c ρ < a)).card
      + (hfin.toFinset.filter (fun ρ ↦ ¬ c ρ < a)).card = hfin.toFinset.card :=
    Finset.card_filter_add_card_filter_not _
  have hne1 : (hfin.toFinset.filter (fun ρ ↦ c ρ < a)).Nonempty := by
    rcases min_choice (c ρ₁) (c ρ₂) with hm | hm
    · exact ⟨ρ₁, Finset.mem_filter.mpr ⟨hρ₁, hm ▸ ha1⟩⟩
    · exact ⟨ρ₂, Finset.mem_filter.mpr ⟨hρ₂, hm ▸ ha1⟩⟩
  have hne2 : (hfin.toFinset.filter (fun ρ ↦ ¬ c ρ < a)).Nonempty := by
    rcases max_choice (c ρ₁) (c ρ₂) with hm | hm
    · exact ⟨ρ₁, Finset.mem_filter.mpr ⟨hρ₁, not_lt.mpr (hm ▸ ha2).le⟩⟩
    · exact ⟨ρ₂, Finset.mem_filter.mpr ⟨hρ₂, not_lt.mpr (hm ▸ ha2).le⟩⟩
  have hcard1 : hfin₁.toFinset.card ≤ N := by rw [hfeq1]; have := hne2.card_pos; lia
  have hcard2 : hfin₂.toFinset.card ≤ N := by rw [hfeq2]; have := hne1.card_pos; lia
  rw [hsplit, ih (hsubR₁R.trans hsub) hre1 him1 hbd₁ hfin₁ hcard1,
    ih (hsubR₂R.trans hsub) hre2 him2 hbd₂ hfin₂ hcard2,
    hfeq1, hfeq2, ← mul_add, Finset.sum_filter_add_sum_filter_not]
private theorem rectangleIntegral_logDeriv_eq_two_pi_I_sum_aux {f : ℂ → ℂ} {U : Set ℂ} {z₀ : ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hU : IsConnected U) (hz₀U : z₀ ∈ U) (hz₀ : f z₀ ≠ 0) :
    ∀ (N : ℕ) {z w : ℂ}, Rectangle z w ⊆ U → z.re ≤ w.re → z.im ≤ w.im →
      (∀ ρ ∈ RectangleBorder z w, f ρ ≠ 0) →
      ∀ (hfin : (Rectangle z w ∩ {ρ | f ρ = 0}).Finite), hfin.toFinset.card ≤ N →
        RectangleIntegral (logDeriv f) z w
          = 2 * (Real.pi : ℂ) * I * ∑ ρ ∈ hfin.toFinset,
              (((meromorphicOrderAt f ρ).untopD 0 : ℤ) : ℂ) := by
  have base : ∀ {z w : ℂ}, Rectangle z w ⊆ U → z.re ≤ w.re → z.im ≤ w.im →
      (∀ ρ ∈ RectangleBorder z w, f ρ ≠ 0) →
      ∀ (hfin : (Rectangle z w ∩ {ρ | f ρ = 0}).Finite), hfin.toFinset.card ≤ 1 →
        RectangleIntegral (logDeriv f) z w
          = 2 * (Real.pi : ℂ) * I * ∑ ρ ∈ hfin.toFinset,
              (((meromorphicOrderAt f ρ).untopD 0 : ℤ) : ℂ) :=
    fun hsub hre him hbd hfin hcard ↦
      rectangleIntegral_logDeriv_eq_two_pi_I_of_subsingleton hf hsub hre him hbd hfin
        fun a ha b hb ↦ Finset.card_le_one.mp hcard a (hfin.mem_toFinset.mpr ha) b
          (hfin.mem_toFinset.mpr hb)
  intro N
  induction N with
  | zero =>
    intro z w hsub hre him hbd hfin hcard
    exact base hsub hre him hbd hfin (hcard.trans (Nat.zero_le 1))
  | succ N ih =>
    intro z w hsub hre him hbd hfin hcard
    by_cases hc1 : hfin.toFinset.card ≤ 1
    · exact base hsub hre him hbd hfin hc1
    ·
      obtain ⟨ρ₁, ρ₂, hρ₁, hρ₂, hne⟩ := Finset.one_lt_card_iff.mp (not_le.mp hc1)
      obtain ⟨hz1, hw1, hzi1, hwi1⟩ := (mem_Rect hre him ρ₁).mp (hfin.mem_toFinset.mp hρ₁).1
      obtain ⟨hz2, hw2, hzi2, hwi2⟩ := (mem_Rect hre him ρ₂).mp (hfin.mem_toFinset.mp hρ₂).1
      have hbi : RectangleBorderIntegrable (logDeriv f)
          (↑z.re + ↑z.im * I) (↑w.re + ↑w.im * I) := by
        rw [Complex.re_add_im, Complex.re_add_im]
        exact (holomorphicOn_logDeriv hf
          ((rectangleBorder_subset_rectangle z w).trans hsub) hbd).continuousOn
            |>.rectangleBorder_integrable
      rcases ne_or_eq ρ₁.re ρ₂.re with hred | hreq
      ·
        obtain ⟨a, ha1, ha2, haS⟩ :=
          exists_mem_Ioo_not_mem_finset (S := hfin.toFinset.image Complex.re) hred
        have hza : z.re ≤ a := (lt_of_le_of_lt (le_min hz1 hz2) ha1).le
        have haw : a ≤ w.re := (lt_of_lt_of_le ha2 (max_le hw1 hw2)).le
        have hane : ∀ ρ ∈ hfin.toFinset, ρ.re ≠ a := fun ρ hρ h ↦
          haS (Finset.mem_image.mpr ⟨ρ, hρ, h⟩)
        have hre1 : z.re ≤ (↑a + ↑w.im * I : ℂ).re := by simpa using hza
        have him1 : z.im ≤ (↑a + ↑w.im * I : ℂ).im := by simpa using him
        have hre2 : (↑a + ↑z.im * I : ℂ).re ≤ w.re := by simpa using haw
        have him2 : (↑a + ↑z.im * I : ℂ).im ≤ w.im := by simpa using him
        have hsubR₁R : Rectangle z (↑a + ↑w.im * I) ⊆ Rectangle z w :=
          RectSubRect' le_rfl hre1 (by simpa using haw) le_rfl him1 (by simp)
        have hsubR₂R : Rectangle (↑a + ↑z.im * I) w ⊆ Rectangle z w :=
          RectSubRect' (by simpa using hza) hre2 le_rfl (by simp) him2 le_rfl
        have hmem₁ : ∀ ρ ∈ Rectangle z w,
            (ρ ∈ Rectangle z (↑a + ↑w.im * I) ↔ ρ.re ≤ a) := fun ρ hρR ↦ by
          rw [mem_Rect hre him] at hρR
          rw [mem_Rect hre1 him1, ofReal_add_mul_I_re, ofReal_add_mul_I_im]; tauto
        have hmem₂ : ∀ ρ ∈ Rectangle z w,
            (ρ ∈ Rectangle (↑a + ↑z.im * I) w ↔ a ≤ ρ.re) := fun ρ hρR ↦ by
          rw [mem_Rect hre him] at hρR
          rw [mem_Rect hre2 him2, ofReal_add_mul_I_re, ofReal_add_mul_I_im]; tauto
        have hsplit := RectangleIntegralHSplit' (f := logDeriv f) (a := a)
          (Set.mem_uIcc.mpr (Or.inl ⟨hza, haw⟩)) hbi
        simp only [Complex.re_add_im] at hsplit
        exact rectangleIntegral_logDeriv_subdivide (c := Complex.re) hf hU hz₀U hz₀ ih hsub hbd
          hfin hcard hρ₁ hρ₂ ha1 ha2 hane hsubR₁R hsubR₂R hre1 him1 hre2 him2
          (rectangleBorder_vcut hza haw).1 (rectangleBorder_vcut hza haw).2 hmem₁ hmem₂ hsplit
      ·
        obtain ⟨b, hb1, hb2, hbS⟩ := exists_mem_Ioo_not_mem_finset
          (S := hfin.toFinset.image Complex.im) (fun h ↦ hne (Complex.ext hreq h))
        have hzb : z.im ≤ b := (lt_of_le_of_lt (le_min hzi1 hzi2) hb1).le
        have hbw : b ≤ w.im := (lt_of_lt_of_le hb2 (max_le hwi1 hwi2)).le
        have hbne : ∀ ρ ∈ hfin.toFinset, ρ.im ≠ b := fun ρ hρ h ↦
          hbS (Finset.mem_image.mpr ⟨ρ, hρ, h⟩)
        have hre1 : z.re ≤ (↑w.re + ↑b * I : ℂ).re := by simpa using hre
        have him1 : z.im ≤ (↑w.re + ↑b * I : ℂ).im := by simpa using hzb
        have hre2 : (↑z.re + ↑b * I : ℂ).re ≤ w.re := by simpa using hre
        have him2 : (↑z.re + ↑b * I : ℂ).im ≤ w.im := by simpa using hbw
        have hsubR₁R : Rectangle z (↑w.re + ↑b * I) ⊆ Rectangle z w :=
          RectSubRect' le_rfl hre1 (by simp) le_rfl him1 (by simpa using hbw)
        have hsubR₂R : Rectangle (↑z.re + ↑b * I) w ⊆ Rectangle z w :=
          RectSubRect' (by simp) hre2 le_rfl (by simpa using hzb) him2 le_rfl
        have hmem₁ : ∀ ρ ∈ Rectangle z w,
            (ρ ∈ Rectangle z (↑w.re + ↑b * I) ↔ ρ.im ≤ b) := fun ρ hρR ↦ by
          rw [mem_Rect hre him] at hρR
          rw [mem_Rect hre1 him1, ofReal_add_mul_I_re, ofReal_add_mul_I_im]; tauto
        have hmem₂ : ∀ ρ ∈ Rectangle z w,
            (ρ ∈ Rectangle (↑z.re + ↑b * I) w ↔ b ≤ ρ.im) := fun ρ hρR ↦ by
          rw [mem_Rect hre him] at hρR
          rw [mem_Rect hre2 him2, ofReal_add_mul_I_re, ofReal_add_mul_I_im]; tauto
        have hsplit := RectangleIntegralVSplit' (f := logDeriv f) (b := b)
          (Set.mem_uIcc.mpr (Or.inl ⟨hzb, hbw⟩)) hbi
        simp only [Complex.re_add_im] at hsplit
        exact rectangleIntegral_logDeriv_subdivide (c := Complex.im) hf hU hz₀U hz₀ ih hsub hbd
          hfin hcard hρ₁ hρ₂ hb1 hb2 hbne hsubR₁R hsubR₂R hre1 him1 hre2 him2
          (rectangleBorder_hcut hzb hbw).1 (rectangleBorder_hcut hzb hbw).2 hmem₁ hmem₂ hsplit
theorem rectangleIntegral_logDeriv_eq_two_pi_I_sum {f : ℂ → ℂ} {U : Set ℂ} {z w z₀ : ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hU : IsConnected U) (hz₀U : z₀ ∈ U) (hz₀ : f z₀ ≠ 0)
    (hsub : Rectangle z w ⊆ U) (hzw_re : z.re ≤ w.re) (hzw_im : z.im ≤ w.im)
    (hbd : ∀ ρ ∈ RectangleBorder z w, f ρ ≠ 0)
    (hfin : (Rectangle z w ∩ {ρ | f ρ = 0}).Finite) :
    RectangleIntegral (logDeriv f) z w
      = 2 * (Real.pi : ℂ) * I * ∑ ρ ∈ hfin.toFinset,
          (((meromorphicOrderAt f ρ).untopD 0 : ℤ) : ℂ) :=
  rectangleIntegral_logDeriv_eq_two_pi_I_sum_aux hf hU hz₀U hz₀ hfin.toFinset.card hsub hzw_re
    hzw_im hbd hfin le_rfl
theorem re_integral_div_eq_log_norm_sub {a b : ℝ} (hab : a ≤ b) {φ φ' : ℝ → ℂ}
    (hφ : ContinuousOn φ (Set.Icc a b)) (h0 : ∀ u ∈ Set.Icc a b, φ u ≠ 0)
    (hderiv : ∀ u ∈ Set.Ioo a b, HasDerivAt φ (φ' u) u)
    (hint : ContinuousOn (fun u ↦ φ' u / φ u) (Set.Icc a b)) :
    (∫ u in a..b, φ' u / φ u).re = Real.log ‖φ b‖ - Real.log ‖φ a‖ := by
  obtain ⟨g, hg, -⟩ :=
    exists_isContLog hab hφ h0 (Complex.exp_log (h0 a (Set.left_mem_Icc.mpr hab)))
  have hftc := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hab hg.1
    (fun u hu ↦ (hg.hasDerivAt hu (hderiv u hu)).hasDerivWithinAt)
    (hint.intervalIntegrable_of_Icc hab)
  have hre : ∀ u ∈ Set.Icc a b, (g u).re = Real.log ‖φ u‖ := fun u hu ↦ by
    rw [← hg.2 u hu, Complex.norm_exp, Real.log_exp]
  rw [hftc, Complex.sub_re, hre b (Set.right_mem_Icc.mpr hab), hre a (Set.left_mem_Icc.mpr hab)]
theorem argVariation_lineSeg_eq_im_integral {f : ℂ → ℂ} {P Q : ℂ}
    (hf : ∀ u ∈ Set.Icc (0 : ℝ) 1, AnalyticAt ℂ f (lineSeg P Q u))
    (hne : ∀ u ∈ Set.Icc (0 : ℝ) 1, f (lineSeg P Q u) ≠ 0) :
    argVariation 0 1 (fun u ↦ f (lineSeg P Q u))
        = (∫ u in (0 : ℝ)..1, logDeriv f (lineSeg P Q u) * (Q - P)).im ∧
      (∫ u in (0 : ℝ)..1, logDeriv f (lineSeg P Q u) * (Q - P)).re
        = Real.log ‖f Q‖ - Real.log ‖f P‖ := by
  have hγderiv : ∀ u : ℝ, HasDerivAt (lineSeg P Q) (Q - P) u := fun u ↦ by
    have h1 : HasDerivAt (fun u : ℝ ↦ (u : ℂ)) 1 u := Complex.ofRealCLM.hasDerivAt
    have h := (h1.mul_const (Q - P)).const_add P
    rwa [one_mul] at h
  have hφcont : ContinuousOn (fun u ↦ f (lineSeg P Q u)) (Set.Icc 0 1) := fun u hu ↦
    (hf u hu).continuousAt.comp_continuousWithinAt (continuous_lineSeg P Q).continuousWithinAt
  have hderivφ : ∀ u ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivAt (fun u ↦ f (lineSeg P Q u)) (deriv f (lineSeg P Q u) * (Q - P)) u := fun u hu ↦
    ((hf u (Set.Ioo_subset_Icc_self hu)).differentiableAt.hasDerivAt).comp u (hγderiv u)
  have hint : ContinuousOn
      (fun u ↦ deriv f (lineSeg P Q u) * (Q - P) / f (lineSeg P Q u)) (Set.Icc 0 1) := fun u hu ↦
    (((hf u hu).deriv.continuousAt.comp_continuousWithinAt
        (continuous_lineSeg P Q).continuousWithinAt).mul continuousWithinAt_const).div
      (hφcont u hu) (hne u hu)
  have heqint : (fun u ↦ deriv f (lineSeg P Q u) * (Q - P) / f (lineSeg P Q u))
      = fun u ↦ logDeriv f (lineSeg P Q u) * (Q - P) := by
    funext u; simp only [logDeriv_apply, mul_div_right_comm]
  refine ⟨by rw [argVariation_eq_im_integral zero_le_one hφcont hne hderivφ hint, heqint], ?_⟩
  have h := re_integral_div_eq_log_norm_sub zero_le_one hφcont hne hderivφ hint
  rw [heqint] at h
  rw [h, lineSeg_one, lineSeg_zero]
noncomputable def rectangleArgVariation (f : ℂ → ℂ) (z w : ℂ) : ℝ :=
  argVariation 0 1 (fun u ↦ f (lineSeg (↑z.re + ↑z.im * I) (↑w.re + ↑z.im * I) u)) +
  argVariation 0 1 (fun u ↦ f (lineSeg (↑w.re + ↑z.im * I) (↑w.re + ↑w.im * I) u)) +
  argVariation 0 1 (fun u ↦ f (lineSeg (↑w.re + ↑w.im * I) (↑z.re + ↑w.im * I) u)) +
  argVariation 0 1 (fun u ↦ f (lineSeg (↑z.re + ↑w.im * I) (↑z.re + ↑z.im * I) u))
private theorem integral_affine_param (F : ℝ → ℂ) (t₁ t₂ : ℝ) :
    ∫ t in t₁..t₂, F t
      = ∫ u in (0 : ℝ)..1, ((t₂ - t₁ : ℝ) : ℂ) * F (t₁ + u * (t₂ - t₁)) := by
  rcases eq_or_ne t₁ t₂ with h | h
  · subst h; simp
  · have hc : t₂ - t₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
    have key : ∫ u in (0 : ℝ)..1, F (t₁ + u * (t₂ - t₁))
        = (t₂ - t₁)⁻¹ • ∫ t in t₁..t₂, F t := by
      have hk := intervalIntegral.integral_comp_mul_add (a := 0) (b := 1) F hc t₁
      simp only [mul_zero, zero_add, mul_one, sub_add_cancel] at hk
      exact (intervalIntegral.integral_congr (fun u _ ↦ by congr 1; ring)).trans hk
    rw [intervalIntegral.integral_const_mul, key, Complex.real_smul, Complex.ofReal_inv,
      ← mul_assoc, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hc), one_mul]
private theorem hIntegral_eq_lineSeg (g : ℂ → ℂ) (x₁ x₂ y : ℝ) :
    HIntegral g x₁ x₂ y
      = ∫ u in (0 : ℝ)..1, g (lineSeg (↑x₁ + ↑y * I) (↑x₂ + ↑y * I) u) *
          ((↑x₂ + ↑y * I) - (↑x₁ + ↑y * I)) := by
  rw [HIntegral, integral_affine_param (fun t ↦ g (↑t + ↑y * I)) x₁ x₂]
  refine intervalIntegral.integral_congr (fun u _ ↦ ?_)
  have hseg : lineSeg (↑x₁ + ↑y * I) (↑x₂ + ↑y * I) u = ↑(x₁ + u * (x₂ - x₁)) + ↑y * I := by
    simp only [lineSeg]; push_cast; ring
  rw [hseg]; push_cast; ring
private theorem vIntegral_eq_lineSeg (g : ℂ → ℂ) (x y₁ y₂ : ℝ) :
    VIntegral g x y₁ y₂
      = ∫ u in (0 : ℝ)..1, g (lineSeg (↑x + ↑y₁ * I) (↑x + ↑y₂ * I) u) *
          ((↑x + ↑y₂ * I) - (↑x + ↑y₁ * I)) := by
  rw [VIntegral, integral_affine_param (fun t ↦ g (↑x + ↑t * I)) y₁ y₂,
    ← intervalIntegral.integral_smul]
  refine intervalIntegral.integral_congr (fun u _ ↦ ?_)
  have hseg : lineSeg (↑x + ↑y₁ * I) (↑x + ↑y₂ * I) u = ↑x + ↑(y₁ + u * (y₂ - y₁)) * I := by
    simp only [lineSeg]; push_cast; ring
  rw [hseg, smul_eq_mul]; push_cast; ring
theorem add_mul_sub_mem_uIcc {a b u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    a + u * (b - a) ∈ Set.uIcc a b := by
  rw [← segment_eq_uIcc, segment_eq_image' ℝ]
  exact ⟨u, hu, by simp [smul_eq_mul]⟩
private theorem lineSeg_mem_horizontal {a b c : ℝ} {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    lineSeg (↑a + ↑c * I) (↑b + ↑c * I) u ∈ Set.uIcc a b ×ℂ ({c} : Set ℝ) := by
  rw [Complex.mem_reProdIm, lineSeg_re, lineSeg_im]
  exact ⟨by simpa using add_mul_sub_mem_uIcc (a := a) (b := b) hu, by simp⟩
private theorem lineSeg_mem_vertical {a c d : ℝ} {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    lineSeg (↑a + ↑c * I) (↑a + ↑d * I) u ∈ ({a} : Set ℝ) ×ℂ Set.uIcc c d := by
  rw [Complex.mem_reProdIm, lineSeg_re, lineSeg_im]
  exact ⟨by simp, by simpa using add_mul_sub_mem_uIcc (a := c) (b := d) hu⟩
theorem rectangleIntegral_logDeriv_eq_I_mul_rectangleArgVariation {f : ℂ → ℂ} {U : Set ℂ}
    {z w : ℂ} (hf : AnalyticOnNhd ℂ f U) (hsub : Rectangle z w ⊆ U)
    (hbd : ∀ ρ ∈ RectangleBorder z w, f ρ ≠ 0) :
    RectangleIntegral (logDeriv f) z w = I * (rectangleArgVariation f z w : ℂ) := by
  set I0 := ∫ u in (0 : ℝ)..1, logDeriv f (lineSeg (↑z.re + ↑z.im * I) (↑w.re + ↑z.im * I) u) *
    ((↑w.re + ↑z.im * I) - (↑z.re + ↑z.im * I)) with hI0
  set I1 := ∫ u in (0 : ℝ)..1, logDeriv f (lineSeg (↑w.re + ↑z.im * I) (↑w.re + ↑w.im * I) u) *
    ((↑w.re + ↑w.im * I) - (↑w.re + ↑z.im * I)) with hI1
  set I2 := ∫ u in (0 : ℝ)..1, logDeriv f (lineSeg (↑w.re + ↑w.im * I) (↑z.re + ↑w.im * I) u) *
    ((↑z.re + ↑w.im * I) - (↑w.re + ↑w.im * I)) with hI2
  set I3 := ∫ u in (0 : ℝ)..1, logDeriv f (lineSeg (↑z.re + ↑w.im * I) (↑z.re + ↑z.im * I) u) *
    ((↑z.re + ↑z.im * I) - (↑z.re + ↑w.im * I)) with hI3
  have edge : ∀ {P Q : ℂ},
      (∀ u ∈ Set.Icc (0 : ℝ) 1, lineSeg P Q u ∈ RectangleBorder z w) →
      argVariation 0 1 (fun u ↦ f (lineSeg P Q u))
          = (∫ u in (0 : ℝ)..1, logDeriv f (lineSeg P Q u) * (Q - P)).im ∧
        (∫ u in (0 : ℝ)..1, logDeriv f (lineSeg P Q u) * (Q - P)).re
          = Real.log ‖f Q‖ - Real.log ‖f P‖ := fun {P Q} hmem ↦
    argVariation_lineSeg_eq_im_integral
      (fun u hu ↦ hf _ (hsub (rectangleBorder_subset_rectangle z w (hmem u hu))))
      (fun u hu ↦ hbd _ (hmem u hu))
  have e0 := edge fun u hu ↦ Or.inl (Or.inl (Or.inl (lineSeg_mem_horizontal hu)))
  have e1 := edge fun u hu ↦ Or.inr (lineSeg_mem_vertical hu)
  have e2 := edge fun u hu ↦
    Or.inl (Or.inr (by rw [Set.uIcc_comm z.re w.re]; exact lineSeg_mem_horizontal hu))
  have e3 := edge fun u hu ↦
    Or.inl (Or.inl (Or.inr (by rw [Set.uIcc_comm z.im w.im]; exact lineSeg_mem_vertical hu)))
  have hsum : RectangleIntegral (logDeriv f) z w = I0 + I1 + I2 + I3 := by
    have h0 : HIntegral (logDeriv f) z.re w.re z.im = I0 := hIntegral_eq_lineSeg _ _ _ _
    have h1 : VIntegral (logDeriv f) w.re z.im w.im = I1 := vIntegral_eq_lineSeg _ _ _ _
    have h2 : HIntegral (logDeriv f) z.re w.re w.im = -I2 := by
      rw [HIntegral_symm, hIntegral_eq_lineSeg]
    have h3 : VIntegral (logDeriv f) z.re z.im w.im = -I3 := by
      rw [VIntegral_symm, vIntegral_eq_lineSeg]
    rw [RectangleIntegral, h0, h1, h2, h3]; ring
  have hre : (I0 + I1 + I2 + I3).re = 0 := by
    rw [hI0, hI1, hI2, hI3]
    simp only [Complex.add_re, e0.2, e1.2, e2.2, e3.2]; ring
  have him : (I0 + I1 + I2 + I3).im = rectangleArgVariation f z w := by
    rw [hI0, hI1, hI2, hI3, rectangleArgVariation, e0.1, e1.1, e2.1, e3.1]
    simp only [Complex.add_im]
  exact hsum.trans (Complex.ext (by rw [hre]; simp) (by rw [him]; simp))
theorem rectangle_zero_count_eq_argVariation {f : ℂ → ℂ} {U : Set ℂ} {z w z₀ : ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hU : IsConnected U) (hz₀U : z₀ ∈ U) (hz₀ : f z₀ ≠ 0)
    (hsub : Rectangle z w ⊆ U) (hzw_re : z.re ≤ w.re) (hzw_im : z.im ≤ w.im)
    (hbd : ∀ ρ ∈ RectangleBorder z w, f ρ ≠ 0)
    (hfin : (Rectangle z w ∩ {ρ | f ρ = 0}).Finite) :
    ∑ ρ ∈ hfin.toFinset, (((meromorphicOrderAt f ρ).untopD 0 : ℤ) : ℝ)
      = 1 / (2 * Real.pi) * rectangleArgVariation f z w := by
  have h2 := rectangleIntegral_logDeriv_eq_I_mul_rectangleArgVariation hf hsub hbd
  rw [rectangleIntegral_logDeriv_eq_two_pi_I_sum hf hU hz₀U hz₀ hsub hzw_re hzw_im hbd hfin,
    show (∑ ρ ∈ hfin.toFinset, (((meromorphicOrderAt f ρ).untopD 0 : ℤ) : ℂ))
      = ((∑ ρ ∈ hfin.toFinset, (((meromorphicOrderAt f ρ).untopD 0 : ℤ) : ℝ) : ℝ) : ℂ) by
      push_cast; rfl] at h2
  have h3 : (I : ℂ) * (2 * (Real.pi : ℂ) *
      ((∑ ρ ∈ hfin.toFinset, (((meromorphicOrderAt f ρ).untopD 0 : ℤ) : ℝ) : ℝ) : ℂ))
      = I * (rectangleArgVariation f z w : ℂ) := by rw [← h2]; ring
  have h5 : 2 * Real.pi * (∑ ρ ∈ hfin.toFinset, (((meromorphicOrderAt f ρ).untopD 0 : ℤ) : ℝ))
      = rectangleArgVariation f z w := by
    exact_mod_cast mul_left_cancel₀ Complex.I_ne_zero h3
  rw [one_div, inv_mul_eq_div, eq_div_iff (by positivity : (2 * Real.pi) ≠ 0)]
  linear_combination h5
theorem rectangleArgVariation_eq_zero_of_analyticOnNhd {f : ℂ → ℂ} {U : Set ℂ} {z w : ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hne : ∀ x ∈ U, f x ≠ 0) (hsub : Rectangle z w ⊆ U) :
    rectangleArgVariation f z w = 0 := by
  have heq := rectangleIntegral_logDeriv_eq_I_mul_rectangleArgVariation hf hsub
    fun ρ hρ ↦ hne ρ (hsub (rectangleBorder_subset_rectangle z w hρ))
  rw [HolomorphicOn.vanishesOnRectangle (holomorphicOn_logDeriv hf (subset_refl U) hne) hsub] at heq
  exact_mod_cast (mul_eq_zero.mp heq.symm).resolve_left Complex.I_ne_zero
end
end CountPort31
section CountPort32
section
open Complex Real
private theorem lineSeg_div (z₀ z₁ c : ℂ) (u : ℝ) :
    lineSeg z₀ z₁ u / c = lineSeg (z₀ / c) (z₁ / c) u := by
  simp only [lineSeg]; ring
private theorem lineSeg_one_sub (z₀ z₁ : ℂ) (u : ℝ) :
    lineSeg z₀ z₁ (1 - u) = lineSeg z₁ z₀ u := by
  simp only [lineSeg]; push_cast; ring
private theorem argVariation_cpow_pi_seg (z₀ z₁ : ℂ) :
    argVariation 0 1 (fun u ↦ (↑π : ℂ) ^ (-(lineSeg z₀ z₁ u) / 2))
      = Real.log π * (-z₁.im / 2) - Real.log π * (-z₀.im / 2) := by
  have hπ : (↑π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hlog : IsContLog 0 1 (fun u ↦ (↑π : ℂ) ^ (-(lineSeg z₀ z₁ u) / 2))
      (fun u ↦ (↑(Real.log π) : ℂ) * (-(lineSeg z₀ z₁ u) / 2)) :=
    ⟨(continuous_const.mul ((continuous_lineSeg z₀ z₁).neg.div_const 2)).continuousOn,
      fun u _ ↦ by
        simp only [Complex.cpow_def_of_ne_zero hπ, Complex.ofReal_log Real.pi_pos.le]⟩
  rw [argVariation_eq_of_isContLog zero_le_one hlog]
  simp only [lineSeg_zero, lineSeg_one, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re,
    Complex.neg_im, Complex.div_ofNat_im, Complex.neg_re, Complex.div_ofNat_re]
  ring
private theorem argVariationContourL_cpow_pi {T : ℝ} :
    argVariationContourL (fun s ↦ (↑π : ℂ) ^ (-s / 2)) T = -(T / 2) * Real.log π := by
  simp only [argVariationContourL]
  rw [argVariation_cpow_pi_seg 2 (2 + I * ↑T),
    argVariation_cpow_pi_seg (2 + I * ↑T) (1 / 2 + I * ↑T)]
  simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.im_ofNat, Complex.one_im, Complex.div_ofNat_im]
  ring
private theorem continuousOn_Gamma_comp {φ : ℝ → ℂ} (hφ : Continuous φ)
    (hre : ∀ u ∈ Set.Icc (0 : ℝ) 1, 0 < (φ u).re) :
    ContinuousOn (fun u ↦ Complex.Gamma (φ u)) (Set.Icc 0 1) := fun u hu ↦
  (Complex.analyticOnNhd_Gamma_re_pos _ (hre u hu)).continuousAt.comp_continuousWithinAt
    hφ.continuousWithinAt
private theorem rectangle_subset_re_pos {T : ℝ} :
    Rectangle (1 / 4 : ℂ) (1 + I * ↑(T / 2)) ⊆ {z : ℂ | 0 < z.re} := fun p hp ↦ by
  rw [Rectangle, Complex.mem_reProdIm] at hp
  rw [show ((1 : ℂ) / 4).re = 1 / 4 by simp, show ((1 : ℂ) + I * ↑(T / 2)).re = 1 by simp,
    Set.uIcc_of_le (by norm_num)] at hp
  exact lt_of_lt_of_le (by norm_num) hp.1.1
private theorem rectangleArgVariation_Gamma {T : ℝ} :
    rectangleArgVariation Complex.Gamma (1 / 4 : ℂ) (1 + I * ↑(T / 2))
    = argVariation 0 1 (fun u ↦ Complex.Gamma (lineSeg (1 / 4) 1 u))
    + argVariation 0 1 (fun u ↦ Complex.Gamma (lineSeg 1 (1 + I * ↑(T / 2)) u))
    + argVariation 0 1
        (fun u ↦ Complex.Gamma (lineSeg (1 + I * ↑(T / 2)) (1 / 4 + I * ↑(T / 2)) u))
    + argVariation 0 1 (fun u ↦ Complex.Gamma (lineSeg (1 / 4 + I * ↑(T / 2)) (1 / 4) u)) := by
  have hbr : (↑((1 + I * ↑(T / 2) : ℂ)).re + ↑(1 / 4 : ℂ).im * I : ℂ) = 1 := by
    apply Complex.ext <;> simp
  have htl : (↑(1 / 4 : ℂ).re + ↑((1 + I * ↑(T / 2) : ℂ)).im * I : ℂ)
      = 1 / 4 + I * ↑(T / 2) := by
    apply Complex.ext <;> simp
  rw [rectangleArgVariation, Complex.re_add_im, Complex.re_add_im, hbr, htl]
private theorem argVariation_Gamma_bottom :
    argVariation 0 1 (fun u ↦ Complex.Gamma (lineSeg (1 / 4 : ℂ) 1 u)) = 0 := by
  have key : ∀ u : ℝ, Complex.Gamma (lineSeg (1 / 4 : ℂ) 1 u)
      = ↑(Real.Gamma (1 / 4 + u * (3 / 4))) := fun u ↦ by
    rw [show lineSeg (1 / 4 : ℂ) 1 u = ↑((1 / 4 + u * (3 / 4) : ℝ)) by
      simp only [lineSeg]; push_cast; ring, Complex.Gamma_ofReal]
  have hpos : ∀ u ∈ Set.Icc (0 : ℝ) 1, (0 : ℝ) < 1 / 4 + u * (3 / 4) := fun u hu ↦ by
    nlinarith [hu.1]
  rw [argVariation_eq_arg_sub_arg zero_le_one
      (continuousOn_Gamma_comp (continuous_lineSeg _ _) fun u hu ↦ by
        rw [lineSeg_re, Complex.one_re, Complex.div_ofNat_re, Complex.one_re]
        nlinarith [hu.1])
      (fun u hu ↦ by
        rw [key u, Complex.mem_slitPlane_iff]
        exact Or.inl (by simpa using Real.Gamma_pos_of_pos (hpos u hu))),
    key, key, Complex.arg_ofReal_of_nonneg (Real.Gamma_pos_of_pos (by norm_num)).le,
    Complex.arg_ofReal_of_nonneg (Real.Gamma_pos_of_pos (by norm_num)).le]
  ring
private theorem lineSeg_vseg_re {T : ℝ} (u : ℝ) :
    (lineSeg (1 / 4 : ℂ) (1 / 4 + I * ↑(T / 2)) u).re = 1 / 4 := by
  rw [lineSeg_re]; simp
private theorem continuousOn_Gamma_vseg {T : ℝ} :
    ContinuousOn (fun u ↦ Complex.Gamma (lineSeg (1 / 4 : ℂ) (1 / 4 + I * ↑(T / 2)) u))
      (Set.Icc 0 1) :=
  continuousOn_Gamma_comp (continuous_lineSeg _ _) fun u _ ↦ by
    rw [lineSeg_vseg_re]; norm_num
private theorem Gamma_vseg_ne_zero {T : ℝ} :
    ∀ u ∈ Set.Icc (0 : ℝ) 1,
      Complex.Gamma (lineSeg (1 / 4 : ℂ) (1 / 4 + I * ↑(T / 2)) u) ≠ 0 :=
  fun u _ ↦ Gamma_ne_zero_of_re_pos (by rw [lineSeg_vseg_re]; norm_num)
private theorem argVariation_Gamma_left {T : ℝ} :
    argVariation 0 1 (fun u ↦ Complex.Gamma (lineSeg (1 / 4 + I * ↑(T / 2)) (1 / 4 : ℂ) u))
      = -argVariation 0 1
          (fun u ↦ Complex.Gamma (lineSeg (1 / 4 : ℂ) (1 / 4 + I * ↑(T / 2)) u)) := by
  rw [← argVariation_reverse zero_le_one continuousOn_Gamma_vseg Gamma_vseg_ne_zero]
  refine congrArg _ (funext fun u ↦ ?_)
  rw [show (0 : ℝ) + 1 - u = 1 - u by ring, lineSeg_one_sub]
private theorem argVariation_Gamma_vseg_reparam {T : ℝ} (hT : 0 < T) :
    argVariation 0 1 (fun u ↦ Complex.Gamma (lineSeg (1 / 4 : ℂ) (1 / 4 + I * ↑(T / 2)) u))
      = argVariation 0 T (fun u ↦ Complex.Gamma (1 / 4 + I * (↑u / 2))) := by
  have hTc : (↑T : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
  rw [← argVariation_comp zero_le_one hT.le ((continuous_id.div_const T).continuousOn)
    (fun v hv ↦ ⟨div_nonneg hv.1 hT.le, (div_le_one hT).mpr hv.2⟩) (by simp)
    (by simp [hT.ne']) continuousOn_Gamma_vseg Gamma_vseg_ne_zero]
  refine congrArg _ (funext fun v ↦ congrArg Complex.Gamma ?_)
  simp only [lineSeg, id_eq]
  push_cast
  field_simp
  ring
private theorem argVariationContourL_Gamma_half {T : ℝ} (hT : 0 < T) :
    argVariationContourL (fun s ↦ Complex.Gamma (s / 2)) T
      = argVariation 0 T (fun u ↦ Complex.Gamma (1 / 4 + I * (↑u / 2))) := by
  have hrect : rectangleArgVariation Complex.Gamma (1 / 4 : ℂ) (1 + I * ↑(T / 2)) = 0 :=
    rectangleArgVariation_eq_zero_of_analyticOnNhd Complex.analyticOnNhd_Gamma_re_pos
      (fun _ hx ↦ Gamma_ne_zero_of_re_pos hx) rectangle_subset_re_pos
  rw [rectangleArgVariation_Gamma, argVariation_Gamma_bottom, argVariation_Gamma_left,
    argVariation_Gamma_vseg_reparam hT] at hrect
  have hseg1 : (fun u ↦ Complex.Gamma (lineSeg 2 (2 + I * ↑T) u / 2))
      = (fun u ↦ Complex.Gamma (lineSeg 1 (1 + I * ↑(T / 2)) u)) := by
    funext u; rw [lineSeg_div]; congr 2 <;> push_cast <;> ring
  have hseg2 : (fun u ↦ Complex.Gamma (lineSeg (2 + I * ↑T) (1 / 2 + I * ↑T) u / 2))
      = (fun u ↦ Complex.Gamma (lineSeg (1 + I * ↑(T / 2)) (1 / 4 + I * ↑(T / 2)) u)) := by
    funext u; rw [lineSeg_div]; congr 2 <;> push_cast <;> ring
  simp only [argVariationContourL]
  rw [hseg1, hseg2]
  linarith [hrect]
private theorem argVariation_Gammaℝ_seg (z₀ z₁ : ℂ) (h0 : 0 < z₀.re) (h1 : 0 < z₁.re) :
    argVariation 0 1 (fun u ↦ Complex.Gammaℝ (lineSeg z₀ z₁ u))
      = argVariation 0 1 (fun u ↦ (↑π : ℂ) ^ (-(lineSeg z₀ z₁ u) / 2))
        + argVariation 0 1 (fun u ↦ Complex.Gamma (lineSeg z₀ z₁ u / 2)) := by
  have hπ : (↑π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hre : ∀ u ∈ Set.Icc (0 : ℝ) 1, 0 < (lineSeg z₀ z₁ u / 2).re := fun u hu ↦ by
    rw [Complex.div_ofNat_re, lineSeg_re]
    rcases le_total z₀.re z₁.re with h | h
    · nlinarith [hu.1]
    · nlinarith [hu.2]
  have hfeq : (fun u ↦ Complex.Gammaℝ (lineSeg z₀ z₁ u))
      = (fun u ↦ (↑π : ℂ) ^ (-(lineSeg z₀ z₁ u) / 2))
        * (fun u ↦ Complex.Gamma (lineSeg z₀ z₁ u / 2)) :=
    funext fun u ↦ Complex.Gammaℝ_def _
  conv_lhs => rw [hfeq]
  exact argVariation_mul zero_le_one
    (((continuous_lineSeg z₀ z₁).neg.div_const 2).const_cpow (Or.inl hπ)).continuousOn
    (fun u _ ↦ by rw [Complex.cpow_def_of_ne_zero hπ]; exact Complex.exp_ne_zero _)
    (continuousOn_Gamma_comp ((continuous_lineSeg z₀ z₁).div_const 2) hre)
    (fun u hu ↦ Gamma_ne_zero_of_re_pos (hre u hu))
theorem argVariation_GammaPi_L {T : ℝ} (hT : 0 < T) :
    argVariationContourL Complex.Gammaℝ T = riemannSiegelTheta T := by
  have hpi := argVariationContourL_cpow_pi (T := T)
  have hga := argVariationContourL_Gamma_half hT
  simp only [argVariationContourL] at hpi hga ⊢
  rw [argVariation_Gammaℝ_seg 2 (2 + I * ↑T) (by norm_num) (by simp),
    argVariation_Gammaℝ_seg (2 + I * ↑T) (1 / 2 + I * ↑T) (by simp) (by norm_num),
    riemannSiegelTheta]
  linarith [hpi, hga]
end
end CountPort32
section CountPort33
section
open MeasureTheory Filter Topology
open scoped Nat
namespace Complex
theorem tendsto_natCast_cpow_nhds_zero {c : ℂ} (hc : c.re < 0) :
    Tendsto (fun R : ℕ ↦ (R : ℂ) ^ c) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine ((tendsto_rpow_neg_atTop (y := -c.re) (by linarith)).comp
    tendsto_natCast_atTop_atTop).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with R hR
  rw [Function.comp_apply, neg_neg]
  exact (Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast hR) c).symm
theorem integrableOn_Ioi_bernoulliFun_fract_mul_cpow (p N : ℕ) (hN : 1 ≤ N) {w : ℂ}
    (hw : w.re < -1) :
    IntegrableOn (fun x : ℝ ↦ (bernoulliFun p (Int.fract x) : ℂ) * (x : ℂ) ^ w)
      (Set.Ioi (N : ℝ)) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  exact Complex.integrableOn_Ioi_bernoulliFun_fract_mul_of_norm_le p (h := fun x : ℝ ↦ x ^ w.re)
    (integrableOn_Ioi_rpow_of_lt hw hN0)
    (Complex.aestronglyMeasurable_ofReal_cpow_Ioi (Nat.cast_nonneg N) w) fun x hx ↦
      le_of_eq (Complex.norm_cpow_eq_rpow_re_of_pos
        (lt_of_lt_of_le hN0 (Set.mem_Ioi.mp hx).le) w)
noncomputable def eulerMaclaurinRemainderIoi (p : ℕ) (f : ℝ → ℂ) (a : ℝ) : ℂ :=
  (-1 : ℂ) ^ (p + 1) / (p ! : ℂ)
    * ∫ x in Set.Ioi a, (bernoulliFun p (Int.fract x) : ℂ) * iteratedDeriv p f x
theorem integrableOn_Ioi_bernoulliFun_fract_iteratedDeriv_cpow
    (s : ℂ) (p N : ℕ) (hN : 1 ≤ N) (hsp : 1 < s.re + p) :
    IntegrableOn (fun x : ℝ ↦ (bernoulliFun p (Int.fract x) : ℂ) *
        iteratedDeriv p (fun y : ℝ ↦ (y : ℂ) ^ (-s)) x) (Set.Ioi (N : ℝ)) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hw : (-s - (p : ℂ)).re < -1 := by
    simp only [Complex.sub_re, Complex.neg_re, Complex.natCast_re]; linarith
  have h : IntegrableOn (fun x : ℝ ↦ (-1 : ℂ) ^ p * (ascPochhammer ℂ p).eval s *
      ((bernoulliFun p (Int.fract x) : ℂ) * (x : ℂ) ^ (-s - (p : ℂ)))) (Set.Ioi (N : ℝ)) :=
    (integrableOn_Ioi_bernoulliFun_fract_mul_cpow p N hN hw).const_mul _
  refine h.congr_fun (fun x hx ↦ ?_) measurableSet_Ioi
  rw [Complex.iteratedDeriv_cpow_ofReal_neg s p (lt_of_lt_of_le hN0 (Set.mem_Ioi.mp hx).le)]
  ring
end Complex
theorem riemannZeta_eq_of_one_lt_re (s : ℂ) (hs : 1 < s.re) (M N : ℕ) (hN : 1 ≤ N) :
    riemannZeta s
      = (∑ n ∈ Finset.Ico 1 N, (n : ℂ) ^ (-s))
        + (N : ℂ) ^ (1 - s) / (s - 1) + (N : ℂ) ^ (-s) / 2
        + (∑ k ∈ Finset.Icc 1 M,
            ((bernoulli (2 * k) : ℝ) / ((2 * k)! : ℝ) : ℂ)
              * (ascPochhammer ℂ (2 * k - 1)).eval s
              * (N : ℂ) ^ (-s - ((2 * k - 1 : ℕ) : ℂ)))
        + Complex.eulerMaclaurinRemainderIoi (2 * M + 1) (fun y : ℝ ↦ (y : ℂ) ^ (-s)) (N : ℝ) := by
  have hsne1 : s ≠ 1 := by rintro rfl; norm_num at hs
  have hs0 : -s ≠ 0 := neg_ne_zero.mpr (by rintro rfl; norm_num at hs)
  have hsum : Summable (fun n : ℕ ↦ (n : ℂ) ^ (-s)) := by
    simpa only [one_div, ← Complex.cpow_neg] using
      (Complex.summable_one_div_nat_cpow (p := s)).mpr hs
  have hzeta : ∑' (n : ℕ), (n : ℂ) ^ (-s) = riemannZeta s := by
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs, hsum.tsum_eq_zero_add,
      Nat.cast_zero, Complex.zero_cpow hs0, zero_add]
    exact tsum_congr fun n ↦ by rw [one_div, ← Complex.cpow_neg]; push_cast; ring_nf
  have hLHS : Tendsto (fun R : ℕ ↦ ∑ n ∈ Finset.Icc N R, (n : ℂ) ^ (-s)) atTop
      (𝓝 ((∑' (n : ℕ), (n : ℂ) ^ (-s)) - ∑ n ∈ Finset.range N, (n : ℂ) ^ (-s))) := by
    have htsum : Tendsto (fun R : ℕ ↦ ∑ i ∈ Finset.range (R + 1), (i : ℂ) ^ (-s)) atTop
        (𝓝 (∑' (n : ℕ), (n : ℂ) ^ (-s))) :=
      hsum.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
    apply (htsum.sub_const _).congr'
    filter_upwards [eventually_ge_atTop N] with R hR
    rw [show Finset.Icc N R = Finset.Ico N (R + 1) from by
          ext x; rw [Finset.mem_Icc, Finset.mem_Ico]; lia,
      Finset.sum_Ico_eq_sub _ (by lia : N ≤ R + 1)]
  have hsp : 1 < s.re + ((2 * M + 1 : ℕ) : ℝ) := by
    push_cast; have : (0 : ℝ) ≤ M := Nat.cast_nonneg M; linarith
  have hint : IntegrableOn (fun x : ℝ ↦ (bernoulliFun (2 * M + 1) (Int.fract x) : ℂ) *
      iteratedDeriv (2 * M + 1) (fun y : ℝ ↦ (y : ℂ) ^ (-s)) x) (Set.Ioi (N : ℝ)) :=
    Complex.integrableOn_Ioi_bernoulliFun_fract_iteratedDeriv_cpow s (2 * M + 1) N hN hsp
  have hrem : Tendsto (fun R : ℕ ↦ eulerMaclaurinRemainder (2 * M + 1)
        (fun y : ℝ ↦ (y : ℂ) ^ (-s)) (N : ℝ) (R : ℝ)) atTop
      (𝓝 (Complex.eulerMaclaurinRemainderIoi (2 * M + 1)
        (fun y : ℝ ↦ (y : ℂ) ^ (-s)) (N : ℝ))) := by
    simp only [Complex.eulerMaclaurinRemainder_eq, Complex.eulerMaclaurinRemainderIoi]
    exact (intervalIntegral_tendsto_integral_Ioi _ hint tendsto_natCast_atTop_atTop).const_mul _
  have h1s : (1 - s).re < 0 := by rw [Complex.sub_re, Complex.one_re]; linarith
  have hns : (-s).re < 0 := by rw [Complex.neg_re]; linarith
  have hT1 : Tendsto (fun R : ℕ ↦ ((R : ℂ) ^ (1 - s) - (N : ℂ) ^ (1 - s)) / (1 - s)) atTop
      (𝓝 (((0 : ℂ) - (N : ℂ) ^ (1 - s)) / (1 - s))) :=
    ((Complex.tendsto_natCast_cpow_nhds_zero h1s).sub_const _).div_const _
  have hT2 : Tendsto (fun R : ℕ ↦ ((N : ℂ) ^ (-s) + (R : ℂ) ^ (-s)) / 2) atTop
      (𝓝 (((N : ℂ) ^ (-s) + 0) / 2)) :=
    (Tendsto.const_add _ (Complex.tendsto_natCast_cpow_nhds_zero hns)).div_const _
  have hT3 : Tendsto (fun R : ℕ ↦ ∑ k ∈ Finset.Icc 1 M,
        ((bernoulli (2 * k) : ℝ) / ((2 * k)! : ℝ) : ℂ) * (ascPochhammer ℂ (2 * k - 1)).eval s
          * ((R : ℂ) ^ (-s - ((2 * k - 1 : ℕ) : ℂ)) - (N : ℂ) ^ (-s - ((2 * k - 1 : ℕ) : ℂ)))) atTop
      (𝓝 (∑ k ∈ Finset.Icc 1 M,
        ((bernoulli (2 * k) : ℝ) / ((2 * k)! : ℝ) : ℂ) * (ascPochhammer ℂ (2 * k - 1)).eval s
          * ((0 : ℂ) - (N : ℂ) ^ (-s - ((2 * k - 1 : ℕ) : ℂ))))) := by
    apply tendsto_finsetSum
    intro k _
    have hek : (-s - ((2 * k - 1 : ℕ) : ℂ)).re < 0 := by
      rw [Complex.sub_re, Complex.neg_re, Complex.natCast_re]
      have := Nat.cast_nonneg (α := ℝ) (2 * k - 1); linarith
    exact Tendsto.const_mul _ ((Complex.tendsto_natCast_cpow_nhds_zero hek).sub_const _)
  have hRHS := (((hT1.add hT2).sub hT3).add hrem)
  have heq : (fun R : ℕ ↦ ∑ n ∈ Finset.Icc N R, (n : ℂ) ^ (-s)) =ᶠ[atTop]
      (fun R : ℕ ↦ ((R : ℂ) ^ (1 - s) - (N : ℂ) ^ (1 - s)) / (1 - s)
          + ((N : ℂ) ^ (-s) + (R : ℂ) ^ (-s)) / 2
          - (∑ k ∈ Finset.Icc 1 M,
              ((bernoulli (2 * k) : ℝ) / ((2 * k)! : ℝ) : ℂ)
                * (ascPochhammer ℂ (2 * k - 1)).eval s
                * ((R : ℂ) ^ (-s - ((2 * k - 1 : ℕ) : ℂ)) - (N : ℂ) ^ (-s - ((2 * k - 1 : ℕ) : ℂ))))
          + eulerMaclaurinRemainder (2 * M + 1) (fun y : ℝ ↦ (y : ℂ) ^ (-s))
              (N : ℝ) (R : ℝ)) := by
    filter_upwards [eventually_ge_atTop N] with R hR
    exact Complex.sum_cpow_eq s hsne1 M N R hN hR
  have hkey := tendsto_nhds_unique (hLHS.congr' heq) hRHS
  rw [hzeta] at hkey
  have hconv : ∑ n ∈ Finset.range N, (n : ℂ) ^ (-s) = ∑ n ∈ Finset.Ico 1 N, (n : ℂ) ^ (-s) := by
    rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive _ (Nat.zero_le 1) hN]
    simp [Complex.zero_cpow hs0]
  have hbern : (∑ k ∈ Finset.Icc 1 M,
        ((bernoulli (2 * k) : ℝ) / ((2 * k)! : ℝ) : ℂ) * (ascPochhammer ℂ (2 * k - 1)).eval s
          * ((0 : ℂ) - (N : ℂ) ^ (-s - ((2 * k - 1 : ℕ) : ℂ))))
      = -∑ k ∈ Finset.Icc 1 M,
          ((bernoulli (2 * k) : ℝ) / ((2 * k)! : ℝ) : ℂ) * (ascPochhammer ℂ (2 * k - 1)).eval s
            * (N : ℂ) ^ (-s - ((2 * k - 1 : ℕ) : ℂ)) := by
    rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl fun k _ ↦ by ring
  have hs1 : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hsne1)
  have hs1' : s - (1 : ℂ) ≠ 0 := sub_ne_zero.mpr hsne1
  rw [hconv, hbern, sub_eq_iff_eq_add] at hkey
  rw [hkey]
  field_simp
  ring
end
end CountPort33
section CountPort34
section
open MeasureTheory Filter Topology
open scoped Nat
namespace Complex
theorem eulerMaclaurinRemainderIoi_cpow_eq (s : ℂ) (p N : ℕ) :
    Complex.eulerMaclaurinRemainderIoi p (fun y : ℝ ↦ (y : ℂ) ^ (-s)) (N : ℝ)
      = -(ascPochhammer ℂ p).eval s / (p ! : ℂ)
          * ∫ x in Set.Ioi (N : ℝ),
              (bernoulliFun p (Int.fract x) : ℂ) * (x : ℂ) ^ (-s - (p : ℂ)) := by
  rw [Complex.eulerMaclaurinRemainderIoi]
  have step1 : (∫ x in Set.Ioi (N : ℝ),
        (bernoulliFun p (Int.fract x) : ℂ) * iteratedDeriv p (fun y : ℝ ↦ (y : ℂ) ^ (-s)) x)
      = ∫ x in Set.Ioi (N : ℝ), ((-1 : ℂ) ^ p * (ascPochhammer ℂ p).eval s)
          * ((bernoulliFun p (Int.fract x) : ℂ) * (x : ℂ) ^ (-s - (p : ℂ))) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    have hx0 : (0 : ℝ) < x := lt_of_le_of_lt (Nat.cast_nonneg N) (Set.mem_Ioi.mp hx)
    dsimp only
    rw [Complex.iteratedDeriv_cpow_ofReal_neg s p hx0]
    ring
  rw [step1, integral_const_mul]
  have h2 : (-1 : ℂ) ^ (p + 1) * (-1 : ℂ) ^ p = -1 := by
    rw [← pow_add]; exact Odd.neg_one_pow ⟨p, by ring⟩
  have hpne : (p ! : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos p).ne'
  field_simp
  linear_combination ((ascPochhammer ℂ p).eval s *
    ∫ x in Set.Ioi (N : ℝ), (bernoulliFun p (Int.fract x) : ℂ) * (x : ℂ) ^ (-s - (p : ℂ))) * h2
theorem differentiableOn_eulerMaclaurinRemainderIoi_cpow (p N : ℕ) (hN : 1 ≤ N) :
    DifferentiableOn ℂ
      (fun s : ℂ ↦ Complex.eulerMaclaurinRemainderIoi p (fun y : ℝ ↦ (y : ℂ) ^ (-s)) (N : ℝ))
      {s : ℂ | (1 : ℝ) - p < s.re} := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hker := Complex.measurable_bernoulliFun_fract p
  have hcpowmeas := Complex.aestronglyMeasurable_ofReal_cpow_Ioi (Nat.cast_nonneg N)
  simp only [eulerMaclaurinRemainderIoi_cpow_eq]
  refine (((ascPochhammer ℂ p).differentiable.neg.div_const (p ! : ℂ)).differentiableOn).mul
    fun s₀ hs₀ ↦ ?_
  rw [Set.mem_ofPred_eq] at hs₀
  obtain ⟨σ₁, hσlo, hσhi⟩ : ∃ σ₁ : ℝ, (1 : ℝ) - p < σ₁ ∧ σ₁ < s₀.re :=
    ⟨((1 - p) + s₀.re) / 2, by linarith, by linarith⟩
  set ε : ℝ := (σ₁ + p - 1) / 2 with hεdef
  have hεpos : 0 < ε := by rw [hεdef]; linarith
  have hexp : (1 : ℝ) < σ₁ + p - ε := by rw [hεdef]; linarith
  obtain ⟨C, hC0, hC⟩ := Complex.exists_norm_bernoulliFun_fract_le p
  have happ := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Set.Ioi (N : ℝ)))
    (F := fun s x ↦ (bernoulliFun p (Int.fract x) : ℂ) * (x : ℂ) ^ (-s - (p : ℂ)))
    (F' := fun s x ↦ (bernoulliFun p (Int.fract x) : ℂ)
      * ((x : ℂ) ^ (-s - (p : ℂ)) * Complex.log x * (-1)))
    (x₀ := s₀) (bound := fun x ↦ C / ε * x ^ (-(σ₁ + p - ε)))
    ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hσhi)
    (Filter.Eventually.of_forall fun s ↦ hker.aestronglyMeasurable.mul (hcpowmeas _))
    (integrableOn_Ioi_bernoulliFun_fract_mul_cpow p N hN
      (by rw [Complex.sub_re, Complex.neg_re, Complex.natCast_re]; linarith))
    (hker.aestronglyMeasurable.mul
      (((hcpowmeas _).mul
        (Complex.measurable_log.comp Complex.measurable_ofReal).aestronglyMeasurable).mul
          aestronglyMeasurable_const))
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx s hs
      have hx1 : (1 : ℝ) ≤ x :=
        le_of_lt (lt_of_le_of_lt (by exact_mod_cast hN) (Set.mem_Ioi.mp hx))
      have hx0 : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx1
      have hlog : (0 : ℝ) ≤ Real.log x := Real.log_nonneg hx1
      rw [show ‖(bernoulliFun p (Int.fract x) : ℂ)
                * ((x : ℂ) ^ (-s - (p : ℂ)) * Complex.log x * (-1))‖
              = ‖(bernoulliFun p (Int.fract x) : ℂ)‖ * x ^ (-s.re - p) * Real.log x from by
            rw [← Complex.ofReal_log hx0.le]
            simp only [norm_mul, norm_neg, norm_one, mul_one,
              Complex.norm_cpow_eq_rpow_re_of_pos hx0, Complex.norm_real, Real.norm_eq_abs,
              Complex.sub_re, Complex.neg_re, Complex.natCast_re, abs_of_nonneg hlog]
            ring,
        show C / ε * x ^ (-(σ₁ + p - ε)) = C * x ^ (-σ₁ - p) * (x ^ ε / ε) from by
          rw [show -(σ₁ + p - ε) = -σ₁ - p + ε from by ring, Real.rpow_add hx0]; ring]
      exact mul_le_mul (mul_le_mul (hC x) (Real.rpow_le_rpow_of_exponent_le hx1 (by linarith))
          (Real.rpow_nonneg hx0.le _) hC0) (Real.log_le_rpow_div hx0.le hεpos) hlog
        (mul_nonneg hC0 (Real.rpow_nonneg hx0.le _)))
    ((integrableOn_Ioi_rpow_of_lt (a := -(σ₁ + p - ε)) (by linarith) hN0).const_mul (C / ε))
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx s _
      have hbase : (x : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.2 (lt_of_lt_of_le hN0 (Set.mem_Ioi.mp hx).le).ne'
      exact HasDerivAt.const_mul _
        ((Complex.hasStrictDerivAt_const_cpow (Or.inl hbase)).hasDerivAt.comp s
          (by simpa using (hasDerivAt_id s).neg.sub_const (p : ℂ))))
  exact happ.2.differentiableAt.differentiableWithinAt
private theorem eulerMaclaurinRemainder_cpow_succ (s : ℂ) (M N R : ℕ) (hN : 1 ≤ N) (hNR : N ≤ R) :
    eulerMaclaurinRemainder (2 * M + 1) (fun y : ℝ ↦ (y : ℂ) ^ (-s)) (N : ℝ) (R : ℝ)
      = ((bernoulli (2 * M + 2) : ℝ) / ((2 * M + 2)! : ℝ) : ℂ)
          * (iteratedDeriv (2 * M + 1) (fun y : ℝ ↦ (y : ℂ) ^ (-s)) (R : ℝ)
              - iteratedDeriv (2 * M + 1) (fun y : ℝ ↦ (y : ℂ) ^ (-s)) (N : ℝ))
        + eulerMaclaurinRemainder (2 * M + 2) (fun y : ℝ ↦ (y : ℂ) ^ (-s))
            (N : ℝ) (R : ℝ) := by
  set f : ℝ → ℂ := fun y : ℝ ↦ (y : ℂ) ^ (-s) with hf
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hNa : ((N : ℤ) : ℝ) = (N : ℝ) := by push_cast; ring
  have hRN : ((N : ℤ) : ℝ) + ((R - N : ℕ) : ℝ) = (R : ℝ) := by push_cast [Nat.cast_sub hNR]; ring
  have hderiv : ∀ q, q < 2 * M + 2 → ∀ x ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (iteratedDeriv q f) (iteratedDeriv (q + 1) f x) x :=
    fun q _ x hx ↦ Complex.hasDerivAt_iteratedDeriv_cpow_ofReal_neg s q hx
  have hpos : Set.uIcc ((N : ℤ) : ℝ) (((N : ℤ) : ℝ) + ((R - N : ℕ) : ℝ)) ⊆ Set.Ioi (0 : ℝ) := by
    rw [hRN, hNa, Set.uIcc_of_le (by exact_mod_cast hNR)]
    exact fun x hx ↦ lt_of_lt_of_le hN0 hx.1
  have hint : ∀ q, 0 < q → q ≤ 2 * M + 2 →
      IntervalIntegrable (iteratedDeriv q f) volume ((N : ℤ) : ℝ)
        (((N : ℤ) : ℝ) + ((R - N : ℕ) : ℝ)) :=
    fun q _ _ ↦ ContinuousOn.intervalIntegrable fun x hx ↦
      (Complex.hasDerivAt_iteratedDeriv_cpow_ofReal_neg s q
        (hpos hx)).continuousAt.continuousWithinAt
  have h1 := Complex.sum_eq (f := f) (N : ℤ) (N := R - N) (p := 2 * M + 1) (by lia)
    (fun q _ x hx ↦ hderiv q (by lia) x (hpos hx)) (fun q hq0 hq ↦ hint q hq0 (by lia))
  have h2 := Complex.sum_eq (f := f) (N : ℤ) (N := R - N) (p := 2 * M + 2) (by lia)
    (fun q hq x hx ↦ hderiv q hq x (hpos hx)) hint
  rw [hRN, hNa, show (2 * M + 1) / 2 + 1 = M + 1 from by lia] at h1
  rw [hRN, hNa, show (2 * M + 2) / 2 + 1 = M + 1 + 1 from by lia,
    Finset.sum_Ico_succ_top (show (1 : ℕ) ≤ M + 1 by lia)] at h2
  simp only [show 2 * (M + 1) = 2 * M + 2 from by ring,
    show 2 * M + 2 - 1 = 2 * M + 1 from by lia] at h2
  linear_combination h2 - h1
theorem eulerMaclaurinRemainderIoi_succ_eq (s : ℂ) (M N : ℕ) (hN : 1 ≤ N)
    (hs : -(2 * M : ℝ) < s.re) :
    Complex.eulerMaclaurinRemainderIoi (2 * M + 1) (fun y : ℝ ↦ (y : ℂ) ^ (-s)) (N : ℝ)
      = ((bernoulli (2 * M + 2) : ℝ) / ((2 * M + 2)! : ℝ) : ℂ)
          * (ascPochhammer ℂ (2 * M + 1)).eval s
          * (N : ℂ) ^ (-s - ((2 * M + 1 : ℕ) : ℂ))
        + Complex.eulerMaclaurinRemainderIoi (2 * M + 2) (fun y : ℝ ↦ (y : ℂ) ^ (-s)) (N : ℝ) := by
  set f : ℝ → ℂ := fun y : ℝ ↦ (y : ℂ) ^ (-s) with hf
  set c : ℂ := -s - ((2 * M + 1 : ℕ) : ℂ) with hc
  set B : ℂ := ((bernoulli (2 * M + 2) : ℝ) / ((2 * M + 2)! : ℝ) : ℂ)
  set P : ℂ := (ascPochhammer ℂ (2 * M + 1)).eval s with hP
  have hcre : c.re < 0 := by
    rw [hc, Complex.sub_re, Complex.neg_re, Complex.natCast_re]; push_cast; linarith
  have hrem : ∀ q : ℕ, 1 < s.re + (q : ℝ) →
      Tendsto (fun R : ℕ ↦ eulerMaclaurinRemainder q f (N : ℝ) (R : ℝ)) atTop
        (𝓝 (Complex.eulerMaclaurinRemainderIoi q f (N : ℝ))) := fun q hq ↦ by
    simp only [Complex.eulerMaclaurinRemainder_eq, Complex.eulerMaclaurinRemainderIoi]
    exact (intervalIntegral_tendsto_integral_Ioi _
      (integrableOn_Ioi_bernoulliFun_fract_iteratedDeriv_cpow s q N hN hq)
      tendsto_natCast_atTop_atTop).const_mul _
  have hcf : ∀ R : ℕ, 1 ≤ R → iteratedDeriv (2 * M + 1) f (R : ℝ) = -P * (R : ℂ) ^ c := by
    intro R hR
    rw [hf, Complex.iteratedDeriv_cpow_ofReal_neg s (2 * M + 1)
        (by exact_mod_cast hR : (0 : ℝ) < R),
      Odd.neg_one_pow ⟨M, by ring⟩, hc, hP]
    push_cast; ring
  have hbdy : Tendsto (fun R : ℕ ↦ B * (iteratedDeriv (2 * M + 1) f (R : ℝ)
        - iteratedDeriv (2 * M + 1) f (N : ℝ))) atTop (𝓝 (B * P * (N : ℂ) ^ c)) := by
    have hbase := (((tendsto_natCast_cpow_nhds_zero hcre).const_mul (-P)).sub_const
      (-P * (N : ℂ) ^ c)).const_mul B
    rw [show B * (-P * 0 - -P * (N : ℂ) ^ c) = B * P * (N : ℂ) ^ c from by ring] at hbase
    refine Tendsto.congr' ?_ hbase
    filter_upwards [eventually_ge_atTop N] with R hR
    rw [hcf R (le_trans hN hR), hcf N hN]
  refine tendsto_nhds_unique (Tendsto.congr' ?_ (hrem (2 * M + 1) (by push_cast; linarith)))
    (hbdy.add (hrem (2 * M + 2) (by push_cast; linarith)))
  filter_upwards [eventually_ge_atTop N] with R hR
  exact eulerMaclaurinRemainder_cpow_succ s M N R hN hR
theorem norm_eulerMaclaurinRemainderIoi_one_ofReal_le {x : ℝ} (hx0 : 0 < x) :
    ‖Complex.eulerMaclaurinRemainderIoi 1 (fun y : ℝ ↦ (y : ℂ) ^ (-(x : ℂ))) 1‖ ≤ 1 / 2 := by
  have h := eulerMaclaurinRemainderIoi_cpow_eq (x : ℂ) 1 1
  simp only [Nat.cast_one, ascPochhammer_one, Polynomial.eval_X, Nat.factorial_one, div_one] at h
  have hb := norm_integral_le_of_norm_le
    (f := fun y : ℝ ↦ (bernoulliFun 1 (Int.fract y) : ℂ) * (y : ℂ) ^ (-(x : ℂ) - 1))
    (μ := volume.restrict (Set.Ioi (1 : ℝ)))
    ((integrableOn_Ioi_rpow_of_lt (show -x - 1 < -1 by linarith) one_pos).const_mul (1 / 2)) ?_
  · rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) one_pos, Real.one_rpow,
      show -x - 1 + 1 = -x from by ring, neg_div_neg_eq] at hb
    rw [h, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0]
    refine (mul_le_mul_of_nonneg_left hb hx0.le).trans_eq ?_
    field_simp
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hy0 : (0 : ℝ) < y := one_pos.trans hy
    have hre : (-(x : ℂ) - 1).re = -x - 1 := by simp
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_cpow_eq_rpow_re_of_pos hy0,
      hre, bernoulliFun_one]
    refine mul_le_mul_of_nonneg_right (abs_le.mpr ⟨by linarith [Int.fract_nonneg y], ?_⟩)
      (Real.rpow_nonneg hy0.le _)
    linarith [Int.fract_lt_one y]
end Complex
noncomputable def zetaEMExpansion (s : ℂ) (M N : ℕ) : ℂ :=
  (∑ n ∈ Finset.Ico 1 N, (n : ℂ) ^ (-s))
    + (N : ℂ) ^ (1 - s) / (s - 1) + (N : ℂ) ^ (-s) / 2
    + (∑ k ∈ Finset.Icc 1 M,
        ((bernoulli (2 * k) : ℝ) / ((2 * k)! : ℝ) : ℂ)
          * (ascPochhammer ℂ (2 * k - 1)).eval s
          * (N : ℂ) ^ (-s - ((2 * k - 1 : ℕ) : ℂ)))
    + ((bernoulli (2 * M + 2) : ℝ) / ((2 * M + 2)! : ℝ) : ℂ)
        * (ascPochhammer ℂ (2 * M + 1)).eval s
        * (N : ℂ) ^ (-s - ((2 * M + 1 : ℕ) : ℂ))
    + Complex.eulerMaclaurinRemainderIoi (2 * M + 2) (fun y : ℝ ↦ (y : ℂ) ^ (-s)) (N : ℝ)
noncomputable abbrev zetaApproximant (s : ℂ) (M N : ℕ) : ℂ :=
  (∑ n ∈ Finset.Ico 1 N, (n : ℂ) ^ (-s))
    + (N : ℂ) ^ (1 - s) / (s - 1) + (N : ℂ) ^ (-s) / 2
    + (∑ k ∈ Finset.Icc 1 M,
        ((bernoulli (2 * k) : ℝ) / ((2 * k)! : ℝ) : ℂ)
          * (ascPochhammer ℂ (2 * k - 1)).eval s
          * (N : ℂ) ^ (-s - ((2 * k - 1 : ℕ) : ℂ)))
noncomputable abbrev zetaRemainder (s : ℂ) (M N : ℕ) : ℂ :=
  ((bernoulli (2 * M + 2) : ℝ) / ((2 * M + 2)! : ℝ) : ℂ)
      * (ascPochhammer ℂ (2 * M + 1)).eval s
      * (N : ℂ) ^ (-s - ((2 * M + 1 : ℕ) : ℂ))
    + Complex.eulerMaclaurinRemainderIoi (2 * M + 2) (fun y : ℝ ↦ (y : ℂ) ^ (-s)) (N : ℝ)
theorem analyticOnNhd_zetaEMExpansion (M N : ℕ) (hN : 1 ≤ N) :
    AnalyticOnNhd ℂ (fun s : ℂ ↦ zetaEMExpansion s M N)
      ({s : ℂ | (-(2 * M + 1 : ℝ)) < s.re} \ {1}) := by
  have hNne : (N : ℂ) ≠ 0 := by exact_mod_cast Nat.one_le_iff_ne_zero.mp hN
  refine DifferentiableOn.analyticOnNhd ?_
    ((isOpen_lt continuous_const Complex.continuous_re).sdiff isClosed_singleton)
  simp only [zetaEMExpansion]
  refine DifferentiableOn.add (DifferentiableOn.add (DifferentiableOn.add
    (DifferentiableOn.add (DifferentiableOn.add ?_ ?_) ?_) ?_) ?_) ?_
  ·
    refine Differentiable.differentiableOn (Differentiable.fun_sum fun n hn ↦ ?_)
    have : (n : ℂ) ≠ 0 := by
      rw [Finset.mem_Ico] at hn; exact_mod_cast Nat.one_le_iff_ne_zero.mp hn.1
    exact differentiable_id.neg.const_cpow (Or.inl this)
  ·
    apply DifferentiableOn.div
    · exact (((differentiable_const (1 : ℂ)).sub differentiable_id).const_cpow
        (Or.inl hNne)).differentiableOn
    · exact (differentiable_id.sub_const 1).differentiableOn
    · intro s hs; exact sub_ne_zero.mpr hs.2
  ·
    exact ((differentiable_id.neg.const_cpow (Or.inl hNne)).div_const 2).differentiableOn
  ·
    refine Differentiable.differentiableOn (Differentiable.fun_sum fun k _ ↦ ?_)
    exact ((differentiable_const _).mul (ascPochhammer ℂ (2 * k - 1)).differentiable).mul
      ((differentiable_id.neg.sub_const _).const_cpow (Or.inl hNne))
  ·
    refine Differentiable.differentiableOn ?_
    exact ((differentiable_const _).mul (ascPochhammer ℂ (2 * M + 1)).differentiable).mul
      ((differentiable_id.neg.sub_const _).const_cpow (Or.inl hNne))
  ·
    refine (Complex.differentiableOn_eulerMaclaurinRemainderIoi_cpow (2 * M + 2) N hN).mono
      fun s hs ↦ ?_
    have hs1 : (-(2 * M + 1 : ℝ)) < s.re := hs.1
    rw [Set.mem_ofPred_eq]
    push_cast
    linarith
theorem riemannZeta_eq (s : ℂ) (M N : ℕ) (hN : 1 ≤ N) (hs : -(2 * M + 1 : ℝ) < s.re)
    (hs1 : s ≠ 1) :
    riemannZeta s = zetaEMExpansion s M N := by
  set H : Set ℂ := {z : ℂ | (-(2 * M + 1 : ℝ)) < z.re} with hHdef
  set U : Set ℂ := H \ {1} with hUdef
  have hUopen : IsOpen U :=
    (isOpen_lt continuous_const Complex.continuous_re).sdiff isClosed_singleton
  have hζ : AnalyticOnNhd ℂ riemannZeta U :=
    DifferentiableOn.analyticOnNhd
      (fun z hz ↦ (differentiableAt_riemannZeta hz.2).differentiableWithinAt) hUopen
  have hE : AnalyticOnNhd ℂ (fun z ↦ zetaEMExpansion z M N) U :=
    analyticOnNhd_zetaEMExpansion M N hN
  have hP : (0 : ℝ) ≤ 2 * (M : ℝ) := by positivity
  have hcH : Convex ℝ H := convex_halfSpace_re_gt _
  have hmH : ∀ z : ℂ, 0 ≤ z.re → z ∈ H := fun z hz ↦ by
    simp only [hHdef, Set.mem_ofPred_eq]; linarith [hP]
  have hA : IsPreconnected ({z : ℂ | 0 < z.im} ∩ H) :=
    ((convex_halfSpace_im_gt 0).inter hcH).isPreconnected
  have hB : IsPreconnected ({z : ℂ | z.im < 0} ∩ H) :=
    ((convex_halfSpace_im_lt 0).inter hcH).isPreconnected
  have hC : IsPreconnected ({z : ℂ | z.re < 1} ∩ H) :=
    ((convex_halfSpace_re_lt 1).inter hcH).isPreconnected
  have hD : IsPreconnected ({z : ℂ | 1 < z.re} ∩ H) :=
    ((convex_halfSpace_re_gt 1).inter hcH).isPreconnected
  have hUconn : IsPreconnected U := by
    have hUV : U = (({z : ℂ | 0 < z.im} ∩ H) ∪ ({z : ℂ | z.re < 1} ∩ H)
          ∪ ({z : ℂ | z.im < 0} ∩ H)) ∪ ({z : ℂ | 1 < z.re} ∩ H) := by
      ext z
      simp only [hUdef, hHdef, Set.mem_sdiff, Set.mem_union, Set.mem_inter_iff, Set.mem_ofPred_eq,
        Set.mem_singleton_iff]
      constructor
      · rintro ⟨hre, hne⟩
        rcases lt_trichotomy z.im 0 with him | him | him
        · exact .inl (.inr ⟨him, hre⟩)
        · rcases lt_trichotomy z.re 1 with hlt | heq | hgt
          · exact .inl (.inl (.inr ⟨hlt, hre⟩))
          · exact absurd (Complex.ext (heq.trans Complex.one_re.symm)
              (him.trans Complex.one_im.symm)) hne
          · exact .inr ⟨hgt, hre⟩
        · exact .inl (.inl (.inl ⟨him, hre⟩))
      · rintro (((⟨h, hre⟩ | ⟨h, hre⟩) | ⟨h, hre⟩) | ⟨h, hre⟩) <;>
          exact ⟨hre, by rintro rfl; simp only [Complex.one_im, Complex.one_re] at h; linarith⟩
    have mem : ∀ z : ℂ, ∀ S : Set ℂ, z ∈ S → 0 ≤ z.re → z ∈ S ∩ H := fun _ _ h hz ↦ ⟨h, hmH _ hz⟩
    rw [hUV]
    exact ((hA.union Complex.I (mem _ _ (by simp) (by simp)) (mem _ _ (by simp) (by simp))
        hC).union (-Complex.I) (.inr (mem _ _ (by simp) (by simp)))
        (mem _ _ (by simp) (by simp)) hB).union
      (2 + Complex.I) (.inl (.inl (mem _ _ (by simp) (by simp))))
      (mem _ _ (by simp) (by simp)) hD
  have hagree : riemannZeta =ᶠ[𝓝 (2 : ℂ)] (fun z ↦ zetaEMExpansion z M N) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show (1 : ℝ) < (2 : ℂ).re by simp)] with z hz
    have hz1 : 1 < z.re := hz
    rw [riemannZeta_eq_of_one_lt_re z hz1 M N hN]
    simp only [zetaEMExpansion]
    rw [Complex.eulerMaclaurinRemainderIoi_succ_eq z M N hN (by linarith : -(2 * M : ℝ) < z.re)]
    ring
  exact hζ.eqOn_of_preconnected_of_eventuallyEq hE hUconn ⟨hmH _ (by simp), by simp⟩ hagree
    ⟨hs, hs1⟩
theorem riemannZeta_eq_order_one {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    riemannZeta s = 1 / (s - 1) + 1 / 2
      + Complex.eulerMaclaurinRemainderIoi 1 (fun y : ℝ ↦ (y : ℂ) ^ (-s)) (1 : ℝ) := by
  have h2 := Complex.eulerMaclaurinRemainderIoi_succ_eq s 0 1 le_rfl (by push_cast; linarith)
  simp only [mul_zero, zero_add, Nat.cast_one, Complex.one_cpow] at h2
  rw [riemannZeta_eq s 0 1 le_rfl (by push_cast; linarith) hs1, zetaEMExpansion]
  simp only [mul_zero, zero_add, Nat.cast_one, Complex.one_cpow, Finset.Ico_self,
    Finset.sum_empty, show Finset.Icc 1 0 = (∅ : Finset ℕ) from Finset.Icc_eq_empty (by lia)]
  linear_combination -h2
theorem riemannZeta_ofReal_re_neg_of_mem_Ioo {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    (riemannZeta (x : ℂ)).re < 0 := by
  obtain ⟨hx0, hx1⟩ := hx
  have hs1 : (x : ℂ) ≠ 1 := by rw [Ne, Complex.ofReal_eq_one]; linarith
  rw [riemannZeta_eq_order_one (by simpa using hx0) hs1, Complex.add_re, Complex.add_re,
    show (1 / ((x : ℂ) - 1)).re = 1 / (x - 1) from by
      rw [show (x : ℂ) - 1 = ((x - 1 : ℝ) : ℂ) from by push_cast; ring, ← Complex.ofReal_one,
        ← Complex.ofReal_div, Complex.ofReal_re],
    show ((1 : ℂ) / 2).re = 1 / 2 from by norm_num]
  have hRre := (Complex.re_le_norm _).trans
    (Complex.norm_eulerMaclaurinRemainderIoi_one_ofReal_le hx0)
  have hlt : 1 / (x - 1) < -1 := by
    rw [div_lt_iff_of_neg (show x - 1 < 0 by linarith)]; linarith
  linarith
end
end CountPort34
section CountPort35
section
open Complex Set
theorem riemannZeta_ofReal_neg_of_mem_Ioo {σ : ℝ} (hσ : σ ∈ Ioo (0 : ℝ) 1) :
    (riemannZeta (σ : ℂ)).im = 0 ∧ (riemannZeta (σ : ℂ)).re < 0 :=
  ⟨Complex.conj_eq_iff_im.mp (by simpa using (riemannZeta_conj (σ : ℂ)).symm),
    riemannZeta_ofReal_re_neg_of_mem_Ioo hσ⟩
private theorem riemannXi_ofReal_ne_zero_of_one_lt {σ : ℝ} (hσ : 1 < σ) :
    riemannXi (σ : ℂ) ≠ 0 := by
  have hσ0 : (σ : ℂ) ≠ 0 := by rw [Ne, Complex.ofReal_eq_zero]; linarith
  have hσ1 : (σ : ℂ) ≠ 1 := by rw [Ne, Complex.ofReal_eq_one]; linarith
  have hΓ : Gammaℝ (σ : ℂ) ≠ 0 :=
    Gammaℝ_ne_zero_of_re_pos (by rw [Complex.ofReal_re]; linarith)
  rw [riemannXi_eq_prefactor_mul hσ0 hσ1 hΓ]
  exact mul_ne_zero (prefactor_ne_zero_of hσ0 hσ1 hΓ)
    (riemannZeta_ne_zero_of_one_le_re (by rw [Complex.ofReal_re]; linarith))
theorem riemannXi_ofReal_ne_zero_of_mem_Icc {σ : ℝ} (hσ : σ ∈ Icc (-1 : ℝ) 2) :
    riemannXi (σ : ℂ) ≠ 0 := by
  obtain ⟨hlo, hhi⟩ := hσ
  rcases lt_trichotomy σ 0 with hneg | rfl | hpos
  ·
    rw [show ((σ : ℂ)) = 1 - ((1 - σ : ℝ) : ℂ) from by push_cast; ring, riemannXi_one_sub]
    exact riemannXi_ofReal_ne_zero_of_one_lt (by linarith)
  · rw [Complex.ofReal_zero, riemannXi_zero]; norm_num
  · rcases lt_trichotomy σ 1 with h1 | rfl | h1
    ·
      exact fun h ↦ (riemannZeta_ofReal_neg_of_mem_Ioo ⟨hpos, h1⟩).2.ne
        (by rw [(riemannXi_eq_zero_iff (by simpa using hpos) (by simpa using h1)).mp h,
          Complex.zero_re])
    · rw [Complex.ofReal_one, riemannXi_one]; norm_num
    · exact riemannXi_ofReal_ne_zero_of_one_lt h1
end
end CountPort35
section CountPort36
section
open Complex Set
variable {a b : ℝ}
theorem argVariation_conj (hab : a ≤ b) {φ : ℝ → ℂ}
    (hφ : ContinuousOn φ (Set.Icc a b)) (h0 : ∀ u ∈ Set.Icc a b, φ u ≠ 0) :
    argVariation a b (fun u => starRingEnd ℂ (φ u)) = - argVariation a b φ := by
  obtain ⟨g, hg, -⟩ :=
    exists_isContLog hab hφ h0 (Complex.exp_log (h0 a (Set.left_mem_Icc.mpr hab)))
  have hg' : IsContLog a b (fun u => starRingEnd ℂ (φ u)) (fun u => starRingEnd ℂ (g u)) := by
    refine ⟨Complex.continuous_conj.comp_continuousOn hg.1, fun u hu => ?_⟩
    change Complex.exp (starRingEnd ℂ (g u)) = starRingEnd ℂ (φ u)
    rw [Complex.exp_conj, hg.2 u hu]
  rw [argVariation_eq_of_isContLog hab hg', argVariation_eq_of_isContLog hab hg]
  simp only [Complex.conj_im]
  ring
theorem riemannXi_ne_zero_of_one_lt_re {s : ℂ} (hs : 1 < s.re) : riemannXi s ≠ 0 := by
  have hs0 : s ≠ 0 := by rintro rfl; simp only [Complex.zero_re] at hs; linarith
  have hs1 : s ≠ 1 := by rintro rfl; simp only [Complex.one_re] at hs; linarith
  have hΓ : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by linarith)
  have hζ : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re (by linarith)
  rw [riemannXi_eq_prefactor_mul hs0 hs1 hΓ]
  exact mul_ne_zero (prefactor_ne_zero_of hs0 hs1 hΓ) hζ
theorem riemannXi_ne_zero_of_zeta_ne_zero_of_im_ne_zero {s : ℂ} (him : s.im ≠ 0)
    (hζ : riemannZeta s ≠ 0) : riemannXi s ≠ 0 := by
  have hs0 : s ≠ 0 := by rintro rfl; simp at him
  have hs1 : s ≠ 1 := by rintro rfl; simp at him
  have hΓ : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_im_ne_zero him
  rw [riemannXi_eq_prefactor_mul hs0 hs1 hΓ]
  exact mul_ne_zero (prefactor_ne_zero_of hs0 hs1 hΓ) hζ
private theorem riemannXi_ofReal_im_eq_zero (σ : ℝ) : (riemannXi (σ : ℂ)).im = 0 := by
  have hc := riemannXi_conj (σ : ℂ)
  rw [Complex.conj_ofReal] at hc
  have := congrArg Complex.im hc
  rw [Complex.conj_im] at this
  linarith
theorem riemannXi_pos_of_mem_Icc {σ : ℝ} (hσ : σ ∈ Icc (-1 : ℝ) 2) :
    0 < (riemannXi (σ : ℂ)).re ∧ (riemannXi (σ : ℂ)).im = 0 := by
  refine ⟨?_, riemannXi_ofReal_im_eq_zero σ⟩
  by_contra hcon
  rw [not_lt] at hcon
  set g : ℝ → ℝ := fun x => (riemannXi (x : ℂ)).re with hg
  have hgcont : ContinuousOn g (Set.uIcc 0 σ) :=
    (Complex.continuous_re.comp
      (differentiable_riemannXi.continuous.comp Complex.continuous_ofReal)).continuousOn
  have hg0 : g 0 = 1 / 2 := by simp [hg, Complex.ofReal_zero, riemannXi_zero]
  have hmem : (0 : ℝ) ∈ Set.uIcc (g 0) (g σ) :=
    Set.mem_uIcc.mpr (Or.inr ⟨hcon, by rw [hg0]; norm_num⟩)
  obtain ⟨c, hc, hgc⟩ := intermediate_value_uIcc hgcont hmem
  have hsub : Set.uIcc 0 σ ⊆ Icc (-1 : ℝ) 2 :=
    Set.uIcc_subset_Icc ⟨by norm_num, by norm_num⟩ hσ
  have hcIcc : c ∈ Icc (-1 : ℝ) 2 := hsub hc
  have hzero : riemannXi (c : ℂ) = 0 :=
    Complex.ext (by simpa [hg] using hgc) (riemannXi_ofReal_im_eq_zero c)
  exact riemannXi_ofReal_ne_zero_of_mem_Icc hcIcc hzero
private theorem riemannXi_lineSeg_continuousOn (z₀ z₁ : ℂ) :
    ContinuousOn (fun u => riemannXi (lineSeg z₀ z₁ u)) (Set.Icc 0 1) :=
  (differentiable_riemannXi.continuous.comp (continuous_lineSeg z₀ z₁)).continuousOn
private theorem riemannXi_lineSeg_ne_zero_of_re_eq_two {z₀ z₁ : ℂ} (h0 : z₀.re = 2)
    (h1 : z₁.re = 2) : ∀ u ∈ Set.Icc (0 : ℝ) 1, riemannXi (lineSeg z₀ z₁ u) ≠ 0 := by
  intro u _
  refine riemannXi_ne_zero_of_one_lt_re ?_
  rw [lineSeg_re, h0, h1]; norm_num
private theorem riemannXi_lineSeg_ne_zero_of_im_eq_T {T : ℝ} (hT : T ≠ 0)
    (hT' : ∀ s : ℂ, s.im = T → riemannZeta s ≠ 0) {z₀ z₁ : ℂ} (h0 : z₀.im = T) (h1 : z₁.im = T) :
    ∀ u ∈ Set.Icc (0 : ℝ) 1, riemannXi (lineSeg z₀ z₁ u) ≠ 0 := by
  intro u _
  have him : (lineSeg z₀ z₁ u).im = T := by rw [lineSeg_im, h0, h1]; ring
  exact riemannXi_ne_zero_of_zeta_ne_zero_of_im_ne_zero (by rw [him]; exact hT) (hT' _ him)
private theorem argVariation_lineSeg_split {f : ℂ → ℂ} (z₀ z₁ : ℂ) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) (hcont : ContinuousOn (fun u => f (lineSeg z₀ z₁ u)) (Set.Icc 0 1))
    (hne : ∀ u ∈ Set.Icc (0 : ℝ) 1, f (lineSeg z₀ z₁ u) ≠ 0) :
    argVariation 0 1 (fun u => f (lineSeg z₀ z₁ u))
      = argVariation 0 1 (fun u => f (lineSeg z₀ (lineSeg z₀ z₁ t) u))
        + argVariation 0 1 (fun u => f (lineSeg (lineSeg z₀ z₁ t) z₁ u)) := by
  have hmap1 : Set.MapsTo (fun v : ℝ => t * v) (Set.Icc 0 1) (Set.Icc 0 t) := by
    intro v hv; refine ⟨?_, ?_⟩ <;> nlinarith [hv.1, hv.2, ht0, ht1]
  have hmap2 : Set.MapsTo (fun v : ℝ => t + (1 - t) * v) (Set.Icc 0 1) (Set.Icc t 1) := by
    intro v hv; refine ⟨?_, ?_⟩ <;> nlinarith [hv.1, hv.2, ht0, ht1]
  have hcont1 : ContinuousOn (fun u => f (lineSeg z₀ z₁ u)) (Set.Icc 0 t) :=
    hcont.mono (Set.Icc_subset_Icc le_rfl ht1)
  have hne1 : ∀ u ∈ Set.Icc (0 : ℝ) t, f (lineSeg z₀ z₁ u) ≠ 0 :=
    fun u hu => hne u ⟨hu.1, hu.2.trans ht1⟩
  have hcont2 : ContinuousOn (fun u => f (lineSeg z₀ z₁ u)) (Set.Icc t 1) :=
    hcont.mono (Set.Icc_subset_Icc ht0 le_rfl)
  have hne2 : ∀ u ∈ Set.Icc t (1 : ℝ), f (lineSeg z₀ z₁ u) ≠ 0 :=
    fun u hu => hne u ⟨ht0.trans hu.1, hu.2⟩
  have e1 : (fun v : ℝ => f (lineSeg z₀ z₁ (t * v)))
      = (fun u => f (lineSeg z₀ (lineSeg z₀ z₁ t) u)) := by
    funext v; congr 1; simp only [lineSeg]; push_cast; ring
  have e2 : (fun v : ℝ => f (lineSeg z₀ z₁ (t + (1 - t) * v)))
      = (fun u => f (lineSeg (lineSeg z₀ z₁ t) z₁ u)) := by
    funext v; congr 1; simp only [lineSeg]; push_cast; ring
  have h1 : argVariation 0 t (fun u => f (lineSeg z₀ z₁ u))
      = argVariation 0 1 (fun u => f (lineSeg z₀ (lineSeg z₀ z₁ t) u)) := by
    rw [← e1]
    exact (argVariation_comp ht0 zero_le_one (by fun_prop) hmap1
      (by show t * 0 = 0; ring) (by show t * 1 = t; ring) hcont1 hne1).symm
  have h2 : argVariation t 1 (fun u => f (lineSeg z₀ z₁ u))
      = argVariation 0 1 (fun u => f (lineSeg (lineSeg z₀ z₁ t) z₁ u)) := by
    rw [← e2]
    exact (argVariation_comp ht1 zero_le_one (by fun_prop) hmap2
      (by show t + (1 - t) * 0 = t; ring) (by show t + (1 - t) * 1 = 1; ring) hcont2 hne2).symm
  rw [argVariation_trans ht0 ht1 hcont hne, h1, h2]
private theorem argVariation_lineSeg_swap {f : ℂ → ℂ} (z₀ z₁ : ℂ)
    (hcont : ContinuousOn (fun u => f (lineSeg z₀ z₁ u)) (Set.Icc 0 1))
    (hne : ∀ u ∈ Set.Icc (0 : ℝ) 1, f (lineSeg z₀ z₁ u) ≠ 0) :
    argVariation 0 1 (fun u => f (lineSeg z₁ z₀ u))
      = - argVariation 0 1 (fun u => f (lineSeg z₀ z₁ u)) := by
  rw [← argVariation_reverse zero_le_one hcont hne]
  congr 1; funext u
  show f (lineSeg z₁ z₀ u) = f (lineSeg z₀ z₁ (0 + 1 - u))
  congr 1
  simp only [lineSeg]; push_cast; ring
private theorem riemannXi_reflect (s : ℂ) :
    riemannXi (1 - starRingEnd ℂ s) = starRingEnd ℂ (riemannXi s) := by
  rw [riemannXi_one_sub, riemannXi_conj]
private theorem argVariation_lineSeg_reflect {z₀ z₁ : ℂ}
    (hcont : ContinuousOn (fun u => riemannXi (lineSeg z₀ z₁ u)) (Set.Icc 0 1))
    (hne : ∀ u ∈ Set.Icc (0 : ℝ) 1, riemannXi (lineSeg z₀ z₁ u) ≠ 0) :
    argVariation 0 1
        (fun u => riemannXi (lineSeg (1 - starRingEnd ℂ z₀) (1 - starRingEnd ℂ z₁) u))
      = - argVariation 0 1 (fun u => riemannXi (lineSeg z₀ z₁ u)) := by
  rw [← argVariation_conj zero_le_one hcont hne]
  congr 1; funext u
  show riemannXi (lineSeg (1 - starRingEnd ℂ z₀) (1 - starRingEnd ℂ z₁) u)
      = starRingEnd ℂ (riemannXi (lineSeg z₀ z₁ u))
  rw [← riemannXi_reflect]
  congr 1
  simp only [lineSeg, map_add, map_sub, map_mul, Complex.conj_ofReal]
  ring
private theorem argVariation_riemannXi_real_eq_zero {z₀ z₁ : ℂ}
    (hpt : ∀ u ∈ Set.Icc (0 : ℝ) 1, ∃ x ∈ Icc (-1 : ℝ) 2, lineSeg z₀ z₁ u = (x : ℂ)) :
    argVariation 0 1 (fun u => riemannXi (lineSeg z₀ z₁ u)) = 0 := by
  have hsp : ∀ u ∈ Set.Icc (0 : ℝ) 1, riemannXi (lineSeg z₀ z₁ u) ∈ Complex.slitPlane := by
    intro u hu
    obtain ⟨x, hx, hxe⟩ := hpt u hu
    rw [hxe, Complex.mem_slitPlane_iff]; left
    exact (riemannXi_pos_of_mem_Icc hx).1
  have harg : ∀ {x : ℝ}, x ∈ Icc (-1 : ℝ) 2 → (riemannXi (x : ℂ)).arg = 0 := by
    intro x hx
    rw [Complex.arg_eq_zero_iff]
    exact ⟨(riemannXi_pos_of_mem_Icc hx).1.le, (riemannXi_pos_of_mem_Icc hx).2⟩
  obtain ⟨x0, hx0, hx0e⟩ := hpt 0 (by norm_num)
  obtain ⟨x1, hx1, hx1e⟩ := hpt 1 (by norm_num)
  rw [lineSeg_zero] at hx0e
  rw [lineSeg_one] at hx1e
  rw [argVariation_eq_arg_sub_arg zero_le_one (riemannXi_lineSeg_continuousOn z₀ z₁) hsp]
  simp only [lineSeg_one, lineSeg_zero]
  rw [hx0e, hx1e, harg hx0, harg hx1]
  ring
theorem argVariation_riemannXi_rectangle_eq_two_mul {T : ℝ} (hT : 0 < T)
    (hT' : ∀ s : ℂ, s.im = T → riemannZeta s ≠ 0) :
    rectangleArgVariation riemannXi (-1) (2 + I * (T : ℂ))
      = 2 * argVariationContourL riemannXi T := by
  have c0 : ((↑(-1 : ℂ).re : ℂ) + ↑(-1 : ℂ).im * I) = (-1 : ℂ) := Complex.re_add_im _
  have c1 : ((↑(2 + I * (T : ℂ)).re : ℂ) + ↑(-1 : ℂ).im * I) = 2 := by apply Complex.ext <;> simp
  have c2 : ((↑(2 + I * (T : ℂ)).re : ℂ) + ↑(2 + I * (T : ℂ)).im * I) = 2 + I * (T : ℂ) :=
    Complex.re_add_im _
  have c3 : ((↑(-1 : ℂ).re : ℂ) + ↑(2 + I * (T : ℂ)).im * I) = -1 + I * (T : ℂ) := by
    apply Complex.ext <;> simp
  have hne_right : ∀ u ∈ Set.Icc (0 : ℝ) 1, riemannXi (lineSeg 2 (2 + I * (T : ℂ)) u) ≠ 0 :=
    riemannXi_lineSeg_ne_zero_of_re_eq_two (by simp) (by simp)
  have hne_right' : ∀ u ∈ Set.Icc (0 : ℝ) 1, riemannXi (lineSeg (2 + I * (T : ℂ)) 2 u) ≠ 0 :=
    riemannXi_lineSeg_ne_zero_of_re_eq_two (by simp) (by simp)
  have hne_s2 : ∀ u ∈ Set.Icc (0 : ℝ) 1,
      riemannXi (lineSeg (2 + I * (T : ℂ)) (1 / 2 + I * (T : ℂ)) u) ≠ 0 :=
    riemannXi_lineSeg_ne_zero_of_im_eq_T hT.ne' hT' (by simp) (by simp)
  have hne_s2' : ∀ u ∈ Set.Icc (0 : ℝ) 1,
      riemannXi (lineSeg (1 / 2 + I * (T : ℂ)) (2 + I * (T : ℂ)) u) ≠ 0 :=
    riemannXi_lineSeg_ne_zero_of_im_eq_T hT.ne' hT' (by simp) (by simp)
  have hne_top : ∀ u ∈ Set.Icc (0 : ℝ) 1,
      riemannXi (lineSeg (2 + I * (T : ℂ)) (-1 + I * (T : ℂ)) u) ≠ 0 :=
    riemannXi_lineSeg_ne_zero_of_im_eq_T hT.ne' hT' (by simp) (by simp)
  have hne_bot : ∀ u ∈ Set.Icc (0 : ℝ) 1, riemannXi (lineSeg (-1) 2 u) ≠ 0 := by
    intro u hu
    have hpt : lineSeg (-1 : ℂ) 2 u = ((-1 + u * 3 : ℝ) : ℂ) := by
      simp only [lineSeg]; push_cast; ring
    rw [hpt]; intro h
    have hmem : (-1 + u * 3 : ℝ) ∈ Icc (-1 : ℝ) 2 := ⟨by nlinarith [hu.1], by nlinarith [hu.2]⟩
    have := (riemannXi_pos_of_mem_Icc hmem).1
    rw [h] at this; simp at this
  have hsplit_bot : argVariation 0 1 (fun u => riemannXi (lineSeg (-1) 2 u))
      = argVariation 0 1 (fun u => riemannXi (lineSeg (-1) (1 / 2) u))
        + argVariation 0 1 (fun u => riemannXi (lineSeg (1 / 2) 2 u)) := by
    have h := argVariation_lineSeg_split (f := riemannXi) (-1) 2 (t := 1 / 2)
      (by norm_num) (by norm_num) (riemannXi_lineSeg_continuousOn _ _) hne_bot
    rw [show lineSeg (-1 : ℂ) 2 (1 / 2) = (1 / 2 : ℂ) from by
      simp only [lineSeg]; push_cast; ring] at h
    exact h
  have hsplit_top :
      argVariation 0 1 (fun u => riemannXi (lineSeg (2 + I * (T : ℂ)) (-1 + I * (T : ℂ)) u))
      = argVariation 0 1 (fun u => riemannXi (lineSeg (2 + I * (T : ℂ)) (1 / 2 + I * (T : ℂ)) u))
        + argVariation 0 1
            (fun u => riemannXi (lineSeg (1 / 2 + I * (T : ℂ)) (-1 + I * (T : ℂ)) u)) := by
    have h := argVariation_lineSeg_split (f := riemannXi) (2 + I * (T : ℂ)) (-1 + I * (T : ℂ))
      (t := 1 / 2) (by norm_num) (by norm_num) (riemannXi_lineSeg_continuousOn _ _) hne_top
    rw [show lineSeg (2 + I * (T : ℂ)) (-1 + I * (T : ℂ)) (1 / 2) = (1 / 2 + I * (T : ℂ)) from by
      simp only [lineSeg]; push_cast; ring] at h
    exact h
  have hbot1 : argVariation 0 1 (fun u => riemannXi (lineSeg (-1) (1 / 2) u)) = 0 :=
    argVariation_riemannXi_real_eq_zero fun u hu =>
      ⟨-1 + u * (3 / 2), ⟨by nlinarith [hu.1], by nlinarith [hu.2]⟩, by
        simp only [lineSeg]; push_cast; ring⟩
  have hbot2 : argVariation 0 1 (fun u => riemannXi (lineSeg (1 / 2) 2 u)) = 0 :=
    argVariation_riemannXi_real_eq_zero fun u hu =>
      ⟨1 / 2 + u * (3 / 2), ⟨by nlinarith [hu.1], by nlinarith [hu.2]⟩, by
        simp only [lineSeg]; push_cast; ring⟩
  have hleft : argVariation 0 1 (fun u => riemannXi (lineSeg (-1 + I * (T : ℂ)) (-1) u))
      = argVariation 0 1 (fun u => riemannXi (lineSeg 2 (2 + I * (T : ℂ)) u)) := by
    have hreflect := argVariation_lineSeg_reflect (z₀ := 2 + I * (T : ℂ)) (z₁ := 2)
      (riemannXi_lineSeg_continuousOn _ _) hne_right'
    have hswap := argVariation_lineSeg_swap (f := riemannXi) 2 (2 + I * (T : ℂ))
      (riemannXi_lineSeg_continuousOn _ _) hne_right
    rw [show (1 - starRingEnd ℂ (2 + I * (T : ℂ))) = -1 + I * (T : ℂ) from by
          simp only [map_add, map_mul, Complex.conj_I, Complex.conj_ofReal, map_ofNat]; ring,
        show (1 - starRingEnd ℂ (2 : ℂ)) = (-1 : ℂ) from by
          simp only [map_ofNat]; norm_num] at hreflect
    rw [hreflect, hswap]; ring
  have hs2' :
      argVariation 0 1 (fun u => riemannXi (lineSeg (1 / 2 + I * (T : ℂ)) (-1 + I * (T : ℂ)) u))
      = argVariation 0 1 (fun u => riemannXi (lineSeg (2 + I * (T : ℂ)) (1 / 2 + I * (T : ℂ)) u))
      := by
    have hreflect := argVariation_lineSeg_reflect (z₀ := 1 / 2 + I * (T : ℂ))
      (z₁ := 2 + I * (T : ℂ)) (riemannXi_lineSeg_continuousOn _ _) hne_s2'
    have hswap := argVariation_lineSeg_swap (f := riemannXi) (2 + I * (T : ℂ))
      (1 / 2 + I * (T : ℂ)) (riemannXi_lineSeg_continuousOn _ _) hne_s2
    rw [show (1 - starRingEnd ℂ (1 / 2 + I * (T : ℂ))) = 1 / 2 + I * (T : ℂ) from by
          simp only [map_add, map_mul, map_div₀, map_one, Complex.conj_I, Complex.conj_ofReal,
            map_ofNat]; ring,
        show (1 - starRingEnd ℂ (2 + I * (T : ℂ))) = -1 + I * (T : ℂ) from by
          simp only [map_add, map_mul, Complex.conj_I, Complex.conj_ofReal, map_ofNat];
          ring] at hreflect
    rw [hreflect, hswap]; ring
  rw [rectangleArgVariation, c0, c1, c2, c3]
  simp only [argVariationContourL]
  rw [hsplit_bot, hsplit_top, hbot1, hbot2, hleft, hs2']
  ring
end
end CountPort36
section CountPort37
section
open ArithmeticFunction hiding log
open Nat hiding log
open Finset Topology
open BigOperators Filter Real Classical Asymptotics
open MeasureTheory intervalIntegral
open scoped ArithmeticFunction.Moebius
open scoped ArithmeticFunction.Omega Chebyshev
noncomputable abbrev nth_prime (n : ℕ) : ℕ :=
  Nat.nth Nat.Prime n
noncomputable def M (x : ℝ) : ℝ :=
  ∑ n ∈ Iic ⌊x⌋₊, (μ n : ℝ)
noncomputable abbrev nth_prime_gap (n : ℕ) : ℕ :=
  nth_prime (n + 1) - nth_prime n
open Classical in
noncomputable def first_gap (g : ℕ) : ℕ :=
  if h : ∃ n, nth_prime_gap n = g then
    nth_prime (Nat.find h)
  else 0
noncomputable def pi (x : ℝ) : ℝ :=
  Nat.primeCounting ⌊x⌋₊
noncomputable def pi_star (x : ℝ) : ℝ :=
  ∑' (k : ℕ), pi (x ^ (1 / (k + 1 : ℝ))) / (k + 1 : ℝ)
noncomputable def Li (x : ℝ) : ℝ := ∫ t in 2..x, 1 / log t
noncomputable def Eψ (x : ℝ) : ℝ := |ψ x - x| / x
noncomputable def admissible_bound (A B C R : ℝ) (x : ℝ) :=
  A * (log x / R) ^ B * exp (-C * (log x / R) ^ ((1 : ℝ) / (2 : ℝ)))
def Eψ.bound (ε x₀ : ℝ) : Prop := ∀ x ≥ x₀, Eψ x ≤ ε
noncomputable def Eπ (x : ℝ) : ℝ :=
  |pi x - Li x| / (x / log x)
noncomputable def Eπ_star (x : ℝ) : ℝ :=
  |pi_star x - Li x| / (x / log x)
def Eπ.bound (ε x₀ : ℝ) : Prop := ∀ x ≥ x₀, Eπ x ≤ ε
def Eπ_star.bound (ε x₀ : ℝ) : Prop :=
  ∀ x ≥ x₀, Eπ_star x ≤ ε
lemma admissible_bound.mono
    (A B C R : ℝ) (hA : 0 < A) (hB : 0 < B)
    (hC : 0 < C) (hR : 0 < R) :
    AntitoneOn (admissible_bound A B C R)
      (Set.Ici (exp (R * (2 * B / C) ^ 2))) := by
  intro a ha b _ hab
  simp only [admissible_bound, mul_assoc]
  have hua : (2 * B / C) ^ 2 ≤ log a / R := by
    rw [le_div_iff₀ hR, mul_comm ((2 * B / C) ^ 2), ← log_exp (R * (2 * B / C) ^ 2)]
    exact log_le_log (exp_pos _) (Set.mem_Ici.mp ha)
  have huab : log a / R ≤ log b / R :=
    div_le_div_of_nonneg_right
      (log_le_log ((exp_pos _).trans_le (Set.mem_Ici.mp ha)) hab) hR.le
  have hua₀ : 0 < log a / R :=
    lt_of_lt_of_le (by positivity) hua
  apply mul_le_mul_of_nonneg_left _ hA.le
  rw [rpow_def_of_pos (hua₀.trans_le huab), rpow_def_of_pos hua₀,
    ← exp_add, ← exp_add, exp_le_exp]
  let sa := (log a / R) ^ ((1 : ℝ) / 2)
  let sb := (log b / R) ^ ((1 : ℝ) / 2)
  rw [show log (log b / R) = 2 * log sb from by
      grind [log_rpow (hua₀.trans_le huab) ((1 : ℝ) / 2)],
    show log (log a / R) = 2 * log sa from by
      grind [log_rpow hua₀ ((1 : ℝ) / 2)]]
  have hsab : sa ≤ sb :=
    rpow_le_rpow (le_trans (by positivity) hua) huab (by positivity)
  have : 2 * B / C ≤ sa := by
    rw [show (2 * B / C : ℝ) = ((2 * B / C) ^ 2) ^ ((1 : ℝ) / 2) from by
      rw [← rpow_natCast _ 2, ← rpow_mul (by positivity)]
      norm_num [rpow_one]]
    exact rpow_le_rpow (by positivity) hua (by positivity)
  suffices h : AntitoneOn (fun t ↦ 2 * B * log t - C * t) (Set.Ici (2 * B / C)) by
    grind [h (Set.mem_Ici.mpr this) (Set.mem_Ici.mpr (this.trans hsab)) hsab]
  apply antitoneOn_of_deriv_nonpos (convex_Ici _)
  · exact ((continuousOn_const.mul (continuousOn_log.mono fun t ht ↦
        ne_of_gt ((div_pos (by positivity) hC).trans_le ht))).sub
      (continuousOn_const.mul continuousOn_id))
  · intro t ht
    rw [interior_Ici] at ht
    exact (((hasDerivAt_log ((div_pos (by positivity) hC).trans ht).ne').const_mul _).sub
      ((hasDerivAt_id t).const_mul C)).differentiableAt.differentiableWithinAt
  · intro t ht
    rw [interior_Ici] at ht
    have hdt : HasDerivAt (fun t ↦ 2 * B * log t - C * t) (2 * B * t⁻¹ - C * 1) t :=
      ((hasDerivAt_log ((div_pos (by positivity) hC).trans ht).ne').const_mul _).sub
        ((hasDerivAt_id t).const_mul C)
    rw [hdt.deriv, mul_one, sub_nonpos, ← div_eq_mul_inv,
      div_le_iff₀ ((div_pos (by positivity) hC).trans ht)]
    linarith [(div_lt_iff₀ hC).mp ht, mul_comm C t]
end
end CountPort37
section CountPort38
section
open Real
noncomputable def riemannZeta.zeroes : Set ℂ := {s : ℂ | riemannZeta s = 0}
noncomputable def riemannZeta.zeroes_rect (I J : Set ℝ) : Set ℂ :=
  {s : ℂ | s.re ∈ I ∧ s.im ∈ J ∧ s ∈ zeroes}
lemma riemannZeta.zeroes_rect_eq (I J : Set ℝ) :
    zeroes_rect I J = (Complex.re ⁻¹' I ∩ Complex.im ⁻¹' J) ∩ zeroes := by
  ext x; simp only [zeroes_rect, Set.mem_ofPred_eq, Set.mem_inter_iff,
    Set.mem_preimage, and_assoc]
section
lemma riemannZeta_differentiableOn_compl_one :
    DifferentiableOn ℂ riemannZeta ({1} : Set ℂ)ᶜ :=
  fun _ hs ↦ (differentiableAt_riemannZeta hs).differentiableWithinAt
lemma riemannZeta_analyticOn_compl_one :
    AnalyticOnNhd ℂ riemannZeta ({1} : Set ℂ)ᶜ :=
  riemannZeta_differentiableOn_compl_one.analyticOnNhd isOpen_compl_singleton
lemma riemannZeta.zeroes_codiscreteWithin_compl_one :
    zeroesᶜ ∈ Filter.codiscreteWithin ({1} : Set ℂ)ᶜ := by
  refine riemannZeta_analyticOn_compl_one.preimage_zero_mem_codiscreteWithin
    ?_ ?_ ?_ (x := 2)
  · exact riemannZeta_ne_zero_of_one_le_re Nat.one_le_ofNat
  · exact Set.mem_compl_singleton_iff.2 (OfNat.one_ne_ofNat 2).symm
  · refine isConnected_compl_singleton_of_one_lt_rank ?_ 1
    rw [Complex.rank_real_complex]
    exact Cardinal.one_lt_two
lemma riemannZeta.zeroes_on_Compact_finite {S : Set ℂ} (hS1 : IsCompact S) (hS2 : 1 ∉ S) :
    (S ∩ zeroes : Set ℂ).Finite := by
  have sub := Set.subset_compl_singleton_iff.mpr hS2
  refine IsCompact.finite ?_ ?_
  · have := riemannZeta_analyticOn_compl_one.continuousOn.mono sub
      |>.preimage_isClosed_of_isClosed (t := {0}) hS1.isClosed isClosed_singleton
    exact hS1.of_isClosed_subset this Set.inter_subset_left
  · rw [Set.inter_comm]
    exact IsDiscrete.mono (isDiscrete_of_codiscreteWithin zeroes_codiscreteWithin_compl_one)
      <| Set.inter_subset_inter_right zeroes sub
open Topology in
lemma riemannZeta_eventually_ne_zero :
    ∀ᶠ s in 𝓝[≠] 1, riemannZeta s ≠ 0 := by
  filter_upwards [riemannZeta_residue_one.eventually_ne (zero_ne_one' ℂ).symm,
    eventually_nhdsWithin_of_forall (fun _ hs ↦ hs)] with s hmul hne
  intro hzero
  rw [hzero, mul_zero] at hmul
  exact false_of_ne hmul
lemma riemannZeta_no_zeroes_near_one : ∃ ε, ε > 0 ∧ ∀ s,
    s ∈ Metric.ball 1 ε → riemannZeta s ≠ 0 := by
  obtain ⟨ε, hε_pos, hball⟩ := Metric.eventually_nhds_iff.1 <|
      eventually_nhdsWithin_iff.1 riemannZeta_eventually_ne_zero
  refine ⟨ε, hε_pos, fun s hs hzero ↦ ?_⟩
  by_cases h : s = 1
  · exact riemannZeta_one_ne_zero (h ▸ hzero)
  · exact hball (Metric.mem_ball.1 hs) (Set.mem_compl_singleton_iff.2 h) hzero
lemma riemannZeta.zeroes_on_Compact_finite' {S : Set ℂ} (hS1 : IsCompact S) :
    (S ∩ zeroes : Set ℂ).Finite := by
  obtain ⟨ε, hε, hball⟩ := riemannZeta_no_zeroes_near_one
  have : S ∩ zeroes ⊆ (S ∩ (Metric.ball 1 ε)ᶜ) ∩ zeroes :=
    fun s ⟨hs, hz⟩ ↦ ⟨⟨hs, fun hmem ↦ hball s hmem hz⟩, hz⟩
  refine Set.Finite.subset (zeroes_on_Compact_finite ?_ ?_) this
  · exact hS1.inter_right Metric.isOpen_ball.isClosed_compl
  · exact fun ⟨_, h⟩ ↦ h (Metric.mem_ball_self hε)
end
noncomputable def riemannZeta.order (s : ℂ) : ℤ := (meromorphicOrderAt (riemannZeta) s).untopD 0
noncomputable def riemannZeta.zeroes_sum {α : Type*} [RCLike α]
    (I J : Set ℝ) (f : ℂ → α) : α :=
  ∑' ρ : riemannZeta.zeroes_rect I J, (f ρ) * (riemannZeta.order ρ)
noncomputable def riemannZeta.N (T : ℝ) : ℝ := zeroes_sum Set.univ (Set.Ioo 0 T) (fun _ ↦ 1)
noncomputable def riemannZeta.N' (σ T : ℝ) : ℝ := zeroes_sum (Set.Ioo σ 1) (Set.Ioo 0 T) 1
structure zero_density_bound where
  T₀ : ℝ
  σ_range : Set ℝ
  c₁ : ℝ → ℝ
  c₂ : ℝ → ℝ
  p : ℝ → ℝ
  q : ℝ → ℝ
  bound : ∀ T ≥ T₀, ∀ σ ∈ σ_range,
      riemannZeta.N' σ T ≤ (c₁ σ) * T ^ (p σ) * (log T) ^ (q σ) + (c₂ σ) * (log T) ^ 2
noncomputable def zero_density_bound.N {ZDB : zero_density_bound} (σ T : ℝ) : ℝ :=
  (ZDB.c₁ σ) * T ^ (ZDB.p σ) * (log T) ^ (ZDB.q σ) + (ZDB.c₂ σ) * (log T) ^ 2
end
end CountPort38
section CountPort39
public section
open scoped Complex ComplexConjugate
set_option backward.isDefEq.respectTransparency false in
theorem intervalIntegral_conj {f : ℝ → ℂ} {a b : ℝ} :
    ∫ (x : ℝ) in a..b, conj (f x) = conj (∫ (x : ℝ) in a..b, f x) := by
  rw [intervalIntegral.intervalIntegral_eq_integral_uIoc, integral_conj, ← RCLike.conj_smul,
    ← intervalIntegral.intervalIntegral_eq_integral_uIoc]
end
end CountPort39
section CountPort40
public section
open scoped BigOperators
namespace Real
lemma pow_div_one_sub_le_two_mul {r : ℝ} (hr : 0 ≤ r) (hrhalf : r ≤ 1 / 2) (m : ℕ) :
    r ^ (m + 1) / (1 - r) ≤ 2 * r ^ (m + 1) := by
  have hpow : 0 ≤ r ^ (m + 1) := pow_nonneg hr _
  have hhalf' : (1 / 2 : ℝ) ≤ 1 - r := by linarith
  calc
    r ^ (m + 1) / (1 - r) ≤ r ^ (m + 1) / (1 / 2 : ℝ) := by
      exact div_le_div_of_nonneg_left hpow (by positivity) hhalf'
    _ = 2 * r ^ (m + 1) := by ring
end Real
namespace Complex
open scoped BigOperators in
lemma neg_log_one_sub_eq_tsum {z : ℂ} (hz : ‖z‖ < 1) :
    -log (1 - z) = ∑' n : ℕ, z ^ (n + 1) / (n + 1) := by
  have h := hasSum_taylorSeries_neg_log hz
  rw [← h.tsum_eq, h.summable.tsum_eq_zero_add]
  simp only [pow_zero, Nat.cast_zero, div_zero, zero_add, Nat.cast_add, Nat.cast_one]
noncomputable
def partialLogSum (m : ℕ) (z : ℂ) : ℂ :=
  -logTaylor (m + 1) (-z)
@[simp]
lemma partialLogSum_zero (z : ℂ) : partialLogSum 0 z = 0 := by
  simp [partialLogSum, logTaylor_succ, logTaylor_zero]
@[simp]
lemma partialLogSum_at_zero (m : ℕ) : partialLogSum m 0 = 0 := by
  simp [partialLogSum, logTaylor_at_zero]
lemma logTaylor_succ_neg (n : ℕ) (z : ℂ) :
    logTaylor (n + 1) (-z) = logTaylor n (-z) - z ^ n / n := by
  rw [logTaylor_succ, Pi.add_apply]
  have hsign : (-1 : ℂ) ^ (n + 1) * (-z) ^ n = -z ^ n := by
    have hzpow : (-z) ^ n = (((-1 : ℂ) * z) ^ n) := by simp
    rw [hzpow, mul_pow, ← mul_assoc, ← pow_add]
    have hpow : (-1 : ℂ) ^ (n + 1 + n) = (-1 : ℂ) := by
      rw [show n + 1 + n = 2 * n + 1 by omega, pow_add, pow_mul]
      norm_num
    rw [hpow]
    ring
  rw [show (-1 : ℂ) ^ (n + 1) * (-z) ^ n / n = -(z ^ n / n) by
    rw [hsign]
    ring]
  abel
lemma logTaylor_neg_eq_neg_sum (m : ℕ) (z : ℂ) :
    logTaylor (m + 1) (-z) = -∑ k ∈ Finset.range m, z ^ (k + 1) / (k + 1) := by
  induction m with
  | zero =>
      simp [logTaylor_succ, logTaylor_zero]
  | succ m hm =>
      rw [logTaylor_succ_neg, hm, Finset.sum_range_succ]
      have hcast : ((m + 1 : ℕ) : ℂ) = (1 + (m : ℂ)) := by
        simp [Nat.cast_add, Nat.cast_one, add_comm]
      rw [hcast]
      ring_nf
lemma partialLogSum_eq_sum (m : ℕ) (z : ℂ) :
    partialLogSum m z = ∑ k ∈ Finset.range m, z ^ (k + 1) / (k + 1) := by
  simpa [partialLogSum] using congrArg Neg.neg (logTaylor_neg_eq_neg_sum m z)
lemma hasDerivAt_partialLogSum (m : ℕ) (z : ℂ) :
    HasDerivAt (partialLogSum m) (∑ j ∈ Finset.range m, z ^ j) z := by
  cases m with
  | zero =>
      have hzero : partialLogSum 0 = fun _ : ℂ ↦ (0 : ℂ) := by
        funext w
        exact partialLogSum_zero w
      simpa [hzero] using (hasDerivAt_const z (c := (0 : ℂ)))
  | succ m =>
      have hsum :
          (∑ j ∈ Finset.range (m + 1), z ^ j) =
            ∑ j ∈ Finset.range (m + 1), (-1) ^ j * (-z) ^ j := by
        refine Finset.sum_congr rfl ?_
        intro j hj
        symm
        calc
          (-1 : ℂ) ^ j * (-z) ^ j = (-1 : ℂ) ^ j * (((-1 : ℂ) * z) ^ j) := by simp
          _ = ((-1 : ℂ) ^ j * (-1 : ℂ) ^ j) * z ^ j := by rw [mul_pow]; ring
          _ = z ^ j := by
                rw [← pow_add, show j + j = 2 * j by omega, pow_mul]
                norm_num
      rw [hsum]
      simpa [partialLogSum] using!
        (((hasDerivAt_logTaylor (m + 1) (-z)).comp z (hasDerivAt_neg z)).neg)
lemma differentiable_partialLogSum (m : ℕ) :
    Differentiable ℂ (fun z : ℂ => partialLogSum m z) := by
  intro z
  exact (hasDerivAt_partialLogSum m z).differentiableAt
noncomputable
def logTail (m : ℕ) (z : ℂ) : ℂ :=
  ∑' k, z ^ (m + 1 + k) / (m + 1 + k)
lemma summable_logTail {z : ℂ} (hz : ‖z‖ < 1) (m : ℕ) :
    Summable (fun k => z ^ (m + 1 + k) / ((m + 1 + k) : ℂ)) := by
  have h_geom : Summable (fun k : ℕ => ‖z‖ ^ k) :=
    summable_geometric_of_lt_one (norm_nonneg z) hz
  refine Summable.of_norm_bounded (g := fun k => ‖z‖ ^ k) h_geom ?_
  intro k
  rw [norm_div, norm_pow]
  have h1 : (1 : ℝ) ≤ (m + 1 + k : ℝ) := by
    have : (0 : ℝ) ≤ (m + k : ℝ) := by positivity
    nlinarith
  have hnorm : ‖(↑m + 1 + ↑k : ℂ)‖ = (m + 1 + k : ℝ) := by
    simpa [Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm] using
      (Complex.norm_natCast (m + 1 + k))
  rw [hnorm]
  calc
    ‖z‖ ^ (m + 1 + k) / (m + 1 + k : ℝ) ≤ ‖z‖ ^ (m + 1 + k) := by
      exact div_le_self (pow_nonneg (norm_nonneg z) _) h1
    _ = ‖z‖ ^ (m + 1) * ‖z‖ ^ k := by rw [pow_add]
    _ ≤ 1 * ‖z‖ ^ k := by
          refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg (norm_nonneg z) k)
          exact pow_le_one₀ (norm_nonneg z) (le_of_lt hz)
    _ = ‖z‖ ^ k := one_mul _
lemma norm_logTail_le {z : ℂ} (hz : ‖z‖ < 1) (m : ℕ) :
    ‖logTail m z‖ ≤ ‖z‖ ^ (m + 1) / (1 - ‖z‖) := by
  dsimp only [logTail]
  have h_rhs_summable : Summable (fun k => ‖z‖ ^ (m + 1 + k)) := by
    simpa [pow_add] using
      (summable_geometric_of_lt_one (norm_nonneg z) hz).mul_left (‖z‖ ^ (m + 1))
  have h_norm_summable : Summable (fun k => ‖z ^ (m + 1 + k) / ((m + 1 + k) : ℂ)‖) := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) ?_ h_rhs_summable
    intro k
    rw [norm_div, norm_pow]
    have hnorm : ‖(↑m + 1 + ↑k : ℂ)‖ = (m + 1 + k : ℝ) := by
      simpa [Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm] using
        (Complex.norm_natCast (m + 1 + k))
    rw [hnorm]
    have hm : 1 ≤ (m + 1 + k : ℝ) := by
      have : (0 : ℝ) ≤ (m + k : ℝ) := by positivity
      nlinarith
    exact div_le_self (pow_nonneg (norm_nonneg z) _) hm
  calc
    ‖∑' k, z ^ (m + 1 + k) / ((m + 1 + k) : ℂ)‖
        ≤ ∑' k, ‖z ^ (m + 1 + k) / ((m + 1 + k) : ℂ)‖ :=
          norm_tsum_le_tsum_norm h_norm_summable
    _ ≤ ∑' k, ‖z‖ ^ (m + 1 + k) := by
          refine h_norm_summable.tsum_le_tsum ?_ h_rhs_summable
          intro k
          rw [norm_div, norm_pow]
          have hm : 1 ≤ (m + 1 + k : ℝ) := by
            have : (0 : ℝ) ≤ (m + k : ℝ) := by positivity
            nlinarith
          have hnorm : ‖(↑m + 1 + ↑k : ℂ)‖ = (m + 1 + k : ℝ) := by
            simpa [Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm] using
              (Complex.norm_natCast (m + 1 + k))
          rw [hnorm]
          exact div_le_self (pow_nonneg (norm_nonneg z) _) hm
    _ = ‖z‖ ^ (m + 1) / (1 - ‖z‖) := by
          have h_eq :
              (fun k => ‖z‖ ^ (m + 1 + k)) = fun k => ‖z‖ ^ (m + 1) * ‖z‖ ^ k := by
            ext k
            rw [pow_add]
          rw [h_eq, tsum_mul_left]
          have h_geom := hasSum_geometric_of_lt_one (norm_nonneg z) hz
          rw [h_geom.tsum_eq, div_eq_mul_inv]
lemma norm_logTail_le_two_mul_norm_pow {z : ℂ} (hz : ‖z‖ < 1) (hzhalf : ‖z‖ ≤ 1 / 2) (m : ℕ) :
    ‖logTail m z‖ ≤ 2 * ‖z‖ ^ (m + 1) :=
  (norm_logTail_le hz m).trans (Real.pow_div_one_sub_le_two_mul (norm_nonneg z) hzhalf m)
lemma neg_log_one_sub_eq_partialLogSum_add_logTail {z : ℂ} (hz : ‖z‖ < 1) (m : ℕ) :
    -log (1 - z) = partialLogSum m z + logTail m z := by
  let f : ℕ → ℂ := fun k ↦ z ^ (k + 1) / ((k : ℂ) + 1)
  have h_summable : Summable f := by
    simpa [f, Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm] using
      (summable_logTail hz 0)
  have h_decomp := h_summable.sum_add_tsum_nat_add m
  rw [neg_log_one_sub_eq_tsum hz, partialLogSum_eq_sum, ← h_decomp]
  congr 1
  dsimp only [logTail]
  refine tsum_congr fun k ↦ ?_
  simp only [f, Nat.cast_add]
  ring_nf
end Complex
end
end CountPort40
section CountPort41
public section
noncomputable section
namespace Complex
variable {z : ℂ}
@[bound]
theorem neg_norm_le_re (z : ℂ) : -‖z‖ ≤ z.re :=
  neg_le_of_abs_le (abs_re_le_norm z)
end Complex
end
end
end CountPort41
section CountPort42
public section
noncomputable section
open scoped BigOperators
open Set
namespace Complex
def weierstrassFactor (m : ℕ) (z : ℂ) : ℂ :=
  (1 - z) * exp (partialLogSum m z)
@[simp]
lemma weierstrassFactor_zero (z : ℂ) : weierstrassFactor 0 z = 1 - z := by
  simp [weierstrassFactor]
@[simp]
lemma weierstrassFactor_at_zero (m : ℕ) : weierstrassFactor m 0 = 1 := by
  simp [weierstrassFactor, partialLogSum_at_zero]
@[simp]
lemma weierstrassFactor_at_one (m : ℕ) : weierstrassFactor m 1 = 0 := by
  simp [weierstrassFactor]
lemma differentiable_weierstrassFactor (m : ℕ) :
    Differentiable ℂ (fun z : ℂ => weierstrassFactor m z) := by
  simpa [weierstrassFactor] using!
    ((differentiable_const (c := (1 : ℂ))).sub differentiable_id).mul
      (differentiable_exp.comp (differentiable_partialLogSum m))
lemma hasDerivAt_weierstrassFactor_at_one (m : ℕ) :
    HasDerivAt (weierstrassFactor m) (-Complex.exp (partialLogSum m 1)) 1 := by
  have hsub : HasDerivAt (fun z : ℂ => 1 - z) (-1) 1 := by
    simpa using! (hasDerivAt_const (1 : ℂ) (c := (1 : ℂ))).sub (hasDerivAt_id 1)
  have hexp :
      HasDerivAt (fun z : ℂ => Complex.exp (partialLogSum m z))
        ((∑ j ∈ Finset.range m, (1 : ℂ) ^ j) * Complex.exp (partialLogSum m 1)) 1 := by
    simpa [mul_comm] using!
      (Complex.hasDerivAt_exp (partialLogSum m 1)).comp 1 (hasDerivAt_partialLogSum m 1)
  simpa [weierstrassFactor] using! hsub.mul hexp
@[simp]
lemma deriv_weierstrassFactor_at_one (m : ℕ) :
    deriv (weierstrassFactor m) 1 = -Complex.exp (partialLogSum m 1) :=
  (hasDerivAt_weierstrassFactor_at_one m).deriv
lemma hasDerivAt_weierstrassFactor_div_at_self (m : ℕ) {a : ℂ} (ha : a ≠ 0) :
    HasDerivAt (fun z : ℂ ↦ weierstrassFactor m (z / a))
      ((-Complex.exp (partialLogSum m 1)) / a) a := by
  have hcomp :
      HasDerivAt ((weierstrassFactor m) ∘ fun z : ℂ ↦ z / a)
        ((-Complex.exp (partialLogSum m 1)) * (1 / a)) a :=
    HasDerivAt.comp (x := a) (h := fun z : ℂ ↦ z / a) (h₂ := weierstrassFactor m)
      (by simpa [ha] using hasDerivAt_weierstrassFactor_at_one m)
      ((hasDerivAt_id a).div_const a)
  simpa [Function.comp, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using! hcomp
@[simp]
lemma deriv_weierstrassFactor_div_at_self (m : ℕ) {a : ℂ} (ha : a ≠ 0) :
    deriv (fun z : ℂ ↦ weierstrassFactor m (z / a)) a =
      (-Complex.exp (partialLogSum m 1)) / a :=
  (hasDerivAt_weierstrassFactor_div_at_self m ha).deriv
lemma weierstrassFactor_eq_exp_neg_tail (m : ℕ) {z : ℂ} (hz : ‖z‖ < 1) (hz1 : z ≠ 1) :
    weierstrassFactor m z = exp (-logTail m z) := by
  unfold weierstrassFactor
  have hz_ne_1 : 1 - z ≠ 0 := sub_ne_zero.mpr hz1.symm
  rw [← exp_log hz_ne_1, ← Complex.exp_add]
  have hsum : log (1 - z) + partialLogSum m z = -logTail m z := by
    have hdecomp := neg_log_one_sub_eq_partialLogSum_add_logTail hz m
    calc
      log (1 - z) + partialLogSum m z
          = log (1 - z) + (partialLogSum m z + logTail m z) - logTail m z := by ring
      _ = log (1 - z) + (-log (1 - z)) - logTail m z := by rw [hdecomp]
      _ = -logTail m z := by ring
  simp [hsum]
theorem weierstrassFactor_sub_one_pow_bound {m : ℕ} {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) :
    ‖weierstrassFactor m z - 1‖ ≤ 4 * ‖z‖ ^ (m + 1) := by
  by_cases hm : m = 0
  · subst hm
    have hmain : ‖(1 - z) - 1‖ ≤ 4 * ‖z‖ ^ 1 := by
      have h : (1 - z) - 1 = -z := by ring
      calc
        ‖(1 - z) - 1‖ = ‖-z‖ := by simp [h]
        _ = ‖z‖ := norm_neg z
        _ = ‖z‖ ^ 1 := by simp
        _ ≤ 4 * ‖z‖ ^ 1 := by nlinarith [pow_nonneg (norm_nonneg z) 1]
    simpa [weierstrassFactor] using hmain
  · have hz_lt : ‖z‖ < 1 := lt_of_le_of_lt hz (by norm_num)
    by_cases hz1 : z = 1
    · exfalso; rw [hz1] at hz; norm_num at hz
    have h_eq : weierstrassFactor m z = exp (-logTail m z) :=
      weierstrassFactor_eq_exp_neg_tail m hz_lt hz1
    rw [h_eq]
    have h_tail_bound := norm_logTail_le_two_mul_norm_pow hz_lt hz m
    have hw_le_one : ‖-logTail m z‖ ≤ 1 := by
      simp only [norm_neg]
      have : ‖logTail m z‖ ≤ 1 := by
        have hm_pos : 0 < m := Nat.pos_of_ne_zero hm
        have h2 : 2 ≤ m + 1 := by
          exact Nat.succ_le_succ (Nat.succ_le_iff.2 hm_pos)
        have hpow : (‖z‖ ^ (m + 1)) ≤ (‖z‖ ^ 2) := by
          have hz1' : ‖z‖ ≤ 1 := by nlinarith [hz]
          have hz0' : 0 ≤ ‖z‖ := norm_nonneg z
          exact pow_le_pow_of_le_one hz0' hz1' h2
        have hmul : 2 * ‖z‖ ^ (m + 1) ≤ 2 * ‖z‖ ^ 2 := by gcongr
        have hsq : 2 * ‖z‖ ^ 2 ≤ 1 := by
          have hz0 : 0 ≤ ‖z‖ := norm_nonneg z
          have hz_sq : ‖z‖ ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := pow_le_pow_left₀ hz0 hz 2
          nlinarith
        exact (h_tail_bound.trans hmul).trans hsq
      linarith
    have h_exp_sub_one : ‖exp (-logTail m z) - 1‖ ≤ 2 * ‖-logTail m z‖ :=
      Complex.norm_exp_sub_one_le hw_le_one
    simp only [norm_neg] at h_exp_sub_one
    calc
      ‖exp (-logTail m z) - 1‖ ≤ 2 * ‖logTail m z‖ := h_exp_sub_one
      _ ≤ 2 * (2 * ‖z‖ ^ (m + 1)) := by gcongr
      _ = 4 * ‖z‖ ^ (m + 1) := by ring
private lemma eventually_le_norm_div_two_of_summable_inv_pow {m : ℕ} {a : ℕ → ℂ}
    (h_sum : Summable (fun n : ℕ => ‖a n‖⁻¹ ^ (m + 1))) (h_nonzero : ∀ n, a n ≠ 0) :
    ∀ R ≥ 0, ∀ᶠ n in Filter.atTop, R ≤ ‖a n‖ / 2 := by
  intro R hR
  by_cases hR0 : R = 0
  · subst hR0
    exact Filter.Eventually.of_forall fun _ => by positivity
  have hRpos : 0 < R := lt_of_le_of_ne hR (by simpa [eq_comm] using hR0)
  have htend : Filter.Tendsto (fun n : ℕ => ‖a n‖⁻¹ ^ (m + 1)) Filter.atTop (nhds (0 : ℝ)) := by
    simpa [Nat.cofinite_eq_atTop] using h_sum.tendsto_cofinite_zero
  have hεpos : 0 < (1 / (2 * R) : ℝ) ^ (m + 1) := by
    have : 0 < (1 / (2 * R) : ℝ) := by
      have : 0 < (2 * R : ℝ) := by positivity
      exact one_div_pos.mpr this
    exact pow_pos this _
  filter_upwards [htend.eventually (eventually_lt_nhds hεpos)] with n hn
  by_contra h
  have hlt : ‖a n‖ / 2 < R := lt_of_not_ge h
  have hle : ‖a n‖ ≤ 2 * R := by nlinarith
  have hanorm_pos : 0 < ‖a n‖ := norm_pos_iff.mpr (h_nonzero n)
  have hinv : (1 / (2 * R : ℝ)) ≤ ‖a n‖⁻¹ := by
    simpa [one_div] using (one_div_le_one_div_of_le hanorm_pos hle)
  have hpow :
      (1 / (2 * R : ℝ)) ^ (m + 1) ≤ ‖a n‖⁻¹ ^ (m + 1) :=
    pow_le_pow_left₀ (by positivity) hinv _
  exact (not_lt_of_ge hpow) hn
private lemma summable_scaled_bound_of_summable_inv_pow {m : ℕ} {a : ℕ → ℂ}
    (h_sum : Summable (fun n : ℕ => ‖a n‖⁻¹ ^ (m + 1))) :
    ∀ R ≥ 0, Summable (fun n : ℕ => 4 * R ^ (m + 1) / ‖a n‖ ^ (m + 1)) := by
  intro R _hR
  simpa [div_eq_mul_inv, inv_pow, mul_assoc, mul_left_comm, mul_comm] using
    h_sum.mul_left (4 * R ^ (m + 1))
lemma continuousOn_weierstrassFactor_div (m : ℕ) (a : ℂ) (s : Set ℂ) :
    ContinuousOn (fun z : ℂ ↦ weierstrassFactor m (z / a)) s := by
  simpa using! (differentiable_weierstrassFactor m).continuous.continuousOn.comp
    (continuous_id.div_const a).continuousOn (mapsTo_univ (fun z : ℂ ↦ z / a) s)
lemma norm_weierstrassFactor_div_sub_one_le_pow_div (m : ℕ) {a z : ℂ}
    (hza : ‖z‖ ≤ ‖a‖ / 2) :
    ‖weierstrassFactor m (z / a) - 1‖ ≤ 4 * ‖z‖ ^ (m + 1) / ‖a‖ ^ (m + 1) := by
  by_cases ha : a = 0
  · have hz : z = 0 := by
      apply norm_eq_zero.mp
      rw [ha] at hza
      simpa using hza
    subst z
    simp [ha]
  · have ha' : 0 < ‖a‖ := norm_pos_iff.mpr ha
    have hza' : ‖z / a‖ ≤ 1 / 2 := by
      rw [Complex.norm_div, div_le_iff₀ ha']
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hza
    have hbase := weierstrassFactor_sub_one_pow_bound (m := m) (z := z / a) hza'
    calc
      ‖weierstrassFactor m (z / a) - 1‖ ≤ ‖z‖ ^ (m + 1) / ‖a‖ ^ (m + 1) * 4 := by
        simpa [Complex.norm_div, div_pow, mul_comm, mul_left_comm, mul_assoc] using hbase
      _ = 4 * ‖z‖ ^ (m + 1) / ‖a‖ ^ (m + 1) := by ring
lemma hasProdUniformlyOn_weierstrassFactor_div_of_bound {K : Set ℂ} (hK : IsCompact K)
    {m : ℕ → ℕ} {a : ℕ → ℂ} {R : ℝ}
    (hR : ∀ z ∈ K, ‖z‖ ≤ R) (hsmall : ∀ᶠ n in Filter.atTop, R ≤ ‖a n‖ / 2)
    (hsumm : Summable (fun n : ℕ ↦ 4 * R ^ (m n + 1) / ‖a n‖ ^ (m n + 1))) :
    HasProdUniformlyOn (fun n z ↦ weierstrassFactor (m n) (z / a n))
      (fun z ↦ ∏' n, weierstrassFactor (m n) (z / a n)) K := by
  have hbound :
      ∀ᶠ n in Filter.atTop,
        ∀ z ∈ K,
          ‖weierstrassFactor (m n) (z / a n) - 1‖ ≤ 4 * R ^ (m n + 1) / ‖a n‖ ^ (m n + 1) := by
    filter_upwards [hsmall] with n hn z hz
    refine (norm_weierstrassFactor_div_sub_one_le_pow_div (m := m n) ?_).trans ?_
    · exact (hR z hz).trans hn
    · have hpow : ‖z‖ ^ (m n + 1) ≤ R ^ (m n + 1) :=
        pow_le_pow_left₀ (norm_nonneg z) (hR z hz) (m n + 1)
      refine div_le_div_of_nonneg_right ?_ (pow_nonneg (norm_nonneg (a n)) _)
      exact mul_le_mul_of_nonneg_left hpow (by positivity)
  have hcts :
      ∀ n, ContinuousOn (fun z ↦ weierstrassFactor (m n) (z / a n) - 1) K := by
    intro n
    exact (continuousOn_weierstrassFactor_div (m n) (a n) K).fun_sub continuousOn_const
  simpa using hsumm.hasProdUniformlyOn_nat_one_add (K := K)
    (f := fun n z ↦ weierstrassFactor (m n) (z / a n) - 1) hK hbound hcts
lemma hasProdLocallyUniformlyOn_weierstrassFactor_div {s : Set ℂ} (hs : IsOpen s)
    {m : ℕ → ℕ} {a : ℕ → ℂ}
    (hsmall : ∀ R ≥ 0, ∀ᶠ n in Filter.atTop, R ≤ ‖a n‖ / 2)
    (hsumm : ∀ R ≥ 0, Summable (fun n : ℕ ↦ 4 * R ^ (m n + 1) / ‖a n‖ ^ (m n + 1))) :
    HasProdLocallyUniformlyOn (fun n z ↦ weierstrassFactor (m n) (z / a n))
      (fun z ↦ ∏' n, weierstrassFactor (m n) (z / a n)) s := by
  apply hasProdLocallyUniformlyOn_of_forall_compact hs
  intro K hKs hK
  obtain ⟨R, hR⟩ : ∃ R, ∀ z ∈ K, ‖z‖ ≤ R := by
    by_cases hKe : K.Nonempty
    · obtain ⟨z, hzK, hzmax⟩ := hK.exists_isMaxOn hKe continuous_norm.continuousOn
      exact ⟨‖z‖, fun w hw ↦ (isMaxOn_iff.mp hzmax) w hw⟩
    · exact ⟨0, fun z hz ↦ False.elim <| hKe ⟨z, hz⟩⟩
  let R' := max R 0
  have hR'0 : 0 ≤ R' := le_max_right _ _
  have hR' : ∀ z ∈ K, ‖z‖ ≤ R' := by
    intro z hz
    exact (hR z hz).trans (le_max_left _ _)
  exact hasProdUniformlyOn_weierstrassFactor_div_of_bound hK hR'
    (hsmall R' hR'0) (hsumm R' hR'0)
lemma hasProdLocallyUniformlyOn_weierstrassFactor_div_of_summable_inv_pow {m : ℕ} {a : ℕ → ℂ}
    (h_sum : Summable (fun n : ℕ => ‖a n‖⁻¹ ^ (m + 1))) (h_nonzero : ∀ n, a n ≠ 0) :
    HasProdLocallyUniformlyOn (fun n z ↦ weierstrassFactor m (z / a n))
      (fun z ↦ ∏' n, weierstrassFactor m (z / a n)) Set.univ := by
  simpa using
    hasProdLocallyUniformlyOn_weierstrassFactor_div (s := (Set.univ : Set ℂ)) isOpen_univ
      (m := fun _ => m) (a := a)
      (eventually_le_norm_div_two_of_summable_inv_pow h_sum h_nonzero)
      (summable_scaled_bound_of_summable_inv_pow h_sum)
end Complex
end
end
end CountPort42
section CountPort43
section
noncomputable section
open Filter Topology
namespace Complex
def canonicalProduct (m : ℕ) (a : ℕ → ℂ) (z : ℂ) : ℂ :=
  ∏' n : ℕ, weierstrassFactor m (z / a n)
@[simp] theorem canonicalProduct_def (m : ℕ) (a : ℕ → ℂ) (z : ℂ) :
    canonicalProduct m a z = ∏' n : ℕ, weierstrassFactor m (z / a n) :=
  rfl
theorem hasProdLocallyUniformlyOn_canonicalProduct {m : ℕ} {a : ℕ → ℂ}
    (h_sum : Summable (fun n : ℕ => ‖a n‖⁻¹ ^ (m + 1))) (h_nonzero : ∀ n, a n ≠ 0) :
    HasProdLocallyUniformlyOn (fun n z ↦ weierstrassFactor m (z / a n))
      (canonicalProduct m a) Set.univ := by
  simpa [canonicalProduct] using!
    hasProdLocallyUniformlyOn_weierstrassFactor_div_of_summable_inv_pow
      (m := m) (a := a) h_sum h_nonzero
theorem multipliableLocallyUniformlyOn_canonicalProduct {m : ℕ} {a : ℕ → ℂ}
    (h_sum : Summable (fun n : ℕ => ‖a n‖⁻¹ ^ (m + 1))) (h_nonzero : ∀ n, a n ≠ 0) :
    MultipliableLocallyUniformlyOn (fun n z ↦ weierstrassFactor m (z / a n))
      (Set.univ : Set ℂ) := by
  simpa using
    (hasProdLocallyUniformlyOn_canonicalProduct h_sum h_nonzero).multipliableLocallyUniformlyOn
@[simp]
theorem canonicalProduct_apply_eq_zero {m : ℕ} {a : ℕ → ℂ}
    (h_sum : Summable (fun n : ℕ => ‖a n‖⁻¹ ^ (m + 1))) (h_nonzero : ∀ n, a n ≠ 0) (n : ℕ) :
    canonicalProduct m a (a n) = 0 := by
  let f : ℕ → ℂ := fun k ↦ weierstrassFactor m (a n / a k)
  have hmult : Multipliable f :=
    (multipliableLocallyUniformlyOn_canonicalProduct h_sum h_nonzero).multipliable (by simp)
  have htend :
      Tendsto (fun N : ℕ ↦ ∏ k ∈ Finset.range N, f k) Filter.atTop
        (𝓝 (canonicalProduct m a (a n))) := by
    simpa [f, canonicalProduct] using hmult.hasProd.tendsto_prod_nat
  have hzero :
      (fun N : ℕ ↦ ∏ k ∈ Finset.range N, f k) =ᶠ[Filter.atTop] fun _ ↦ (0 : ℂ) := by
    refine Filter.eventually_atTop.2 ⟨n + 1, fun N hN ↦ ?_⟩
    have hnN : n ∈ Finset.range N := Finset.mem_range.mpr <| lt_of_lt_of_le (Nat.lt_succ_self n) hN
    apply Finset.prod_eq_zero hnN
    simp [f, h_nonzero n, weierstrassFactor_at_one]
  exact tendsto_nhds_unique_of_eventuallyEq htend tendsto_const_nhds hzero
end Complex
end
end
end CountPort43
section CountPort44
section
open Filter Topology Set
namespace MeromorphicOn
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {U K : Set 𝕜} {z : 𝕜}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
lemma divisor_support_inter_compact_finite (f : 𝕜 → E) {U K : Set 𝕜}
    (hK : IsCompact K) (hKU : K ⊆ U) :
    (K ∩ (MeromorphicOn.divisor f U).support).Finite := by
  classical
  set D : Function.locallyFinsuppWithin U ℤ := MeromorphicOn.divisor f U
  have hloc :
      ∀ x ∈ K, ∃ V : Set 𝕜, V ∈ 𝓝 x ∧ Set.Finite (V ∩ D.support) := by
    intro x hxK
    rcases D.supportLocallyFiniteWithinDomain x (hKU hxK) with ⟨V, hV, hfin⟩
    exact ⟨V, hV, hfin⟩
  choose V hVnhds hVfin using hloc
  rcases hK.elim_nhds_subcover' (U := fun x hx => V x hx) (hU := fun x hx => hVnhds x hx) with
    ⟨t, ht⟩
  have hsub :
      K ∩ D.support ⊆ ⋃ x ∈ t, (V (x : 𝕜) x.2 ∩ D.support) := by
    intro y hy
    rcases hy with ⟨hyK, hyS⟩
    have hycov : y ∈ ⋃ x ∈ t, V (x : 𝕜) x.2 := ht hyK
    rcases Set.mem_iUnion.1 hycov with ⟨x, hycov'⟩
    rcases Set.mem_iUnion.1 hycov' with ⟨hxT, hyV⟩
    refine Set.mem_iUnion.2 ⟨x, Set.mem_iUnion.2 ?_⟩
    exact ⟨hxT, ⟨hyV, hyS⟩⟩
  have hfinU : Set.Finite (⋃ x ∈ t, (V (x : 𝕜) x.2 ∩ D.support)) := by
    classical
    refine (t.finite_toSet).biUnion ?_
    intro x hx
    simpa using (hVfin (x : 𝕜) x.2)
  exact hfinU.subset hsub
end MeromorphicOn
end
end CountPort44
section CountPort45
section
open Set
namespace Complex.Hadamard
def divisorZeroIndex (f : ℂ → ℂ) (U : Set ℂ) : Type :=
  Σ z : ℂ, Fin (Int.toNat (MeromorphicOn.divisor f U z))
abbrev divisorZeroIndex₀ (f : ℂ → ℂ) (U : Set ℂ) : Type :=
  {p : divisorZeroIndex f U // p.1 ≠ 0}
abbrev divisorZeroIndex₀_val {f : ℂ → ℂ} {U : Set ℂ} (p : divisorZeroIndex₀ f U) : ℂ :=
  p.1.1
@[simp]
lemma divisorZeroIndex₀_val_ne_zero {f : ℂ → ℂ} {U : Set ℂ} (p : divisorZeroIndex₀ f U) :
    divisorZeroIndex₀_val p ≠ 0 := p.2
@[simp]
lemma divisorZeroIndex₀_val_mem_divisor_support {f : ℂ → ℂ} {U : Set ℂ}
    (p : divisorZeroIndex₀ f U) :
    MeromorphicOn.divisor f U (divisorZeroIndex₀_val p) ≠ 0 := by
  have hn :
      Int.toNat (MeromorphicOn.divisor f U (divisorZeroIndex₀_val p)) ≠ 0 := by
    intro h0
    have q0 : Fin 0 := by
      simpa [divisorZeroIndex₀_val, h0] using p.1.2
    exact Fin.elim0 q0
  intro hdiv
  have : Int.toNat (MeromorphicOn.divisor f U (divisorZeroIndex₀_val p)) = 0 := by
    simp [hdiv]
  exact hn this
noncomputable def divisorCanonicalProduct (m : ℕ) (f : ℂ → ℂ) (U : Set ℂ) (z : ℂ) : ℂ :=
  ∏' p : divisorZeroIndex₀ f U, weierstrassFactor m (z / divisorZeroIndex₀_val p)
@[simp]
lemma divisorCanonicalProduct_zero (m : ℕ) (f : ℂ → ℂ) (U : Set ℂ) :
    divisorCanonicalProduct m f U 0 = 1 := by
  simp [divisorCanonicalProduct]
end Complex.Hadamard
end
end CountPort45
section CountPort46
section
namespace Complex
section UniformMul
end UniformMul
end Complex
end
end CountPort46
section CountPort47
section
open Filter Function Complex Finset Topology
open scoped Topology BigOperators
open Set
namespace Complex.Hadamard
lemma finite_divisorZeroIndex₀_subtype_norm_le {f : ℂ → ℂ} {U : Set ℂ} (B : ℝ)
    (hBU : Metric.closedBall (0 : ℂ) B ⊆ U) :
    Finite {p : divisorZeroIndex₀ f U // ‖divisorZeroIndex₀_val p‖ ≤ B} := by
  set D : Function.locallyFinsuppWithin U ℤ := MeromorphicOn.divisor f U
  have hK : IsCompact (Metric.closedBall (0 : ℂ) B) := isCompact_closedBall _ _
  have hpts0 : ((Metric.closedBall (0 : ℂ) B) ∩ D.support).Finite :=
    MeromorphicOn.divisor_support_inter_compact_finite (f := f) (U := U)
      (K := Metric.closedBall (0 : ℂ) B) hK hBU
  set pts : Set ℂ := ((Metric.closedBall (0 : ℂ) B) ∩ D.support) \ {0}
  have hpts : pts.Finite := hpts0.sdiff
  let : Fintype pts := hpts.fintype
  let T : Type := Σ z : pts, Fin (Int.toNat (D z.1))
  have : Finite T := by infer_instance
  let F :
      {p : divisorZeroIndex₀ f U // ‖divisorZeroIndex₀_val p‖ ≤ B} → T := fun p =>
    ⟨⟨divisorZeroIndex₀_val p.1, by
        have hball : divisorZeroIndex₀_val p.1 ∈ Metric.closedBall (0 : ℂ) B := by
          simpa [Metric.mem_closedBall, dist_zero_right] using p.2
        have hsupport : divisorZeroIndex₀_val p.1 ∈ D.support := by
          have hne_toNat :
              Int.toNat (MeromorphicOn.divisor f U (divisorZeroIndex₀_val p.1)) ≠ 0 := by
            intro h0
            have hpfin :
                Fin (Int.toNat (MeromorphicOn.divisor f U (divisorZeroIndex₀_val p.1))) := by
              simpa [D] using p.1.1.2
            have : Fin 0 := by simpa [h0] using hpfin
            exact Fin.elim0 this
          have hne_D : D (divisorZeroIndex₀_val p.1) ≠ 0 := by
            intro hD0
            apply hne_toNat
            simp [D, hD0]
          simp [D, Function.locallyFinsuppWithin.support, Function.support]
        have hne0 : divisorZeroIndex₀_val p.1 ≠ 0 := divisorZeroIndex₀_val_ne_zero p.1
        exact ⟨⟨hball, hsupport⟩, by simp [Set.mem_singleton_iff]⟩⟩,
      p.1.1.2⟩
  refine Finite.of_injective F ?_
  intro p q hpq
  apply Subtype.ext
  apply Subtype.ext
  have h' := (Sigma.mk.inj_iff.1 hpq)
  have hz : divisorZeroIndex₀_val p.1 = divisorZeroIndex₀_val q.1 := congrArg Subtype.val h'.1
  apply (Sigma.mk.inj_iff).2
  refine ⟨hz, ?_⟩
  exact h'.2
lemma divisorZeroIndex₀_norm_le_finite {f : ℂ → ℂ} {U : Set ℂ} (B : ℝ)
    (hBU : Metric.closedBall (0 : ℂ) B ⊆ U) :
    ({p : divisorZeroIndex₀ f U | ‖divisorZeroIndex₀_val p‖ ≤ B} : Set _).Finite := by
  let s : Set (divisorZeroIndex₀ f U) := {p | ‖divisorZeroIndex₀_val p‖ ≤ B}
  have : Finite (↥s) :=
    finite_divisorZeroIndex₀_subtype_norm_le (f := f) (U := U) B hBU
  exact Set.toFinite s
end Complex.Hadamard
end
end CountPort47
section CountPort48
section
open Set
namespace Complex.Hadamard
end Complex.Hadamard
end
end CountPort48
section CountPort49
section
noncomputable section
open Set
open scoped Topology BigOperators
namespace Complex.Hadamard
theorem divisorZeroIndex₀_fiber_finite (f : ℂ → ℂ) (z₀ : ℂ) :
    ({p : divisorZeroIndex₀ f (Set.univ : Set ℂ) | divisorZeroIndex₀_val p = z₀} :
      Set _).Finite := by
  have hsub :
      ({p : divisorZeroIndex₀ f (Set.univ : Set ℂ) | divisorZeroIndex₀_val p = z₀} : Set _)
        ⊆ ({p : divisorZeroIndex₀ f (Set.univ : Set ℂ) | ‖divisorZeroIndex₀_val p‖ ≤ ‖z₀‖} :
          Set _) := by
    intro p hp
    have : divisorZeroIndex₀_val p = z₀ := hp
    simp [this]
  have hfin :
      ({p : divisorZeroIndex₀ f (Set.univ : Set ℂ) | ‖divisorZeroIndex₀_val p‖ ≤ ‖z₀‖} :
        Set _).Finite := by
    have : Metric.closedBall (0 : ℂ) ‖z₀‖ ⊆ (Set.univ : Set ℂ) := by simp
    simpa using (divisorZeroIndex₀_norm_le_finite (f := f) (U := (Set.univ : Set ℂ))
      (B := ‖z₀‖) this)
  exact hfin.subset hsub
def divisorZeroIndex₀_fiberFinset (f : ℂ → ℂ) (z₀ : ℂ) :
    Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ)) :=
  (divisorZeroIndex₀_fiber_finite (f := f) z₀).toFinset
@[simp]
lemma mem_divisorZeroIndex₀_fiberFinset (f : ℂ → ℂ) (z₀ : ℂ)
    (p : divisorZeroIndex₀ f (Set.univ : Set ℂ)) :
    p ∈ divisorZeroIndex₀_fiberFinset (f := f) z₀ ↔ divisorZeroIndex₀_val p = z₀ := by
  simp [divisorZeroIndex₀_fiberFinset]
end Complex.Hadamard
end
end
end CountPort49
section CountPort50
section
open Filter Function Complex Finset Topology
open scoped Topology BigOperators
open Set
namespace Complex.Hadamard
noncomputable def divisorComplementFactor
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ)
    (p : divisorZeroIndex₀ f (Set.univ : Set ℂ)) (z : ℂ) : ℂ := by
  classical
  exact if p ∈ divisorZeroIndex₀_fiberFinset (f := f) z₀ then (1 : ℂ)
    else weierstrassFactor m (z / divisorZeroIndex₀_val p)
@[simp]
theorem divisorComplementFactor_eq_one_of_mem
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ)
    (p : divisorZeroIndex₀ f (Set.univ : Set ℂ)) (z : ℂ)
    (hp : p ∈ divisorZeroIndex₀_fiberFinset (f := f) z₀) :
    divisorComplementFactor m f z₀ p z = 1 := by
  classical
  simp [divisorComplementFactor, hp]
@[simp]
theorem divisorComplementFactor_eq_weierstrassFactor_of_not_mem
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ)
    (p : divisorZeroIndex₀ f (Set.univ : Set ℂ)) (z : ℂ)
    (hp : p ∉ divisorZeroIndex₀_fiberFinset (f := f) z₀) :
    divisorComplementFactor m f z₀ p z =
      weierstrassFactor m (z / divisorZeroIndex₀_val p) := by
  classical
  simp [divisorComplementFactor, hp]
noncomputable def divisorPartialProduct (m : ℕ) (f : ℂ → ℂ)
    (s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ))) (z : ℂ) : ℂ :=
  ∏ p ∈ s, weierstrassFactor m (z / divisorZeroIndex₀_val p)
@[simp]
lemma divisorPartialProduct_def (m : ℕ) (f : ℂ → ℂ)
    (s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ))) (z : ℂ) :
    divisorPartialProduct m f s z = ∏ p ∈ s, weierstrassFactor m (z / divisorZeroIndex₀_val p) :=
  rfl
noncomputable def divisorComplementPartialProduct
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ)
    (s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ))) (z : ℂ) : ℂ :=
  ∏ p ∈ s, divisorComplementFactor m f z₀ p z
@[simp]
lemma divisorComplementPartialProduct_def
    (m : ℕ) (f : ℂ → ℂ) (z₀ : ℂ)
    (s : Finset (divisorZeroIndex₀ f (Set.univ : Set ℂ))) (z : ℂ) :
    divisorComplementPartialProduct m f z₀ s z =
      ∏ p ∈ s, if divisorZeroIndex₀_val p = z₀ then (1 : ℂ)
        else weierstrassFactor m (z / divisorZeroIndex₀_val p) := by
  simp [divisorComplementPartialProduct, divisorComplementFactor,
    mem_divisorZeroIndex₀_fiberFinset]
end Complex.Hadamard
end
end CountPort50
section CountPort51
section
noncomputable section
open Complex Filter Function Finset Topology
open scoped Topology BigOperators
open Set
namespace Complex.Hadamard
end Complex.Hadamard
end
end
end CountPort51
section CountPort52
section
open Filter Function Complex Finset Topology
open scoped Topology BigOperators
open Set
namespace Complex.Hadamard
open Filter
end Complex.Hadamard
end
end CountPort52
section CountPort53
section
open Filter Function Complex Finset Topology
open scoped Topology BigOperators
open Set
namespace Complex.Hadamard
end Complex.Hadamard
end
end CountPort53
section CountPort54
section
namespace Complex.Hadamard
open scoped Topology
open Set
end Hadamard
end Complex
end
end CountPort54
section CountPort55
section
open Set
open scoped ENNReal
namespace Metric
variable {X : Type*} [PseudoMetricSpace X]
def annulusIoo (x : X) (r R : ℝ) : Set X := (fun y : X ↦ dist y x) ⁻¹' Ioo r R
def annulusIoc (x : X) (r R : ℝ) : Set X := (fun y : X ↦ dist y x) ⁻¹' Ioc r R
def annulusIco (x : X) (r R : ℝ) : Set X := (fun y : X ↦ dist y x) ⁻¹' Ico r R
def annulusIcc (x : X) (r R : ℝ) : Set X := (fun y : X ↦ dist y x) ⁻¹' Icc r R
def annulusIoi (x : X) (r : ℝ) : Set X := (fun y : X ↦ dist y x) ⁻¹' Ioi r
def annulusIci (x : X) (r : ℝ) : Set X := (fun y : X ↦ dist y x) ⁻¹' Ici r
variable {x : X} {r R : ℝ}
@[simp] lemma annulusIoo_eq_empty {x : X} {r R : ℝ} (h : R ≤ r) : annulusIoo x r R = ∅ := by
  simp [annulusIoo, Ioo_eq_empty_of_le h]
@[simp] lemma annulusIoc_eq_empty {x : X} {r R : ℝ} (h : R ≤ r) : annulusIoc x r R = ∅ := by
  simp [annulusIoc, Ioc_eq_empty_of_le h]
@[simp] lemma annulusIco_eq_empty {x : X} {r R : ℝ} (h : R ≤ r) : annulusIco x r R = ∅ := by
  simp [annulusIco, Ico_eq_empty_of_le h]
@[simp] lemma annulusIcc_eq_empty {x : X} {r R : ℝ} (h : R < r) : annulusIcc x r R = ∅ := by
  simp [annulusIcc, Icc_eq_empty_of_lt h]
@[gcongr]
lemma annulusIoo_mono {x : X} {r₁ R₁ r₂ R₂ : ℝ} (hr : r₂ ≤ r₁) (hR : R₁ ≤ R₂) :
    annulusIoo x r₁ R₁ ⊆ annulusIoo x r₂ R₂ := by
  intro y hy
  exact ⟨lt_of_le_of_lt hr hy.1, lt_of_lt_of_le hy.2 hR⟩
@[gcongr]
lemma annulusIoc_mono {x : X} {r₁ R₁ r₂ R₂ : ℝ} (hr : r₂ ≤ r₁) (hR : R₁ ≤ R₂) :
    annulusIoc x r₁ R₁ ⊆ annulusIoc x r₂ R₂ := by
  intro y hy
  exact ⟨lt_of_le_of_lt hr hy.1, hy.2.trans hR⟩
@[gcongr]
lemma annulusIco_mono {x : X} {r₁ R₁ r₂ R₂ : ℝ} (hr : r₂ ≤ r₁) (hR : R₁ ≤ R₂) :
    annulusIco x r₁ R₁ ⊆ annulusIco x r₂ R₂ := by
  intro y hy
  exact ⟨hr.trans hy.1, lt_of_lt_of_le hy.2 hR⟩
@[gcongr]
lemma annulusIcc_mono {x : X} {r₁ R₁ r₂ R₂ : ℝ} (hr : r₂ ≤ r₁) (hR : R₁ ≤ R₂) :
    annulusIcc x r₁ R₁ ⊆ annulusIcc x r₂ R₂ := by
  intro y hy
  exact ⟨hr.trans hy.1, hy.2.trans hR⟩
@[simp]
lemma annulusIoc_union_annulusIoo {x : X} {r r' R : ℝ} (h₁ : r ≤ r') (h₂ : r' < R) :
    annulusIoc x r r' ∪ annulusIoo x r' R = annulusIoo x r R := by
  simpa [annulusIoc, annulusIoo, preimage_union] using
    congrArg (fun s : Set ℝ ↦ (fun y : X ↦ dist y x) ⁻¹' s) (Ioc_union_Ioo_eq_Ioo h₁ h₂)
@[simp]
lemma annulusIoc_union_annulusIoc {x : X} {r r' R : ℝ} (h₁ : r ≤ r') (h₂ : r' ≤ R) :
    annulusIoc x r r' ∪ annulusIoc x r' R = annulusIoc x r R := by
  simpa [annulusIoc, preimage_union] using
    congrArg (fun s : Set ℝ ↦ (fun y : X ↦ dist y x) ⁻¹' s) (Ioc_union_Ioc_eq_Ioc h₁ h₂)
@[simp]
lemma annulusIoo_union_annulusIco {x : X} {r r' R : ℝ} (h₁ : r < r') (h₂ : r' ≤ R) :
    annulusIoo x r r' ∪ annulusIco x r' R = annulusIoo x r R := by
  simpa [annulusIoo, annulusIco, preimage_union] using
    congrArg (fun s : Set ℝ ↦ (fun y : X ↦ dist y x) ⁻¹' s) (Ioo_union_Ico_eq_Ioo h₁ h₂)
@[simp]
lemma annulusIoo_union_annulusIcc {x : X} {r r' R : ℝ} (h₁ : r < r') (h₂ : r' ≤ R) :
    annulusIoo x r r' ∪ annulusIcc x r' R = annulusIoc x r R := by
  simpa [annulusIoo, annulusIcc, annulusIoc, preimage_union] using
    congrArg (fun s : Set ℝ ↦ (fun y : X ↦ dist y x) ⁻¹' s) (Ioo_union_Icc_eq_Ioc h₁ h₂)
@[simp]
lemma annulusIcc_union_annulusIoo {x : X} {r r' R : ℝ} (h₁ : r ≤ r') (h₂ : r' < R) :
    annulusIcc x r r' ∪ annulusIoo x r' R = annulusIco x r R := by
  simpa [annulusIcc, annulusIoo, annulusIco, preimage_union] using
    congrArg (fun s : Set ℝ ↦ (fun y : X ↦ dist y x) ⁻¹' s) (Icc_union_Ioo_eq_Ico h₁ h₂)
@[simp]
lemma annulusIcc_union_annulusIoc {x : X} {r r' R : ℝ} (h₁ : r ≤ r') (h₂ : r' ≤ R) :
    annulusIcc x r r' ∪ annulusIoc x r' R = annulusIcc x r R := by
  simpa [annulusIcc, annulusIoc, preimage_union] using
    congrArg (fun s : Set ℝ ↦ (fun y : X ↦ dist y x) ⁻¹' s) (Icc_union_Ioc_eq_Icc h₁ h₂)
@[simp]
lemma annulusIco_union_annulusIco {x : X} {r r' R : ℝ} (h₁ : r ≤ r') (h₂ : r' ≤ R) :
    annulusIco x r r' ∪ annulusIco x r' R = annulusIco x r R := by
  simpa [annulusIco, preimage_union] using
    congrArg (fun s : Set ℝ ↦ (fun y : X ↦ dist y x) ⁻¹' s) (Ico_union_Ico_eq_Ico h₁ h₂)
@[simp]
lemma annulusIco_union_annulusIcc {x : X} {r r' R : ℝ} (h₁ : r ≤ r') (h₂ : r' ≤ R) :
    annulusIco x r r' ∪ annulusIcc x r' R = annulusIcc x r R := by
  simpa [annulusIco, annulusIcc, preimage_union] using
    congrArg (fun s : Set ℝ ↦ (fun y : X ↦ dist y x) ⁻¹' s) (Ico_union_Icc_eq_Icc h₁ h₂)
@[simp]
lemma annulusIoc_union_annulusIoi {x : X} {r R : ℝ} (h : r ≤ R) :
    annulusIoc x r R ∪ annulusIoi x R = annulusIoi x r := by
  simpa [annulusIoc, annulusIoi, preimage_union] using
    congrArg (fun s : Set ℝ ↦ (fun y : X ↦ dist y x) ⁻¹' s) (Ioc_union_Ioi_eq_Ioi h)
@[simp]
lemma annulusIoo_union_annulusIci {x : X} {r R : ℝ} (h : r < R) :
    annulusIoo x r R ∪ annulusIci x R = annulusIoi x r := by
  simpa [annulusIoo, annulusIci, annulusIoi, preimage_union] using
    congrArg (fun s : Set ℝ ↦ (fun y : X ↦ dist y x) ⁻¹' s) (Ioo_union_Ici_eq_Ioi h)
@[simp]
lemma annulusIcc_union_annulusIoi {x : X} {r R : ℝ} (h : r ≤ R) :
    annulusIcc x r R ∪ annulusIoi x R = annulusIci x r := by
  simpa [annulusIcc, annulusIoi, annulusIci, preimage_union] using
    congrArg (fun s : Set ℝ ↦ (fun y : X ↦ dist y x) ⁻¹' s) (Icc_union_Ioi_eq_Ici h)
@[simp]
lemma annulusIco_union_annulusIci {x : X} {r R : ℝ} (h : r ≤ R) :
    annulusIco x r R ∪ annulusIci x R = annulusIci x r := by
  simpa [annulusIco, annulusIci, preimage_union] using
    congrArg (fun s : Set ℝ ↦ (fun y : X ↦ dist y x) ⁻¹' s) (Ico_union_Ici_eq_Ici h)
open scoped Function
variable {ι : Type*} [LinearOrder ι] [SuccOrder ι]
end Metric
namespace Metric
variable {X : Type*} [PseudoEMetricSpace X]
def eannulusIoo (x : X) (r R : ℝ≥0∞) : Set X := (fun y : X ↦ edist y x) ⁻¹' Ioo r R
def eannulusIoc (x : X) (r R : ℝ≥0∞) : Set X := (fun y : X ↦ edist y x) ⁻¹' Ioc r R
def eannulusIco (x : X) (r R : ℝ≥0∞) : Set X := (fun y : X ↦ edist y x) ⁻¹' Ico r R
def eannulusIcc (x : X) (r R : ℝ≥0∞) : Set X := (fun y : X ↦ edist y x) ⁻¹' Icc r R
def eannulusIoi (x : X) (r : ℝ≥0∞) : Set X := (fun y : X ↦ edist y x) ⁻¹' Ioi r
def eannulusIci (x : X) (r : ℝ≥0∞) : Set X := (fun y : X ↦ edist y x) ⁻¹' Ici r
@[simp] lemma eannulusIoo_eq_preimage (x : X) (r R : ℝ≥0∞) :
    eannulusIoo x r R = (fun y : X ↦ edist y x) ⁻¹' Ioo r R := rfl
@[simp] lemma eannulusIoc_eq_preimage (x : X) (r R : ℝ≥0∞) :
    eannulusIoc x r R = (fun y : X ↦ edist y x) ⁻¹' Ioc r R := rfl
@[simp] lemma eannulusIco_eq_preimage (x : X) (r R : ℝ≥0∞) :
    eannulusIco x r R = (fun y : X ↦ edist y x) ⁻¹' Ico r R := rfl
@[simp] lemma eannulusIcc_eq_preimage (x : X) (r R : ℝ≥0∞) :
    eannulusIcc x r R = (fun y : X ↦ edist y x) ⁻¹' Icc r R := rfl
@[simp] lemma eannulusIoi_eq_preimage (x : X) (r : ℝ≥0∞) :
    eannulusIoi x r = (fun y : X ↦ edist y x) ⁻¹' Ioi r := rfl
@[simp] lemma eannulusIci_eq_preimage (x : X) (r : ℝ≥0∞) :
    eannulusIci x r = (fun y : X ↦ edist y x) ⁻¹' Ici r := rfl
lemma eannulusIoo_eq_empty {x : X} {r R : ℝ≥0∞} (h : R ≤ r) : eannulusIoo x r R = ∅ := by
  simp [eannulusIoo, Ioo_eq_empty_of_le h]
@[gcongr]
lemma eannulusIoo_mono {x : X} {r₁ R₁ r₂ R₂ : ℝ≥0∞} (hr : r₂ ≤ r₁) (hR : R₁ ≤ R₂) :
    eannulusIoo x r₁ R₁ ⊆ eannulusIoo x r₂ R₂ := by
  intro y hy
  exact ⟨lt_of_le_of_lt hr hy.1, lt_of_lt_of_le hy.2 hR⟩
@[gcongr]
lemma eannulusIoc_mono {x : X} {r₁ R₁ r₂ R₂ : ℝ≥0∞} (hr : r₂ ≤ r₁) (hR : R₁ ≤ R₂) :
    eannulusIoc x r₁ R₁ ⊆ eannulusIoc x r₂ R₂ := by
  intro y hy; exact ⟨lt_of_le_of_lt hr hy.1, hy.2.trans hR⟩
@[gcongr]
lemma eannulusIco_mono {x : X} {r₁ R₁ r₂ R₂ : ℝ≥0∞} (hr : r₂ ≤ r₁) (hR : R₁ ≤ R₂) :
    eannulusIco x r₁ R₁ ⊆ eannulusIco x r₂ R₂ := by
  intro y hy; exact ⟨hr.trans hy.1, lt_of_lt_of_le hy.2 hR⟩
@[gcongr]
lemma eannulusIcc_mono {x : X} {r₁ R₁ r₂ R₂ : ℝ≥0∞} (hr : r₂ ≤ r₁) (hR : R₁ ≤ R₂) :
    eannulusIcc x r₁ R₁ ⊆ eannulusIcc x r₂ R₂ := by
  intro y hy; exact ⟨hr.trans hy.1, hy.2.trans hR⟩
open scoped Function
variable {ι : Type*} [LinearOrder ι] [SuccOrder ι]
end Metric
namespace Metric
variable {X : Type*} [PseudoMetricSpace X]
variable {x : X} {r R : ℝ}
end Metric
end
end CountPort55
section CountPort56
section
namespace Complex.Hadamard
open Filter Topology Set Complex
open scoped BigOperators Topology
noncomputable def centeredHadamardDenom (m : ℕ) (c : ℂ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  (z - c) ^ (analyticOrderNatAt f c) *
    divisorCanonicalProduct m (fun w : ℂ => f (w + c)) (Set.univ : Set ℂ) (z - c)
@[simp]
theorem centeredHadamardDenom_center_eq_one {m : ℕ} {c : ℂ} {f : ℂ → ℂ}
    (h : analyticOrderNatAt f c = 0) :
    centeredHadamardDenom m c f c = 1 := by
  simp [centeredHadamardDenom, h, sub_self, divisorCanonicalProduct_zero, pow_zero]
@[simp]
theorem centeredHadamardDenom_center_eq_zero {m : ℕ} {c : ℂ} {f : ℂ → ℂ}
    (h : analyticOrderNatAt f c ≠ 0) : centeredHadamardDenom m c f c = 0 := by
  have hn : 0 < analyticOrderNatAt f c := by
    exact Nat.pos_of_ne_zero h
  simp [centeredHadamardDenom, sub_self, zero_pow hn.ne']
end Complex.Hadamard
end
end CountPort56
section CountPort57
section
open Filter Function MeromorphicOn Metric Real Set
namespace Function.locallyFinsuppWithin
variable {E : Type*} [NormedAddCommGroup E]
end Function.locallyFinsuppWithin
namespace Function.locallyFinsuppWithin
end Function.locallyFinsuppWithin
end
end CountPort57
section CountPort58
section
namespace Real
end Real
end
end CountPort58
section CountPort59
section
namespace Real
end Real
end
end CountPort59
section CountPort60
section
namespace Real
variable {α E : Type*} [SeminormedAddCommGroup E]
variable {F : Type*} [NormedAddCommGroup F]
open Metric Complex
end Real
end
end CountPort60
section CountPort61
section
open Filter Function MeromorphicOn Metric Real Set
namespace Function.locallyFinsuppWithin
variable {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
end Function.locallyFinsuppWithin
end
end CountPort61
section CountPort62
section
open Set
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
theorem Differentiable.divisor_nonneg {f : ℂ → E} (hf : Differentiable ℂ f) :
    0 ≤ MeromorphicOn.divisor f (univ : Set ℂ) :=
  MeromorphicOn.AnalyticOnNhd.divisor_nonneg (hf.differentiableOn.analyticOnNhd isOpen_univ)
end
end CountPort62
section CountPort63
section
noncomputable section
open scoped BigOperators
open Filter
namespace Real
end Real
end
end
end CountPort63
section CountPort64
section
noncomputable section
open Filter Topology Set Complex
open scoped BigOperators Topology
namespace Complex.Hadamard
open scoped Real
open scoped BigOperators
end Complex.Hadamard
end
end
end CountPort64
section CountPort65
section
open Real Complex Function
namespace Backlund
end Backlund
end
end CountPort65
section CountPort66
section
noncomputable section
namespace Kadiri
open Complex Filter
lemma zeroes_rect_Ioo_critical_positive_height_finite (T : ℝ) :
    (riemannZeta.zeroes_rect (.Ioo 0 1) (.Ioo 0 T)).Finite := by
  rw [riemannZeta.zeroes_rect_eq]
  let S : Set ℂ := (Complex.re ⁻¹' Set.Icc (0 : ℝ) 1) ∩
    (Complex.im ⁻¹' Set.Icc (0 : ℝ) T)
  have hS : IsCompact S := by
    exact Complex.equivRealProdCLM.toHomeomorph.isClosedEmbedding.isCompact_preimage
      (isCompact_Icc.prod isCompact_Icc)
  refine (riemannZeta.zeroes_on_Compact_finite' (S := S) hS).subset ?_
  intro z hz
  rcases hz with ⟨⟨hre, him⟩, hzeta⟩
  exact ⟨⟨Set.Ioo_subset_Icc_self hre, Set.Ioo_subset_Icc_self him⟩, hzeta⟩
lemma positiveHeightZero_ne_one {T : ℝ}
    (rho : riemannZeta.zeroes_rect (.univ : Set ℝ) (.Ioo 0 T)) :
    (rho : ℂ) ≠ 1 := by
  intro h
  have him : (rho : ℂ).im ∈ Set.Ioo (0 : ℝ) T := rho.property.2.1
  rw [h] at him
  norm_num at him
lemma riemannZeta_analyticAt_positiveHeightZero {T : ℝ}
    (rho : riemannZeta.zeroes_rect (.univ : Set ℝ) (.Ioo 0 T)) :
    AnalyticAt ℂ riemannZeta (rho : ℂ) := by
  exact riemannZeta_analyticOn_compl_one (rho : ℂ)
    (by simpa [Set.mem_compl_iff] using positiveHeightZero_ne_one rho)
lemma riemannZeta_positiveHeightZero_zero {T : ℝ}
    (rho : riemannZeta.zeroes_rect (.univ : Set ℝ) (.Ioo 0 T)) :
    riemannZeta (rho : ℂ) = 0 := by
  exact rho.property.2.2
lemma riemannZeta_eventually_ne_zero_punctured_positiveHeightZero {T : ℝ}
    (rho : riemannZeta.zeroes_rect (.univ : Set ℝ) (.Ioo 0 T)) :
    ∀ᶠ z in nhdsWithin (rho : ℂ) ({(rho : ℂ)}ᶜ), riemannZeta z ≠ 0 := by
  have hmem_compl_one : (rho : ℂ) ∈ ({1} : Set ℂ)ᶜ := by
    simpa [Set.mem_compl_iff] using positiveHeightZero_ne_one rho
  have hdisj : Disjoint (nhdsWithin (rho : ℂ) ({(rho : ℂ)}ᶜ))
      (𝓟 (({1} : Set ℂ)ᶜ \ riemannZeta.zeroesᶜ)) := by
    exact (mem_codiscreteWithin.mp riemannZeta.zeroes_codiscreteWithin_compl_one)
      (rho : ℂ) hmem_compl_one
  have hnot_zeroes : (({1} : Set ℂ)ᶜ \ riemannZeta.zeroesᶜ)ᶜ ∈
      nhdsWithin (rho : ℂ) ({(rho : ℂ)}ᶜ) :=
    Filter.disjoint_principal_right.mp hdisj
  have heventually_compl_one : ∀ᶠ z in nhdsWithin (rho : ℂ) ({(rho : ℂ)}ᶜ),
      z ∈ ({1} : Set ℂ)ᶜ := by
    exact nhdsWithin_le_nhds (isOpen_compl_singleton.mem_nhds hmem_compl_one)
  filter_upwards [hnot_zeroes, heventually_compl_one] with z hznot hz_compl_one hzero
  have hz_zero : z ∈ riemannZeta.zeroes := by
    simpa [riemannZeta.zeroes] using hzero
  exact hznot ⟨hz_compl_one, by simpa using hz_zero⟩
lemma riemannZeta_meromorphicOrderAt_ne_top_positiveHeightZero {T : ℝ}
    (rho : riemannZeta.zeroes_rect (.univ : Set ℝ) (.Ioo 0 T)) :
    meromorphicOrderAt riemannZeta (rho : ℂ) ≠ ⊤ := by
  have han := riemannZeta_analyticAt_positiveHeightZero rho
  exact (meromorphicOrderAt_ne_top_iff_eventually_ne_zero han.meromorphicAt).2
    (riemannZeta_eventually_ne_zero_punctured_positiveHeightZero rho)
lemma riemannZeta_order_pos_positiveHeightZero {T : ℝ}
    (rho : riemannZeta.zeroes_rect (.univ : Set ℝ) (.Ioo 0 T)) :
    0 < riemannZeta.order (rho : ℂ) := by
  have han := riemannZeta_analyticAt_positiveHeightZero rho
  have hzero := riemannZeta_positiveHeightZero_zero rho
  have horder_ne_top := riemannZeta_meromorphicOrderAt_ne_top_positiveHeightZero rho
  have hanOrder_ne_zero : analyticOrderAt riemannZeta (rho : ℂ) ≠ 0 := by
    intro h
    exact (han.analyticOrderAt_eq_zero.mp h) hzero
  unfold riemannZeta.order
  cases hO : analyticOrderAt riemannZeta (rho : ℂ) with
  | top =>
      exfalso
      exact horder_ne_top (by simp [han.meromorphicOrderAt_eq, hO])
  | coe n =>
      have hn_pos : 0 < n := by
        exact Nat.pos_of_ne_zero (by
          intro hn
          exact hanOrder_ne_zero (by simp [hO, hn]))
      rw [han.meromorphicOrderAt_eq, hO, ENat.map_natCast, WithTop.untopD_coe]
      exact_mod_cast hn_pos
lemma riemannZeta_one_sub_ne_zero_of_one_le_re {w : ℂ}
    (hw_re : 1 ≤ w.re) (hcos : Complex.cos (↑Real.pi * w / 2) ≠ 0) :
    riemannZeta (1 - w) ≠ 0 := by
  have hw_neg_nat : ∀ n : ℕ, w ≠ -↑n := by
    intro n hn
    have hre' : w.re = -(n : ℝ) := by rw [hn]; simp
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    rw [hre'] at hw_re; linarith
  have hw_ne_one : w ≠ 1 := by
    rintro rfl
    refine hcos ?_
    have h2 : (↑Real.pi * (1 : ℂ) / 2) = ((Real.pi / 2 : ℝ) : ℂ) := by push_cast; ring
    rw [h2, ← Complex.ofReal_cos, Real.cos_pi_div_two, Complex.ofReal_zero]
  have hpow : (2 * ↑Real.pi : ℂ) ^ (-w) ≠ 0 := by
    rw [Complex.cpow_ne_zero_iff]; left
    norm_num [Complex.ofReal_ne_zero, Real.pi_ne_zero]
  have hGamma : Complex.Gamma w ≠ 0 := Complex.Gamma_ne_zero hw_neg_nat
  have hzeta_w : riemannZeta w ≠ 0 := riemannZeta_ne_zero_of_one_le_re hw_re
  have hfe := riemannZeta_one_sub (s := w) hw_neg_nat hw_ne_one
  rw [hfe]
  exact mul_ne_zero
    (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hpow) hGamma) hcos) hzeta_w
lemma riemannZeta_ne_zero_of_re_nonpos_im_ne_zero {z : ℂ}
    (hre : z.re ≤ 0) (him : z.im ≠ 0) : riemannZeta z ≠ 0 := by
  set w : ℂ := 1 - z with hw
  have hw_im : w.im ≠ 0 := by rw [hw]; simp [him]
  have hw_re : 1 ≤ w.re := by rw [hw]; simp; linarith
  have hcos : Complex.cos (↑Real.pi * w / 2) ≠ 0 := by
    rw [Complex.cos_ne_zero_iff]
    intro k hk
    have hleft : (↑Real.pi * w / 2).im ≠ 0 := by
      rw [show (↑Real.pi * w / 2).im = Real.pi * w.im / 2 by
        simp [div_eq_mul_inv, mul_assoc]]
      exact div_ne_zero (mul_ne_zero Real.pi_ne_zero hw_im) two_ne_zero
    have hright : (((2 * (k : ℂ) + 1) * (Real.pi : ℂ) / 2).im) = 0 := by
      simp [div_eq_mul_inv, mul_assoc]
    exact hleft (by rw [hk, hright])
  have hres := riemannZeta_one_sub_ne_zero_of_one_le_re hw_re hcos
  rwa [show (1 : ℂ) - w = z by rw [hw]; ring] at hres
lemma positiveHeightZero_re_mem_Ioo {T : ℝ}
    (rho : riemannZeta.zeroes_rect (.univ : Set ℝ) (.Ioo 0 T)) :
    (rho : ℂ).re ∈ Set.Ioo (0 : ℝ) 1 := by
  have him_pos : 0 < (rho : ℂ).im := rho.property.2.1.1
  have hzeta : riemannZeta (rho : ℂ) = 0 := rho.property.2.2
  have hnot_re_nonpos : ¬ (rho : ℂ).re ≤ 0 := by
    intro hre
    exact (riemannZeta_ne_zero_of_re_nonpos_im_ne_zero hre him_pos.ne') hzeta
  have hre_pos : 0 < (rho : ℂ).re := lt_of_not_ge hnot_re_nonpos
  have hnot_re_one_le : ¬ 1 ≤ (rho : ℂ).re := by
    intro hre
    exact (riemannZeta_ne_zero_of_one_le_re hre) hzeta
  have hre_lt_one : (rho : ℂ).re < 1 := lt_of_not_ge hnot_re_one_le
  exact ⟨hre_pos, hre_lt_one⟩
lemma zeroes_rect_univ_positive_height_finite (T : ℝ) :
    (riemannZeta.zeroes_rect (.univ : Set ℝ) (.Ioo 0 T)).Finite := by
  have hsub :
      riemannZeta.zeroes_rect (.univ : Set ℝ) (.Ioo 0 T) ⊆
        riemannZeta.zeroes_rect (.Ioo (0 : ℝ) 1) (.Ioo 0 T) := by
    intro z hz
    exact ⟨positiveHeightZero_re_mem_Ioo ⟨z, hz⟩, hz.2.1, hz.2.2⟩
  exact (zeroes_rect_Ioo_critical_positive_height_finite T).subset hsub
end Kadiri
end
end
end CountPort66
section CountPort67
section
open Complex
theorem riemannZeta_re_mem_Ioo_of_eq_zero_of_im_ne_zero {s : ℂ}
    (hz : riemannZeta s = 0) (him : s.im ≠ 0) : s.re ∈ Set.Ioo (0 : ℝ) 1 :=
  ⟨not_le.mp fun h ↦ Kadiri.riemannZeta_ne_zero_of_re_nonpos_im_ne_zero h him hz,
    not_le.mp fun h ↦ riemannZeta_ne_zero_of_one_le_re h hz⟩
theorem riemannZeta.N_eq_tsum_riemannXi_order (T : ℝ) :
    riemannZeta.N T =
      ∑' ρ : {z : ℂ // riemannXi z = 0 ∧ z.re ∈ Set.Ioo (0 : ℝ) 1 ∧ z.im ∈ Set.Ioo (0 : ℝ) T},
        (((meromorphicOrderAt riemannXi (ρ : ℂ)).untopD 0 : ℤ) : ℝ) := by
  have hset : riemannZeta.zeroes_rect Set.univ (Set.Ioo 0 T) =
      {z : ℂ | riemannXi z = 0 ∧ z.re ∈ Set.Ioo (0 : ℝ) 1 ∧ z.im ∈ Set.Ioo (0 : ℝ) T} := by
    ext z
    constructor
    · rintro ⟨-, hzim, hzero⟩
      have hre := riemannZeta_re_mem_Ioo_of_eq_zero_of_im_ne_zero hzero hzim.1.ne'
      obtain ⟨hre0, hre1⟩ := Set.mem_Ioo.mp hre
      exact ⟨(riemannXi_eq_zero_iff hre0 hre1).mpr hzero, hre, hzim⟩
    · rintro ⟨hxi, hre, hzim⟩
      obtain ⟨hre0, hre1⟩ := Set.mem_Ioo.mp hre
      exact ⟨Set.mem_univ _, hzim, (riemannXi_eq_zero_iff hre0 hre1).mp hxi⟩
  calc riemannZeta.N T
      = ∑' ρ : ↥(riemannZeta.zeroes_rect Set.univ (Set.Ioo 0 T)),
          (((meromorphicOrderAt riemannXi (ρ : ℂ)).untopD 0 : ℤ) : ℝ) := by
        simp only [riemannZeta.N, riemannZeta.zeroes_sum]
        refine tsum_congr fun ρ ↦ ?_
        obtain ⟨-, hzim, hzero⟩ := ρ.property
        obtain ⟨hre0, hre1⟩ := Set.mem_Ioo.mp
          (riemannZeta_re_mem_Ioo_of_eq_zero_of_im_ne_zero hzero hzim.1.ne')
        simp only [one_mul, riemannZeta.order,
          meromorphicOrderAt_riemannXi_eq_riemannZeta hre0 hre1]
    _ = _ := (Equiv.setCongr hset).tsum_eq
        (fun ρ ↦ (((meromorphicOrderAt riemannXi (ρ : ℂ)).untopD 0 : ℤ) : ℝ))
private theorem eq_ofReal_re_add_I_mul {T : ℝ} {z : ℂ} (hz : z.im = T) :
    z = (↑z.re : ℂ) + Complex.I * (T : ℂ) := by
  apply Complex.ext <;> simp [hz]
theorem riemannZeta_ne_zero_of_forall_re_mem_Ico {T : ℝ} (hT : 0 < T)
    (h : ∀ σ : ℝ, σ ∈ Set.Ico (1 / 2 : ℝ) 1 →
      riemannZeta ((σ : ℂ) + Complex.I * (T : ℂ)) ≠ 0) :
    ∀ s : ℂ, s.im = T → riemannZeta s ≠ 0 := by
  intro s hs hz0
  have him : s.im ≠ 0 := by rw [hs]; exact hT.ne'
  obtain ⟨hre0, hre1⟩ := Set.mem_Ioo.mp (riemannZeta_re_mem_Ioo_of_eq_zero_of_im_ne_zero hz0 him)
  have hxi : riemannXi s = 0 := (riemannXi_eq_zero_iff hre0 hre1).mpr hz0
  rcases le_or_gt (1 / 2 : ℝ) s.re with hge | hlt
  ·
    apply h s.re ⟨hge, hre1⟩
    rw [← eq_ofReal_re_add_I_mul hs]; exact hz0
  ·
    set w : ℂ := 1 - starRingEnd ℂ s with hw
    have hxi_w : riemannXi w = 0 := by
      rw [hw, riemannXi_one_sub, riemannXi_conj, hxi, map_zero]
    have hw_re : w.re = 1 - s.re := by simp [hw]
    have hw_im : w.im = T := by rw [hw]; simp [hs]
    apply h w.re ⟨by rw [hw_re]; linarith, by rw [hw_re]; linarith⟩
    rw [← eq_ofReal_re_add_I_mul hw_im]
    exact (riemannXi_eq_zero_iff (by rw [hw_re]; linarith) (by rw [hw_re]; linarith)).mp hxi_w
end
end CountPort67
section CountPort68
section
open Complex Set
theorem riemannXi_re_mem_Ioo_of_eq_zero {s : ℂ} (hs : riemannXi s = 0) :
    s.re ∈ Set.Ioo (0 : ℝ) 1 := by
  have hge : ∀ z : ℂ, 1 ≤ z.re → riemannXi z ≠ 0 := by
    intro z hz hzero
    have hz0 : z ≠ 0 := by rintro rfl; rw [Complex.zero_re] at hz; norm_num at hz
    have hz1 : z ≠ 1 := by rintro rfl; rw [riemannXi_one] at hzero; norm_num at hzero
    have hΓ : Complex.Gammaℝ z ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos (by linarith)
    rw [riemannXi_eq_prefactor_mul hz0 hz1 hΓ] at hzero
    exact mul_ne_zero (prefactor_ne_zero_of hz0 hz1 hΓ)
      (riemannZeta_ne_zero_of_one_le_re hz) hzero
  refine ⟨?_, ?_⟩
  · by_contra h
    rw [not_lt] at h
    have h1 : 1 ≤ (1 - s).re := by rw [Complex.sub_re, Complex.one_re]; linarith
    exact hge (1 - s) h1 (by rw [riemannXi_one_sub]; exact hs)
  · by_contra h
    rw [not_lt] at h
    exact hge s h hs
theorem riemannZeta_eq_zero_of_riemannXi_eq_zero {s : ℂ} (hs : riemannXi s = 0) :
    riemannZeta s = 0 :=
  have h := riemannXi_re_mem_Ioo_of_eq_zero hs
  (riemannXi_eq_zero_iff h.1 h.2).mp hs
theorem riemannXi_ne_zero_of_im_eq_zero {z : ℂ} (hz : z.im = 0) : riemannXi z ≠ 0 := by
  intro hξ
  obtain ⟨hr0, hr1⟩ := riemannXi_re_mem_Ioo_of_eq_zero hξ
  have hz' : z = (↑z.re : ℂ) := by apply Complex.ext <;> simp [hz]
  rw [hz'] at hξ
  exact riemannXi_ofReal_ne_zero_of_mem_Icc ⟨by linarith, by linarith⟩ hξ
private theorem argVariation_riemannXi_seg (z₀ z₁ : ℂ)
    (hre : ∀ u ∈ Set.Icc (0 : ℝ) 1, 0 < (lineSeg z₀ z₁ u).re)
    (hne1 : ∀ u ∈ Set.Icc (0 : ℝ) 1, lineSeg z₀ z₁ u ≠ 1)
    (hζ : ∀ u ∈ Set.Icc (0 : ℝ) 1, riemannZeta (lineSeg z₀ z₁ u) ≠ 0) :
    argVariation 0 1 (fun u ↦ riemannXi (lineSeg z₀ z₁ u))
      = argVariation 0 1
          (fun u ↦ (1 / 2 : ℂ) * (lineSeg z₀ z₁ u * (lineSeg z₀ z₁ u - 1)))
        + argVariation 0 1 (fun u ↦ Complex.Gammaℝ (lineSeg z₀ z₁ u))
        + argVariation 0 1 (fun u ↦ riemannZeta (lineSeg z₀ z₁ u)) := by
  have hsne : ∀ u ∈ Set.Icc (0 : ℝ) 1, lineSeg z₀ z₁ u ≠ 0 := by
    intro u hu heq; simpa [heq] using hre u hu
  have hPcont : ContinuousOn
      (fun u ↦ (1 / 2 : ℂ) * (lineSeg z₀ z₁ u * (lineSeg z₀ z₁ u - 1))) (Set.Icc 0 1) :=
    (continuous_const.mul ((continuous_lineSeg z₀ z₁).mul
      ((continuous_lineSeg z₀ z₁).sub continuous_const))).continuousOn
  have hGcont : ContinuousOn (fun u ↦ Complex.Gammaℝ (lineSeg z₀ z₁ u)) (Set.Icc 0 1) := by
    intro u hu
    exact ContinuousAt.comp_continuousWithinAt (g := Complex.Gammaℝ) (f := lineSeg z₀ z₁)
      (Complex.analyticAt_Gammaℝ (hre u hu)).continuousAt
      (continuous_lineSeg z₀ z₁).continuousWithinAt
  have hZcont : ContinuousOn (fun u ↦ riemannZeta (lineSeg z₀ z₁ u)) (Set.Icc 0 1) := by
    intro u hu
    exact ContinuousAt.comp_continuousWithinAt (g := riemannZeta) (f := lineSeg z₀ z₁)
      (differentiableAt_riemannZeta (hne1 u hu)).continuousAt
      (continuous_lineSeg z₀ z₁).continuousWithinAt
  have hPne : ∀ u ∈ Set.Icc (0 : ℝ) 1,
      (1 / 2 : ℂ) * (lineSeg z₀ z₁ u * (lineSeg z₀ z₁ u - 1)) ≠ 0 := fun u hu ↦
    mul_ne_zero (one_div_ne_zero two_ne_zero)
      (mul_ne_zero (hsne u hu) (sub_ne_zero.mpr (hne1 u hu)))
  have hGne : ∀ u ∈ Set.Icc (0 : ℝ) 1, Complex.Gammaℝ (lineSeg z₀ z₁ u) ≠ 0 :=
    fun u hu ↦ Complex.Gammaℝ_ne_zero_of_re_pos (hre u hu)
  have hEq : Set.EqOn (fun u ↦ riemannXi (lineSeg z₀ z₁ u))
      (((fun u ↦ (1 / 2 : ℂ) * (lineSeg z₀ z₁ u * (lineSeg z₀ z₁ u - 1)))
        * (fun u ↦ Complex.Gammaℝ (lineSeg z₀ z₁ u)))
        * (fun u ↦ riemannZeta (lineSeg z₀ z₁ u))) (Set.Icc 0 1) := by
    intro u hu
    change riemannXi (lineSeg z₀ z₁ u) = _
    rw [riemannXi_eq_prefactor_mul (hsne u hu) (hne1 u hu)
      (Complex.Gammaℝ_ne_zero_of_re_pos (hre u hu))]
    simp only [Pi.mul_apply]
  rw [argVariation_congr zero_le_one hEq,
    argVariation_mul zero_le_one (hPcont.mul hGcont)
      (fun u hu ↦ mul_ne_zero (hPne u hu) (hGne u hu)) hZcont hζ,
    argVariation_mul zero_le_one hPcont hPne hGcont hGne]
private theorem rectangle_corner_eq (T : ℝ) :
    (2 + I * (T : ℂ)).re = 2 ∧ (2 + I * (T : ℂ)).im = T
      ∧ (-1 : ℂ).re = -1 ∧ (-1 : ℂ).im = 0 :=
  ⟨by simp, by simp, by norm_num, by norm_num⟩
private theorem riemannXi_ne_zero_of_mem_rectangleBorder {T : ℝ}
    (hT' : ∀ s : ℂ, s.im = T → riemannZeta s ≠ 0) {ρ : ℂ}
    (hρ : ρ ∈ RectangleBorder (-1) (2 + I * (T : ℂ))) : riemannXi ρ ≠ 0 := by
  intro hξ
  obtain ⟨hr0, hr1⟩ := riemannXi_re_mem_Ioo_of_eq_zero hξ
  obtain ⟨hwre, hwim, hm1re, hm1im⟩ := rectangle_corner_eq T
  simp only [RectangleBorder, Set.mem_union, Complex.mem_reProdIm, Set.mem_singleton_iff,
    hwre, hwim, hm1re, hm1im] at hρ
  rcases hρ with ((⟨_, him⟩ | ⟨hre, _⟩) | ⟨_, him⟩) | ⟨hre, _⟩
  ·
    exact riemannXi_ne_zero_of_im_eq_zero him hξ
  ·
    rw [hre] at hr0; norm_num at hr0
  ·
    exact hT' ρ him (riemannZeta_eq_zero_of_riemannXi_eq_zero hξ)
  ·
    rw [hre] at hr1; norm_num at hr1
theorem riemannZeta.N_eq {T : ℝ} (hT : 0 < T)
    (hT' : ∀ s : ℂ, s.im = T → riemannZeta s ≠ 0) :
    riemannZeta.N T = riemannSiegelTheta T / Real.pi + 1 + argZeta T := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  obtain ⟨hwre, hwim, hm1re, hm1im⟩ := rectangle_corner_eq T
  have hle_re : (-1 : ℂ).re ≤ (2 + I * (T : ℂ)).re := by rw [hm1re, hwre]; norm_num
  have hle_im : (-1 : ℂ).im ≤ (2 + I * (T : ℂ)).im := by rw [hm1im, hwim]; exact hT.le
  have hRS : (Rectangle (-1) (2 + I * (T : ℂ)) ∩ {ρ : ℂ | riemannXi ρ = 0})
      = {z : ℂ | riemannXi z = 0 ∧ z.re ∈ Set.Ioo (0 : ℝ) 1
          ∧ z.im ∈ Set.Ioo (0 : ℝ) T} := by
    ext z
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hzR, hξ⟩
      obtain ⟨hr0, hr1⟩ := riemannXi_re_mem_Ioo_of_eq_zero hξ
      rw [mem_Rect hle_re hle_im,
        hm1re, hm1im, hwre, hwim] at hzR
      obtain ⟨_, _, hzim0, hzimT⟩ := hzR
      exact ⟨hξ, ⟨hr0, hr1⟩,
        hzim0.lt_of_ne fun heq ↦ riemannXi_ne_zero_of_im_eq_zero heq.symm hξ,
        hzimT.lt_of_ne fun heq ↦ hT' z heq (riemannZeta_eq_zero_of_riemannXi_eq_zero hξ)⟩
    · rintro ⟨hξ, ⟨hr0, hr1⟩, hi0, hiT⟩
      refine ⟨?_, hξ⟩
      rw [mem_Rect hle_re hle_im,
        hm1re, hm1im, hwre, hwim]
      exact ⟨by linarith, by linarith, hi0.le, hiT.le⟩
  have hfin : (Rectangle (-1) (2 + I * (T : ℂ)) ∩ {ρ : ℂ | riemannXi ρ = 0}).Finite := by
    have hcompact : IsCompact (Rectangle (-1) (2 + I * (T : ℂ))) :=
      isCompact_uIcc.reProdIm isCompact_uIcc
    refine (riemannZeta.zeroes_on_Compact_finite' hcompact).subset ?_
    rintro z ⟨hzR, hξ⟩
    exact ⟨hzR, riemannZeta_eq_zero_of_riemannXi_eq_zero hξ⟩
  have hap : (∑ ρ ∈ hfin.toFinset, (((meromorphicOrderAt riemannXi ρ).untopD 0 : ℤ) : ℝ))
      = 1 / (2 * Real.pi) * rectangleArgVariation riemannXi (-1) (2 + I * (T : ℂ)) := by
    refine rectangle_zero_count_eq_argVariation (z := (-1 : ℂ)) (w := 2 + I * (T : ℂ))
      (z₀ := (2 : ℂ)) analyticOnNhd_riemannXi
      isConnected_univ (Set.mem_univ _) ?_ (Set.subset_univ _) hle_re hle_im
      (fun ρ hρ ↦ riemannXi_ne_zero_of_mem_rectangleBorder hT' hρ) hfin
    have h2 := riemannXi_ofReal_ne_zero_of_mem_Icc (σ := 2) ⟨by norm_num, le_refl _⟩
    simpa using h2
  have hbridge : (∑' ρ : {z : ℂ // riemannXi z = 0 ∧ z.re ∈ Set.Ioo (0 : ℝ) 1
        ∧ z.im ∈ Set.Ioo (0 : ℝ) T},
      (((meromorphicOrderAt riemannXi (ρ : ℂ)).untopD 0 : ℤ) : ℝ))
      = ∑ ρ ∈ hfin.toFinset, (((meromorphicOrderAt riemannXi ρ).untopD 0 : ℤ) : ℝ) := by
    rw [← Finset.tsum_subtype' hfin.toFinset
        (fun ρ ↦ (((meromorphicOrderAt riemannXi ρ).untopD 0 : ℤ) : ℝ)), hfin.coe_toFinset]
    exact (Equiv.setCongr hRS.symm).tsum_eq
      (fun ρ ↦ (((meromorphicOrderAt riemannXi (ρ : ℂ)).untopD 0 : ℤ) : ℝ))
  have hhalf := argVariation_riemannXi_rectangle_eq_two_mul hT hT'
  have h2re : (2 : ℂ).re = 2 := by norm_num
  have hc2re : (1 / 2 + I * (T : ℂ)).re = 1 / 2 := by simp
  have hc2im : (1 / 2 + I * (T : ℂ)).im = T := by simp
  have hcontour : argVariationContourL riemannXi T
      = argVariationContourL (fun s ↦ (1 / 2 : ℂ) * (s * (s - 1))) T
        + argVariationContourL Complex.Gammaℝ T + argVariationContourL riemannZeta T := by
    have hseg1 := argVariation_riemannXi_seg 2 (2 + I * (T : ℂ))
      (fun u _ ↦ by rw [lineSeg_re, h2re, hwre]; norm_num)
      (fun u _ heq ↦ by
        have := congrArg Complex.re heq
        rw [lineSeg_re, h2re, hwre, Complex.one_re] at this; norm_num at this)
      (fun u _ ↦ riemannZeta_ne_zero_of_one_le_re (by rw [lineSeg_re, h2re, hwre]; norm_num))
    have hseg2 := argVariation_riemannXi_seg (2 + I * (T : ℂ)) (1 / 2 + I * (T : ℂ))
      (fun u hu ↦ by rw [lineSeg_re, hwre, hc2re]; nlinarith [hu.1, hu.2])
      (fun u _ heq ↦ by
        have := congrArg Complex.im heq
        rw [lineSeg_im, hwim, hc2im, Complex.one_im] at this
        simp only [sub_self, mul_zero, add_zero] at this; exact hT.ne' this)
      (fun u _ ↦ hT' _ (by rw [lineSeg_im, hwim, hc2im]; ring))
    simp only [argVariationContourL]
    rw [hseg1, hseg2]; ring
  rw [argVariation_poly_L hT, argVariation_GammaPi_L hT] at hcontour
  have hZval : argVariationContourL riemannZeta T = Real.pi * argZeta T := by
    rw [argZeta]; field_simp
  rw [riemannZeta.N_eq_tsum_riemannXi_order, hbridge, hap, hhalf, hcontour, hZval]
  field_simp
  ring
theorem riemannZeta.N_eq_of_forall_re_mem_Ico {T : ℝ} (hT : 0 < T)
    (h : ∀ σ : ℝ, σ ∈ Set.Ico (1 / 2 : ℝ) 1 →
      riemannZeta ((σ : ℂ) + Complex.I * (T : ℂ)) ≠ 0) :
    riemannZeta.N T = riemannSiegelTheta T / Real.pi + 1 + argZeta T :=
  riemannZeta.N_eq hT (riemannZeta_ne_zero_of_forall_re_mem_Ico hT h)
end
end CountPort68


