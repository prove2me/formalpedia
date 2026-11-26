-- Prove2me | Definitions.Def_RHT1000_Support_20261118_B003
-- name    : RHT1000_Support_20261118_B003
-- status  : Definition
-- author  : @bueno_ricardo
-- created : 2026-11-18T16:27:04.837634+00:00
-- url     : https://prove2.me/theorems/7dbafe58-656a-424d-ae66-7b4c778ddc45
-- title:
--   Suporte completo para T1000 — bloco 3 de 10
-- statement:
--   Definições e lemas auxiliares completos para a prova finita T1000. Este bloco não afirma sozinho a conclusão T1000 nem RH. A divisão reduz o tempo de compilação sem substituir demonstrações por hipóteses.
-- source:
--   Código adaptado de Salvatore Mercuri e Bhavik Mehta, smmercuri/zeta, tag v1-1e8 (3dab648), com dependências e avisos de autoria preservados. Fonte histórica integral T1000: https://axle.axiommath.ai/check#r=d2dcb520-c50a-44dc-a527-de0f7a51b892 . Reorganização em módulos ordinários para compatibilidade com Prove2Me; atribuição da adaptação: projeto Desenvolvimento RH, Ricardo Marangoni Brandão Bueno.

import Definitions.Def_RHT1000_Support_20261118_B002
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
section CertificatePort27
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
end CertificatePort27

section CertificatePort28
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
end CertificatePort28

section CertificatePort29
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
end CertificatePort29

section CertificatePort30
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
end CertificatePort30

section CertificatePort31
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
end CertificatePort31

section CertificatePort32
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
end CertificatePort32

section CertificatePort33
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
end CertificatePort33

section CertificatePort34
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
theorem zetaEMExpansion_eq_approximant_add_remainder (s : ℂ) (M N : ℕ) :
    zetaEMExpansion s M N = zetaApproximant s M N + zetaRemainder s M N := by
  rw [zetaEMExpansion, zetaApproximant, zetaRemainder]; ring
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
theorem riemannZeta_eq_approximant_add_remainder (s : ℂ) (M N : ℕ) (hN : 1 ≤ N)
    (hs : -(2 * M + 1 : ℝ) < s.re) (hs1 : s ≠ 1) :
    riemannZeta s = zetaApproximant s M N + zetaRemainder s M N := by
  rw [riemannZeta_eq s M N hN hs hs1, zetaEMExpansion_eq_approximant_add_remainder]
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
end CertificatePort34

section CertificatePort35
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
end CertificatePort35

section CertificatePort36
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
end CertificatePort36

section CertificatePort37
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
noncomputable abbrev nth_prime' (n : ℕ) : ℕ :=
  Nat.nth Nat.Prime (n - 1)
noncomputable abbrev Psi (x : ℝ) : ℝ := ψ x
noncomputable def M (x : ℝ) : ℝ :=
  ∑ n ∈ Iic ⌊x⌋₊, (μ n : ℝ)
noncomputable abbrev nth_prime_gap (n : ℕ) : ℕ :=
  nth_prime (n + 1) - nth_prime n
def prime_gap_record (p g : ℕ) : Prop :=
  ∃ n, nth_prime n = p ∧ nth_prime_gap n = g ∧
    ∀ k, nth_prime k < p → nth_prime_gap k < g
open Classical in
noncomputable def first_gap (g : ℕ) : ℕ :=
  if h : ∃ n, nth_prime_gap n = g then
    nth_prime (Nat.find h)
  else 0
def first_gap_record (g P : ℕ) : Prop :=
  first_gap g = P ∧
    ∀ g' ∈ Finset.Ico 1 g,
      Even g' ∨ g' = 1 → first_gap g' ∈ Set.Ico 1 P
def HasPrimeInInterval (x h : ℝ) : Prop :=
  ∃ p : ℕ, Nat.Prime p ∧ x < p ∧ p ≤ x + h
def HasPrimeInInterval.log_thm (X₀ : ℝ) (k : ℝ) :=
  ∀ x ≥ X₀, HasPrimeInInterval x (x / (log x) ^ k)
noncomputable def pi (x : ℝ) : ℝ :=
  Nat.primeCounting ⌊x⌋₊
noncomputable def pi_star (x : ℝ) : ℝ :=
  ∑' (k : ℕ), pi (x ^ (1 / (k + 1 : ℝ))) / (k + 1 : ℝ)
noncomputable def li (x : ℝ) : ℝ :=
  lim ((𝓝[>] (0 : ℝ)).map (fun ε ↦
    ∫ t in Set.diff (Set.Ioc 0 x) (Set.Ioo (1 - ε) (1 + ε)),
      1 / log t))
noncomputable def Li (x : ℝ) : ℝ := ∫ t in 2..x, 1 / log t
noncomputable def Eψ (x : ℝ) : ℝ := |ψ x - x| / x
noncomputable def admissible_bound (A B C R : ℝ) (x : ℝ) :=
  A * (log x / R) ^ B * exp (-C * (log x / R) ^ ((1 : ℝ) / (2 : ℝ)))
def Eψ.classicalBound (A B C R x₀ : ℝ) : Prop :=
  ∀ x ≥ x₀, Eψ x ≤ admissible_bound A B C R x
def Eψ.bound (ε x₀ : ℝ) : Prop := ∀ x ≥ x₀, Eψ x ≤ ε
def Eψ.numericalBound (x₀ : ℝ) (ε : ℝ → ℝ) : Prop :=
  Eψ.bound (ε x₀) x₀
noncomputable def Eπ (x : ℝ) : ℝ :=
  |pi x - Li x| / (x / log x)
noncomputable def Eπ_star (x : ℝ) : ℝ :=
  |pi_star x - Li x| / (x / log x)
noncomputable def Eθ (x : ℝ) : ℝ := |θ x - x| / x
def Eθ.classicalBound (A B C R x₀ : ℝ) : Prop :=
  ∀ x ≥ x₀, Eθ x ≤ admissible_bound A B C R x
def Eθ.numericalBound (x₀ : ℝ) (ε : ℝ → ℝ) : Prop :=
  ∀ x ≥ x₀, Eθ x ≤ ε x₀
def Eπ.classicalBound (A B C R x₀ : ℝ) : Prop :=
  ∀ x ≥ x₀, Eπ x ≤ admissible_bound A B C R x
def Eπ.bound (ε x₀ : ℝ) : Prop := ∀ x ≥ x₀, Eπ x ≤ ε
def Eπ.numericalBound (x₀ : ℝ) (ε : ℝ → ℝ) : Prop :=
  Eπ.bound (ε x₀) x₀
def Eπ.vinogradovBound (A B C x₀ : ℝ) : Prop :=
  ∀ x ≥ x₀, Eπ x ≤
    A * (log x) ^ B * exp (-C * (log x) ^ ((3 : ℝ) / 5) / (log (log x)) ^ ((1 : ℝ) / 5))
def Eπ_star.classicalBound (A B C R x₀ : ℝ) : Prop :=
  ∀ x ≥ x₀, Eπ_star x ≤ admissible_bound A B C R x
def Eπ_star.bound (ε x₀ : ℝ) : Prop :=
  ∀ x ≥ x₀, Eπ_star x ≤ ε
def Eπ_star.numericalBound (x₀ : ℝ) (ε : ℝ → ℝ) : Prop :=
  Eπ_star.bound (ε x₀) x₀
def Eπ_star.vinogradovBound (A B C x₀ : ℝ) : Prop :=
  ∀ x ≥ x₀, Eπ_star x ≤
    A * (log x) ^ B * exp (-C * (log x) ^ ((3 : ℝ) / 5) / (log (log x)) ^ ((1 : ℝ) / 5))
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
end CertificatePort37

section CertificatePort38
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
noncomputable def riemannZeta.RH_up_to (T : ℝ) : Prop :=
  IsEmpty (riemannZeta.zeroes_rect (Set.Ioo 0.5 1) (Set.Icc 0 T))
noncomputable def riemannZeta.classicalZeroFree (R : ℝ) :=
  ∀ (σ t : ℝ), t ≥ 3 → σ ≥ 1 - 1 / (R * log t) →
  riemannZeta (σ + t * Complex.I) ≠ 0
noncomputable def riemannZeta.N (T : ℝ) : ℝ := zeroes_sum Set.univ (Set.Ioo 0 T) (fun _ ↦ 1)
noncomputable def riemannZeta.N' (σ T : ℝ) : ℝ := zeroes_sum (Set.Ioo σ 1) (Set.Ioo 0 T) 1
noncomputable def riemannZeta.RvM (b₁ b₂ b₃ T : ℝ) : ℝ :=
  b₁ * log T + b₂ * log (log T) + b₃
def riemannZeta.Riemann_vonMangoldt_bound (b₁ b₂ b₃ : ℝ) : Prop :=
  ∀ T ≥ 2, |riemannZeta.N T - (T / (2 * π) * log (T / (2 * π)) - T / (2 * π) + 7 / 8)| ≤
    RvM b₁ b₂ b₃ T
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
end CertificatePort38

section CertificatePort39
public section
open scoped Complex ComplexConjugate
set_option backward.isDefEq.respectTransparency false in
theorem intervalIntegral_conj {f : ℝ → ℂ} {a b : ℝ} :
    ∫ (x : ℝ) in a..b, conj (f x) = conj (∫ (x : ℝ) in a..b, f x) := by
  rw [intervalIntegral.intervalIntegral_eq_integral_uIoc, integral_conj, ← RCLike.conj_smul,
    ← intervalIntegral.intervalIntegral_eq_integral_uIoc]
end
end CertificatePort39

section CertificatePort40
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
end CertificatePort40

section CertificatePort41
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
end CertificatePort41


