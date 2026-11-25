-- Prove2me | solution 1 for Arxiv1003_4724.long_wave_permittivity_kubo_form
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T16:37:03.441561+00:00
-- url     : https://prove2.me/submissions/32c5289d-0b73-4c2c-b20e-4fd8d11730d1

import Mathlib
import Definitions.Def_Arxiv1003_4724_Basic

open MeasureTheory Filter Topology
namespace Arxiv1003_4724

lemma lw_int (w : ℂ) (hw : 0 < w.im) (f : ℝ → ℂ) (hf : Continuous f) (M : ℝ)
    (hM : ∀ t, ‖f t‖ ≤ M) :
    IntegrableOn (fun t : ℝ => Complex.exp (Complex.I * w * t) * f t) (Set.Ioi 0) := by
  have hb : IntegrableOn (fun t : ℝ => M * Real.exp (-w.im * t)) (Set.Ioi 0) :=
    (integrableOn_exp_mul_Ioi (by linarith) 0).const_mul M
  refine hb.mono' (by fun_prop) (Eventually.of_forall fun t => ?_)
  rw [norm_mul, Complex.norm_exp]
  have : (Complex.I * w * t).re = -w.im * t := by simp
  rw [this, mul_comm]
  exact mul_le_mul_of_nonneg_right (hM t) (Real.exp_pos _).le

lemma lw_tend (w : ℂ) (hw : 0 < w.im) (f : ℝ → ℂ) (M : ℝ)
    (hM : ∀ t, ‖f t‖ ≤ M) :
    Tendsto (fun t : ℝ => Complex.exp (Complex.I * w * t) * f t) atTop (𝓝 0) := by
  have h1 : Tendsto (fun t : ℝ => M * Real.exp (-w.im * t)) atTop (𝓝 0) := by
    have := (Real.tendsto_exp_atBot.comp
      (tendsto_id.const_mul_atTop_of_neg (r := -w.im) (by linarith))).const_mul M
    simpa using this
  refine squeeze_zero_norm (fun t => ?_) h1
  rw [norm_mul, Complex.norm_exp]
  have : (Complex.I * w * t).re = -w.im * t := by simp
  rw [this, mul_comm]
  exact mul_le_mul_of_nonneg_right (hM t) (Real.exp_pos _).le

theorem long_wave_permittivity_kubo_form {A ι : Type*} [Ring A] [StarRing A] [Algebra ℂ A]
    [StarModule ℂ A] [Fintype ι]
    (ω : A →ₗ[ℂ] ℂ) (τ : ℝ → A ≃⋆ₐ[ℂ] A) (Dip Cur : Fin 3 → A)
    (hM : IsLongWaveModel ω τ Dip Cur) (hbar V e : ℝ) (hhbar : 0 < hbar) (hV : 0 < V)
    (he : 0 < e) (N : ι → A) (hN : ∀ a, IsSelfAdjoint (N a)) (z m : ι → ℝ)
    (hm : ∀ a, 0 < m a)
    (h26 : 4 * Real.pi * Complex.I / (3 * hbar * V) * ∑ β, ω ⁅Cur β, Dip β⁆ =
      (plasmaFreqSq z e (meanDensity ω N V) m : ℂ)) :
    (∀ w : ℂ, 0 < w.im →
      1 - (plasmaFreqSq z e (meanDensity ω N V) m : ℂ) / w ^ 2 - phiFn ω τ hbar V Cur w / w ^ 2 =
        1 + 4 * Real.pi * Complex.I * kuboSigma ω τ hbar V Dip Cur w / w) ∧
    (∀ (epsQ sigQ : ℝ → ℝ → ℂ) (x : ℝ), x ≠ 0 → ∀ E s : ℂ,
      (∀ q : ℝ, 0 < q → epsQ q x = 1 + 4 * Real.pi * Complex.I * sigQ q x / x) →
      Tendsto (fun q => epsQ q x) (𝓝[>] (0 : ℝ)) (𝓝 E) →
      Tendsto (fun η : ℝ => 1 - (plasmaFreqSq z e (meanDensity ω N V) m : ℂ) /
          ((x : ℂ) + η * Complex.I) ^ 2 -
          phiFn ω τ hbar V Cur ((x : ℂ) + η * Complex.I) / ((x : ℂ) + η * Complex.I) ^ 2)
        (𝓝[>] (0 : ℝ)) (𝓝 E) →
      Tendsto (fun η : ℝ => kuboSigma ω τ hbar V Dip Cur ((x : ℂ) + η * Complex.I))
        (𝓝[>] (0 : ℝ)) (𝓝 s) →
      E = 1 + 4 * Real.pi * Complex.I * s / x ∧
        Tendsto (fun q => sigQ q x) (𝓝[>] (0 : ℝ)) (𝓝 s)) := by
  obtain ⟨-, hdyn, hst, -, hder, hcc⟩ := hM
  have hinv : ∀ s X, τ (-s) (τ s X) = X := fun s X => by
    rw [← hdyn.2, neg_add_cancel, hdyn.1]
  have hinv' : ∀ s X, τ s (τ (-s) X) = X := fun s X => by
    rw [← hdyn.2, add_neg_cancel, hdyn.1]
  have hmem1 : ∀ β : Fin 3, Cur β ∈ ({Dip β, Cur β} : Set A) := fun β => by simp
  have hmem2 : ∀ β : Fin 3, Dip β ∈ ({Dip β, Cur β} : Set A) := fun β => by simp
  -- derivative of C_IP is -C_II
  have hcd : ∀ β : Fin 3, ∀ t, HasDerivAt (commCorr ω τ (Cur β) (Dip β))
      (-commCorr ω τ (Cur β) (Cur β) t) t := by
    intro β t
    have e1 : commCorr ω τ (Cur β) (Dip β) =
        fun s => ω (Cur β * τ (-s) (Dip β)) - ω (τ (-s) (Dip β) * Cur β) := by
      funext s
      simp only [commCorr, Ring.lie_def, map_sub]
      congr 1
      · rw [← hst (-s), map_mul, hinv]
      · rw [← hst (-s), map_mul, hinv]
    have d1 := HasDerivAt.scomp t (hder β (Cur β) (-t)).2 (hasDerivAt_neg t)
    have d2 := HasDerivAt.scomp t (hder β (Cur β) (-t)).1 (hasDerivAt_neg t)
    rw [e1]
    refine (d1.sub d2).congr_deriv ?_
    simp only [commCorr, Ring.lie_def, map_sub]
    have a1 : ω (τ t (Cur β) * Cur β) = ω (Cur β * τ (-t) (Cur β)) := by
      rw [← hst t (Cur β * τ (-t) (Cur β)), map_mul (τ t), hinv']
    have a2 : ω (Cur β * τ t (Cur β)) = ω (τ (-t) (Cur β) * Cur β) := by
      rw [← hst t (τ (-t) (Cur β) * Cur β), map_mul (τ t), hinv']
    rw [a1, a2]
    simp only [neg_smul, one_smul]
    ring
  have part1 : ∀ w : ℂ, 0 < w.im →
      1 - (plasmaFreqSq z e (meanDensity ω N V) m : ℂ) / w ^ 2 - phiFn ω τ hbar V Cur w / w ^ 2 =
        1 + 4 * Real.pi * Complex.I * kuboSigma ω τ hbar V Dip Cur w / w := by
    intro w hw
    have hw0 : w ≠ 0 := by intro h; rw [h] at hw; simp at hw
    have hK : ∀ β : Fin 3,
        (∫ t in Set.Ioi (0:ℝ), Complex.exp (Complex.I * w * t) * commCorr ω τ (Cur β) (Dip β) t)
          = ((∫ t in Set.Ioi (0:ℝ), Complex.exp (Complex.I * w * t) *
              commCorr ω τ (Cur β) (Cur β) t) - ω ⁅Cur β, Dip β⁆) / (Complex.I * w) := by
      intro β
      obtain ⟨cIP, MIP, hMIP⟩ := hcc β (Cur β) (hmem1 β) (Dip β) (hmem2 β)
      obtain ⟨cII, MII, hMII⟩ := hcc β (Cur β) (hmem1 β) (Cur β) (hmem1 β)
      have i1 := lw_int w hw _ cIP MIP hMIP
      have i2 := lw_int w hw _ cII MII hMII
      have hF : ∀ t : ℝ, HasDerivAt
          (fun t : ℝ => Complex.exp (Complex.I * w * t) * commCorr ω τ (Cur β) (Dip β) t)
          (Complex.I * w * (Complex.exp (Complex.I * w * t) * commCorr ω τ (Cur β) (Dip β) t)
            - Complex.exp (Complex.I * w * t) * commCorr ω τ (Cur β) (Cur β) t) t := by
        intro t
        have h0 : HasDerivAt (fun t : ℝ => Complex.I * w * (t:ℂ)) (Complex.I * w * 1) t :=
          ((hasDerivAt_id t).ofReal_comp).const_mul _
        exact (h0.cexp.mul (hcd β t)).congr_deriv (by ring)
      have hfi := integral_Ioi_of_hasDerivAt_of_tendsto' (a := 0) (fun t _ => hF t)
        ((i1.const_mul (Complex.I * w)).sub i2) (lw_tend w hw _ MIP hMIP)
      rw [integral_sub (i1.const_mul _) i2, integral_const_mul] at hfi
      have hc0 : commCorr ω τ (Cur β) (Dip β) 0 = ω ⁅Cur β, Dip β⁆ := by
        simp [commCorr, hdyn.1]
      simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul, hc0, zero_sub] at hfi
      have hIw : Complex.I * w ≠ 0 := mul_ne_zero Complex.I_ne_zero hw0
      field_simp
      linear_combination hfi
    unfold phiFn kuboSigma retardedGreen
    simp only [hK, ← Finset.mul_sum, ← Finset.sum_div, Finset.sum_sub_distrib]
    rw [← h26]
    have hh : (hbar : ℂ) ≠ 0 := by exact_mod_cast hhbar.ne'
    have hV' : (V : ℂ) ≠ 0 := by exact_mod_cast hV.ne'
    field_simp
    ring_nf
  refine ⟨part1, ?_⟩
  intro epsQ sigQ x hx E s hQ hE hE2 hs
  have hx' : (x : ℂ) ≠ 0 := by exact_mod_cast hx
  have hw : Tendsto (fun η : ℝ => (x : ℂ) + η * Complex.I) (𝓝[>] (0 : ℝ)) (𝓝 (x : ℂ)) := by
    have : Tendsto (fun η : ℝ => (x : ℂ) + η * Complex.I) (𝓝 (0 : ℝ))
        (𝓝 ((x : ℂ) + ((0:ℝ):ℂ) * Complex.I)) := ((by fun_prop :
          Continuous fun η : ℝ => (x : ℂ) + η * Complex.I).tendsto 0)
    simpa using this.mono_left nhdsWithin_le_nhds
  have hR : Tendsto (fun η : ℝ => 1 + 4 * Real.pi * Complex.I *
      kuboSigma ω τ hbar V Dip Cur ((x : ℂ) + η * Complex.I) / ((x : ℂ) + η * Complex.I))
      (𝓝[>] (0 : ℝ)) (𝓝 (1 + 4 * Real.pi * Complex.I * s / x)) :=
    tendsto_const_nhds.add ((tendsto_const_nhds.mul hs).div hw hx')
  have hE3 : Tendsto (fun η : ℝ => 1 + 4 * Real.pi * Complex.I *
      kuboSigma ω τ hbar V Dip Cur ((x : ℂ) + η * Complex.I) / ((x : ℂ) + η * Complex.I))
      (𝓝[>] (0 : ℝ)) (𝓝 E) := by
    refine hE2.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with η hη
    apply part1
    simpa using hη
  have hEq : E = 1 + 4 * Real.pi * Complex.I * s / x := tendsto_nhds_unique hE3 hR
  refine ⟨hEq, ?_⟩
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hT : Tendsto (fun q => (epsQ q x - 1) * x / (4 * Real.pi * Complex.I))
      (𝓝[>] (0 : ℝ)) (𝓝 ((E - 1) * x / (4 * Real.pi * Complex.I))) :=
    ((hE.sub tendsto_const_nhds).mul_const _).div_const _
  have hv : (E - 1) * x / (4 * Real.pi * Complex.I) = s := by
    rw [hEq]; field_simp; ring
  rw [hv] at hT
  refine hT.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with q hq
  rw [hQ q hq]
  field_simp
  ring

end Arxiv1003_4724
open Arxiv1003_4724 in
theorem solution {A ι : Type*} [Ring A] [StarRing A] [Algebra ℂ A]
    [StarModule ℂ A] [Fintype ι]
    (ω : A →ₗ[ℂ] ℂ) (τ : ℝ → A ≃⋆ₐ[ℂ] A) (Dip Cur : Fin 3 → A)
    (hM : IsLongWaveModel ω τ Dip Cur) (hbar V e : ℝ) (hhbar : 0 < hbar) (hV : 0 < V)
    (he : 0 < e) (N : ι → A) (hN : ∀ a, IsSelfAdjoint (N a)) (z m : ι → ℝ)
    (hm : ∀ a, 0 < m a)
    (h26 : 4 * Real.pi * Complex.I / (3 * hbar * V) * ∑ β, ω ⁅Cur β, Dip β⁆ =
      (plasmaFreqSq z e (meanDensity ω N V) m : ℂ)) :
    (∀ w : ℂ, 0 < w.im →
      1 - (plasmaFreqSq z e (meanDensity ω N V) m : ℂ) / w ^ 2 - phiFn ω τ hbar V Cur w / w ^ 2 =
        1 + 4 * Real.pi * Complex.I * kuboSigma ω τ hbar V Dip Cur w / w) ∧
    (∀ (epsQ sigQ : ℝ → ℝ → ℂ) (x : ℝ), x ≠ 0 → ∀ E s : ℂ,
      (∀ q : ℝ, 0 < q → epsQ q x = 1 + 4 * Real.pi * Complex.I * sigQ q x / x) →
      Tendsto (fun q => epsQ q x) (𝓝[>] (0 : ℝ)) (𝓝 E) →
      Tendsto (fun η : ℝ => 1 - (plasmaFreqSq z e (meanDensity ω N V) m : ℂ) /
          ((x : ℂ) + η * Complex.I) ^ 2 -
          phiFn ω τ hbar V Cur ((x : ℂ) + η * Complex.I) / ((x : ℂ) + η * Complex.I) ^ 2)
        (𝓝[>] (0 : ℝ)) (𝓝 E) →
      Tendsto (fun η : ℝ => kuboSigma ω τ hbar V Dip Cur ((x : ℂ) + η * Complex.I))
        (𝓝[>] (0 : ℝ)) (𝓝 s) →
      E = 1 + 4 * Real.pi * Complex.I * s / x ∧
        Tendsto (fun q => sigQ q x) (𝓝[>] (0 : ℝ)) (𝓝 s)) :=
  long_wave_permittivity_kubo_form ω τ Dip Cur hM hbar V e hhbar hV he N hN z m hm h26
