-- Prove2me | solution 1 for Arxiv1506_07229.two_dimensional_limit_static_permittivity_positive
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T14:58:13.161447+00:00
-- url     : https://prove2.me/submissions/f57ab7a1-f489-431b-a9ff-f5561a63d1c6

import Mathlib
import Definitions.Def_Arxiv1506_07229_Basic

open MeasureTheory Filter Topology Real ComplexConjugate
namespace Arxiv1506_07229

theorem slab_two_dimensional_electron_gas_limit (n η q ω : ℝ) (hn : 0 < n) (hη : 0 < η)
    (hq : 0 < q) (wp2 : ℝ → ℝ)
    (hwp : Tendsto (fun a => wp2 a * a) (𝓝[>] 0) (𝓝 (4 * π * n))) :
    Tendsto (fun a => (slabInvEps (drudeEps (wp2 a) η ω) a q)⁻¹) (𝓝[>] 0)
      (𝓝 (twoDEGEps n η q ω)) := by
  set s : ℂ := ((ω : ℂ) + (η : ℂ) * Complex.I) ^ 2 with hs
  have hs0 : s ≠ 0 := by
    apply pow_ne_zero; intro h; have := congrArg Complex.im h; simp at this; linarith
  set L : ℂ := -((4 * π * n : ℝ) : ℂ) / s with hL
  have hL0 : L ≠ 0 := by
    rw [hL]; refine div_ne_zero (neg_ne_zero.mpr ?_) hs0
    exact_mod_cast (by positivity : (0:ℝ) < 4 * π * n).ne'
  have hden : 2 + L * q ≠ 0 := by
    intro h
    have h2 : s * 2 = 4 * π * n * q := by
      rw [hL] at h; field_simp at h; push_cast at h ⊢; linear_combination h
    have him := congrArg Complex.im h2
    have hre := congrArg Complex.re h2
    simp [hs, sq] at him hre
    have hω : ω = 0 := by
      rcases mul_eq_zero.mp (show ω * η = 0 by nlinarith) with h | h
      · exact h
      · linarith
    subst hω
    nlinarith [Real.pi_pos, mul_pos (mul_pos Real.pi_pos hn) hq, sq_nonneg η]
  -- e(a) = a * ε(a)
  set e : ℝ → ℂ := fun a => (a : ℂ) - ((wp2 a * a : ℝ) : ℂ) / s with he
  have he_lim : Tendsto e (𝓝[>] 0) (𝓝 L) := by
    have h1 : Tendsto (fun a : ℝ => (a : ℂ)) (𝓝[>] 0) (𝓝 0) := by
      have := (Complex.continuous_ofReal.tendsto (0:ℝ)).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
      simpa using this
    have h2 : Tendsto (fun a => ((wp2 a * a : ℝ) : ℂ)) (𝓝[>] 0) (𝓝 ((4 * π * n : ℝ) : ℂ)) :=
      (Complex.continuous_ofReal.tendsto _).comp hwp
    have := h1.sub (h2.div_const s)
    rw [hL]; convert this using 2; ring
  set r : ℝ → ℂ := fun a => (((Real.exp (a * q) - 1) / a : ℝ) : ℂ) with hr
  have hr_lim : Tendsto r (𝓝[>] 0) (𝓝 (q : ℂ)) := by
    have hd : HasDerivAt (fun a : ℝ => Real.exp (a * q)) q 0 := by
      have := ((hasDerivAt_id (0:ℝ)).mul_const q).exp
      simpa using this
    have hsl := (hasDerivAt_iff_tendsto_slope.mp hd).mono_left
      (nhdsWithin_mono _ (fun x (hx : x ∈ Set.Ioi (0:ℝ)) => ne_of_gt hx))
    have : Tendsto (fun a : ℝ => (Real.exp (a * q) - 1) / a) (𝓝[>] 0) (𝓝 q) := by
      refine hsl.congr' ?_
      filter_upwards with a
      simp [slope_def_field]
    exact (Complex.continuous_ofReal.tendsto _).comp this
  have hcont : ∀ (g : ℝ → ℝ), Continuous g → Tendsto (fun a : ℝ => ((g a : ℝ) : ℂ)) (𝓝[>] 0) (𝓝 ((g 0 : ℝ) : ℂ)) :=
    fun g hg => ((Complex.continuous_ofReal.comp hg).tendsto 0).mono_left nhdsWithin_le_nhds
  have hE := hcont (fun a => Real.exp (a * q / 2)) (by fun_prop)
  have hE2 := hcont (fun a => Real.exp (a * q)) (by fun_prop)
  have hEm := hcont (fun a => Real.exp (-(q * a / 2))) (by fun_prop)
  have hsh := hcont (fun a => Real.sinh (q * a / 2)) (by fun_prop)
  have ha := hcont (fun a => q * a / 2) (by fun_prop)
  have hid := hcont (fun a => a) (by fun_prop)
  simp only [mul_zero, zero_div, neg_zero, Real.exp_zero, Real.sinh_zero, zero_mul] at hE hE2 hEm hsh ha hid
  -- the explicit form
  set F : ℝ → ℂ := fun a =>
    1 + ((q * a / 2 : ℝ) : ℂ) * ((a : ℂ) / e a - 1) +
      (-(e a * r a) * ((1 - (a : ℂ) / e a) * (Real.exp (a * q / 2) : ℂ) /
        (1 + (Real.exp (a * q) : ℂ) + e a * r a))) * (Real.exp (-(q * a / 2)) : ℂ) +
      2 * ((1 - (a : ℂ) / e a) * (Real.exp (a * q / 2) : ℂ) /
        (1 + (Real.exp (a * q) : ℂ) + e a * r a)) * (Real.sinh (q * a / 2) : ℂ) with hF
  have hF_lim : Tendsto F (𝓝[>] 0) (𝓝 (2 / (2 + L * q))) := by
    have hae : Tendsto (fun a : ℝ => (a : ℂ) / e a) (𝓝[>] 0) (𝓝 0) := by
      have := hid.div he_lim hL0; rw [Complex.ofReal_zero, zero_div] at this; exact this
    have hD : Tendsto (fun a : ℝ => 1 + (Real.exp (a * q) : ℂ) + e a * r a) (𝓝[>] 0) (𝓝 (2 + L * q)) := by
      have := (tendsto_const_nhds (x := (1:ℂ))).add hE2 |>.add (he_lim.mul hr_lim)
      convert this using 2; norm_num
    have hA2 : Tendsto (fun a : ℝ => (1 - (a : ℂ) / e a) * (Real.exp (a * q / 2) : ℂ) /
        (1 + (Real.exp (a * q) : ℂ) + e a * r a)) (𝓝[>] 0) (𝓝 (1 / (2 + L * q))) := by
      have := ((tendsto_const_nhds (x := (1:ℂ))).sub hae |>.mul hE).div hD hden
      convert this using 2 <;> simp
    have c1 : Tendsto (fun _ : ℝ => (1:ℂ)) (𝓝[>] 0) (𝓝 1) := tendsto_const_nhds
    have c2 : Tendsto (fun _ : ℝ => (2:ℂ)) (𝓝[>] 0) (𝓝 2) := tendsto_const_nhds
    have t1 := ha.mul (hae.sub c1)
    have t2 := ((he_lim.mul hr_lim).neg.mul hA2).mul hEm
    have t3 := (c2.mul hA2).mul hsh
    have := ((c1.add t1).add t2).add t3
    convert this using 2
    simp only [Complex.ofReal_zero, Complex.ofReal_one]
    field_simp
    ring
  have hev : ∀ᶠ a in 𝓝[>] (0:ℝ), slabInvEps (drudeEps (wp2 a) η ω) a q = F a := by
    filter_upwards [self_mem_nhdsWithin, he_lim.eventually_ne hL0] with a (ha0 : 0 < a) hea
    have ha0' : (a : ℂ) ≠ 0 := by exact_mod_cast ha0.ne'
    have heps : drudeEps (wp2 a) η ω = e a / a := by
      simp only [drudeEps, he]; rw [← hs]; push_cast; field_simp
    have hr' : r a = ((Real.exp (a * q) : ℂ) - 1) / a := by
      simp only [hr]; push_cast; ring
    have hepsne : drudeEps (wp2 a) η ω ≠ 0 := by rw [heps]; exact div_ne_zero hea ha0'
    simp only [hF, slabInvEps, slabA1, slabA2, hr']
    rw [heps]
    have e3 : Real.exp (a * q / 2) = Real.exp (a * q / 2) := rfl
    push_cast
    field_simp
    ring
  have hlim2 : Tendsto (fun a => (slabInvEps (drudeEps (wp2 a) η ω) a q)⁻¹) (𝓝[>] 0)
      (𝓝 (2 / (2 + L * q))⁻¹) :=
    (hF_lim.congr' (hev.mono fun a h => h.symm)).inv₀ (div_ne_zero two_ne_zero hden)
  convert hlim2 using 2
  rw [twoDEGEps, inv_div, hL, ← hs]
  field_simp
  push_cast
  ring

theorem two_dimensional_limit_static_permittivity_positive (n η q : ℝ) (hn : 0 < n)
    (hη : 0 < η) (hq : 0 < q) (wp2 : ℝ → ℝ)
    (hwp : Tendsto (fun a => wp2 a * a) (𝓝[>] 0) (𝓝 (4 * π * n))) :
    Tendsto (fun a => (slabInvEps (drudeEps (wp2 a) η 0) a q)⁻¹) (𝓝[>] 0)
        (𝓝 (((1 + 2 * π * n * q / η ^ 2 : ℝ)) : ℂ)) ∧
      twoDEGEps n η q 0 = ((1 + 2 * π * n * q / η ^ 2 : ℝ) : ℂ) ∧
      0 < 1 + 2 * π * n * q / η ^ 2 := by
  have h2 : twoDEGEps n η q 0 = ((1 + 2 * π * n * q / η ^ 2 : ℝ) : ℂ) := by
    have hη' : (η : ℂ) ≠ 0 := by exact_mod_cast hη.ne'
    unfold twoDEGEps
    push_cast
    rw [zero_add, mul_pow, Complex.I_sq]
    field_simp
    ring
  refine ⟨?_, h2, by positivity⟩
  rw [← h2]
  exact slab_two_dimensional_electron_gas_limit n η q 0 hn hη hq wp2 hwp

end Arxiv1506_07229
open Arxiv1506_07229 in
theorem solution (n η q : ℝ) (hn : 0 < n)
    (hη : 0 < η) (hq : 0 < q) (wp2 : ℝ → ℝ)
    (hwp : Tendsto (fun a => wp2 a * a) (𝓝[>] 0) (𝓝 (4 * π * n))) :
    Tendsto (fun a => (slabInvEps (drudeEps (wp2 a) η 0) a q)⁻¹) (𝓝[>] 0)
        (𝓝 (((1 + 2 * π * n * q / η ^ 2 : ℝ)) : ℂ)) ∧
      twoDEGEps n η q 0 = ((1 + 2 * π * n * q / η ^ 2 : ℝ) : ℂ) ∧
      0 < 1 + 2 * π * n * q / η ^ 2 :=
  two_dimensional_limit_static_permittivity_positive n η q hn hη hq wp2 hwp
