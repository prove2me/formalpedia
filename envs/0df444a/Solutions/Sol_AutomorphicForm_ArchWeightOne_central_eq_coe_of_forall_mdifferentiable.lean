-- Prove2me | solution 1 for AutomorphicForm.ArchWeightOne.central_eq_coe_of_forall_mdifferentiable
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/cfaedbcf-3f72-51ec-b611-5a40d3d2d8ad

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_ArchWeightOne_central_eq_coe_of_forall_mdifferentiable

set_option autoImplicit false

open scoped Manifold Topology
open Complex Filter Metric Set

noncomputable section

namespace Q1CentralExp

abbrev S (z : UpperHalfPlane) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(z.im : ℝ), (z.re : ℝ); 0, 1]
    (by simp [Matrix.det_fin_two_of]; exact z.im_ne_zero)

abbrev R (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![a, b; -b, a]
    (by rw [Matrix.det_fin_two_of, show a * a - b * -b = a ^ 2 + b ^ 2 by ring, hab]
        exact one_ne_zero)

abbrev W : GL (Fin 2) ℝ := R 0 1 (by norm_num)

theorem S_I : S UpperHalfPlane.I = 1 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [UpperHalfPlane.I_im, UpperHalfPlane.I_re]

def winv (z : UpperHalfPlane) : UpperHalfPlane :=
  ⟨⟨-(z.re : ℝ) / ((z.re : ℝ) ^ 2 + (z.im : ℝ) ^ 2), (z.im : ℝ) / ((z.re : ℝ) ^ 2 + (z.im : ℝ) ^ 2)⟩,
    by
      show 0 < (z.im : ℝ) / ((z.re : ℝ) ^ 2 + (z.im : ℝ) ^ 2)
      have := z.im_pos
      positivity⟩

private theorem _root_.Q1CentralExp.normSq_pos (z : UpperHalfPlane) : 0 < (z.re : ℝ) ^ 2 + (z.im : ℝ) ^ 2 := by
  have := z.im_pos; positivity

p2m_export "Q1CentralExp" "normSq_pos"
theorem winv_re (z : UpperHalfPlane) :
    (winv z).re = -(z.re : ℝ) / ((z.re : ℝ) ^ 2 + (z.im : ℝ) ^ 2) := rfl

theorem winv_im (z : UpperHalfPlane) :
    (winv z).im = (z.im : ℝ) / ((z.re : ℝ) ^ 2 + (z.im : ℝ) ^ 2) := rfl

theorem coe_winv (z : UpperHalfPlane) : ((winv z : UpperHalfPlane) : ℂ) = -((z : ℂ))⁻¹ := by
  have hz : (z : ℂ) ≠ 0 := UpperHalfPlane.ne_zero z
  have hns : ((z.re : ℝ) ^ 2 + (z.im : ℝ) ^ 2 : ℝ) ≠ 0 := (normSq_pos z).ne'
  have hzc : (z : ℂ) = ⟨z.re, z.im⟩ := by apply Complex.ext <;> simp
  rw [hzc]
  apply Complex.ext
  · show -(z.re : ℝ) / ((z.re : ℝ) ^ 2 + (z.im : ℝ) ^ 2) = _
    simp [Complex.inv_re, Complex.normSq_mk]
    field_simp
  · show (z.im : ℝ) / ((z.re : ℝ) ^ 2 + (z.im : ℝ) ^ 2) = _
    simp [Complex.inv_im, Complex.normSq_mk]
    field_simp

def lam (z : UpperHalfPlane) : ℝ := Real.sqrt ((z.re : ℝ) ^ 2 + (z.im : ℝ) ^ 2)

theorem lam_pos (z : UpperHalfPlane) : 0 < lam z := Real.sqrt_pos.mpr (normSq_pos z)

theorem lam_sq (z : UpperHalfPlane) : lam z ^ 2 = (z.re : ℝ) ^ 2 + (z.im : ℝ) ^ 2 :=
  Real.sq_sqrt (normSq_pos z).le

theorem lam_eq_norm (z : UpperHalfPlane) : lam z = ‖(z : ℂ)‖ := by
  rw [lam, Complex.norm_eq_sqrt_sq_add_sq]
  simp

theorem rot_param (z : UpperHalfPlane) :
    (-(z.re : ℝ) / lam z) ^ 2 + ((z.im : ℝ) / lam z) ^ 2 = 1 := by
  have hl := lam_pos z
  have hl2 := lam_sq z
  field_simp
  nlinarith [hl2]

theorem W_mul_S (z : UpperHalfPlane) :
    W * S z = S (winv z) * R (-(z.re : ℝ) / lam z) ((z.im : ℝ) / lam z) (rot_param z) *
      Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 (lam z) (lam_pos z).ne') := by
  have hl := lam_pos z
  have hl2 := lam_sq z
  have hns : ((z.re : ℝ) ^ 2 + (z.im : ℝ) ^ 2 : ℝ) ≠ 0 := (normSq_pos z).ne'
  apply Units.ext
  ext i j
  simp only [Units.val_mul]
  show (!![(0 : ℝ), 1; -1, 0] * !![(z.im : ℝ), (z.re : ℝ); 0, 1]) i j
    = (!![((winv z).im : ℝ), ((winv z).re : ℝ); 0, 1] * !![-(z.re : ℝ) / lam z, (z.im : ℝ) / lam z;
        -((z.im : ℝ) / lam z), -(z.re : ℝ) / lam z] * (Matrix.scalar (Fin 2) (lam z))) i j
  rw [winv_im, winv_re]
  have hl0 : lam z ≠ 0 := hl.ne'
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.scalar_apply, Matrix.diagonal]
  · left; field_simp; ring
  · field_simp; linarith [hl2]
  · field_simp
  · field_simp

end Q1CentralExp

end

open Q1CentralExp in
theorem solution
    (F : GL (Fin 2) ℝ → ℂ) (ω : ℝˣ → ℂ)
    (hrot : ∀ (g : GL (Fin 2) ℝ) (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1),
      F (g * Matrix.GeneralLinearGroup.mkOfDetNeZero !![a, b; -b, a]
        (by rw [Matrix.det_fin_two_of, show a * a - b * -b = a ^ 2 + b ^ 2 by ring, hab]
            exact one_ne_zero)) = (⟨a, b⟩ : ℂ) * F g)
    (hcen : ∀ (g : GL (Fin 2) ℝ) (t : ℝˣ), 0 < (t : ℝ) →
      F (g * Matrix.GeneralLinearGroup.scalar (Fin 2) t) = ω t * F g)
    (hhol : ∀ m : GL (Fin 2) ℝ, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) fun z : UpperHalfPlane =>
      ((z.im : ℝ) : ℂ)⁻¹ * F (m * Matrix.GeneralLinearGroup.mkOfDetNeZero
        !![(z.im : ℝ), (z.re : ℝ); 0, 1] (by simp [Matrix.det_fin_two_of]; exact z.im_ne_zero)))
    (hne : ∃ g : GL (Fin 2) ℝ, F g ≠ 0)
    (t : ℝˣ) (ht : 0 < (t : ℝ)) :
    ω t = ((t : ℝ) : ℂ) := by
  obtain ⟨g₀, hg₀⟩ := hne

  let u : ∀ r : ℝ, 0 < r → ℝˣ := fun r hr => Units.mk0 r hr.ne'

  have hω1 : ω 1 = 1 := by
    have h := hcen g₀ 1 (by simp)
    rw [map_one, mul_one] at h
    exact (mul_eq_right₀ hg₀).mp h.symm
  have hωmul : ∀ (r s : ℝ) (hr : 0 < r) (hs : 0 < s),
      ω (u (r * s) (mul_pos hr hs)) = ω (u r hr) * ω (u s hs) := by
    intro r s hr hs
    have hprod : u (r * s) (mul_pos hr hs) = u r hr * u s hs := by ext; rfl
    have h1 := hcen g₀ (u (r * s) (mul_pos hr hs)) (mul_pos hr hs)
    rw [hprod, map_mul, ← mul_assoc, hcen _ (u s hs) hs, hcen _ (u r hr) hr, ← mul_assoc] at h1
    have := mul_right_cancel₀ hg₀ h1
    rw [hprod, ← this, mul_comm]

  set ψ : ℝ → ℂ := fun r => if hr : 0 < r then ω (u r hr) / (r : ℂ) else 0 with hψdef
  have hψ1 : ψ 1 = 1 := by
    rw [hψdef]
    simp only [dif_pos one_pos]
    rw [show u 1 one_pos = 1 by ext; rfl, hω1]; simp

  set U : Set ℂ := {z : ℂ | 0 < z.im} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_im
  set fH : UpperHalfPlane → ℂ := fun z => ((z.im : ℝ) : ℂ)⁻¹ * F (g₀ * S z) with hfHdef
  have hfH : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) fH := hhol g₀
  set fC : ℂ → ℂ := fH ∘ UpperHalfPlane.ofComplex with hfCdef
  have hfC : DifferentiableOn ℂ fC U := UpperHalfPlane.mdifferentiable_iff.mp hfH
  have hfCi : fC Complex.I = F g₀ := by
    have : fC Complex.I = fH UpperHalfPlane.I := by
      rw [hfCdef, Function.comp_apply]
      rw [show (Complex.I : ℂ) = ((UpperHalfPlane.I : UpperHalfPlane) : ℂ) from rfl,
        UpperHalfPlane.ofComplex_apply]
    rw [this, hfHdef]
    simp only [S_I, mul_one, UpperHalfPlane.I_im]
    simp

  set HH : UpperHalfPlane → ℂ := fun z => ((z.im : ℝ) : ℂ)⁻¹ * F (g₀ * W * S z) with hHHdef
  have hHH : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) HH := hhol (g₀ * W)
  set HC : ℂ → ℂ := HH ∘ UpperHalfPlane.ofComplex with hHCdef
  have hHC : DifferentiableOn ℂ HC U := UpperHalfPlane.mdifferentiable_iff.mp hHH

  have hident : ∀ z : UpperHalfPlane,
      HH z = ψ (lam z) * (fH (winv z) * (-((z : ℂ))⁻¹)) := by
    intro z
    have hl := lam_pos z
    have hl2 := lam_sq z
    have hns : ((z.re : ℝ) ^ 2 + (z.im : ℝ) ^ 2 : ℝ) ≠ 0 := (normSq_pos z).ne'
    have hmat := W_mul_S z

    have hF : F (g₀ * W * S z) = ω (u (lam z) hl) *
        ((⟨-(z.re : ℝ) / lam z, (z.im : ℝ) / lam z⟩ : ℂ) * F (g₀ * S (winv z))) := by
      rw [mul_assoc g₀, hmat, ← mul_assoc, ← mul_assoc, hcen _ _ hl, hrot _ _ _ (rot_param z)]

    rw [hHHdef, hfHdef]
    simp only
    rw [hF]
    have hy : ((z.im : ℝ) : ℂ) ≠ 0 := by exact_mod_cast z.im_ne_zero
    have hlc : ((lam z : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hl.ne'
    have hy' : (((winv z).im : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (winv z).im_ne_zero
    have hψl : ψ (lam z) = ω (u (lam z) hl) * ((lam z : ℝ) : ℂ)⁻¹ := by
      rw [hψdef]; simp only [dif_pos hl]; rw [div_eq_mul_inv]

    have ofReal_mul_mk : ∀ r a b : ℝ, ((r : ℂ) * (⟨a, b⟩ : ℂ)) = ⟨r * a, r * b⟩ := by
      intro r a b; apply Complex.ext <;> simp
    have key2 : ((z.im : ℝ) : ℂ)⁻¹ * (⟨-(z.re : ℝ) / lam z, (z.im : ℝ) / lam z⟩ : ℂ)
        = ((lam z : ℝ) : ℂ)⁻¹ * ((((winv z).im : ℝ) : ℂ)⁻¹ * (-((z : ℂ))⁻¹)) := by
      rw [← coe_winv z]
      rw [show ((winv z : UpperHalfPlane) : ℂ) = ⟨(winv z).re, (winv z).im⟩ by
        apply Complex.ext <;> simp]
      rw [winv_re, winv_im, ← Complex.ofReal_inv, ← Complex.ofReal_inv, ← Complex.ofReal_inv,
        ofReal_mul_mk, ofReal_mul_mk, ofReal_mul_mk]
      have hyr : (z.im : ℝ) ≠ 0 := z.im_ne_zero
      have hl0 : lam z ≠ 0 := hl.ne'
      apply Complex.ext
      · simp only; field_simp
      · simp only; field_simp
    calc ((z.im : ℝ) : ℂ)⁻¹ * (ω (u (lam z) hl) * ((⟨-(z.re : ℝ) / lam z, (z.im : ℝ) / lam z⟩ : ℂ) *
            F (g₀ * S (winv z))))
        = ω (u (lam z) hl) * (((z.im : ℝ) : ℂ)⁻¹ * (⟨-(z.re : ℝ) / lam z, (z.im : ℝ) / lam z⟩ : ℂ)) *
            F (g₀ * S (winv z)) := by ring
      _ = ω (u (lam z) hl) * (((lam z : ℝ) : ℂ)⁻¹ * ((((winv z).im : ℝ) : ℂ)⁻¹ * (-((z : ℂ))⁻¹))) *
            F (g₀ * S (winv z)) := by rw [key2]
      _ = _ := by rw [hψl]; ring

  set GC : ℂ → ℂ := fun z => fC (-z⁻¹) * (-z⁻¹) with hGCdef
  have hmapsU : MapsTo (fun z : ℂ => -z⁻¹) U U := by
    intro z hz
    show 0 < (-z⁻¹).im
    have hz0 : z ≠ 0 := fun h => by rw [h] at hz; simp [hU] at hz
    rw [Complex.neg_im, Complex.inv_im, neg_div, neg_neg]
    exact div_pos hz (Complex.normSq_pos.mpr hz0)
  have hGC : DifferentiableOn ℂ GC U := by
    have hinv : DifferentiableOn ℂ (fun z : ℂ => -z⁻¹) U := by
      refine DifferentiableOn.neg (differentiableOn_inv.mono ?_)
      intro z hz h0
      simp only [hU, Set.mem_setOf_eq] at hz
      have h0' : z = 0 := h0
      rw [h0'] at hz; simp at hz
    exact (hfC.comp hinv hmapsU).mul hinv
  have hidentC : ∀ z ∈ U, HC z = ψ ‖z‖ * GC z := by
    intro z hz
    have hzz : UpperHalfPlane.ofComplex z = ⟨z, hz⟩ := UpperHalfPlane.ofComplex_apply_of_im_pos hz
    rw [hHCdef, hGCdef, hfCdef]
    simp only [Function.comp_apply]
    rw [hzz, hident ⟨z, hz⟩, lam_eq_norm]
    congr 2
    rw [← coe_winv ⟨z, hz⟩, UpperHalfPlane.ofComplex_apply]

  have hGCi : GC Complex.I ≠ 0 := by
    rw [hGCdef]
    simp only
    rw [show -(Complex.I)⁻¹ = Complex.I by simp, hfCi]
    exact mul_ne_zero hg₀ Complex.I_ne_zero
  have hIU : Complex.I ∈ U := by simp [hU]
  obtain ⟨ρ, hρpos, hρ⟩ : ∃ ρ > 0, ball Complex.I ρ ⊆ U ∩ {z | GC z ≠ 0} := by
    have hopen : IsOpen (U ∩ {z | GC z ≠ 0}) := by
      rw [Set.inter_comm]
      exact hGC.continuousOn.isOpen_inter_preimage hUo isOpen_ne
        |> fun h => by simpa [Set.inter_comm, Set.preimage] using h
    exact Metric.isOpen_iff.mp hopen Complex.I ⟨hIU, hGCi⟩
  set B : Set ℂ := ball Complex.I ρ with hB
  have hBU : B ⊆ U := fun z hz => (hρ hz).1
  have hBne : ∀ z ∈ B, GC z ≠ 0 := fun z hz => (hρ hz).2

  set Ψ : ℂ → ℂ := fun z => HC z / GC z with hΨdef'
  have hΨ : DifferentiableOn ℂ Ψ B := (hHC.mono hBU).div (hGC.mono hBU) hBne
  have hΨeq : ∀ z ∈ B, Ψ z = ψ ‖z‖ := by
    intro z hz
    rw [hΨdef']
    simp only
    rw [hidentC z (hBU hz), mul_div_assoc, div_self (hBne z hz), mul_one]

  have hBo : IsOpen B := isOpen_ball
  have hderiv0 : ∀ z ∈ B, deriv Ψ z = 0 := by
    intro z₁ hz₁
    have hz₁0 : z₁ ≠ 0 := by
      intro h; have := hBU hz₁; rw [h] at this; simp [hU] at this
    have hd : HasDerivAt Ψ (deriv Ψ z₁) z₁ := (hΨ.differentiableAt (hBo.mem_nhds hz₁)).hasDerivAt

    set γ : ℂ → ℂ := fun s => z₁ * Complex.exp (s * Complex.I) with hγdef
    have hγ0 : γ 0 = z₁ := by simp [hγdef]
    have hγd : HasDerivAt γ (z₁ * (Complex.exp (0 * Complex.I) * Complex.I)) 0 := by
      have h1 : HasDerivAt (fun s : ℂ => s * Complex.I) Complex.I 0 := by
        simpa using (hasDerivAt_id (0 : ℂ)).mul_const Complex.I
      have h2 := (Complex.hasDerivAt_exp (0 * Complex.I)).comp 0 h1
      exact (h2.const_mul z₁)
    have hcomp : HasDerivAt (fun s : ℝ => Ψ (γ s)) (deriv Ψ z₁ * (z₁ * Complex.I)) 0 := by
      have hd' : HasDerivAt Ψ (deriv Ψ z₁) (γ 0) := by rw [hγ0]; exact hd
      have h := hd'.comp (0 : ℂ) hγd
      simp only [zero_mul, Complex.exp_zero, one_mul] at h
      have h' : HasDerivAt (Ψ ∘ γ) (deriv Ψ z₁ * (z₁ * Complex.I)) ((0 : ℝ) : ℂ) := by
        simpa using h
      exact HasDerivAt.comp_ofReal h'

    have hconst : (fun s : ℝ => Ψ (γ s)) =ᶠ[𝓝 0] fun _ => ψ ‖z₁‖ := by
      have hcont : Continuous fun s : ℝ => γ s := by
        rw [hγdef]; fun_prop
      have hev : ∀ᶠ s : ℝ in 𝓝 0, γ s ∈ B := by
        have : γ ((0 : ℝ) : ℂ) ∈ B := by rw [Complex.ofReal_zero, hγ0]; exact hz₁
        exact hcont.continuousAt.preimage_mem_nhds (hBo.mem_nhds this)
      filter_upwards [hev] with s hs
      rw [hΨeq _ hs, hγdef]
      simp only [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
    have hzero : HasDerivAt (fun s : ℝ => Ψ (γ s)) 0 0 :=
      (hasDerivAt_const (0 : ℝ) (ψ ‖z₁‖)).congr_of_eventuallyEq hconst
    have huniq := hcomp.unique hzero
    rcases mul_eq_zero.mp huniq with h | h
    · exact h
    · rcases mul_eq_zero.mp h with h | h
      · exact absurd h hz₁0
      · exact absurd h Complex.I_ne_zero

  have hΨconst : ∀ z ∈ B, Ψ z = 1 := by
    intro z hz
    have hIB : Complex.I ∈ B := mem_ball_self hρpos
    have h := Convex.norm_image_sub_le_of_norm_deriv_le (f := Ψ) (C := 0) (s := B)
      (fun w hw => hΨ.differentiableAt (hBo.mem_nhds hw)) (fun w hw => by rw [hderiv0 w hw]; simp)
      (convex_ball _ _) hIB hz
    simp only [zero_mul, norm_le_zero_iff, sub_eq_zero] at h
    rw [h, hΨeq _ hIB, Complex.norm_I, hψ1]

  have hnear : ∀ r : ℝ, ∀ hr : 0 < r, |r - 1| < ρ → ω (u r hr) = r := by
    intro r hr hr1
    have hmem : ((r : ℂ) * Complex.I) ∈ B := by
      show dist ((r : ℂ) * Complex.I) Complex.I < ρ
      rw [dist_eq_norm, show (r : ℂ) * Complex.I - Complex.I = ((r - 1 : ℝ) : ℂ) * Complex.I by
        push_cast; ring, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
      exact hr1
    have h := hΨconst _ hmem
    rw [hΨeq _ hmem, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hr] at h
    simp only [hψdef, dif_pos hr] at h
    have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    field_simp at h
    simpa using h

  have hωpow : ∀ (r : ℝ) (hr : 0 < r) (n : ℕ), ω (u (r ^ n) (pow_pos hr _)) = ω (u r hr) ^ n := by
    intro r hr n
    induction n with
    | zero =>
      have h1 : u (r ^ 0) (pow_pos hr _) = 1 := Units.ext (by show r ^ 0 = (1 : ℝ); simp)
      rw [h1, hω1, pow_zero]
    | succ n ih =>
      have hsplit : ω (u (r ^ (n + 1)) (pow_pos hr _))
          = ω (u (r ^ n * r) (mul_pos (pow_pos hr _) hr)) := by
        congr 1
      rw [hsplit, hωmul _ _ (pow_pos hr _) hr, ih, pow_succ]

  have hroot : Tendsto (fun n : ℕ => (t : ℝ) ^ ((n : ℝ) + 1)⁻¹) atTop (𝓝 1) := by
    have h1 : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
      simpa using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    have h2 := ((Real.continuousAt_const_rpow ht.ne').tendsto).comp h1
    simp at h2
    exact h2
  obtain ⟨n, hn⟩ := (hroot.eventually (Metric.ball_mem_nhds 1 hρpos)).exists
  set r : ℝ := (t : ℝ) ^ ((n : ℝ) + 1)⁻¹ with hr
  have hrpos : 0 < r := Real.rpow_pos_of_pos ht _
  have hr1 : |r - 1| < ρ := by simpa [Real.dist_eq] using hn
  have hrn : r ^ (n + 1) = t := by
    rw [hr, show ((n : ℝ) + 1) = ((n + 1 : ℕ) : ℝ) by push_cast; ring]
    exact Real.rpow_inv_natCast_pow ht.le (Nat.succ_ne_zero n)
  have hut : u (r ^ (n + 1)) (pow_pos hrpos _) = t := by ext; exact hrn
  calc ω t = ω (u (r ^ (n + 1)) (pow_pos hrpos _)) := by rw [hut]
    _ = ω (u r hrpos) ^ (n + 1) := hωpow r hrpos (n + 1)
    _ = ((r : ℂ)) ^ (n + 1) := by rw [hnear r hrpos hr1]
    _ = ((t : ℝ) : ℂ) := by rw [← Complex.ofReal_pow, hrn]

end S_AutomorphicForm_ArchWeightOne_central_eq_coe_of_forall_mdifferentiable
end P2MW
export P2MW.S_AutomorphicForm_ArchWeightOne_central_eq_coe_of_forall_mdifferentiable (solution)
