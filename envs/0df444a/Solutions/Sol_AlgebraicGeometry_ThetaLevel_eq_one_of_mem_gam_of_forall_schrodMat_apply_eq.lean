-- Prove2me | solution 1 for AlgebraicGeometry.ThetaLevel.eq_one_of_mem_gam_of_forall_schrodMat_apply_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/ff9f215c-c59a-540c-bf27-f4dd073746b4

import Definitions.Def_AlgebraicGeometry_ThetaLevelGroup
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_ThetaLevel_eq_one_of_mem_gam_of_forall_schrodMat_apply_eq

set_option autoImplicit false

open scoped BigOperators
open AlgebraicGeometry AlgebraicGeometry.ThetaLevel

namespace K77TH3
namespace HeisFaithful

variable {g : ℕ} (δ : Fin g → ℕ) [∀ i, NeZero (δ i)] (d : ℕ) [NeZero d] (B : Type) [CommRing B] (ω : B) {n : ℕ}
  (e : Fin n ≃ HH δ)

theorem exists_isUnit_one_sub_thetaChar (hδd : ∏ i, δ i = d) (ζ : B) (hζ : ζ ^ d = 1)
    (hζu : ∀ j : ℕ, 0 < j → j < d → IsUnit (1 - ζ ^ j)) (hω : ω ^ 2 = ζ) (x : HH δ) (hx : x ≠ 0) :
    ∃ k : HH δ, IsUnit (1 - omegaPow d B ω (pair δ d k x)) := by
  classical
  obtain ⟨i₀, hi₀⟩ : ∃ i, x i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hx (funext hcon)
  refine ⟨Pi.single i₀ 1, ?_⟩

  have hdvd : δ i₀ ∣ d := hδd ▸ Finset.dvd_prod_of_mem δ (Finset.mem_univ i₀)
  have hdvd2 : δ i₀ ∣ 2 * d := Dvd.dvd.mul_left hdvd 2
  have hpair : pair δ d (Pi.single i₀ 1) x = iota δ d i₀ (x i₀) := by
    rw [pair, Finset.sum_eq_single i₀]
    · simp
    · intro i _ hi
      simp [hi]
    · intro hh; exact absurd (Finset.mem_univ _) hh
  obtain ⟨m, hm⟩ := hdvd

  set v : ℕ := (x i₀).val with hv
  have hvpos : 0 < v := by
    rw [hv, Nat.pos_iff_ne_zero]; exact fun h0 => hi₀ ((ZMod.val_eq_zero _).mp h0)
  have hvlt : v < δ i₀ := ZMod.val_lt _
  have hcast : (x i₀ : ZMod (δ i₀)) = ((v : ℕ) : ZMod (δ i₀)) := by rw [hv, ZMod.natCast_zmod_val]
  have hq : 2 * d / δ i₀ = 2 * m := by
    rw [hm, show 2 * (δ i₀ * m) = (2 * m) * δ i₀ by ring, Nat.mul_div_cancel _ (Nat.pos_of_ne_zero (NeZero.ne _))]
  have hval : iota δ d i₀ (x i₀) = ((2 * (m * v) : ℕ) : ZMod (2 * d)) := by
    rw [hcast, iota_natCast δ d i₀ hdvd2, hq]; push_cast; ring
  have h2d : ω ^ (2 * d) = 1 := by rw [pow_mul, hω, hζ]
  rw [hpair, hval, omegaPow_natCast d B ω h2d, pow_mul, hω]
  have hm0 : m ≠ 0 := by rintro rfl; exact NeZero.ne d (by rw [hm, mul_zero])
  have hmv1 : 0 < m * v := Nat.mul_pos (Nat.pos_of_ne_zero hm0) hvpos
  have hmv2 : m * v < d := by
    calc m * v < m * δ i₀ := Nat.mul_lt_mul_of_pos_left hvlt (Nat.pos_of_ne_zero hm0)
      _ = d := by rw [hm, mul_comm]
  exact hζu _ hmv1 hmv2

theorem eq_zero_of_omegaPow_eq_one [Nontrivial B] (ζ : B) (hζu : ∀ j : ℕ, 0 < j → j < d → IsUnit (1 - ζ ^ j))
    (hω : ω ^ 2 = ζ) (a : ZMod (2 * d)) (hda : (d : ZMod (2 * d)) * a = 0) (ha : omegaPow d B ω a = 1) : a = 0 := by
  have h2 : NeZero (2 * d) := ⟨mul_ne_zero two_ne_zero (NeZero.ne d)⟩

  have hval : (a : ZMod (2 * d)) = ((a.val : ℕ) : ZMod (2 * d)) := (ZMod.natCast_zmod_val a).symm
  have hdvd : 2 * d ∣ d * a.val := by
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_mul, ← hval]; exact hda
  obtain ⟨m, hm⟩ : 2 ∣ a.val := by
    obtain ⟨c, hc⟩ := hdvd
    refine ⟨c, ?_⟩
    have : d * a.val = d * (2 * c) := by rw [hc]; ring
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero (NeZero.ne d)) this
  have hmlt : m < d := by
    have := ZMod.val_lt a
    omega
  have hpow : ζ ^ m = 1 := by
    rw [← hω, ← pow_mul, ← hm]; exact ha
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · rw [hval, hm, hm0]; simp
  · exfalso
    have hu := hζu m hmpos hmlt
    rw [hpow, sub_self] at hu
    exact not_isUnit_zero hu

theorem components_of_schrodMat_eq [Nontrivial B] (hδd : ∏ i, δ i = d) (ζ : B) (hζ : ζ ^ d = 1)
    (hζu : ∀ j : ℕ, 0 < j → j < d → IsUnit (1 - ζ ^ j)) (hω : ω ^ 2 = ζ)
    (w z : Heis δ d) (hwz : schrodMat δ d B ω e w = schrodMat δ d B ω e z) :
    w.h = z.h ∧ w.k = z.k ∧ omegaPow d B ω w.a = omegaPow d B ω z.a := by
  have h2d : ω ^ (2 * d) = 1 := by rw [pow_mul, hω, hζ]
  have hωu : IsUnit ω := IsUnit.of_pow_eq_one h2d (mul_ne_zero two_ne_zero (NeZero.ne d))
  have hunit : ∀ a : ZMod (2 * d), IsUnit (omegaPow d B ω a) := fun a => by unfold omegaPow; exact hωu.pow _

  have hent : ∀ y : HH δ,
      (if y + z.h = y + w.h then omegaPow d B ω (w.a + pair δ d w.k y) else 0) = omegaPow d B ω (z.a + pair δ d z.k y) := by
    intro y
    have := congrFun (congrFun hwz (e.symm (y + z.h))) (e.symm y)
    simpa [schrodMat_apply] using this
  have hh : w.h = z.h := by
    have h0 := hent 0
    by_contra hne
    rw [if_neg (fun h' => hne (add_left_cancel h').symm)] at h0
    exact not_isUnit_zero (h0 ▸ hunit _)
  have hent' : ∀ y, omegaPow d B ω (w.a + pair δ d w.k y) = omegaPow d B ω (z.a + pair δ d z.k y) := by
    intro y; have h1 := hent y; rwa [if_pos (by rw [hh])] at h1
  have ha : omegaPow d B ω w.a = omegaPow d B ω z.a := by simpa [pair_zero_right] using hent' 0
  refine ⟨hh, ?_, ha⟩

  by_contra hk
  obtain ⟨y, hy⟩ := exists_isUnit_one_sub_thetaChar δ d B ω hδd ζ hζ hζu hω (w.k - z.k) (sub_ne_zero.mpr hk)
  have hchar : omegaPow d B ω (pair δ d (w.k - z.k) y) = 1 := by
    have h1 := hent' y
    rw [omegaPow_add d B ω h2d, omegaPow_add d B ω h2d, ha] at h1
    have h2 := (hunit z.a).mul_left_cancel h1

    have h3 : omegaPow d B ω (pair δ d (w.k - z.k) y) * omegaPow d B ω (pair δ d z.k y) =
        omegaPow d B ω (pair δ d z.k y) := by
      rw [← omegaPow_add d B ω h2d, ← pair_add_left, sub_add_cancel, h2]
    exact (hunit _).mul_right_cancel (h3.trans (one_mul _).symm)
  rw [pair_comm] at hchar
  rw [hchar, sub_self] at hy
  exact not_isUnit_zero hy

omit [∀ i, NeZero (δ i)] [NeZero d] in
theorem pow_theta_like (a : ZMod (2 * d)) (h : HH δ) (m : ℕ) :
    (⟨a, h, 0⟩ : Heis δ d) ^ m = ⟨m • a, m • h, 0⟩ := by
  induction m with
  | zero => rw [pow_zero]; exact Heis.ext (by simp) (by simp) (by simp)
  | succ m ih =>
    rw [pow_succ, ih]
    exact Heis.ext (by simp [pair_zero_left, add_smul, add_comm]) (by simp [add_smul, add_comm]) (by simp)

omit [∀ i, NeZero (δ i)] [NeZero d] in
theorem pow_eta_like (a : ZMod (2 * d)) (k : HH δ) (m : ℕ) :
    (⟨a, 0, k⟩ : Heis δ d) ^ m = ⟨m • a, 0, m • k⟩ := by
  induction m with
  | zero => rw [pow_zero]; exact Heis.ext (by simp) (by simp) (by simp)
  | succ m ih =>
    rw [pow_succ, ih]
    exact Heis.ext (by simp [pair_zero_right, add_smul, add_comm]) (by simp) (by simp [add_smul, add_comm])

theorem d_nsmul_eq_zero (hδd : ∏ i, δ i = d) (h : HH δ) : d • h = 0 := by
  funext i
  have hdvd : δ i ∣ d := hδd ▸ Finset.dvd_prod_of_mem δ (Finset.mem_univ i)
  rw [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul, (ZMod.natCast_eq_zero_iff d (δ i)).mpr hdvd, zero_mul]

end K77TH3.HeisFaithful

open K77TH3.HeisFaithful in
theorem solution
    {g : ℕ} (δ : Fin g → ℕ) [∀ i, NeZero (δ i)] (d : ℕ) [NeZero d] (hδd : ∏ i, δ i = d)
    (B : Type) [CommRing B] [Nontrivial B] (ζ ω : B) (hζ : ζ ^ d = 1) (hζu : ∀ j : ℕ, 0 < j → j < d → IsUnit (1 - ζ ^ j))
    (hω : ω ^ 2 = ζ) {n : ℕ} (e : Fin n ≃ HH δ)
    (γ : MulAut (Heis δ d)) (hγ : γ ∈ Heis.Gam δ d) (h : ∀ z : Heis δ d, schrodMat δ d B ω e (γ z) = schrodMat δ d B ω e z) :
    γ = 1 := by
  have comp := fun z => components_of_schrodMat_eq δ d B ω e hδd ζ hζ hζu hω (γ z) z (h z)

  have hθ : ∀ x : HH δ, γ (Heis.theta x) = Heis.theta x := by
    intro x
    obtain ⟨c1, c2, c3⟩ := comp (Heis.theta x)
    simp only [Heis.theta_h, Heis.theta_k, Heis.theta_a, omegaPow_zero] at c1 c2 c3
    have hshape : γ (Heis.theta x) = ⟨(γ (Heis.theta x)).a, x, 0⟩ := Heis.ext rfl c1 c2

    have hpow : (γ (Heis.theta x)) ^ d = 1 := by
      rw [← map_pow, show Heis.theta x = (⟨0, x, 0⟩ : Heis δ d) from rfl, pow_theta_like, smul_zero,
        d_nsmul_eq_zero δ d hδd, show (⟨0, 0, 0⟩ : Heis δ d) = 1 from rfl, map_one]
    rw [hshape, pow_theta_like, d_nsmul_eq_zero δ d hδd] at hpow
    have hda : (d : ZMod (2 * d)) * (γ (Heis.theta x)).a = 0 := by
      have := congrArg Heis.a hpow
      simpa [nsmul_eq_mul] using this
    have ha0 := eq_zero_of_omegaPow_eq_one d B ω ζ hζu hω _ hda c3
    rw [hshape, ha0]; rfl

  have hη : ∀ x : HH δ, γ (Heis.eta x) = Heis.eta x := by
    intro x
    obtain ⟨c1, c2, c3⟩ := comp (Heis.eta x)
    simp only [Heis.eta_h, Heis.eta_k, Heis.eta_a, omegaPow_zero] at c1 c2 c3
    have hshape : γ (Heis.eta x) = ⟨(γ (Heis.eta x)).a, 0, x⟩ := Heis.ext rfl c1 c2
    have hpow : (γ (Heis.eta x)) ^ d = 1 := by
      rw [← map_pow, show Heis.eta x = (⟨0, 0, x⟩ : Heis δ d) from rfl, pow_eta_like, smul_zero,
        d_nsmul_eq_zero δ d hδd, show (⟨0, 0, 0⟩ : Heis δ d) = 1 from rfl, map_one]
    rw [hshape, pow_eta_like, d_nsmul_eq_zero δ d hδd] at hpow
    have hda : (d : ZMod (2 * d)) * (γ (Heis.eta x)).a = 0 := by
      have := congrArg Heis.a hpow
      simpa [nsmul_eq_mul] using this
    have ha0 := eq_zero_of_omegaPow_eq_one d B ω ζ hζu hω _ hda c3
    rw [hshape, ha0]; rfl
  refine MulEquiv.ext fun z => ?_
  show γ z = z
  conv_lhs => rw [← Heis.cen_mul_theta_mul_eta z]
  rw [map_mul, map_mul, hγ, hθ, hη, Heis.cen_mul_theta_mul_eta]

end S_AlgebraicGeometry_ThetaLevel_eq_one_of_mem_gam_of_forall_schrodMat_apply_eq
end P2MW
export P2MW.S_AlgebraicGeometry_ThetaLevel_eq_one_of_mem_gam_of_forall_schrodMat_apply_eq (solution)
