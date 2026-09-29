-- Prove2me | solution 1 for AlgebraicGeometry.ThetaLevel.forall_schrod_eta_apply_eq_and_bijective_of_isUnit_sum_schrod_eta_single_apply
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/e05d99c2-9b62-5cb6-a483-d662bba7f057

import Definitions.Def_AlgebraicGeometry_ThetaLevelGroup
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_ThetaLevel_forall_schrod_eta_apply_eq_and_bijective_of_isUnit_sum_schrod_eta_single_apply

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped BigOperators
open AlgebraicGeometry AlgebraicGeometry.ThetaLevel

namespace AlgC4c

variable {g : ℕ} (δ : Fin g → ℕ) [∀ i, NeZero (δ i)] (d : ℕ) [NeZero d] (B : Type) [CommRing B] (ω : B)

omit [NeZero d] in
theorem eta_mul_eta (k k' : HH δ) : (Heis.eta k * Heis.eta k' : Heis δ d) = Heis.eta (k + k') := by
  refine Heis.ext ?_ ?_ ?_ <;> simp [Heis.eta, pair_zero_right]

omit [NeZero d] in
theorem theta_zero : (Heis.theta (0 : HH δ) : Heis δ d) = 1 := by
  refine Heis.ext ?_ ?_ ?_ <;> simp [Heis.theta]

omit [NeZero d] in

theorem mul_theta_eq (w : Heis δ d) (x : HH δ) :
    w * Heis.theta x = Heis.cen (w.a + pair δ d w.k x) * Heis.theta (w.h + x) * Heis.eta w.k := by
  refine Heis.ext ?_ ?_ ?_ <;> simp [Heis.cen, Heis.theta, Heis.eta, pair_zero_left, pair_zero_right]

omit [NeZero d] in
theorem schrod_cen (a : ZMod (2 * d)) : schrod δ d B ω (Heis.cen a) = omegaPow d B ω a • LinearMap.id := by
  refine LinearMap.ext fun v => funext fun x => ?_
  simp [schrod_apply, thetaChar, pair_zero_left, omegaPow_zero]

omit [NeZero d] in
theorem schrod_eta_apply (k : HH δ) (v : HH δ → B) (x : HH δ) :
    schrod δ d B ω (Heis.eta k) v x = thetaChar δ d B ω k x * v x := by
  simp [schrod_apply, omegaPow_zero]

omit [NeZero d] in
theorem schrod_theta_single (h y : HH δ) :
    schrod δ d B ω (Heis.theta h) (Pi.single y 1) = Pi.single (y + h) 1 := by
  classical
  funext x
  simp only [schrod_apply, Heis.theta_a, Heis.theta_h, Heis.theta_k, thetaChar, pair_zero_left, omegaPow_zero,
    one_mul]
  by_cases hx : x = y + h
  · subst hx; rw [add_sub_cancel_right, Pi.single_eq_same, Pi.single_eq_same]
  · have : x - h ≠ y := fun h' => hx (by rw [← h']; abel)
    simp [Pi.single_eq_of_ne this, Pi.single_eq_of_ne hx]

theorem thetaChar_add_left (hω2d : ω ^ (2 * d) = 1) (k k' x : HH δ) :
    thetaChar δ d B ω (k + k') x = thetaChar δ d B ω k x * thetaChar δ d B ω k' x := by
  simp only [thetaChar, pair_add_left, omegaPow_add d B ω hω2d]

theorem thetaChar_add_right (hω2d : ω ^ (2 * d) = 1) (k x x' : HH δ) :
    thetaChar δ d B ω k (x + x') = thetaChar δ d B ω k x * thetaChar δ d B ω k x' := by
  simp only [thetaChar, pair_add_right, omegaPow_add d B ω hω2d]

omit [NeZero d] in
theorem thetaChar_zero_right (k : HH δ) : thetaChar δ d B ω k 0 = 1 := by
  simp [thetaChar, pair_zero_right, omegaPow_zero]

omit [NeZero d] in
theorem pair_single (i : Fin g) (x : HH δ) : pair δ d (Pi.single i 1) x = iota δ d i (x i) := by
  classical
  unfold pair
  rw [Fintype.sum_eq_single i]
  · simp
  · intro j hj
    rw [Pi.single_eq_of_ne hj, zero_mul, map_zero]

theorem exists_isUnit_thetaChar_sub (hδd : ∏ i, δ i = d) (ζ : B) (hζ : ζ ^ d = 1)
    (hζu : ∀ j : ℕ, 0 < j → j < d → IsUnit (1 - ζ ^ j)) (hω : ω ^ 2 = ζ)
    {x y : HH δ} (hxy : x ≠ y) :
    ∃ k : HH δ, IsUnit (thetaChar δ d B ω k x - thetaChar δ d B ω k y) := by
  classical
  have hω2d : ω ^ (2 * d) = 1 := by rw [pow_mul, hω, hζ]
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := Function.ne_iff.mp hxy
  refine ⟨Pi.single i 1, ?_⟩
  have hdvd : δ i ∣ d := hδd ▸ Finset.dvd_prod_of_mem δ (Finset.mem_univ i)
  have hdvd2 : δ i ∣ 2 * d := Dvd.dvd.mul_left hdvd 2
  set z : ZMod (δ i) := x i - y i with hz
  have hz0 : z ≠ 0 := sub_ne_zero.mpr hi
  have hsplit : thetaChar δ d B ω (Pi.single i 1) x =
      thetaChar δ d B ω (Pi.single i 1) y * omegaPow d B ω (iota δ d i z) := by
    simp only [thetaChar, pair_single]
    rw [← omegaPow_add d B ω hω2d, ← map_add]
    congr 2
    rw [hz]; abel
  set m : ℕ := d / δ i * z.val with hm
  have hpos : 0 < d / δ i := Nat.div_pos (Nat.le_of_dvd (NeZero.pos d) hdvd) (NeZero.pos (δ i))
  have hm0 : 0 < m := Nat.mul_pos hpos ((ZMod.val_pos).mpr hz0)
  have hmd : m < d := by
    calc m = d / δ i * z.val := rfl
      _ < d / δ i * δ i := Nat.mul_lt_mul_of_pos_left (ZMod.val_lt z) hpos
      _ = d := Nat.div_mul_cancel hdvd
  have hval : omegaPow d B ω (iota δ d i z) = ζ ^ m := by
    have : z = ((z.val : ℕ) : ZMod (δ i)) := (ZMod.natCast_zmod_val z).symm
    rw [this, iota_natCast δ d i hdvd2, ← Nat.cast_mul, omegaPow_natCast d B ω hω2d,
      Nat.mul_div_assoc 2 hdvd, mul_assoc, pow_mul, hω]
  have hu1 : IsUnit (thetaChar δ d B ω (Pi.single i 1) y) := by
    simp only [thetaChar, omegaPow]
    exact (IsUnit.of_pow_eq_one hω2d (mul_ne_zero two_ne_zero (NeZero.ne d))).pow _
  rw [hsplit, hval, ← mul_sub_one, ← neg_sub, mul_neg]
  exact (hu1.mul (hζu m hm0 hmd)).neg

omit [NeZero d] in
theorem card_HH (hδd : ∏ i, δ i = d) : Fintype.card (HH δ) = d := by
  rw [← hδd]
  simp [HH, Fintype.card_pi, ZMod.card]

theorem sum_thetaChar (hδd : ∏ i, δ i = d) (ζ : B) (hζ : ζ ^ d = 1)
    (hζu : ∀ j : ℕ, 0 < j → j < d → IsUnit (1 - ζ ^ j)) (hω : ω ^ 2 = ζ) (x : HH δ) :
    ∑ k : HH δ, thetaChar δ d B ω k x = if x = 0 then ((d : ℕ) : B) else 0 := by
  classical
  have hω2d : ω ^ (2 * d) = 1 := by rw [pow_mul, hω, hζ]
  by_cases hx : x = 0
  · subst hx
    simp [thetaChar_zero_right, card_HH δ d hδd]
  · rw [if_neg hx]
    obtain ⟨k₀, hk₀⟩ := exists_isUnit_thetaChar_sub δ d B ω hδd ζ hζ hζu hω hx
    rw [thetaChar_zero_right] at hk₀
    set S := ∑ k : HH δ, thetaChar δ d B ω k x with hS
    have hinv : thetaChar δ d B ω k₀ x * S = S := by
      rw [hS, Finset.mul_sum]
      simp_rw [← thetaChar_add_left δ d B ω hω2d]
      exact Fintype.sum_equiv (Equiv.addLeft k₀) _ _ (fun k => rfl)
    have h0 : (thetaChar δ d B ω k₀ x - 1) * S = 0 := by rw [sub_mul, one_mul, hinv, sub_self]
    exact hk₀.mul_right_eq_zero.mp h0

end AlgC4c

open AlgC4c in
theorem solution
    {g : ℕ} (δ : Fin g → ℕ) [∀ i, NeZero (δ i)] (d : ℕ) [NeZero d] (hδd : ∏ i, δ i = d)
    (B : Type) [CommRing B] (hd : IsUnit ((d : ℕ) : B)) (ζ ω : B) (hζ : ζ ^ d = 1)
    (hζu : ∀ j : ℕ, 0 < j → j < d → IsUnit (1 - ζ ^ j)) (hω : ω ^ 2 = ζ) {n : ℕ} (e : Fin n ≃ HH δ)
    (γ : MulAut (Heis δ d)) (hγ : γ ∈ Heis.Gam δ d)
    (y₀ : HH δ) (hy₀ : IsUnit ((∑ k : HH δ, schrod δ d B ω (γ (Heis.eta k)) (Pi.single y₀ 1)) y₀)) :
    (∀ k : HH δ, schrod δ d B ω (γ (Heis.eta k)) (∑ k' : HH δ, schrod δ d B ω (γ (Heis.eta k')) (Pi.single y₀ 1)) =
        ∑ k' : HH δ, schrod δ d B ω (γ (Heis.eta k')) (Pi.single y₀ 1)) ∧
      Function.Bijective fun c : HH δ → B =>
        ∑ x : HH δ, c x • schrod δ d B ω (γ (Heis.theta x)) (∑ k' : HH δ, schrod δ d B ω (γ (Heis.eta k')) (Pi.single y₀ 1)) := by
  classical
  have hω2d : ω ^ (2 * d) = 1 := by rw [pow_mul, hω, hζ]
  set v : HH δ → B := ∑ k' : HH δ, schrod δ d B ω (γ (Heis.eta k')) (Pi.single y₀ 1) with hv

  have hmul : ∀ z z' : Heis δ d, schrod δ d B ω (γ (z * z')) = schrod δ d B ω (γ z) ∘ₗ schrod δ d B ω (γ z') := by
    intro z z'; rw [map_mul, schrod_mul δ d B ω hω2d]
  have hcen : ∀ a : ZMod (2 * d), schrod δ d B ω (γ (Heis.cen a)) = omegaPow d B ω a • LinearMap.id := by
    intro a; rw [hγ a, schrod_cen]

  have hfix : ∀ k : HH δ, schrod δ d B ω (γ (Heis.eta k)) v = v := by
    intro k
    rw [hv, map_sum]
    have hterm : ∀ k', schrod δ d B ω (γ (Heis.eta k)) (schrod δ d B ω (γ (Heis.eta k')) (Pi.single y₀ 1)) =
        schrod δ d B ω (γ (Heis.eta (k + k'))) (Pi.single y₀ 1) := by
      intro k'
      rw [← LinearMap.comp_apply, ← hmul, eta_mul_eta]
    simp_rw [hterm]
    exact Fintype.sum_equiv (Equiv.addLeft k) _ _ (fun k' => rfl)
  refine ⟨hfix, ?_⟩

  let Φ : (HH δ → B) →ₗ[B] (HH δ → B) :=
    ∑ x : HH δ, (LinearMap.proj x : (HH δ → B) →ₗ[B] B).smulRight (schrod δ d B ω (γ (Heis.theta x)) v)
  have hΦ : ∀ c : HH δ → B, Φ c = ∑ x : HH δ, c x • schrod δ d B ω (γ (Heis.theta x)) v := by
    intro c
    simp [Φ, LinearMap.sum_apply, LinearMap.smulRight_apply]
  have hΦ' : (fun c : HH δ → B => ∑ x : HH δ, c x • schrod δ d B ω (γ (Heis.theta x)) v) = ⇑Φ :=
    funext fun c => (hΦ c).symm
  rw [hΦ']

  have hstab : ∀ (w : Heis δ d) (c : HH δ → B), ∃ c' : HH δ → B, schrod δ d B ω (γ w) (Φ c) = Φ c' := by
    intro w c
    refine ⟨fun x' => omegaPow d B ω (w.a + pair δ d w.k (x' - w.h)) * c (x' - w.h), ?_⟩
    rw [hΦ, hΦ, map_sum]
    have key : ∀ x, schrod δ d B ω (γ w) (c x • schrod δ d B ω (γ (Heis.theta x)) v) =
        (omegaPow d B ω (w.a + pair δ d w.k x) * c x) • schrod δ d B ω (γ (Heis.theta (w.h + x))) v := by
      intro x
      rw [map_smul, ← LinearMap.comp_apply, ← hmul, mul_theta_eq, hmul, hmul, hcen, LinearMap.comp_apply,
        LinearMap.comp_apply, hfix, LinearMap.smul_apply, LinearMap.id_apply, smul_smul, mul_comm]
    simp_rw [key]
    symm
    exact Fintype.sum_equiv (Equiv.subRight w.h) _ _ (fun x => by rw [Equiv.subRight_apply, add_sub_cancel])
  set W : Submodule B (HH δ → B) := LinearMap.range Φ with hW
  have hWstab : ∀ (z : Heis δ d) (u : HH δ → B), u ∈ W → schrod δ d B ω z u ∈ W := by
    intro z u hu
    obtain ⟨c, rfl⟩ := hu
    obtain ⟨c', hc'⟩ := hstab (γ.symm z) c
    rw [MulEquiv.apply_symm_apply] at hc'
    exact ⟨c', hc'.symm⟩

  have hvW : v ∈ W := by
    refine ⟨Pi.single 0 1, ?_⟩
    rw [hΦ, Fintype.sum_eq_single (0 : HH δ)]
    · rw [Pi.single_eq_same, one_smul, theta_zero, map_one, schrod_one, LinearMap.id_apply]
    · intro x hx; rw [Pi.single_eq_of_ne hx, zero_smul]

  have hproj : ∑ k : HH δ, thetaChar δ d B ω k (-y₀) • schrod δ d B ω (Heis.eta k) v =
      (((d : ℕ) : B) * v y₀) • Pi.single y₀ 1 := by
    funext x
    simp only [Finset.sum_apply, Pi.smul_apply, schrod_eta_apply, smul_eq_mul]
    have : ∀ k, thetaChar δ d B ω k (-y₀) * (thetaChar δ d B ω k x * v x) = thetaChar δ d B ω k (x + -y₀) * v x := by
      intro k; rw [thetaChar_add_right δ d B ω hω2d]; ring
    simp_rw [this]
    rw [← Finset.sum_mul, sum_thetaChar δ d B ω hδd ζ hζ hζu hω]
    by_cases hx : x = y₀
    · subst hx; simp
    · rw [if_neg (fun h => hx (by rwa [← sub_eq_add_neg, sub_eq_zero] at h)), Pi.single_eq_of_ne hx, mul_zero,
        zero_mul]
  have hprojW : (((d : ℕ) : B) * v y₀) • (Pi.single y₀ 1 : HH δ → B) ∈ W := by
    rw [← hproj]
    exact W.sum_mem fun k _ => W.smul_mem _ (hWstab _ _ hvW)
  have hδ₀W : (Pi.single y₀ 1 : HH δ → B) ∈ W := by
    have hu : IsUnit (((d : ℕ) : B) * v y₀) := hd.mul (by simpa [hv] using hy₀)
    obtain ⟨b, hb⟩ := hu.exists_left_inv
    have : (Pi.single y₀ 1 : HH δ → B) = b • ((((d : ℕ) : B) * v y₀) • Pi.single y₀ 1) := by
      rw [smul_smul, hb, one_smul]
    rw [this]
    exact W.smul_mem b hprojW
  have hallW : ∀ y : HH δ, (Pi.single y 1 : HH δ → B) ∈ W := by
    intro y
    have : (Pi.single y 1 : HH δ → B) = schrod δ d B ω (Heis.theta (y - y₀)) (Pi.single y₀ 1) := by
      rw [schrod_theta_single]; congr 1; abel
    rw [this]
    exact hWstab _ _ hδ₀W
  have htop : W = ⊤ := by
    refine eq_top_iff.mpr fun c _ => ?_
    rw [← Finset.univ_sum_single c]
    refine W.sum_mem fun y _ => ?_
    have : (Pi.single y (c y) : HH δ → B) = c y • Pi.single y 1 := by
      funext x
      by_cases hx : x = y
      · subst hx; simp
      · simp [Pi.single_eq_of_ne hx]
    rw [this]
    exact W.smul_mem _ (hallW y)
  have hsurj : Function.Surjective Φ := LinearMap.range_eq_top.mp (hW ▸ htop)
  exact ⟨OrzechProperty.injective_of_surjective_endomorphism Φ hsurj, hsurj⟩

end S_AlgebraicGeometry_ThetaLevel_forall_schrod_eta_apply_eq_and_bijective_of_isUnit_sum_schrod_eta_single_apply
end P2MW
export P2MW.S_AlgebraicGeometry_ThetaLevel_forall_schrod_eta_apply_eq_and_bijective_of_isUnit_sum_schrod_eta_single_apply (solution)
