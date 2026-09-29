-- Prove2me | solution 1 for AlgebraicGeometry.ThetaLevel.exists_gam_forall_smul_mul_schrodMat_eq_of_forall_smul_mul_schrodMat_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/5655dc2c-e7ea-520f-8c0b-782ccee6fd70

import Definitions.Def_AlgebraicGeometry_ThetaLevelGroup
import Theorems.Thm_AlgebraicGeometry_ThetaLevel_schrodMat_one_and_schrodMat_mul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_ThetaLevel_exists_gam_forall_smul_mul_schrodMat_eq_of_forall_smul_mul_schrodMat_eq

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open AlgebraicGeometry AlgebraicGeometry.ThetaLevel

namespace K77TH3
namespace LGG

section Basic

variable {g : ℕ} (δ : Fin g → ℕ) [∀ i, NeZero (δ i)] (d : ℕ) [NeZero d] {S : Type} [CommRing S] (ω : S)
  {n : ℕ} (e : Fin n ≃ HH δ)

theorem schrodMat_cen (a : ZMod (2 * d)) :
    schrodMat δ d S ω e (Heis.cen a) = omegaPow d S ω a • (1 : Matrix (Fin n) (Fin n) S) := by
  ext i j
  rw [schrodMat_apply, Matrix.smul_apply, smul_eq_mul]
  simp only [Heis.cen_h, Heis.cen_a, Heis.cen_k, add_zero, pair_zero_left, EmbeddingLike.apply_eq_iff_eq]
  by_cases hij : i = j
  · subst hij; simp
  · rw [if_neg hij, Matrix.one_apply_ne hij, mul_zero]

theorem schrodMat_entry (z : Heis δ d) (y : HH δ) :
    schrodMat δ d S ω e z (e.symm (y + z.h)) (e.symm y) = omegaPow d S ω (z.a + pair δ d z.k y) := by
  rw [schrodMat_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply, if_pos rfl]

theorem schrodMat_entry_ne (z : Heis δ d) (y h' : HH δ) (hh : h' ≠ z.h) :
    schrodMat δ d S ω e z (e.symm (y + h')) (e.symm y) = 0 := by
  rw [schrodMat_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply, if_neg]
  exact fun h0 => hh (add_left_cancel h0)

theorem exists_isUnit_one_sub_omegaPow_pair (hδd : ∏ i, δ i = d) (ζ : S) (hζ : ζ ^ d = 1)
    (hζu : ∀ j : ℕ, 0 < j → j < d → IsUnit (1 - ζ ^ j)) (hω : ω ^ 2 = ζ) (x : HH δ) (hx : x ≠ 0) :
    ∃ k : HH δ, IsUnit (1 - omegaPow d S ω (pair δ d k x)) := by
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
  rw [hpair, hval, omegaPow_natCast d S ω h2d, pow_mul, hω]
  have hm0 : m ≠ 0 := by rintro rfl; exact NeZero.ne d (by rw [hm, mul_zero])
  have hmv1 : 0 < m * v := Nat.mul_pos (Nat.pos_of_ne_zero hm0) hvpos
  have hmv2 : m * v < d := by
    calc m * v < m * δ i₀ := Nat.mul_lt_mul_of_pos_left hvlt (Nat.pos_of_ne_zero hm0)
      _ = d := by rw [hm, mul_comm]
  exact hζu _ hmv1 hmv2

theorem eq_zero_or_eq_of_omegaPow_mul_eq (ζ : S) (hζ : ζ ^ d = 1) (hζu : ∀ j : ℕ, 0 < j → j < d → IsUnit (1 - ζ ^ j))
    (hω : ω ^ 2 = ζ) (ε : S) (hε : ε ≠ 0) (b : ZMod (2 * d)) (hb : omegaPow d S ω b * ε = ε) :
    b = 0 ∨ b = (d : ZMod (2 * d)) := by
  have h2 : NeZero (2 * d) := ⟨mul_ne_zero two_ne_zero (NeZero.ne d)⟩

  have hsq : ζ ^ b.val * ε = ε := by
    have e1 : ζ ^ b.val = omegaPow d S ω b * omegaPow d S ω b := by
      rw [← hω, ← pow_mul, omegaPow, ← pow_add]; congr 1; ring
    rw [e1, mul_assoc, hb, hb]

  set r := b.val % d with hr
  have hζr : ζ ^ b.val = ζ ^ r := by
    conv_lhs => rw [← Nat.mod_add_div b.val d, pow_add, pow_mul, hζ, one_pow, mul_one]
  rw [hζr] at hsq
  have hr0 : r = 0 := by
    by_contra hr0
    have hu := hζu r (Nat.pos_of_ne_zero hr0) (hr ▸ Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne d)))
    have : (1 - ζ ^ r) * ε = 0 := by rw [sub_mul, one_mul, hsq, sub_self]
    exact hε ((hu.mul_right_eq_zero).mp this)

  have hdvd : d ∣ b.val := Nat.dvd_of_mod_eq_zero (hr ▸ hr0 : b.val % d = 0)
  obtain ⟨q, hq⟩ := hdvd
  have hlt : b.val < 2 * d := ZMod.val_lt b
  have hq2 : q < 2 := by
    rw [hq, mul_comm] at hlt
    exact Nat.lt_of_mul_lt_mul_right hlt
  have hbv : b = ((b.val : ℕ) : ZMod (2 * d)) := (ZMod.natCast_zmod_val b).symm
  interval_cases q
  · left; rw [hbv, hq, mul_zero, Nat.cast_zero]
  · right; rw [hbv, hq, mul_one]

end Basic

end K77TH3.LGG

namespace K77TH3
namespace LGG

section Inj

variable {g : ℕ} (δ : Fin g → ℕ) [∀ i, NeZero (δ i)] (d : ℕ) [NeZero d] {S : Type} [CommRing S] (ω : S)
  {n : ℕ} (e : Fin n ≃ HH δ)

theorem isUnit_omegaPow (hω2d : ω ^ (2 * d) = 1) (a : ZMod (2 * d)) : IsUnit (omegaPow d S ω a) := by
  unfold omegaPow
  exact (IsUnit.of_pow_eq_one hω2d (mul_ne_zero two_ne_zero (NeZero.ne d))).pow _

theorem parts_eq_of_smul_schrodMat_eq (hδd : ∏ i, δ i = d) (ζ : S) (hζ : ζ ^ d = 1)
    (hζu : ∀ j : ℕ, 0 < j → j < d → IsUnit (1 - ζ ^ j)) (hω : ω ^ 2 = ζ) (ε : S) (hε : ε ≠ 0)
    (w₁ w₂ : Heis δ d) (h : ε • schrodMat δ d S ω e w₁ = ε • schrodMat δ d S ω e w₂) :
    w₁.h = w₂.h ∧ w₁.k = w₂.k ∧ omegaPow d S ω (w₁.a - w₂.a) * ε = ε := by
  have h2d : ω ^ (2 * d) = 1 := by rw [pow_mul, hω, hζ]
  have hu := isUnit_omegaPow d ω h2d
  have hent : ∀ i j, ε * schrodMat δ d S ω e w₁ i j = ε * schrodMat δ d S ω e w₂ i j := fun i j => by
    have := congrFun (congrFun h i) j
    simpa [Matrix.smul_apply] using this

  have hh : w₁.h = w₂.h := by
    by_contra hne
    have h1 := hent (e.symm (0 + w₁.h)) (e.symm 0)
    rw [schrodMat_entry, schrodMat_entry_ne δ d ω e w₂ 0 w₁.h hne, mul_zero] at h1
    exact hε ((hu _).mul_left_eq_zero.mp h1)
  refine ⟨hh, ?_, ?_⟩
  ·
    by_contra hk
    have hy : ∀ y, ε * omegaPow d S ω (w₁.a + pair δ d w₁.k y) = ε * omegaPow d S ω (w₂.a + pair δ d w₂.k y) := by
      intro y
      have h1 := hent (e.symm (y + w₁.h)) (e.symm y)
      rw [schrodMat_entry] at h1
      rw [hh] at h1
      rwa [schrodMat_entry] at h1
    have h0 := hy 0
    simp only [pair_zero_right, add_zero] at h0
    obtain ⟨y, hyu⟩ := exists_isUnit_one_sub_omegaPow_pair δ d ω hδd ζ hζ hζu hω (w₁.k - w₂.k) (sub_ne_zero.mpr hk)
    have key : omegaPow d S ω (pair δ d (w₁.k - w₂.k) y) * ε = ε := by
      have h1 := hy y
      rw [omegaPow_add d S ω h2d, omegaPow_add d S ω h2d] at h1

      have h2 : ε * omegaPow d S ω (pair δ d w₁.k y) * omegaPow d S ω w₂.a =
          ε * omegaPow d S ω (pair δ d w₂.k y) * omegaPow d S ω w₂.a := by
        linear_combination h1 - (omegaPow d S ω (pair δ d w₁.k y)) * h0
      have h3 := (hu w₂.a).mul_right_cancel h2

      have h4 : omegaPow d S ω (pair δ d (w₁.k - w₂.k) y) * omegaPow d S ω (pair δ d w₂.k y) =
          omegaPow d S ω (pair δ d w₁.k y) := by
        rw [← omegaPow_add d S ω h2d, ← pair_add_left, sub_add_cancel]
      have h5 : omegaPow d S ω (pair δ d (w₁.k - w₂.k) y) * ε * omegaPow d S ω (pair δ d w₂.k y) =
          ε * omegaPow d S ω (pair δ d w₂.k y) := by
        linear_combination ε * h4 + h3
      exact (hu _).mul_right_cancel h5
    rw [pair_comm] at key
    have : (1 - omegaPow d S ω (pair δ d y (w₁.k - w₂.k))) * ε = 0 := by rw [sub_mul, one_mul, key, sub_self]
    exact hε (hyu.mul_right_eq_zero.mp this)
  ·
    have h0 := hent (e.symm (0 + w₁.h)) (e.symm 0)
    rw [schrodMat_entry, hh, schrodMat_entry] at h0
    simp only [pair_zero_right, add_zero] at h0
    have h4 : omegaPow d S ω (w₁.a - w₂.a) * omegaPow d S ω w₂.a = omegaPow d S ω w₁.a := by
      rw [← omegaPow_add d S ω h2d, sub_add_cancel]
    have h5 : omegaPow d S ω (w₁.a - w₂.a) * ε * omegaPow d S ω w₂.a = ε * omegaPow d S ω w₂.a := by
      linear_combination ε * h4 + h0
    exact (hu _).mul_right_cancel h5

end Inj

end K77TH3.LGG

namespace K77TH3
namespace LGG

section Parity

variable {g : ℕ} (δ : Fin g → ℕ) [∀ i, NeZero (δ i)] (d : ℕ) [NeZero d] {S : Type} [CommRing S] (ω : S)
  {n : ℕ} (e : Fin n ≃ HH δ)

def par : ZMod (2 * d) →+* ZMod 2 := ZMod.castHom (dvd_mul_right 2 d) (ZMod 2)

omit [NeZero d] in
theorem par_natCast (m : ℕ) : par d (m : ZMod (2 * d)) = (m : ZMod 2) := map_natCast (par d) m

theorem par_pair (hδd : ∏ i, δ i = d) (k h : HH δ) : par d (pair δ d k h) = 0 := by
  rw [pair, map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  have hdvd : δ i ∣ d := hδd ▸ Finset.dvd_prod_of_mem δ (Finset.mem_univ i)
  rw [← ZMod.natCast_zmod_val (k i * h i), iota_natCast δ d i (Dvd.dvd.mul_left hdvd 2), map_mul, par_natCast,
    Nat.mul_div_assoc 2 hdvd, Nat.cast_mul, ZMod.natCast_self, zero_mul, zero_mul]

theorem par_mul_a (hδd : ∏ i, δ i = d) (z z' : Heis δ d) : par d (z * z').a = par d z.a + par d z'.a := by
  rw [Heis.mul_a, map_add, map_add, par_pair δ d hδd, add_zero]

omit [NeZero d] in
theorem ZMod.two_add_one_eq_of_ne (x y : ZMod 2) (h : x ≠ y) : x + 1 = y := by
  fin_cases x <;> fin_cases y <;> simp_all <;> decide

theorem schrodMat_shift (hω2d : ω ^ (2 * d) = 1) (w : Heis δ d) (b : ZMod (2 * d)) :
    schrodMat δ d S ω e ⟨w.a + b, w.h, w.k⟩ = omegaPow d S ω b • schrodMat δ d S ω e w := by
  ext i j
  rw [schrodMat_apply, Matrix.smul_apply, schrodMat_apply, smul_eq_mul]
  split_ifs
  · rw [show w.a + b + pair δ d w.k (e j) = b + (w.a + pair δ d w.k (e j)) by abel, omegaPow_add d S ω hω2d]
  · rw [mul_zero]

theorem odd_of_omegaPow_d_mul_eq (ζ : S) (hζu : ∀ j : ℕ, 0 < j → j < d → IsUnit (1 - ζ ^ j)) (hω : ω ^ 2 = ζ)
    (ε : S) (hε : ε ≠ 0) (hA : omegaPow d S ω (d : ZMod (2 * d)) * ε = ε) : ¬ 2 ∣ d := by
  rintro ⟨m, hm⟩
  have h2 : NeZero (2 * d) := ⟨mul_ne_zero two_ne_zero (NeZero.ne d)⟩
  have hval : omegaPow d S ω (d : ZMod (2 * d)) = ζ ^ m := by
    rw [omegaPow, ZMod.val_natCast, Nat.mod_eq_of_lt (by have := Nat.pos_of_ne_zero (NeZero.ne d); omega), hm, pow_mul, hω]
  rw [hval] at hA
  have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; exact NeZero.ne d (by rw [hm, mul_zero]))
  have hmd : m < d := by omega
  have : (1 - ζ ^ m) * ε = 0 := by rw [sub_mul, one_mul, hA, sub_self]
  exact hε ((hζu m hm0 hmd).mul_right_eq_zero.mp this)

omit [NeZero d] in
theorem par_d_eq_one (hd : ¬ 2 ∣ d) : par d (d : ZMod (2 * d)) = 1 := by
  rw [par_natCast, ZMod.natCast_eq_one_iff_odd]
  exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hd)

end Parity

end K77TH3.LGG

namespace K77TH3
namespace LGG

section Main

variable {g : ℕ} (δ : Fin g → ℕ) [∀ i, NeZero (δ i)] (d : ℕ) [NeZero d] {S : Type} [CommRing S] (ω : S)
  {n : ℕ} (e : Fin n ≃ HH δ)

omit [∀ i, NeZero (δ i)] [NeZero d] in
theorem smul_mul_smul_of_idem {m : ℕ} (ε : S) (hε : IsIdempotentElem ε) (A B : Matrix (Fin m) (Fin m) S) :
    (ε • A) * (ε • B) = ε • (A * B) := by
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hε.eq]

def conj (T Ti : Matrix (Fin n) (Fin n) S) (z : Heis δ d) : Matrix (Fin n) (Fin n) S :=
  T * schrodMat δ d S ω e z * Ti

theorem conj_mul (hω2d : ω ^ (2 * d) = 1) (T Ti : Matrix (Fin n) (Fin n) S) (hTiT : Ti * T = 1) (z z' : Heis δ d) :
    conj δ d ω e T Ti (z * z') = conj δ d ω e T Ti z * conj δ d ω e T Ti z' := by
  unfold conj
  rw [(schrodMat_one_and_schrodMat_mul δ d S ω hω2d e).2,
    Matrix.mul_assoc (T * schrodMat δ d S ω e z) Ti, ← Matrix.mul_assoc Ti, ← Matrix.mul_assoc Ti, hTiT,
    Matrix.one_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc]

theorem conj_cen (T Ti : Matrix (Fin n) (Fin n) S) (hTTi : T * Ti = 1) (a : ZMod (2 * d)) :
    conj δ d ω e T Ti (Heis.cen a) = schrodMat δ d S ω e (Heis.cen a) := by
  unfold conj
  rw [schrodMat_cen, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hTTi]

theorem schrodMat_eq_conj (T Ti : Matrix (Fin n) (Fin n) S) (hTiT : Ti * T = 1) (z : Heis δ d) :
    schrodMat δ d S ω e z = Ti * conj δ d ω e T Ti z * T := by
  unfold conj
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hTiT, Matrix.one_mul, Matrix.mul_assoc, hTiT, Matrix.mul_one]

theorem smul_conj_of_hw (T Ti : Matrix (Fin n) (Fin n) S) (hTTi : T * Ti = 1) (ε : S) (w : Heis δ d → Heis δ d)
    (hw : ∀ z, ε • (T * schrodMat δ d S ω e z) = ε • (schrodMat δ d S ω e (w z) * T)) (z : Heis δ d) :
    ε • conj δ d ω e T Ti z = ε • schrodMat δ d S ω e (w z) := by
  unfold conj
  rw [← Matrix.smul_mul, hw z, Matrix.smul_mul, Matrix.mul_assoc, hTTi, Matrix.mul_one]

def wnorm (hA : Prop) [Decidable hA] (w : Heis δ d → Heis δ d) (z : Heis δ d) : Heis δ d :=
  if hA ∧ par d (w z).a ≠ par d z.a then ⟨(w z).a + (d : ZMod (2 * d)), (w z).h, (w z).k⟩ else w z

theorem wnorm_h (hA : Prop) [Decidable hA] (w : Heis δ d → Heis δ d) (z : Heis δ d) :
    (wnorm δ d hA w z).h = (w z).h := by
  unfold wnorm; split_ifs <;> rfl

theorem wnorm_k (hA : Prop) [Decidable hA] (w : Heis δ d → Heis δ d) (z : Heis δ d) :
    (wnorm δ d hA w z).k = (w z).k := by
  unfold wnorm; split_ifs <;> rfl

theorem par_wnorm (hA : Prop) [Decidable hA] (hAtrue : hA) (hd : ¬ 2 ∣ d) (w : Heis δ d → Heis δ d) (z : Heis δ d) :
    par d (wnorm δ d hA w z).a = par d z.a := by
  unfold wnorm
  split_ifs with h
  · change par d ((w z).a + (d : ZMod (2 * d))) = par d z.a
    rw [map_add, par_d_eq_one d hd]
    exact ZMod.two_add_one_eq_of_ne _ _ h.2
  · push Not at h
    exact h hAtrue

theorem smul_schrodMat_wnorm (hω2d : ω ^ (2 * d) = 1) (ε : S) (hAprop : Prop) [Decidable hAprop]
    (hAimp : hAprop → omegaPow d S ω (d : ZMod (2 * d)) * ε = ε) (w : Heis δ d → Heis δ d) (z : Heis δ d) :
    ε • schrodMat δ d S ω e (wnorm δ d hAprop w z) = ε • schrodMat δ d S ω e (w z) := by
  unfold wnorm
  split_ifs with h
  · rw [schrodMat_shift δ d ω e hω2d, smul_smul, mul_comm, hAimp h.1]
  · rfl

end Main

end K77TH3.LGG

namespace K77TH3
namespace LGG

section Final

variable {g : ℕ} (δ : Fin g → ℕ) [∀ i, NeZero (δ i)] (d : ℕ) [NeZero d] {S : Type} [CommRing S] (ω : S)
  {n : ℕ} (e : Fin n ≃ HH δ)

theorem exists_gam (hδd : ∏ i, δ i = d) (ζ : S) (hζ : ζ ^ d = 1) (hζu : ∀ j : ℕ, 0 < j → j < d → IsUnit (1 - ζ ^ j))
    (hω : ω ^ 2 = ζ) (T : Matrix (Fin n) (Fin n) S) (hT : IsUnit T) (ε : S) (hε : IsIdempotentElem ε)
    (w : Heis δ d → Heis δ d)
    (hw : ∀ z, ε • (T * schrodMat δ d S ω e z) = ε • (schrodMat δ d S ω e (w z) * T)) :
    ∃ γ : Heis.Gam δ d, ∀ z, ε • (T * schrodMat δ d S ω e z) = ε • (schrodMat δ d S ω e (γ.1 z) * T) := by
  classical
  by_cases hε0 : ε = 0
  · exact ⟨1, fun z => by simp [hε0]⟩
  have h2d : ω ^ (2 * d) = 1 := by rw [pow_mul, hω, hζ]
  have hϑmul := (schrodMat_one_and_schrodMat_mul δ d S ω h2d e).2
  set Ti : Matrix (Fin n) (Fin n) S := ↑(hT.unit⁻¹) with hTi
  have hTTi : T * Ti = 1 := by rw [hTi]; exact hT.mul_val_inv
  have hTiT : Ti * T = 1 := by rw [hTi]; exact hT.val_inv_mul

  let hA : Prop := omegaPow d S ω (d : ZMod (2 * d)) * ε = ε
  set w' : Heis δ d → Heis δ d := wnorm δ d hA w with hw'

  have hC : ∀ z, ε • conj δ d ω e T Ti z = ε • schrodMat δ d S ω e (w' z) := fun z => by
    rw [hw', smul_schrodMat_wnorm δ d ω e h2d ε hA (fun h => h) w z, smul_conj_of_hw δ d ω e T Ti hTTi ε w hw z]

  have hpar : hA → ∀ z, par d (w' z).a = par d z.a := fun hAtrue z => by
    rw [hw']
    exact par_wnorm δ d hA hAtrue (odd_of_omegaPow_d_mul_eq d ω ζ hζu hω ε hε0 hAtrue) w z

  have inj : ∀ w₁ w₂ : Heis δ d, ε • schrodMat δ d S ω e w₁ = ε • schrodMat δ d S ω e w₂ →
      (hA → par d w₁.a = par d w₂.a) → w₁ = w₂ := by
    intro w₁ w₂ h hp
    obtain ⟨hh, hk, ha⟩ := parts_eq_of_smul_schrodMat_eq δ d ω e hδd ζ hζ hζu hω ε hε0 w₁ w₂ h
    rcases eq_zero_or_eq_of_omegaPow_mul_eq d ω ζ hζ hζu hω ε hε0 _ ha with h0 | hd'
    · exact Heis.ext (sub_eq_zero.mp h0) hh hk
    · exfalso
      have hAtrue : hA := by show omegaPow d S ω (d : ZMod (2 * d)) * ε = ε; rw [← hd']; exact ha
      have hodd := odd_of_omegaPow_d_mul_eq d ω ζ hζu hω ε hε0 hAtrue
      have hp' := hp hAtrue
      have : par d (w₁.a - w₂.a) = 1 := by rw [hd', par_d_eq_one d hodd]
      rw [map_sub, hp', sub_self] at this
      exact zero_ne_one this

  have hmul : ∀ z z', w' (z * z') = w' z * w' z' := by
    intro z z'
    apply inj
    · rw [← hC, conj_mul δ d ω e h2d T Ti hTiT, ← smul_mul_smul_of_idem ε hε, hC, hC, smul_mul_smul_of_idem ε hε,
        hϑmul]
    · intro hAtrue
      rw [hpar hAtrue, par_mul_a δ d hδd, par_mul_a δ d hδd, hpar hAtrue, hpar hAtrue]

  have hinj : Function.Injective w' := by
    intro z₁ z₂ h12
    apply inj
    · rw [schrodMat_eq_conj δ d ω e T Ti hTiT z₁, schrodMat_eq_conj δ d ω e T Ti hTiT z₂, ← Matrix.smul_mul,
        ← Matrix.mul_smul, hC, ← Matrix.smul_mul, ← Matrix.mul_smul Ti, hC, h12]
    · intro hAtrue
      rw [← hpar hAtrue z₁, ← hpar hAtrue z₂, h12]
  have hbij : Function.Bijective w' := Finite.injective_iff_bijective.mp hinj

  let φ : Heis δ d →* Heis δ d := MonoidHom.mk' w' hmul
  let γ : MulAut (Heis δ d) := MulEquiv.ofBijective φ hbij
  have hγ : ∀ z, γ z = w' z := fun z => rfl
  have hγmem : γ ∈ Heis.Gam δ d := by
    intro a
    rw [hγ]
    apply inj
    · rw [← hC, conj_cen δ d ω e T Ti hTTi]
    · intro hAtrue
      rw [hpar hAtrue]
  refine ⟨⟨γ, hγmem⟩, fun z => ?_⟩
  change ε • (T * schrodMat δ d S ω e z) = ε • (schrodMat δ d S ω e (γ z) * T)
  rw [hγ]
  symm
  rw [← Matrix.smul_mul, ← hC, Matrix.smul_mul]
  unfold conj
  rw [Matrix.mul_assoc, hTiT, Matrix.mul_one]

end Final

end K77TH3.LGG

open K77TH3.LGG in
theorem solution
    {g : ℕ} (δ : Fin g → ℕ) [hδ : ∀ i, NeZero (δ i)] (N : ℕ) (hδd : ∏ i, δ i = N + 1)
    (e : Fin (N + 1) ≃ ((i : Fin g) → ZMod (δ i)))
    (B : Type) [CommRing B] (hd : IsUnit ((N + 1 : ℕ) : B))
    (ζ : B) (hζ : ζ ^ (N + 1) = 1) (hζu : ∀ j : ℕ, 0 < j → j < N + 1 → IsUnit (1 - ζ ^ j))
    (ω : B) (hω : ω ^ 2 = ζ)
    {S : Type} [CommRing S] (φB : B →+* S)
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) S) (hT : IsUnit T)
    (ε : S) (hε : IsIdempotentElem ε)
    (w : Heis δ (N + 1) → Heis δ (N + 1))
    (hw : ∀ z : Heis δ (N + 1), ε • (T * schrodMat δ (N + 1) S (φB ω) e z) =
      ε • (schrodMat δ (N + 1) S (φB ω) e (w z) * T)) :
    ∃ γ : (Heis.Gam (δ := δ) (d := N + 1)),
      ∀ z : Heis δ (N + 1), ε • (T * schrodMat δ (N + 1) S (φB ω) e z) =
        ε • (schrodMat δ (N + 1) S (φB ω) e (γ.1 z) * T) := by
  have hζS : φB ζ ^ (N + 1) = 1 := by rw [← map_pow, hζ, map_one]
  have hωS : φB ω ^ 2 = φB ζ := by rw [← map_pow, hω]
  have hζuS : ∀ j : ℕ, 0 < j → j < N + 1 → IsUnit (1 - φB ζ ^ j) := fun j hj hj' => by
    have := (hζu j hj hj').map φB
    rwa [map_sub, map_one, map_pow] at this
  exact exists_gam δ (N + 1) (φB ω) e hδd (φB ζ) hζS hζuS hωS T hT ε hε w hw

end

end S_AlgebraicGeometry_ThetaLevel_exists_gam_forall_smul_mul_schrodMat_eq_of_forall_smul_mul_schrodMat_eq
end P2MW
export P2MW.S_AlgebraicGeometry_ThetaLevel_exists_gam_forall_smul_mul_schrodMat_eq_of_forall_smul_mul_schrodMat_eq (solution)
