-- Prove2me | Definitions.Def_LeanPool_RamanujanNagell_Helpers
-- name    : LeanPool_RamanujanNagell_Helpers
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-20T22:39:33.709204+00:00
-- url     : https://prove2.me/theorems/67ccc10d-b251-479e-9f99-0f14704140f8
-- title:
--   Helpers
-- statement:
--   Definitions and structural lemmas for Helpers, from Barinder S. Banwait and Xinze Li; maintained by LeanPool contributors's pinned The Ramanujan-Nagell theorem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/RamanujanNagell/Helpers.lean

module
public import Mathlib.Algebra.QuadraticAlgebra.Basic
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.NormNum.GCD
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace RamanujanNagell
open QuadraticAlgebra
abbrev R : Type := QuadraticAlgebra ℤ (-2) 1
def θ : R := ⟨0, 1⟩
def θ' : R := ⟨1, -1⟩
lemma four_norm_eq (z : R) :
    4 * QuadraticAlgebra.norm z = (2 * z.re + z.im) ^ 2 + 7 * z.im ^ 2 := by
  rw [QuadraticAlgebra.norm_def]; ring
lemma norm_nonneg (z : R) : 0 ≤ QuadraticAlgebra.norm z := by
  have h := four_norm_eq z
  have h1 : 0 ≤ (2 * z.re + z.im) ^ 2 := sq_nonneg _
  have h2 : 0 ≤ 7 * z.im ^ 2 := by positivity
  linarith
lemma norm_eq_zero_iff (z : R) : QuadraticAlgebra.norm z = 0 ↔ z = 0 := by
  refine ⟨fun h => ?_, fun h => h ▸ QuadraticAlgebra.norm_zero⟩
  have h4 := four_norm_eq z
  rw [h] at h4
  have hv : z.im = 0 := by nlinarith [sq_nonneg (2 * z.re + z.im), sq_nonneg z.im]
  have hu : z.re = 0 := by nlinarith [h4, hv, sq_nonneg z.re]
  exact QuadraticAlgebra.ext hu hv
lemma norm_pos {z : R} (hz : z ≠ 0) : 0 < QuadraticAlgebra.norm z := by
  rcases lt_or_eq_of_le (norm_nonneg z) with h | h
  · exact h
  · exact absurd ((norm_eq_zero_iff z).mp h.symm) hz
lemma b_mul_star_eq_norm (b : R) :
    b * star b = ((QuadraticAlgebra.norm b : ℤ) : R) := by
  apply QuadraticAlgebra.ext
  · simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.re_star, QuadraticAlgebra.im_star,
      QuadraticAlgebra.re_intCast, QuadraticAlgebra.norm_def, Int.cast_id]
    ring
  · simp only [QuadraticAlgebra.im_mul, QuadraticAlgebra.re_star, QuadraticAlgebra.im_star,
      QuadraticAlgebra.im_intCast]
    ring
lemma N_mul_rem_eq (a b q : R) :
    ((QuadraticAlgebra.norm b : ℤ) : R) * (a - b * q) =
      b * (a * star b - ((QuadraticAlgebra.norm b : ℤ) : R) * q) := by
  have hbs := b_mul_star_eq_norm b
  calc ((QuadraticAlgebra.norm b : ℤ) : R) * (a - b * q)
      = (b * star b) * (a - b * q) := by rw [← hbs]
    _ = b * (a * star b - (b * star b) * q) := by ring
    _ = b * (a * star b - ((QuadraticAlgebra.norm b : ℤ) : R) * q) := by rw [hbs]
lemma N_mul_norm_rem_eq (a b q : R) (hb : b ≠ 0) :
    QuadraticAlgebra.norm b * QuadraticAlgebra.norm (a - b * q) =
      QuadraticAlgebra.norm (a * star b - ((QuadraticAlgebra.norm b : ℤ) : R) * q) := by
  have hN_pos : 0 < QuadraticAlgebra.norm b := norm_pos hb
  have hN_ne : QuadraticAlgebra.norm b ≠ 0 := hN_pos.ne'
  have h_key := N_mul_rem_eq a b q
  have h_norm : QuadraticAlgebra.norm
      (((QuadraticAlgebra.norm b : ℤ) : R) * (a - b * q)) =
      QuadraticAlgebra.norm
      (b * (a * star b - ((QuadraticAlgebra.norm b : ℤ) : R) * q)) := by
    rw [h_key]
  rw [map_mul, map_mul, QuadraticAlgebra.norm_intCast] at h_norm
  have h_sq : (QuadraticAlgebra.norm b) ^ 2 =
              QuadraticAlgebra.norm b * QuadraticAlgebra.norm b := sq _
  have : QuadraticAlgebra.norm b *
         (QuadraticAlgebra.norm b * QuadraticAlgebra.norm (a - b * q)) =
         QuadraticAlgebra.norm b *
         QuadraticAlgebra.norm (a * star b - ((QuadraticAlgebra.norm b : ℤ) : R) * q) := by
    rwa [← mul_assoc, ← h_sq]
  exact mul_left_cancel₀ hN_ne this
noncomputable def quot (a b : R) : R :=
  let N : ℤ := QuadraticAlgebra.norm b
  if N = 0 then 0
  else
    let s : R := a * star b
    let n : ℤ := round ((s.im : ℚ) / N)
    let m : ℤ := round ((2 * (s.re : ℚ) + s.im - N * n) / (2 * N))
    ⟨m, n⟩
noncomputable def rem (a b : R) : R := a - b * quot a b
@[simp] lemma quot_zero (a : R) : quot a 0 = 0 := by unfold quot; simp
lemma quot_mul_add_rem_eq (a b : R) : b * quot a b + rem a b = a := by
  unfold rem; ring
lemma sq_le_of_round_eq {N w : ℤ} {r : ℚ} (h2N : (0 : ℚ) < 2 * N)
    (habs : |r| ≤ 1 / 2) (heq : r * (2 * N) = ((w : ℤ) : ℚ)) : w ^ 2 ≤ N ^ 2 := by
  have h_abs : |((w : ℤ) : ℚ)| ≤ N := by
    rw [← heq, abs_mul, abs_of_pos h2N]
    have := mul_le_mul_of_nonneg_right habs h2N.le
    linarith
  have h_sq : ((w : ℤ) : ℚ) ^ 2 ≤ (N : ℚ) ^ 2 := by
    rw [(sq_abs ((w : ℤ) : ℚ)).symm]
    exact sq_le_sq' (by linarith [abs_nonneg ((w : ℤ) : ℚ)]) h_abs
  exact_mod_cast h_sq
lemma sixteen_norm_rem_le (a b : R) (hb : b ≠ 0) :
    16 * QuadraticAlgebra.norm (rem a b) ≤ 11 * QuadraticAlgebra.norm b := by
  set N := QuadraticAlgebra.norm b with hN_def
  have hN_pos : 0 < N := norm_pos hb
  have hN_ne : N ≠ 0 := hN_pos.ne'
  set s : R := a * star b with hs_def
  set n : ℤ := round ((s.im : ℚ) / N) with hn_def
  set m : ℤ := round ((2 * (s.re : ℚ) + s.im - N * n) / (2 * N)) with hm_def
  have hquot : quot a b = (⟨m, n⟩ : R) := by
    change (if QuadraticAlgebra.norm b = 0 then (0 : R) else _) = _
    rw [if_neg hN_ne]
  set u : ℤ := s.re - N * m with hu_def
  set v : ℤ := s.im - N * n with hv_def
  have hNq_pos : (0 : ℚ) < N := by exact_mod_cast hN_pos
  have hNq : (N : ℚ) ≠ 0 := hNq_pos.ne'
  have h2Nq_pos : (0 : ℚ) < 2 * N := by linarith
  have hv_bd : (2 * v) ^ 2 ≤ N ^ 2 :=
    sq_le_of_round_eq h2Nq_pos (abs_sub_round ((s.im : ℚ) / N))
      (by rw [← hn_def]; push_cast [hv_def]; field_simp)
  have huv_bd : (2 * u + v) ^ 2 ≤ N ^ 2 :=
    sq_le_of_round_eq h2Nq_pos (abs_sub_round ((2 * (s.re : ℚ) + s.im - N * n) / (2 * N)))
      (by rw [← hm_def]; push_cast [hu_def, hv_def]; field_simp; ring)
  have h_chain : N * QuadraticAlgebra.norm (rem a b) = u ^ 2 + u * v + 2 * v ^ 2 := by
    unfold rem
    rw [hquot]
    have h := N_mul_norm_rem_eq a b (⟨m, n⟩ : R) hb
    rw [h]
    have hre : (a * star b - ((N : ℤ) : R) * (⟨m, n⟩ : R)).re = u := by
      simp_all
    have him : (a * star b - ((N : ℤ) : R) * (⟨m, n⟩ : R)).im = v := by
      simp_all
    rw [QuadraticAlgebra.norm_def, hre, him]; ring
  have h_bd : 16 * (u ^ 2 + u * v + 2 * v ^ 2) ≤ 11 * N ^ 2 := by
    nlinarith [hv_bd, huv_bd]
  nlinarith [h_chain, h_bd, hN_pos, sq N]
noncomputable def normMeasure (a : R) : ℕ := Int.natAbs (QuadraticAlgebra.norm a)
lemma natAbs_norm_rem_lt (a : R) {b : R} (hb : b ≠ 0) :
    normMeasure (rem a b) < normMeasure b := by
  unfold normMeasure
  have hN_pos : 0 < QuadraticAlgebra.norm b := norm_pos hb
  have hr_nn : 0 ≤ QuadraticAlgebra.norm (rem a b) := norm_nonneg _
  have h_bd := sixteen_norm_rem_le a b hb
  have hr_lt : QuadraticAlgebra.norm (rem a b) < QuadraticAlgebra.norm b := by linarith
  zify
  rwa [abs_of_nonneg hr_nn, abs_of_nonneg hN_pos.le]
lemma norm_mul_left_not_lt (a : R) {b : R} (hb : b ≠ 0) :
    ¬ normMeasure (a * b) < normMeasure a := by
  unfold normMeasure
  have hN_pos : 0 < QuadraticAlgebra.norm b := norm_pos hb
  have ha_nn : 0 ≤ QuadraticAlgebra.norm a := norm_nonneg a
  have hab : QuadraticAlgebra.norm (a * b) =
             QuadraticAlgebra.norm a * QuadraticAlgebra.norm b := map_mul _ _ _
  have hab_nn : 0 ≤ QuadraticAlgebra.norm (a * b) := hab ▸ mul_nonneg ha_nn hN_pos.le
  intro h
  zify at h
  rw [abs_of_nonneg hab_nn, abs_of_nonneg ha_nn, hab] at h
  nlinarith [ha_nn, hN_pos]
noncomputable instance instEuclideanDomain : EuclideanDomain R where
  quotient := quot
  quotient_zero := quot_zero
  remainder := rem
  quotient_mul_add_remainder_eq := quot_mul_add_rem_eq
  r := fun a b => normMeasure a < normMeasure b
  r_wellFounded := (measure normMeasure).wf
  remainder_lt := by exact natAbs_norm_rem_lt
  mul_left_not_lt := by exact norm_mul_left_not_lt
instance instPrincipalIdealRing : IsPrincipalIdealRing R :=
  by infer_instance
instance instUniqueFactorizationMonoid : UniqueFactorizationMonoid R := inferInstance
end RamanujanNagell


