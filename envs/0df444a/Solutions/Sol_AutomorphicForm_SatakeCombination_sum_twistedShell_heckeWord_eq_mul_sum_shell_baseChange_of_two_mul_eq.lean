-- Prove2me | solution 1 for AutomorphicForm.SatakeCombination.sum_twistedShell_heckeWord_eq_mul_sum_shell_baseChange_of_two_mul_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/eadc55f8-a9e4-5fb3-9e25-cfd3e5aeba86

import Mathlib
import Definitions.Def_AutomorphicForm_SatakeCombinationCoeff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_SatakeCombination_sum_twistedShell_heckeWord_eq_mul_sum_shell_baseChange_of_two_mul_eq

set_option autoImplicit false

namespace WInert
open MvPolynomial Finset

noncomputable section

abbrev PX : MvPolynomial (Fin 2) ℂ := X 0
abbrev PY : MvPolynomial (Fin 2) ℂ := X 1

def hp (s : ℕ) : MvPolynomial (Fin 2) ℂ := ∑ i ∈ range (s + 1), PX ^ i * PY ^ (s - i)

theorem hp_zero : hp 0 = 1 := by simp [hp]

theorem hp_one : hp 1 = PX + PY := by
  simp [hp, sum_range_succ]
  ring

theorem mul_hp (s : ℕ) : (PX + PY) * hp (s + 1) = hp (s + 2) + PX * PY * hp s := by
  simp only [hp]
  rw [sum_range_succ' (fun i => PX ^ i * PY ^ (s + 2 - i))]
  have h1 : ∀ i ∈ range (s + 2), PX ^ (i + 1) * PY ^ (s + 2 - (i + 1)) = PX * (PX ^ i * PY ^ (s + 1 - i)) := by
    intro i hi
    have : s + 2 - (i + 1) = s + 1 - i := by omega
    rw [this]; ring
  rw [sum_congr rfl h1, ← mul_sum]
  have h2 : ∀ i ∈ range (s + 1), PX * PY * (PX ^ i * PY ^ (s - i)) = PY * (PX ^ (i+1) * PY ^ (s + 1 - (i + 1))) := by
    intro i hi
    have hi' : i ≤ s := by simpa [mem_range, Nat.lt_succ_iff] using hi
    have : s + 1 - (i + 1) = s - i := by omega
    rw [this]; ring
  rw [mul_sum (range (s+1)), sum_congr rfl h2, ← mul_sum]
  have hS : (∑ i ∈ range (s + 2), PX ^ i * PY ^ (s + 1 - i)) =
      (∑ i ∈ range (s + 1), PX ^ (i + 1) * PY ^ (s + 1 - (i + 1))) + PY ^ (s + 1) := by
    rw [sum_range_succ']; simp
  rw [hS]
  simp only [pow_zero, one_mul, Nat.sub_zero]
  ring

def zS (R : ℂ) : MvPolynomial (Fin 2) ℂ := C R⁻¹ * (PX * PY)

def tS (R : ℂ) : ℕ → MvPolynomial (Fin 2) ℂ
  | 0 => 1
  | 1 => PX + PY
  | (s + 2) => hp (s + 2) - zS R * hp s

theorem tS_zero (R : ℂ) : tS R 0 = 1 := rfl
theorem tS_one (R : ℂ) : tS R 1 = PX + PY := rfl
theorem tS_add_two (R : ℂ) (s : ℕ) : tS R (s + 2) = hp (s + 2) - zS R * hp s := rfl

def wt (R : ℂ) : ℕ → ℂ
  | 0 => 0
  | 1 => R + 1
  | (_ + 2) => R

theorem XY_eq (R : ℂ) (hR : R ≠ 0) : PX * PY = C R * zS R := by
  simp only [zS, ← mul_assoc, ← C_mul, mul_inv_cancel₀ hR, C_1, one_mul]

theorem mul_tS_zero (R : ℂ) : (PX + PY) * tS R 0 = tS R 1 := by simp [tS]

theorem mul_tS_one (R : ℂ) (hR : R ≠ 0) : (PX + PY) * tS R 1 = tS R 2 + C (wt R 1) * zS R * tS R 0 := by
  simp only [tS, wt, hp_zero, mul_one]
  have := mul_hp 0
  rw [hp_one, hp_zero, mul_one] at this
  rw [this, XY_eq R hR, C_add, C_1]
  ring

theorem mul_tS_add_two (R : ℂ) (hR : R ≠ 0) (s : ℕ) :
    (PX + PY) * tS R (s + 2) = tS R (s + 3) + C (wt R (s + 2)) * zS R * tS R (s + 1) := by
  rcases s with _ | s
  · simp only [tS, wt, hp_zero, mul_one]
    have e1 := mul_hp 1
    rw [mul_sub, e1, hp_one, XY_eq R hR]
    ring
  · simp only [tS, wt]
    have e1 := mul_hp (s + 2)
    have e0 := mul_hp s
    rw [mul_sub, e1, show (PX + PY) * (zS R * hp (s+1)) = zS R * ((PX + PY) * hp (s+1)) by ring, e0,
      XY_eq R hR]
    ring

theorem mul_tS (R : ℂ) (hR : R ≠ 0) (s : ℕ) :
    (PX + PY) * tS R s = tS R (s + 1) + C (wt R s) * zS R * tS R (s - 1) := by
  rcases s with _ | _ | s
  · simp [wt, mul_tS_zero]
  · simpa using mul_tS_one R hR
  · simpa using mul_tS_add_two R hR s

section Walk

variable (r : ℕ) (W : ℕ → ℕ → ℕ)
  (h0s : ∀ s : ℕ, W 0 (s + 1) = 0)
  (hroot : ∀ n : ℕ, W (n + 1) 0 = (r + 1) * W n 1)
  (hstep : ∀ n s : ℕ, W (n + 1) (s + 1) = W n s + r * W n (s + 2))

include h0s hstep in
theorem W_eq_zero_of_lt : ∀ n s : ℕ, n < s → W n s = 0 := by
  intro n
  induction n with
  | zero =>
    intro s hs
    obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
    exact h0s t
  | succ n ih =>
    intro s hs
    obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
    rw [hstep, ih t (by omega), ih (t + 2) (by omega)]
    simp

include h0s hroot hstep in
theorem W_eq_zero_of_odd : ∀ n s : ℕ, (n + s) % 2 = 1 → W n s = 0 := by
  intro n
  induction n with
  | zero =>
    intro s hs
    rcases s with _ | s
    · simp at hs
    · exact h0s s
  | succ n ih =>
    intro s hs
    rcases s with _ | s
    · rw [hroot, ih 1 (by omega)]; simp
    · rw [hstep, ih s (by omega), ih (s + 2) (by omega)]; simp

include hroot hstep in

theorem W_succ_cast (n s : ℕ) :
    ((W (n + 1) s : ℕ) : ℂ) = (if s = 0 then 0 else ((W n (s - 1) : ℕ) : ℂ)) + wt (r : ℂ) (s + 1) * ((W n (s + 1) : ℕ) : ℂ) := by
  rcases s with _ | s
  · rw [hroot]; simp [wt]
  · rw [hstep]; simp [wt]

include h0s hroot hstep in

theorem word_expansion (hr : (r : ℂ) ≠ 0) (h00 : W 0 0 = 1) (n : ℕ) :
    (PX + PY) ^ n = ∑ s ∈ range (n + 1), C ((W n s : ℕ) : ℂ) * zS (r : ℂ) ^ ((n - s) / 2) * tS (r : ℂ) s := by
  induction n with
  | zero => simp [h00, tS_zero]
  | succ n ih =>
    set R : ℂ := (r : ℂ) with hRdef
    have hW0 : ∀ s, n < s → ((W n s : ℕ) : ℂ) = 0 := fun s hs => by
      rw [W_eq_zero_of_lt r W h0s hstep n s hs]; simp

    rw [pow_succ, ih, sum_mul]
    have step1 : ∀ s ∈ range (n + 1),
        C ((W n s : ℕ) : ℂ) * zS R ^ ((n - s) / 2) * tS R s * (PX + PY) =
          C ((W n s : ℕ) : ℂ) * zS R ^ ((n - s) / 2) * tS R (s + 1) +
          C ((W n s : ℕ) : ℂ) * zS R ^ ((n - s) / 2) * (C (wt R s) * zS R * tS R (s - 1)) := by
      intro s hs
      rw [show C ((W n s : ℕ) : ℂ) * zS R ^ ((n - s) / 2) * tS R s * (PX + PY) =
        C ((W n s : ℕ) : ℂ) * zS R ^ ((n - s) / 2) * ((PX + PY) * tS R s) by ring, mul_tS R hr s]
      ring
    rw [sum_congr rfl step1, sum_add_distrib]

    have tgt : ∀ s ∈ range (n + 2),
        C ((W (n + 1) s : ℕ) : ℂ) * zS R ^ ((n + 1 - s) / 2) * tS R s =
          C (if s = 0 then 0 else ((W n (s - 1) : ℕ) : ℂ)) * zS R ^ ((n + 1 - s) / 2) * tS R s +
          C (wt R (s + 1) * ((W n (s + 1) : ℕ) : ℂ)) * zS R ^ ((n + 1 - s) / 2) * tS R s := by
      intro s hs
      rw [W_succ_cast r W hroot hstep n s, C_add]
      ring
    rw [sum_congr rfl tgt, sum_add_distrib]
    congr 1
    ·
      rw [sum_range_succ' (fun s => C (if s = 0 then 0 else ((W n (s - 1) : ℕ) : ℂ)) *
        zS R ^ ((n + 1 - s) / 2) * tS R s)]
      simp only [Nat.succ_ne_zero, if_false, if_true, C_0, zero_mul, add_zero, Nat.add_sub_cancel,
        Nat.add_sub_add_right]
    ·
      rw [sum_range_succ' (fun s => C ((W n s : ℕ) : ℂ) * zS R ^ ((n - s) / 2) *
        (C (wt R s) * zS R * tS R (s - 1)))]
      simp only [wt, C_0, zero_mul, mul_zero, add_zero, Nat.add_sub_cancel]
      rw [sum_range_succ, sum_range_succ, hW0 (n + 1) (by omega), hW0 (n + 2) (by omega)]
      simp only [mul_zero, C_0, zero_mul, add_zero]
      apply sum_congr rfl
      intro s hs
      have hs' : s < n := by simpa using hs
      by_cases hpar : (n + (s + 1)) % 2 = 1
      · rw [W_eq_zero_of_odd r W h0s hroot hstep n (s + 1) hpar]; simp
      · have he : (n - (s + 1)) / 2 + 1 = (n + 1 - s) / 2 := by omega
        rw [← he, pow_succ, C_mul]
        ring

end Walk

section Functional

def ev (u w : ℕ) : Fin 2 →₀ ℕ := Finsupp.single 0 u + Finsupp.single 1 w

@[scoped simp] theorem ev_zero (u w : ℕ) : ev u w 0 = u := by simp [ev]
@[scoped simp] theorem ev_one (u w : ℕ) : ev u w 1 = w := by simp [ev]

def Λ (lam : (Fin 2 →₀ ℕ) → ℂ) : MvPolynomial (Fin 2) ℂ →ₗ[ℂ] ℂ :=
  Finsupp.linearCombination ℂ lam ∘ₗ (AddMonoidAlgebra.coeffLinearEquiv ℂ).toLinearMap

theorem Λ_monomial (lam : (Fin 2 →₀ ℕ) → ℂ) (m : Fin 2 →₀ ℕ) (c : ℂ) :
    Λ lam (monomial m c) = c * lam m := by
  rw [← single_eq_monomial]
  show Finsupp.linearCombination ℂ lam (AddMonoidAlgebra.single m c).coeff = _
  rw [AddMonoidAlgebra.coeff_single, Finsupp.linearCombination_single, smul_eq_mul]

theorem XY_pow_eq_monomial (u w : ℕ) : PX ^ u * PY ^ w = monomial (ev u w) 1 := by
  rw [PX, PY, X_pow_eq_monomial, X_pow_eq_monomial, monomial_mul, one_mul]
  rfl

theorem Λ_C_mul_XY (lam : (Fin 2 →₀ ℕ) → ℂ) (c : ℂ) (u w : ℕ) :
    Λ lam (C c * (PX ^ u * PY ^ w)) = c * lam (ev u w) := by
  rw [XY_pow_eq_monomial, C_mul_monomial, mul_one, Λ_monomial]

def Hsum (lam : (Fin 2 →₀ ℕ) → ℂ) (a s : ℕ) : ℂ := ∑ i ∈ range (s + 1), lam (ev (a + i) (a + s - i))

theorem Hsum_zero (lam : (Fin 2 →₀ ℕ) → ℂ) (a : ℕ) : Hsum lam a 0 = lam (ev a a) := by simp [Hsum]

theorem Hsum_one (lam : (Fin 2 →₀ ℕ) → ℂ) (a : ℕ) :
    Hsum lam a 1 = lam (ev a (a + 1)) + lam (ev (a + 1) a) := by
  simp [Hsum, sum_range_succ]

theorem Hsum_add_two (lam : (Fin 2 →₀ ℕ) → ℂ) (a s : ℕ) :
    Hsum lam a (s + 2) = lam (ev a (a + s + 2)) + Hsum lam (a + 1) s + lam (ev (a + s + 2) a) := by
  unfold Hsum
  rw [sum_range_succ, sum_range_succ']
  have h : ∀ i ∈ range (s + 1),
      lam (ev (a + (i + 1)) (a + (s + 2) - (i + 1))) = lam (ev (a + 1 + i) (a + 1 + s - i)) := by
    intro i hi
    have hi' : i ≤ s := by simpa [Nat.lt_succ_iff] using hi
    have e1 : a + (i + 1) = a + 1 + i := by omega
    have e2 : a + (s + 2) - (i + 1) = a + 1 + s - i := by omega
    rw [e1, e2]
  rw [sum_congr rfl h]
  have e1 : a + (s + 2) - 0 = a + s + 2 := by omega
  have e2 : a + (s + 2) - (s + 2) = a := by omega
  have e3 : a + (s + 2) = a + s + 2 := by omega
  rw [e1, e2, e3, Nat.add_zero]
  ring

theorem zS_pow (R : ℂ) (a : ℕ) : zS R ^ a = C (R⁻¹ ^ a) * (PX * PY) ^ a := by
  rw [zS, mul_pow, C_pow]

theorem Λ_zS_pow_mul_hp (lam : (Fin 2 →₀ ℕ) → ℂ) (R c : ℂ) (a s : ℕ) :
    Λ lam (C c * zS R ^ a * hp s) = c * R⁻¹ ^ a * Hsum lam a s := by
  rw [zS_pow, hp, Hsum, mul_sum, map_sum, mul_sum]
  apply sum_congr rfl
  intro i hi
  have hi' : i ≤ s := by simpa [Nat.lt_succ_iff] using hi
  have : C c * (C (R⁻¹ ^ a) * (PX * PY) ^ a) * (PX ^ i * PY ^ (s - i)) =
      C (c * R⁻¹ ^ a) * (PX ^ (a + i) * PY ^ (a + s - i)) := by
    rw [mul_pow, C_mul, show a + s - i = a + (s - i) by omega, pow_add, pow_add]; ring
  rw [this, Λ_C_mul_XY]

theorem Λ_zS_pow_mul_tS_zero (lam : (Fin 2 →₀ ℕ) → ℂ) (R c : ℂ) (a : ℕ) :
    Λ lam (C c * zS R ^ a * tS R 0) = c * R⁻¹ ^ a * lam (ev a a) := by
  rw [tS_zero, ← hp_zero, Λ_zS_pow_mul_hp, Hsum_zero]

theorem Λ_zS_pow_mul_tS_one (lam : (Fin 2 →₀ ℕ) → ℂ) (R c : ℂ) (a : ℕ) :
    Λ lam (C c * zS R ^ a * tS R 1) = c * R⁻¹ ^ a * (lam (ev a (a + 1)) + lam (ev (a + 1) a)) := by
  rw [tS_one, ← hp_one, Λ_zS_pow_mul_hp, Hsum_one]

theorem Λ_zS_pow_mul_tS_add_two (lam : (Fin 2 →₀ ℕ) → ℂ) (R c : ℂ) (a s : ℕ) :
    Λ lam (C c * zS R ^ a * tS R (s + 2)) =
      c * R⁻¹ ^ a * (lam (ev a (a + s + 2)) + lam (ev (a + s + 2) a) + (1 - R⁻¹) * Hsum lam (a + 1) s) := by
  rw [tS_add_two, mul_sub, map_sub, Λ_zS_pow_mul_hp,
    show C c * zS R ^ a * (zS R * hp s) = C c * zS R ^ (a + 1) * hp s by ring, Λ_zS_pow_mul_hp,
    Hsum_add_two]
  ring

end Functional

section Cells

def ω (R : ℂ) : ℂ := 1 - R⁻¹

def AG (R : ℂ) (d : ℕ) : ℂ := ∑ s ∈ Icc 1 d, (s : ℂ) * R ^ s

theorem sum_Icc_one_eq_sum_range {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ∑ i ∈ Icc 1 n, f i = ∑ i ∈ range n, f (i + 1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_Icc_succ_top (by omega), ih, sum_range_succ]

theorem AG_zero (R : ℂ) : AG R 0 = 0 := by simp [AG]

theorem AG_succ (R : ℂ) (d : ℕ) : AG R (d + 1) = AG R d + ((d + 1 : ℕ) : ℂ) * R ^ (d + 1) := by
  rw [AG, sum_Icc_succ_top (by omega)]; rfl

theorem AG_closed (R : ℂ) (d : ℕ) :
    (R - 1) ^ 2 * AG R d = R + (d : ℂ) * R ^ (d + 2) - ((d + 1 : ℕ) : ℂ) * R ^ (d + 1) := by
  induction d with
  | zero => simp [AG_zero]
  | succ d ih =>
    rw [AG_succ, mul_add, ih]
    push_cast
    ring

def lamA (R : ℂ) (r d : ℕ) (e : Fin 2 →₀ ℕ) : ℂ :=
  if e 0 + e 1 = 2 * r then
    (if e 0 = r then R ^ r * ω R * AG R d else (R ^ (r + d) - R ^ (min (e 0) (e 1))) / 2)
  else 0

def lamB (R : ℂ) (ra rb : ℕ) (e : Fin 2 →₀ ℕ) : ℂ :=
  if e 0 + e 1 = ra + rb then (R ^ ra - R ^ (min (min (e 0) (e 1)) ra)) / 2 else 0

theorem lamA_ev (R : ℂ) (r d u w : ℕ) : lamA R r d (ev u w) =
    if u + w = 2 * r then (if u = r then R ^ r * ω R * AG R d else (R ^ (r + d) - R ^ (min u w)) / 2)
    else 0 := by
  simp [lamA]

theorem lamB_ev (R : ℂ) (ra rb u w : ℕ) : lamB R ra rb (ev u w) =
    if u + w = ra + rb then (R ^ ra - R ^ (min (min u w) ra)) / 2 else 0 := by
  simp [lamB]

theorem Hsum_lamA_off (R : ℂ) (r d a s : ℕ) (h : 2 * a + s ≠ 2 * r) : Hsum (lamA R r d) a s = 0 := by
  unfold Hsum
  apply sum_eq_zero
  intro i hi
  have hi' : i ≤ s := by simpa [Nat.lt_succ_iff] using hi
  rw [lamA_ev, if_neg (by omega)]

theorem Hsum_lamB_off (R : ℂ) (ra rb a s : ℕ) (h : 2 * a + s ≠ ra + rb) : Hsum (lamB R ra rb) a s = 0 := by
  unfold Hsum
  apply sum_eq_zero
  intro i hi
  have hi' : i ≤ s := by simpa [Nat.lt_succ_iff] using hi
  rw [lamB_ev, if_neg (by omega)]

theorem Hsum_lamB_high (R : ℂ) (ra rb a s : ℕ) (h : ra ≤ a) : Hsum (lamB R ra rb) a s = 0 := by
  unfold Hsum
  apply sum_eq_zero
  intro i hi
  have hi' : i ≤ s := by simpa [Nat.lt_succ_iff] using hi
  rw [lamB_ev]
  split_ifs with h1
  · have : min (min (a + i) (a + s - i)) ra = ra := by omega
    rw [this, sub_self, zero_div]
  · rfl

theorem Hsum_lamB_diag (R : ℂ) (ra rb : ℕ) (hlt : ra < rb) :
    ∀ N a s : ℕ, a + N = ra → 2 * a + s = ra + rb →
      Hsum (lamB R ra rb) a s = (N : ℂ) * R ^ ra - R ^ a * ∑ i ∈ range N, R ^ i := by
  intro N
  induction N with
  | zero =>
    intro a s ha hs
    rw [Hsum_lamB_high R ra rb a s (by omega)]
    simp
  | succ N ih =>
    intro a s ha hs
    obtain ⟨s', rfl⟩ : ∃ s', s = s' + 2 := ⟨s - 2, by omega⟩
    rw [Hsum_add_two, ih (a + 1) s' (by omega) (by omega), lamB_ev, lamB_ev,
      if_pos (by omega), if_pos (by omega)]
    have m1 : min (min a (a + s' + 2)) ra = a := by omega
    have m2 : min (min (a + s' + 2) a) ra = a := by omega
    rw [m1, m2, sum_range_succ', pow_zero]
    simp only [pow_succ, ← sum_mul]
    push_cast
    ring

theorem Hsum_lamA_diag (R : ℂ) (r d : ℕ) :
    ∀ n a : ℕ, a + n = r →
      Hsum (lamA R r d) a (2 * n) =
        R ^ r * ω R * AG R d + (n : ℂ) * R ^ (r + d) - R ^ a * ∑ i ∈ range n, R ^ i := by
  intro n
  induction n with
  | zero =>
    intro a ha
    rw [Nat.mul_zero, Hsum_zero, lamA_ev, if_pos (by omega), if_pos (by omega)]
    have : a = r := by omega
    subst this
    simp
  | succ n ih =>
    intro a ha
    rw [show 2 * (n + 1) = 2 * n + 2 by ring, Hsum_add_two, ih (a + 1) (by omega), lamA_ev, lamA_ev,
      if_pos (by omega), if_neg (by omega), if_pos (by omega), if_neg (by omega)]
    have m1 : min a (a + 2 * n + 2) = a := by omega
    have m2 : min (a + 2 * n + 2) a = a := by omega
    rw [m1, m2, sum_range_succ', pow_zero]
    simp only [pow_succ, ← sum_mul]
    push_cast
    ring

theorem omega_mul_pow_succ (R : ℂ) (hR : R ≠ 0) (a : ℕ) : (1 - R⁻¹) * R ^ (a + 1) = R ^ a * (R - 1) := by
  field_simp
  ring

theorem lamA_ev_off (R : ℂ) (r d u w : ℕ) (h : u + w ≠ 2 * r) : lamA R r d (ev u w) = 0 := by
  rw [lamA_ev, if_neg h]

theorem lamA_ev_diag (R : ℂ) (r d : ℕ) : lamA R r d (ev r r) = R ^ r * ω R * AG R d := by
  rw [lamA_ev, if_pos (by omega), if_pos rfl]

theorem lamA_ev_on (R : ℂ) (r d u w : ℕ) (h : u + w = 2 * r) (hu : u ≠ r) :
    lamA R r d (ev u w) = (R ^ (r + d) - R ^ (min u w)) / 2 := by
  rw [lamA_ev, if_pos h, if_neg hu]

theorem lamB_ev_off (R : ℂ) (ra rb u w : ℕ) (h : u + w ≠ ra + rb) : lamB R ra rb (ev u w) = 0 := by
  rw [lamB_ev, if_neg h]

theorem lamB_ev_on (R : ℂ) (ra rb u w : ℕ) (h : u + w = ra + rb) :
    lamB R ra rb (ev u w) = (R ^ ra - R ^ (min (min u w) ra)) / 2 := by
  rw [lamB_ev, if_pos h]

def JδA (R : ℂ) (r d a s : ℕ) : ℂ :=
  if s = 0 ∧ a = r then ω R * AG R d
  else if 2 * a + s = 2 * r ∧ 2 ≤ s then ((d + s / 2 : ℕ) : ℂ) * R ^ (d + s / 2) * ω R else 0

def JδB (R : ℂ) (ra rb a s : ℕ) : ℂ :=
  if 2 * a + s = ra + rb ∧ a < ra then ((ra - a : ℕ) : ℂ) * R ^ (ra - a) * ω R else 0

theorem JδA_diag (R : ℂ) (r d : ℕ) : JδA R r d r 0 = ω R * AG R d := by
  simp [JδA]

theorem JδA_on (R : ℂ) (r d a s : ℕ) (h1 : 2 * a + s = 2 * r) (h2 : 2 ≤ s) :
    JδA R r d a s = ((d + s / 2 : ℕ) : ℂ) * R ^ (d + s / 2) * ω R := by
  have : ¬ (s = 0 ∧ a = r) := by omega
  rw [JδA, if_neg this, if_pos ⟨h1, h2⟩]

theorem JδA_off (R : ℂ) (r d a s : ℕ) (h1 : ¬ (s = 0 ∧ a = r)) (h2 : ¬ (2 * a + s = 2 * r ∧ 2 ≤ s)) :
    JδA R r d a s = 0 := by
  rw [JδA, if_neg h1, if_neg h2]

theorem JδB_on (R : ℂ) (ra rb a s : ℕ) (h1 : 2 * a + s = ra + rb) (h2 : a < ra) :
    JδB R ra rb a s = ((ra - a : ℕ) : ℂ) * R ^ (ra - a) * ω R := by
  rw [JδB, if_pos ⟨h1, h2⟩]

theorem JδB_off (R : ℂ) (ra rb a s : ℕ) (h : ¬ (2 * a + s = ra + rb ∧ a < ra)) : JδB R ra rb a s = 0 := by
  rw [JδB, if_neg h]

theorem inv_pow_mul_pow (R : ℂ) (hR : R ≠ 0) (a : ℕ) : R⁻¹ ^ a * R ^ a = 1 := by
  rw [inv_pow, inv_mul_cancel₀ (pow_ne_zero a hR)]

theorem evalB (R : ℂ) (hR : R ≠ 0) (ra rb : ℕ) (hlt : ra < rb) (c : ℂ) (a s : ℕ) :
    Λ (lamB R ra rb) (C c * zS R ^ a * tS R s) = c * JδB R ra rb a s := by
  rcases s with _ | _ | s
  · rw [Λ_zS_pow_mul_tS_zero]
    by_cases h : a + a = ra + rb
    · have : min (min a a) ra = ra := by omega
      rw [lamB_ev_on R ra rb a a h, this, sub_self, zero_div, JδB_off R ra rb a 0 (by omega)]; ring
    · rw [lamB_ev_off R ra rb a a h, JδB_off R ra rb a 0 (by omega)]; ring
  · rw [Λ_zS_pow_mul_tS_one]
    by_cases h : a + (a + 1) = ra + rb
    · have m1 : min (min a (a + 1)) ra = ra := by omega
      have m2 : min (min (a + 1) a) ra = ra := by omega
      rw [lamB_ev_on R ra rb _ _ h, lamB_ev_on R ra rb _ _ (by omega), m1, m2,
        JδB_off R ra rb a 1 (by omega)]; ring
    · rw [lamB_ev_off R ra rb _ _ h, lamB_ev_off R ra rb _ _ (by omega), JδB_off R ra rb a 1 (by omega)]
      ring
  · rw [Λ_zS_pow_mul_tS_add_two]
    by_cases h : a + (a + s + 2) = ra + rb
    · by_cases ha : a < ra
      · obtain ⟨N, hN⟩ : ∃ N, a + 1 + N = ra := ⟨ra - a - 1, by omega⟩
        rw [Hsum_lamB_diag R ra rb hlt N (a + 1) s hN (by omega), lamB_ev_on R ra rb _ _ h,
          lamB_ev_on R ra rb _ _ (by omega), JδB_on R ra rb a (s + 2) (by omega) ha]
        have m1 : min (min a (a + s + 2)) ra = a := by omega
        have m2 : min (min (a + s + 2) a) ra = a := by omega
        rw [m1, m2]
        set S := ∑ i ∈ range N, R ^ i with hS
        have key : S * (R - 1) = R ^ N - 1 := geom_sum_mul R N
        have e1 := omega_mul_pow_succ R hR a
        have e2 : (1 - R⁻¹) * ((N : ℂ) * R ^ ra - R ^ (a + 1) * S) =
            (1 - R⁻¹) * (N : ℂ) * R ^ ra - R ^ a * (R ^ N - 1) := by
          rw [← key]; linear_combination (-S) * e1
        rw [e2]
        have hra : ra = a + (N + 1) := by omega
        have hsub : ra - a = N + 1 := by omega
        rw [hsub, hra]
        unfold ω
        rw [inv_pow]
        push_cast
        field_simp
        ring
      · rw [Hsum_lamB_high R ra rb (a + 1) s (by omega), lamB_ev_on R ra rb _ _ h,
          lamB_ev_on R ra rb _ _ (by omega), JδB_off R ra rb a (s + 2) (by omega)]
        have m1 : min (min a (a + s + 2)) ra = ra := by omega
        have m2 : min (min (a + s + 2) a) ra = ra := by omega
        rw [m1, m2]; ring
    · rw [lamB_ev_off R ra rb _ _ h, lamB_ev_off R ra rb _ _ (by omega),
        Hsum_lamB_off R ra rb (a + 1) s (by omega), JδB_off R ra rb a (s + 2) (by omega)]
      ring

theorem evalA (R : ℂ) (hR : R ≠ 0) (r d : ℕ) (c : ℂ) (a s : ℕ) :
    Λ (lamA R r d) (C c * zS R ^ a * tS R s) = c * JδA R r d a s := by
  rcases s with _ | _ | s
  · rw [Λ_zS_pow_mul_tS_zero]
    by_cases h : a = r
    · subst h
      rw [lamA_ev_diag, JδA_diag]
      have := inv_pow_mul_pow R hR a
      linear_combination (c * ω R * AG R d) * this
    · rw [lamA_ev_off R r d a a (by omega), JδA_off R r d a 0 (by omega) (by omega)]; ring
  · rw [Λ_zS_pow_mul_tS_one, lamA_ev_off R r d _ _ (by omega), lamA_ev_off R r d _ _ (by omega),
      JδA_off R r d a 1 (by omega) (by omega)]
    ring
  · rw [Λ_zS_pow_mul_tS_add_two]
    by_cases h : a + (a + s + 2) = 2 * r
    · obtain ⟨n, hn⟩ : ∃ n, s = 2 * n := ⟨s / 2, by omega⟩
      subst hn
      have har : a + 1 + n = r := by omega
      rw [Hsum_lamA_diag R r d n (a + 1) har, lamA_ev_on R r d _ _ h (by omega),
        lamA_ev_on R r d _ _ (by omega) (by omega), JδA_on R r d a (2 * n + 2) (by omega) (by omega)]
      have m1 : min a (a + 2 * n + 2) = a := by omega
      have m2 : min (a + 2 * n + 2) a = a := by omega
      have hd : d + (2 * n + 2) / 2 = d + n + 1 := by omega
      rw [m1, m2, hd]
      set S := ∑ i ∈ range n, R ^ i with hS
      have key : S * (R - 1) = R ^ n - 1 := geom_sum_mul R n
      have e1 := omega_mul_pow_succ R hR a
      have e2 : (1 - R⁻¹) * (R ^ r * ω R * AG R d + (n : ℂ) * R ^ (r + d) - R ^ (a + 1) * S) =
          (1 - R⁻¹) * (R ^ r * ω R * AG R d + (n : ℂ) * R ^ (r + d)) - R ^ a * (R ^ n - 1) := by
        rw [← key]; linear_combination (-S) * e1
      rw [e2]
      have hr : r = a + n + 1 := by omega
      subst hr
      have e3 := AG_closed R d
      push_cast at e3
      unfold ω
      rw [inv_pow]
      push_cast
      field_simp
      linear_combination (2 * c * R ^ (a + n + 1)) * e3
    · rw [lamA_ev_off R r d _ _ h, lamA_ev_off R r d _ _ (by omega), Hsum_lamA_off R r d (a + 1) s (by omega),
        JδA_off R r d a (s + 2) (by omega) (by omega)]
      ring

end Cells

section Words

variable (p : ℕ) (P : ℂ) (hP : (p : ℂ) = P) (hP0 : P ≠ 0) (W : ℕ → ℕ → ℕ)
  (h00 : W 0 0 = 1) (h0s : ∀ s : ℕ, W 0 (s + 1) = 0)
  (hroot : ∀ n : ℕ, W (n + 1) 0 = (p + 1) * W n 1)
  (hstep : ∀ n s : ℕ, W (n + 1) (s + 1) = W n s + p * W n (s + 2))

include hP hP0 h00 h0s hroot hstep in

theorem Λ_word (lam : (Fin 2 →₀ ℕ) → ℂ) (J : ℕ → ℕ → ℂ)
    (heval : ∀ (c : ℂ) (a s : ℕ), Λ lam (C c * zS P ^ a * tS P s) = c * J a s) (n m : ℕ) :
    Λ lam ((PX + PY) ^ n * zS P ^ m) = ∑ s ∈ range (n + 1), ((W n s : ℕ) : ℂ) * J (m + (n - s) / 2) s := by
  have hp0 : (p : ℂ) ≠ 0 := by rwa [hP]
  rw [word_expansion p W h0s hroot hstep hp0 h00 n, hP, sum_mul, map_sum]
  apply sum_congr rfl
  intro s hs
  rw [show C ((W n s : ℕ) : ℂ) * zS P ^ ((n - s) / 2) * tS P s * zS P ^ m =
      C ((W n s : ℕ) : ℂ) * zS P ^ (m + (n - s) / 2) * tS P s by rw [pow_add]; ring]
  exact heval _ _ _

def JBform (P : ℂ) (ra t : ℕ) (h : ℤ → ℕ → ℂ) : ℂ :=
  ∑ i ∈ Icc 1 ra, (i : ℂ) * P ^ i * (1 - P⁻¹) * h ((ra : ℤ) - i) (t + 2 * i)

def JAform (P : ℂ) (r d : ℕ) (h : ℤ → ℕ → ℂ) : ℂ :=
  h r 0 * ∑ s ∈ Icc 1 d, (s : ℂ) * P ^ s * (1 - P⁻¹) +
    ∑ i ∈ Icc 1 r, ((d + i : ℕ) : ℂ) * P ^ (d + i) * (1 - P⁻¹) * h ((r : ℤ) - i) (2 * i)

include hP hP0 h00 h0s hroot hstep in

theorem perWordB (n m : ℕ) (cell : ℤ → ℕ → ℂ)
    (hcell : ∀ (a : ℤ) (s : ℕ), cell a s = if 2 * a + s = (n : ℤ) + 2 * (m : ℤ) then (W n s : ℂ) else 0)
    (ra rb t : ℕ) (hlt : ra < rb) (ht : ra + t = rb) :
    JBform P ra t cell = Λ (lamB P ra rb) ((PX + PY) ^ n * zS P ^ m) := by
  rw [Λ_word p P hP hP0 W h00 h0s hroot hstep _ _ (evalB P hP0 ra rb hlt) n m, JBform]
  have hind : ∀ i : ℕ, (2 * ((ra : ℤ) - (i : ℤ)) + ((t + 2 * i : ℕ) : ℤ) = (n : ℤ) + 2 * (m : ℤ)) ↔
      (ra + rb = n + 2 * m) := by
    intro i; push_cast; omega
  simp_rw [hcell, hind]
  by_cases hc : ra + rb = n + 2 * m
  · simp only [hc, if_true]
    symm
    apply Finset.sum_bij_ne_zero (fun s _ _ => (s - t) / 2)
    · intro s hs hne
      have hs' : s ≤ n := by simpa [Nat.lt_succ_iff] using hs
      have hW : W n s ≠ 0 := fun h => by simp [h] at hne
      have hJ : JδB P ra rb (m + (n - s) / 2) s ≠ 0 := fun h => by simp [h] at hne
      have hpar : (n + s) % 2 = 0 := by
        by_contra hodd; exact hW (W_eq_zero_of_odd p W h0s hroot hstep n s (by omega))
      have hc2 : 2 * (m + (n - s) / 2) + s = ra + rb ∧ m + (n - s) / 2 < ra := by
        by_contra hno; exact hJ (JδB_off P ra rb _ _ hno)
      simp only [mem_Icc]; omega
    · intro s1 hs1 hne1 s2 hs2 hne2 heq
      have hs1' : s1 ≤ n := by simpa [Nat.lt_succ_iff] using hs1
      have hs2' : s2 ≤ n := by simpa [Nat.lt_succ_iff] using hs2
      have hW1 : W n s1 ≠ 0 := fun h => by simp [h] at hne1
      have hW2 : W n s2 ≠ 0 := fun h => by simp [h] at hne2
      have hJ1 : JδB P ra rb (m + (n - s1) / 2) s1 ≠ 0 := fun h => by simp [h] at hne1
      have hJ2 : JδB P ra rb (m + (n - s2) / 2) s2 ≠ 0 := fun h => by simp [h] at hne2
      have hp1 : (n + s1) % 2 = 0 := by
        by_contra hodd; exact hW1 (W_eq_zero_of_odd p W h0s hroot hstep n s1 (by omega))
      have hp2 : (n + s2) % 2 = 0 := by
        by_contra hodd; exact hW2 (W_eq_zero_of_odd p W h0s hroot hstep n s2 (by omega))
      have hc1 : 2 * (m + (n - s1) / 2) + s1 = ra + rb ∧ m + (n - s1) / 2 < ra := by
        by_contra hno; exact hJ1 (JδB_off P ra rb _ _ hno)
      have hc2' : 2 * (m + (n - s2) / 2) + s2 = ra + rb ∧ m + (n - s2) / 2 < ra := by
        by_contra hno; exact hJ2 (JδB_off P ra rb _ _ hno)
      omega
    · intro i hi hne
      have hi' : 1 ≤ i ∧ i ≤ ra := by simpa [mem_Icc] using hi
      have hW : W n (t + 2 * i) ≠ 0 := fun h => by simp [h] at hne
      have hle : t + 2 * i ≤ n := by
        by_contra hlt'; exact hW (W_eq_zero_of_lt p W h0s hstep n _ (by omega))
      refine ⟨t + 2 * i, by simpa [Nat.lt_succ_iff] using hle, ?_, by omega⟩
      rw [JδB_on P ra rb (m + (n - (t + 2 * i)) / 2) (t + 2 * i) (by omega) (by omega)]
      have e1 : ra - (m + (n - (t + 2 * i)) / 2) = i := by omega
      rw [e1]
      intro h0
      apply hne
      unfold ω at h0
      linear_combination h0
    · intro s hs hne
      have hs' : s ≤ n := by simpa [Nat.lt_succ_iff] using hs
      have hW : W n s ≠ 0 := fun h => by simp [h] at hne
      have hJ : JδB P ra rb (m + (n - s) / 2) s ≠ 0 := fun h => by simp [h] at hne
      have hpar : (n + s) % 2 = 0 := by
        by_contra hodd; exact hW (W_eq_zero_of_odd p W h0s hroot hstep n s (by omega))
      have hc2 : 2 * (m + (n - s) / 2) + s = ra + rb ∧ m + (n - s) / 2 < ra := by
        by_contra hno; exact hJ (JδB_off P ra rb _ _ hno)
      rw [JδB_on P ra rb _ _ hc2.1 hc2.2]
      have e1 : t + 2 * ((s - t) / 2) = s := by omega
      have e2 : ra - (m + (n - s) / 2) = (s - t) / 2 := by omega
      rw [e1, e2]
      unfold ω
      ring
  · simp only [hc, if_false, mul_zero, sum_const_zero]
    symm
    apply sum_eq_zero
    intro s hs
    have hs' : s ≤ n := by simpa [Nat.lt_succ_iff] using hs
    by_cases hpar : (n + s) % 2 = 1
    · rw [W_eq_zero_of_odd p W h0s hroot hstep n s hpar]; simp
    · rw [JδB_off P ra rb _ _ (by omega)]; simp

include hP hP0 h00 h0s hroot hstep in

theorem perWordA (n m : ℕ) (cell : ℤ → ℕ → ℂ)
    (hcell : ∀ (a : ℤ) (s : ℕ), cell a s = if 2 * a + s = (n : ℤ) + 2 * (m : ℤ) then (W n s : ℂ) else 0)
    (r d : ℕ) :
    JAform P r d cell = Λ (lamA P r d) ((PX + PY) ^ n * zS P ^ m) := by
  rw [Λ_word p P hP hP0 W h00 h0s hroot hstep _ _ (evalA P hP0 r d) n m, JAform]
  have hind0 : (2 * (r : ℤ) + ((0 : ℕ) : ℤ) = (n : ℤ) + 2 * (m : ℤ)) ↔ (2 * r = n + 2 * m) := by
    push_cast; omega
  have hind : ∀ i : ℕ, (2 * ((r : ℤ) - (i : ℤ)) + ((2 * i : ℕ) : ℤ) = (n : ℤ) + 2 * (m : ℤ)) ↔
      (2 * r = n + 2 * m) := by
    intro i; push_cast; omega
  simp_rw [hcell, hind0, hind]
  have hAG : ∑ s ∈ Icc 1 d, (s : ℂ) * P ^ s * (1 - P⁻¹) = ω P * AG P d := by
    rw [AG, ω, mul_sum]; apply sum_congr rfl; intro s hs; ring
  rw [hAG]
  by_cases hc : 2 * r = n + 2 * m
  · simp only [hc, if_true]
    symm
    have hr : m + (n - 0) / 2 = r := by omega
    have hsum : (∑ x ∈ range n, ((W n (x + 1) : ℕ) : ℂ) * JδA P r d (m + (n - (x + 1)) / 2) (x + 1)) =
        ∑ i ∈ Icc 1 r, ((d + i : ℕ) : ℂ) * P ^ (d + i) * (1 - P⁻¹) * ((W n (2 * i) : ℕ) : ℂ) := by
      apply Finset.sum_bij_ne_zero (fun s _ _ => (s + 1) / 2)
      · intro s hs hne
        have hs' : s + 1 ≤ n := by have := mem_range.1 hs; omega
        have hW : W n (s + 1) ≠ 0 := fun h => by simp [h] at hne
        have hJ : JδA P r d (m + (n - (s + 1)) / 2) (s + 1) ≠ 0 := fun h => by simp [h] at hne
        have hpar : (n + (s + 1)) % 2 = 0 := by
          by_contra hodd; exact hW (W_eq_zero_of_odd p W h0s hroot hstep n (s + 1) (by omega))
        have hc2 : 2 * (m + (n - (s + 1)) / 2) + (s + 1) = 2 * r ∧ 2 ≤ s + 1 := by
          by_contra hno; exact hJ (JδA_off P r d _ _ (by omega) hno)
        simp only [mem_Icc]; omega
      · intro s1 hs1 hne1 s2 hs2 hne2 heq
        have hW1 : W n (s1 + 1) ≠ 0 := fun h => by simp [h] at hne1
        have hW2 : W n (s2 + 1) ≠ 0 := fun h => by simp [h] at hne2
        have hp1 : (n + (s1 + 1)) % 2 = 0 := by
          by_contra hodd; exact hW1 (W_eq_zero_of_odd p W h0s hroot hstep n (s1 + 1) (by omega))
        have hp2 : (n + (s2 + 1)) % 2 = 0 := by
          by_contra hodd; exact hW2 (W_eq_zero_of_odd p W h0s hroot hstep n (s2 + 1) (by omega))
        omega
      · intro i hi hne
        have hi' : 1 ≤ i ∧ i ≤ r := by simpa [mem_Icc] using hi
        have hW : W n (2 * i) ≠ 0 := fun h => by simp [h] at hne
        have hle : 2 * i ≤ n := by
          by_contra hlt'; exact hW (W_eq_zero_of_lt p W h0s hstep n _ (by omega))
        refine ⟨2 * i - 1, mem_range.2 (by omega), ?_, by omega⟩
        have e0 : 2 * i - 1 + 1 = 2 * i := by omega
        rw [e0, JδA_on P r d (m + (n - 2 * i) / 2) (2 * i) (by omega) (by omega)]
        have e1 : d + 2 * i / 2 = d + i := by omega
        rw [e1]
        intro h0
        apply hne
        unfold ω at h0
        linear_combination h0
      · intro s hs hne
        have hs' : s + 1 ≤ n := by have := mem_range.1 hs; omega
        have hW : W n (s + 1) ≠ 0 := fun h => by simp [h] at hne
        have hJ : JδA P r d (m + (n - (s + 1)) / 2) (s + 1) ≠ 0 := fun h => by simp [h] at hne
        have hpar : (n + (s + 1)) % 2 = 0 := by
          by_contra hodd; exact hW (W_eq_zero_of_odd p W h0s hroot hstep n (s + 1) (by omega))
        have hc2 : 2 * (m + (n - (s + 1)) / 2) + (s + 1) = 2 * r ∧ 2 ≤ s + 1 := by
          by_contra hno; exact hJ (JδA_off P r d _ _ (by omega) hno)
        rw [JδA_on P r d _ _ hc2.1 hc2.2]
        have e1 : 2 * ((s + 1) / 2) = s + 1 := by omega
        have e2 : d + (s + 1) / 2 = d + (s + 1) / 2 := rfl
        rw [e1]
        unfold ω
        ring
    rw [sum_range_succ', hsum, hr, JδA_diag]
    ring
  · simp only [hc, if_false, zero_mul, mul_zero, sum_const_zero, zero_add]
    symm
    apply sum_eq_zero
    intro s hs
    have hs' : s ≤ n := by simpa [Nat.lt_succ_iff] using hs
    by_cases hpar : (n + s) % 2 = 1
    · rw [W_eq_zero_of_odd p W h0s hroot hstep n s hpar]; simp
    · rw [JδA_off P r d _ _ (by omega) (by omega)]; simp

end Words

section BaseChange

open AutomorphicForm (satakePow)
open AutomorphicForm.SatakeCombination (univWord)

theorem satakePow_newton_aux {A : Type*} [CommRing A] (x y : A) : ∀ n : ℕ,
    satakePow (n + 1) (x + y) (x * y) = x ^ (n + 1) + y ^ (n + 1) ∧
      satakePow (n + 2) (x + y) (x * y) = x ^ (n + 2) + y ^ (n + 2)
  | 0 => by
    refine ⟨by simp, ?_⟩
    rw [AutomorphicForm.satakePow_add_two, AutomorphicForm.satakePow_one, AutomorphicForm.satakePow_zero]
    ring
  | n + 1 => by
    obtain ⟨h1, h2⟩ := satakePow_newton_aux x y n
    refine ⟨h2, ?_⟩
    rw [show n + 1 + 2 = (n + 1) + 2 from rfl, AutomorphicForm.satakePow_add_two,
      show n + 1 + 1 = n + 2 from rfl, h2, h1]
    ring

theorem satakePow_newton {A : Type*} [CommRing A] (x y : A) (n : ℕ) :
    satakePow (n + 1) (x + y) (x * y) = x ^ (n + 1) + y ^ (n + 1) :=
  (satakePow_newton_aux x y n).1

theorem map_satakePow_aux {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (u v : A) : ∀ n : ℕ,
    f (satakePow n u v) = satakePow n (f u) (f v) ∧ f (satakePow (n + 1) u v) = satakePow (n + 1) (f u) (f v)
  | 0 => by
    refine ⟨?_, by simp⟩
    simp only [AutomorphicForm.satakePow_zero]
    exact map_ofNat f 2
  | n + 1 => by
    obtain ⟨h1, h2⟩ := map_satakePow_aux f u v n
    refine ⟨h2, ?_⟩
    rw [show n + 1 + 1 = n + 2 from rfl, AutomorphicForm.satakePow_add_two, AutomorphicForm.satakePow_add_two,
      map_sub, map_mul, map_mul, h2, h1]

theorem map_satakePow {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (u v : A) (n : ℕ) :
    f (satakePow n u v) = satakePow n (f u) (f v) :=
  (map_satakePow_aux f u v n).1

def σS : MvPolynomial (Fin 2) ℂ →ₐ[ℂ] MvPolynomial (Fin 2) ℂ := aeval ![PX + PY, PX * PY]

theorem σS_X0 : σS (X 0) = PX + PY := by simp [σS]
theorem σS_X1 : σS (X 1) = PX * PY := by simp [σS]

theorem σS_univWord (ℓ k j : ℕ) (hℓ : 1 ≤ ℓ) :
    σS (univWord (ℓ - 1) k j) = (PX ^ ℓ + PY ^ ℓ) ^ k * (PX * PY) ^ (ℓ * j) := by
  obtain ⟨L, rfl⟩ : ∃ L, ℓ = L + 1 := ⟨ℓ - 1, by omega⟩
  rw [Nat.add_sub_cancel, univWord, map_mul, map_pow, map_pow, map_pow,
    show (σS (satakePow (L + 1) (X 0) (X 1)) : MvPolynomial (Fin 2) ℂ) =
      satakePow (L + 1) (σS (X 0)) (σS (X 1)) from map_satakePow σS.toRingHom _ _ _,
    σS_X0, σS_X1, satakePow_newton, ← pow_mul]

theorem σS_monomial (e : Fin 2 →₀ ℕ) (c : ℂ) :
    σS (monomial e c) = C c * ((PX + PY) ^ (e 0) * (PX * PY) ^ (e 1)) := by
  rw [σS, aeval_monomial, Finsupp.prod_pow, Fin.prod_univ_two]
  simp [MvPolynomial.algebraMap_eq]

theorem expand_word (ℓ k j : ℕ) :
    expand ℓ ((PX + PY) ^ k * (PX * PY) ^ j) = (PX ^ ℓ + PY ^ ℓ) ^ k * (PX * PY) ^ (ℓ * j) := by
  rw [map_mul, map_pow, map_pow, map_add, map_mul, PX, PY, expand_X, expand_X, ← mul_pow, ← pow_mul]

theorem satake_baseChange (q ℓ k j : ℕ) (hq : (q : ℂ) ≠ 0) (hℓ : 1 ≤ ℓ) :
    ∑ e ∈ (univWord (ℓ - 1) k j).support,
        C ((univWord (ℓ - 1) k j).coeff e * (q : ℂ) ^ (e 1) / (q : ℂ) ^ (ℓ * j)) *
          ((PX + PY) ^ (e 0) * zS (q : ℂ) ^ (e 1)) =
      C (((q : ℂ) ^ (ℓ * j))⁻¹) * expand ℓ ((PX + PY) ^ k * (PX * PY) ^ j) := by
  rw [expand_word, ← σS_univWord ℓ k j hℓ]
  conv_rhs => rw [as_sum (univWord (ℓ - 1) k j)]
  rw [map_sum, mul_sum]
  apply sum_congr rfl
  intro e he
  rw [σS_monomial, zS_pow]
  simp only [C_mul', mul_smul_comm, smul_smul]
  congr 1
  rw [inv_pow]
  field_simp

theorem Λ_expand (lam : (Fin 2 →₀ ℕ) → ℂ) (ℓ : ℕ) (F : MvPolynomial (Fin 2) ℂ) :
    Λ lam (expand ℓ F) = Λ (fun m => lam (ℓ • m)) F := by
  have : (Λ lam).comp (expand ℓ : MvPolynomial (Fin 2) ℂ →ₐ[ℂ] MvPolynomial (Fin 2) ℂ).toLinearMap =
      Λ (fun m => lam (ℓ • m)) := by
    apply MvPolynomial.linearMap_ext
    intro m
    refine LinearMap.ext fun c => ?_
    show Λ lam (expand ℓ (monomial m c)) = Λ (fun m => lam (ℓ • m)) (monomial m c)
    rw [expand_monomial, Λ_monomial, Λ_monomial]
  exact congrArg (fun L => L F) this

theorem Λ_sum_weights {ι : Type*} (S : Finset ι) (c : ι → ℂ) (lam : ι → (Fin 2 →₀ ℕ) → ℂ)
    (F : MvPolynomial (Fin 2) ℂ) :
    Λ (fun m => ∑ i ∈ S, c i * lam i m) F = ∑ i ∈ S, c i * Λ (lam i) F := by
  have : Λ (fun m => ∑ i ∈ S, c i * lam i m) = ∑ i ∈ S, c i • Λ (lam i) := by
    apply MvPolynomial.linearMap_ext
    intro m
    refine LinearMap.ext fun a => ?_
    show Λ _ (monomial m a) = (∑ i ∈ S, c i • Λ (lam i)) (monomial m a)
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, Λ_monomial]
    rw [mul_sum]
    apply sum_congr rfl; intro i hi; ring
  rw [this]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]

theorem Λ_C_mul (lam : (Fin 2 →₀ ℕ) → ℂ) (c : ℂ) (F : MvPolynomial (Fin 2) ℂ) :
    Λ lam (C c * F) = c * Λ lam F := by
  rw [C_mul', map_smul, smul_eq_mul]

theorem ev_smul (ℓ u w : ℕ) : ℓ • ev u w = ev (ℓ * u) (ℓ * w) := by
  simp [ev, smul_add, Finsupp.smul_single]

theorem eq_ev (m : Fin 2 →₀ ℕ) : m = ev (m 0) (m 1) := by
  ext i
  fin_cases i <;> simp

theorem min_mul_left' (ℓ u w : ℕ) : min (ℓ * u) (ℓ * w) = ℓ * min u w := by
  rcases le_total u w with h | h
  · rw [min_eq_left (Nat.mul_le_mul_left ℓ h), min_eq_left h]
  · rw [min_eq_right (Nat.mul_le_mul_left ℓ h), min_eq_right h]

theorem lamB_scale (q : ℂ) (ℓ ρa ρb : ℕ) (hℓ : 1 ≤ ℓ) (m : Fin 2 →₀ ℕ) :
    lamB q (ℓ * ρa) (ℓ * ρb) (ℓ • m) = lamB (q ^ ℓ) ρa ρb m := by
  rw [eq_ev m, ev_smul, lamB_ev, lamB_ev]
  by_cases h : m 0 + m 1 = ρa + ρb
  · rw [if_pos (by rw [← Nat.mul_add, ← Nat.mul_add, h]), if_pos h, min_mul_left', min_mul_left',
      ← pow_mul, ← pow_mul]
  · rw [if_neg, if_neg h]
    intro h'
    rw [← Nat.mul_add, ← Nat.mul_add] at h'
    exact h (Nat.eq_of_mul_eq_mul_left (by omega) h')

theorem tele (Pf G : ℕ → ℂ) (d : ℕ) :
    ∑ i ∈ range (d + 1), (Pf i - Pf (i + 1)) * G i =
      Pf 0 * G 0 - Pf (d + 1) * G d + ∑ i ∈ range d, Pf (i + 1) * (G (i + 1) - G i) := by
  induction d with
  | zero => simp; ring
  | succ d ih => rw [sum_range_succ, ih, sum_range_succ]; ring

section Shell

variable (q ℓ : ℕ) (hq : 1 ≤ q) (hℓ : 1 ≤ ℓ) (d : ℕ) (Pf : ℕ → ℂ) (hP0 : Pf 0 = 1)
  (hP : ∀ i : ℕ, 1 ≤ i → i ≤ d →
    Pf i = ((q : ℂ) ^ ((ℓ - 1) * (i - 1)) * ∑ t ∈ Finset.range ℓ, (q : ℂ) ^ t)⁻¹)
  (hPd : ∀ i : ℕ, d < i → Pf i = 0)

include hq hℓ hP in

theorem shell_atom (s : ℕ) (h1 : 1 ≤ s) (h2 : s ≤ d) :
    (1 - ((q : ℂ) ^ ℓ)⁻¹) * ((q : ℂ) ^ ℓ) ^ s * Pf s = (1 - (q : ℂ)⁻¹) * (q : ℂ) ^ s := by
  rw [hP s h1 h2]
  obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
  obtain ⟨L, rfl⟩ : ∃ L, ℓ = L + 1 := ⟨ℓ - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  rw [pow_mul, pow_succ (q : ℂ) L]
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  have hN : (∑ t ∈ range (L + 1), (q : ℂ) ^ t) * ((q : ℂ) - 1) = (q : ℂ) ^ (L + 1) - 1 := geom_sum_mul _ _
  rw [pow_succ (q : ℂ) L] at hN
  have hNpos : (0 : ℝ) < ∑ t ∈ range (L + 1), (q : ℝ) ^ t :=
    sum_pos (fun t _ => pow_pos (by exact_mod_cast (show 0 < q by omega)) t) ⟨0, by simp⟩
  have hN0 : (∑ t ∈ range (L + 1), (q : ℂ) ^ t) ≠ 0 := by
    have : (∑ t ∈ range (L + 1), (q : ℂ) ^ t) = ((∑ t ∈ range (L + 1), (q : ℝ) ^ t : ℝ) : ℂ) := by push_cast; rfl
    rw [this]; exact_mod_cast hNpos.ne'
  set N := ∑ t ∈ range (L + 1), (q : ℂ) ^ t with hNdef
  have hA0 : (q : ℂ) ^ L ≠ 0 := pow_ne_zero _ hq0
  have hQ0 : (q : ℂ) ^ L * (q : ℂ) ≠ 0 := mul_ne_zero hA0 hq0
  have e1 : (1 - ((q : ℂ) ^ L * (q : ℂ))⁻¹) * ((q : ℂ) ^ L * (q : ℂ)) ^ (s' + 1) =
      ((q : ℂ) ^ L * (q : ℂ) - 1) * ((q : ℂ) ^ L * (q : ℂ)) ^ s' := by
    rw [pow_succ]; field_simp
  have e2 : (1 - (q : ℂ)⁻¹) * (q : ℂ) ^ (s' + 1) = ((q : ℂ) - 1) * (q : ℂ) ^ s' := by
    rw [pow_succ]; field_simp
  rw [e1, e2, ← hN, mul_pow]
  field_simp

include hq hℓ hP0 hP hPd in
theorem shell_mean :
    ∑ i ∈ range (d + 1), (Pf i - Pf (i + 1)) * ((q : ℂ) ^ ℓ) ^ i = (q : ℂ) ^ d := by
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  have hQ0 : (q : ℂ) ^ ℓ ≠ 0 := pow_ne_zero _ hq0
  rw [tele, hP0, hPd (d + 1) (by omega)]
  have : ∀ i ∈ range d, Pf (i + 1) * (((q : ℂ) ^ ℓ) ^ (i + 1) - ((q : ℂ) ^ ℓ) ^ i) =
      ((q : ℂ) - 1) * (q : ℂ) ^ i := by
    intro i hi
    have hi' : i < d := mem_range.1 hi
    have h := shell_atom q ℓ hq hℓ d Pf hP (i + 1) (by omega) (by omega)
    have e : Pf (i + 1) * (((q : ℂ) ^ ℓ) ^ (i + 1) - ((q : ℂ) ^ ℓ) ^ i) =
        (1 - ((q : ℂ) ^ ℓ)⁻¹) * ((q : ℂ) ^ ℓ) ^ (i + 1) * Pf (i + 1) := by
      field_simp; ring
    rw [e, h]; field_simp; ring
  rw [sum_congr rfl this, ← mul_sum, mul_comm ((q : ℂ) - 1), geom_sum_mul]
  ring

include hq hℓ hP hPd in
theorem shell_AG :
    ∑ i ∈ range (d + 1), (Pf i - Pf (i + 1)) * (ω ((q : ℂ) ^ ℓ) * AG ((q : ℂ) ^ ℓ) i) =
      ω (q : ℂ) * AG (q : ℂ) d := by
  rw [tele, hPd (d + 1) (by omega), AG_zero]
  have : ∀ i ∈ range d, Pf (i + 1) * (ω ((q : ℂ) ^ ℓ) * AG ((q : ℂ) ^ ℓ) (i + 1) - ω ((q : ℂ) ^ ℓ) * AG ((q : ℂ) ^ ℓ) i) =
      ((i + 1 : ℕ) : ℂ) * ((1 - (q : ℂ)⁻¹) * (q : ℂ) ^ (i + 1)) := by
    intro i hi
    have hi' : i < d := mem_range.1 hi
    rw [AG_succ, ← shell_atom q ℓ hq hℓ d Pf hP (i + 1) (by omega) (by omega), ω]
    ring
  rw [sum_congr rfl this]
  simp only [mul_zero, zero_mul, sub_zero, zero_add]
  rw [AG, ω, sum_Icc_one_eq_sum_range, mul_sum]
  apply sum_congr rfl; intro i hi; ring

include hPd in
theorem shell_total : ∑ i ∈ range (d + 1), (Pf i - Pf (i + 1)) = Pf 0 := by
  have := tele Pf (fun _ => 1) d
  simp only [mul_one, sub_self, mul_zero, sum_const_zero, add_zero] at this
  rw [this, hPd (d + 1) (by omega)]; ring

include hq hℓ hP0 hP hPd in

theorem lamA_scale (ρ : ℕ) (m : Fin 2 →₀ ℕ) :
    lamA (q : ℂ) (ℓ * ρ) d (ℓ • m) =
      ∑ i ∈ range (d + 1), (Pf i - Pf (i + 1)) * lamA ((q : ℂ) ^ ℓ) ρ i m := by
  rw [eq_ev m, ev_smul, lamA_ev]
  simp_rw [lamA_ev]
  by_cases h : m 0 + m 1 = 2 * ρ
  · have h' : ℓ * m 0 + ℓ * m 1 = 2 * (ℓ * ρ) := by rw [← Nat.mul_add, h]; ring
    rw [if_pos h']
    simp only [h, if_true]
    by_cases hu : m 0 = ρ
    · rw [if_pos (by rw [hu]), mul_assoc, ← shell_AG q ℓ hq hℓ d Pf hP hPd, mul_sum]
      simp only [hu, if_true, pow_mul]
      apply sum_congr rfl; intro i hi; ring
    · have hu' : ℓ * m 0 ≠ ℓ * ρ := fun e => hu (Nat.eq_of_mul_eq_mul_left (by omega) e)
      rw [if_neg hu']
      simp only [hu, if_false]
      have e : ∀ i : ℕ, (Pf i - Pf (i + 1)) * ((((q : ℂ) ^ ℓ) ^ (ρ + i) - ((q : ℂ) ^ ℓ) ^ (min (m 0) (m 1))) / 2) =
          (((q : ℂ) ^ ℓ) ^ ρ * ((Pf i - Pf (i + 1)) * ((q : ℂ) ^ ℓ) ^ i) -
            ((q : ℂ) ^ ℓ) ^ (min (m 0) (m 1)) * (Pf i - Pf (i + 1))) / 2 := by
        intro i; ring
      simp_rw [e]
      rw [← sum_div, sum_sub_distrib, ← mul_sum, ← mul_sum, shell_mean q ℓ hq hℓ d Pf hP0 hP hPd,
        shell_total d Pf hPd, hP0, min_mul_left', ← pow_mul, ← pow_mul, pow_add]
      ring
  · have h' : ℓ * m 0 + ℓ * m 1 ≠ 2 * (ℓ * ρ) := by
      intro e; rw [← Nat.mul_add, show 2 * (ℓ * ρ) = ℓ * (2 * ρ) by ring] at e
      exact h (Nat.eq_of_mul_eq_mul_left (by omega) e)
    rw [if_neg h']
    simp only [h, if_false, mul_zero, sum_const_zero]

include hq hℓ hP0 hP hPd in
theorem ΛA_expand (ρ : ℕ) (F : MvPolynomial (Fin 2) ℂ) :
    Λ (lamA (q : ℂ) (ℓ * ρ) d) (expand ℓ F) =
      ∑ i ∈ range (d + 1), (Pf i - Pf (i + 1)) * Λ (lamA ((q : ℂ) ^ ℓ) ρ i) F := by
  rw [Λ_expand, show (fun m => lamA (q : ℂ) (ℓ * ρ) d (ℓ • m)) =
      fun m => ∑ i ∈ range (d + 1), (Pf i - Pf (i + 1)) * lamA ((q : ℂ) ^ ℓ) ρ i m from
    funext (lamA_scale q ℓ hq hℓ d Pf hP0 hP hPd ρ)]
  exact Λ_sum_weights _ _ _ F

end Shell

theorem ΛB_expand (q : ℂ) (ℓ ρa ρb : ℕ) (hℓ : 1 ≤ ℓ) (F : MvPolynomial (Fin 2) ℂ) :
    Λ (lamB q (ℓ * ρa) (ℓ * ρb)) (expand ℓ F) = Λ (lamB (q ^ ℓ) ρa ρb) F := by
  rw [Λ_expand]
  congr 2
  exact funext (lamB_scale q ℓ ρa ρb hℓ)

end BaseChange

section Assembly

theorem JBform_sum {ι : Type*} (S : Finset ι) (c : ι → ℂ) (g : ι → ℤ → ℕ → ℂ) (P : ℂ) (ra t : ℕ) :
    JBform P ra t (fun a s => ∑ e ∈ S, c e * g e a s) = ∑ e ∈ S, c e * JBform P ra t (g e) := by
  unfold JBform
  simp only [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl; intro e _
  apply sum_congr rfl; intro i _
  ring

theorem JAform_sum {ι : Type*} (S : Finset ι) (c : ι → ℂ) (g : ι → ℤ → ℕ → ℂ) (P : ℂ) (r d : ℕ) :
    JAform P r d (fun a s => ∑ e ∈ S, c e * g e a s) = ∑ e ∈ S, c e * JAform P r d (g e) := by
  unfold JAform
  simp only [mul_sum, sum_mul, mul_add, sum_add_distrib]
  congr 1
  · rw [sum_comm]
    apply sum_congr rfl; intro e _
    apply sum_congr rfl; intro i _
    ring
  · rw [sum_comm]
    apply sum_congr rfl; intro e _
    apply sum_congr rfl; intro i _
    ring

theorem reindex_shells (T : ℕ → ℕ → ℂ) (d ρ : ℕ) (hT0 : ∀ i n : ℕ, ρ < n → T i n = 0) :
    ∑ m ∈ Icc 1 (ρ + d), ∑ i ∈ range (min d (m - 1) + 1), T i (m - i) =
      ∑ i ∈ range (d + 1), ∑ n ∈ Icc 1 ρ, T i n := by
  rw [sum_sigma', sum_sigma']
  symm
  apply Finset.sum_bij_ne_zero (fun (x : Σ _ : ℕ, ℕ) _ _ => (⟨x.1 + x.2, x.1⟩ : Σ _ : ℕ, ℕ))
  · intro x hx hne
    obtain ⟨i, n⟩ := x
    simp only [Finset.mem_sigma, mem_range, mem_Icc] at hx ⊢
    refine ⟨by omega, Nat.lt_succ_iff.mpr (le_min_iff.mpr ⟨by omega, by omega⟩)⟩
  · intro x hx hnex y hy hney h
    obtain ⟨i, n⟩ := x
    obtain ⟨i', n'⟩ := y
    simp only [Sigma.mk.inj_iff, heq_eq_eq] at h ⊢
    omega
  · intro y hy hne
    obtain ⟨m, i⟩ := y
    simp only [Finset.mem_sigma, mem_range, mem_Icc] at hy
    obtain ⟨⟨h1m, hmle⟩, hi⟩ := hy
    have hmin := le_min_iff.mp (Nat.lt_succ_iff.mp hi)
    obtain ⟨n, rfl⟩ : ∃ n, m = i + n := ⟨m - i, by omega⟩
    simp only [Nat.add_sub_cancel_left] at hne ⊢
    have hn : n ≤ ρ := by
      by_contra hc; exact hne (hT0 i n (by omega))
    refine ⟨⟨i, n⟩, ?_, hne, rfl⟩
    simp only [Finset.mem_sigma, mem_range, mem_Icc]
    omega
  · intro x hx hne
    obtain ⟨i, n⟩ := x
    simp only [Nat.add_sub_cancel_left]

theorem mixture (c0 Q : ℂ) (Pf : ℕ → ℂ) (d ρ : ℕ) (hPd : ∀ i : ℕ, d < i → Pf i = 0) (φ : ℤ → ℕ → ℂ)
    (hφvan : ∀ n : ℕ, ρ < n → φ ((ρ : ℤ) - (n : ℤ)) (2 * n) = 0) :
    ∑ m ∈ Icc 1 (ρ + d), c0 * m * Q ^ m * (1 - Q⁻¹) *
        (φ ρ 0 * Pf m + ∑ i ∈ range (min d (m - 1) + 1),
          (Pf i - Pf (i + 1)) * φ ((ρ : ℤ) - ((m - i : ℕ) : ℤ)) (2 * (m - i))) =
      c0 * ∑ i ∈ range (d + 1), (Pf i - Pf (i + 1)) * JAform Q ρ i φ := by
  set T : ℕ → ℕ → ℂ := fun i n =>
    ((i + n : ℕ) : ℂ) * Q ^ (i + n) * (1 - Q⁻¹) * ((Pf i - Pf (i + 1)) * φ ((ρ : ℤ) - (n : ℤ)) (2 * n)) with hT
  have hT0 : ∀ i n : ℕ, ρ < n → T i n = 0 := by
    intro i n hn; simp only [hT, hφvan n hn]; ring

  have hsplit : ∀ m ∈ Icc 1 (ρ + d),
      c0 * m * Q ^ m * (1 - Q⁻¹) *
        (φ ρ 0 * Pf m + ∑ i ∈ range (min d (m - 1) + 1),
          (Pf i - Pf (i + 1)) * φ ((ρ : ℤ) - ((m - i : ℕ) : ℤ)) (2 * (m - i))) =
      c0 * (φ ρ 0 * ((m : ℂ) * Q ^ m * (1 - Q⁻¹) * Pf m)) +
        c0 * ∑ i ∈ range (min d (m - 1) + 1), T i (m - i) := by
    intro m hm
    rw [mul_add, mul_sum, mul_sum]
    congr 1
    · ring
    · apply sum_congr rfl
      intro i hi
      have him : i + (m - i) = m := by
        have := mem_range.1 hi; omega
      simp only [hT, him]
      ring
  rw [sum_congr rfl hsplit, sum_add_distrib]
  have hsplitR : ∀ i ∈ range (d + 1), (Pf i - Pf (i + 1)) * JAform Q ρ i φ =
      φ ρ 0 * ((Pf i - Pf (i + 1)) * ∑ s ∈ Icc 1 i, (s : ℂ) * Q ^ s * (1 - Q⁻¹)) +
        ∑ n ∈ Icc 1 ρ, T i n := by
    intro i hi
    rw [JAform, mul_add]
    congr 1
    · ring
    · rw [mul_sum]
      apply sum_congr rfl; intro n hn; simp only [hT]; ring
  have L1 : ∑ m ∈ Icc 1 (ρ + d), c0 * (φ ρ 0 * ((m : ℂ) * Q ^ m * (1 - Q⁻¹) * Pf m)) =
      c0 * (φ ρ 0 * ∑ i ∈ range d, (((i + 1 : ℕ) : ℂ) * Q ^ (i + 1) * (1 - Q⁻¹) * Pf (i + 1))) := by
    rw [← mul_sum, ← mul_sum, sum_Icc_one_eq_sum_range, show ρ + d = d + ρ by ring, sum_range_add]
    have e2 : ∀ x ∈ range ρ,
        ((d + x + 1 : ℕ) : ℂ) * Q ^ (d + x + 1) * (1 - Q⁻¹) * Pf (d + x + 1) = 0 := by
      intro x hx; rw [hPd (d + x + 1) (by omega)]; ring
    rw [sum_congr rfl e2, sum_const_zero, add_zero]
  have L2 : ∑ m ∈ Icc 1 (ρ + d), c0 * ∑ i ∈ range (min d (m - 1) + 1), T i (m - i) =
      c0 * ∑ i ∈ range (d + 1), ∑ n ∈ Icc 1 ρ, T i n := by
    rw [← mul_sum, reindex_shells T d ρ hT0]
  have R1 : ∑ i ∈ range (d + 1), (Pf i - Pf (i + 1)) * JAform Q ρ i φ =
      φ ρ 0 * ∑ i ∈ range d, (((i + 1 : ℕ) : ℂ) * Q ^ (i + 1) * (1 - Q⁻¹) * Pf (i + 1)) +
        ∑ i ∈ range (d + 1), ∑ n ∈ Icc 1 ρ, T i n := by
    rw [sum_congr rfl hsplitR, sum_add_distrib, ← mul_sum]
    congr 1
    congr 1
    rw [tele, hPd (d + 1) (by omega)]
    rw [Finset.Icc_eq_empty_of_lt (show (0 : ℕ) < 1 by norm_num), sum_empty, mul_zero, zero_mul, sub_zero,
      zero_add]
    apply sum_congr rfl
    intro i hi
    rw [sum_Icc_succ_top (by omega)]
    ring
  rw [L1, L2, R1]
  ring

end Assembly

end

end WInert
p2m_reactivate "P2MW.S_AutomorphicForm_SatakeCombination_sum_twistedShell_heckeWord_eq_mul_sum_shell_baseChange_of_two_mul_eq.WInert"

open AutomorphicForm.SatakeCombination (univWord)
open WInert

theorem solution
    (q ℓ : ℕ) (hq : 1 ≤ q) (hℓ : 1 ≤ ℓ)
    (Wq WQ : ℕ → ℕ → ℕ)
    (hq00 : Wq 0 0 = 1) (hq0s : ∀ s : ℕ, Wq 0 (s + 1) = 0)
    (hqroot : ∀ n : ℕ, Wq (n + 1) 0 = (q + 1) * Wq n 1)
    (hqstep : ∀ n s : ℕ, Wq (n + 1) (s + 1) = Wq n s + q * Wq n (s + 2))
    (hQ00 : WQ 0 0 = 1) (hQ0s : ∀ s : ℕ, WQ 0 (s + 1) = 0)
    (hQroot : ∀ n : ℕ, WQ (n + 1) 0 = (q ^ ℓ + 1) * WQ n 1)
    (hQstep : ∀ n s : ℕ, WQ (n + 1) (s + 1) = WQ n s + q ^ ℓ * WQ n (s + 2))
    (k j : ℕ)
    (φ : ℤ → ℕ → ℂ)
    (hφ : ∀ (a : ℤ) (s : ℕ), φ a s = if 2 * a + s = (k : ℤ) + 2 * j then (WQ k s : ℂ) else 0)
    (f : ℤ → ℕ → ℂ)
    (hf : ∀ (a : ℤ) (s : ℕ), f a s =
      ∑ e ∈ (univWord (ℓ - 1) k j).support,
        (univWord (ℓ - 1) k j).coeff e * (q : ℂ) ^ (e 1) / (q : ℂ) ^ (ℓ * j) *
          (if 2 * a + s = (e 0 : ℤ) + 2 * (e 1 : ℤ) then (Wq (e 0) s : ℂ) else 0))
    (d : ℕ) (P : ℕ → ℂ) (hP0 : P 0 = 1)
    (hP : ∀ i : ℕ, 1 ≤ i → i ≤ d →
      P i = ((q : ℂ) ^ ((ℓ - 1) * (i - 1)) * ∑ t ∈ Finset.range ℓ, (q : ℂ) ^ t)⁻¹)
    (hPd : ∀ i : ℕ, d < i → P i = 0)
    (ρ : ℕ) (hρ : k + 2 * j = 2 * ρ) :
    ∑ m ∈ Finset.Icc 1 (ρ + d),
        (ℓ : ℂ) * m * ((q : ℂ) ^ ℓ) ^ m * (1 - ((q : ℂ) ^ ℓ)⁻¹) *
          (φ ρ 0 * P m +
            ∑ i ∈ Finset.range (min d (m - 1) + 1),
              (P i - P (i + 1)) * φ ((ρ : ℤ) - ((m - i : ℕ) : ℤ)) (2 * (m - i))) =
      (ℓ : ℂ) *
        (f ((ℓ * ρ : ℕ) : ℤ) 0 * ∑ s ∈ Finset.Icc 1 d, (s : ℂ) * (q : ℂ) ^ s * (1 - (q : ℂ)⁻¹) +
          ∑ i ∈ Finset.Icc 1 (ℓ * ρ),
            ((d + i : ℕ) : ℂ) * (q : ℂ) ^ (d + i) * (1 - (q : ℂ)⁻¹) * f (((ℓ * ρ : ℕ) : ℤ) - i) (2 * i)) := by
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  have hQ0 : (q : ℂ) ^ ℓ ≠ 0 := pow_ne_zero _ hq0
  have hQnat : ((q ^ ℓ : ℕ) : ℂ) = (q : ℂ) ^ ℓ := Nat.cast_pow q ℓ
  have hφvan : ∀ n : ℕ, ρ < n → φ ((ρ : ℤ) - (n : ℤ)) (2 * n) = 0 := by
    intro n hn
    rw [hφ]
    split_ifs with h
    · rw [W_eq_zero_of_lt (q ^ ℓ) WQ hQ0s hQstep k (2 * n) (by omega)]; simp
    · rfl
  rw [mixture (ℓ : ℂ) ((q : ℂ) ^ ℓ) P d ρ hPd φ hφvan]
  change _ = (ℓ : ℂ) * JAform (q : ℂ) (ℓ * ρ) d f
  congr 1
  have hL : ∀ i ∈ Finset.range (d + 1), (P i - P (i + 1)) * JAform ((q : ℂ) ^ ℓ) ρ i φ =
      (((q : ℂ) ^ ℓ)⁻¹) ^ j * ((P i - P (i + 1)) * Λ (lamA ((q : ℂ) ^ ℓ) ρ i) ((PX + PY) ^ k * (PX * PY) ^ j)) := by
    intro i hi
    rw [perWordA (q ^ ℓ) ((q : ℂ) ^ ℓ) hQnat hQ0 WQ hQ00 hQ0s hQroot hQstep k j φ hφ ρ i, zS_pow,
      show (PX + PY) ^ k * (MvPolynomial.C ((((q : ℂ) ^ ℓ)⁻¹) ^ j) * (PX * PY) ^ j) =
        MvPolynomial.C ((((q : ℂ) ^ ℓ)⁻¹) ^ j) * ((PX + PY) ^ k * (PX * PY) ^ j) by ring, Λ_C_mul]
    ring
  rw [Finset.sum_congr rfl hL, ← Finset.mul_sum, ← ΛA_expand q ℓ hq hℓ d P hP0 hP hPd ρ]
  rw [show f = (fun (a : ℤ) (s : ℕ) => ∑ e ∈ (univWord (ℓ - 1) k j).support,
        (univWord (ℓ - 1) k j).coeff e * (q : ℂ) ^ (e 1) / (q : ℂ) ^ (ℓ * j) *
          (if 2 * a + s = (e 0 : ℤ) + 2 * (e 1 : ℤ) then (Wq (e 0) s : ℂ) else 0)) from
      funext fun a => funext fun s => hf a s,
    JAform_sum]
  have hcells : ∀ e ∈ (univWord (ℓ - 1) k j).support,
      (univWord (ℓ - 1) k j).coeff e * (q : ℂ) ^ (e 1) / (q : ℂ) ^ (ℓ * j) *
        JAform (q : ℂ) (ℓ * ρ) d
          (fun (a : ℤ) (s : ℕ) => if 2 * a + s = (e 0 : ℤ) + 2 * (e 1 : ℤ) then (Wq (e 0) s : ℂ) else 0) =
      Λ (lamA (q : ℂ) (ℓ * ρ) d)
        (MvPolynomial.C ((univWord (ℓ - 1) k j).coeff e * (q : ℂ) ^ (e 1) / (q : ℂ) ^ (ℓ * j)) *
          ((PX + PY) ^ (e 0) * zS (q : ℂ) ^ (e 1))) := by
    intro e he
    rw [perWordA q (q : ℂ) rfl hq0 Wq hq00 hq0s hqroot hqstep (e 0) (e 1) _ (fun a s => rfl) (ℓ * ρ) d, Λ_C_mul]
  rw [Finset.sum_congr rfl hcells, ← map_sum, satake_baseChange q ℓ k j hq0 hℓ, Λ_C_mul, pow_mul, inv_pow]

end S_AutomorphicForm_SatakeCombination_sum_twistedShell_heckeWord_eq_mul_sum_shell_baseChange_of_two_mul_eq
end P2MW
export P2MW.S_AutomorphicForm_SatakeCombination_sum_twistedShell_heckeWord_eq_mul_sum_shell_baseChange_of_two_mul_eq (solution)
