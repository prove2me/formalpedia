-- Prove2me | Definitions.Def_DetDLP_W1_Euclid
-- name    : DetDLP_W1_Euclid
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-23T21:25:20.081577+00:00
-- url     : https://prove2.me/theorems/62f6d7a5-74d2-4c8f-a497-d98ca3131192
-- title:
--   Binary Euclidean Bezout transducer
-- statement:
--   A finite Euclidean transducer computes the gcd of two natural numbers and a coefficient whose product with the first input is congruent to that gcd modulo the second input. Its answer function returns the corresponding reduced residue precisely when the gcd divides the second exponent.

import Definitions.Def_DetDLP_Machine

set_option autoImplicit false
namespace DetDLP_W1_Euclid

abbrev State := ℕ × ℕ × ℕ × ℕ

def init (n u : ℕ) : State := (n,u,0,1)

def step (n : ℕ) (s : State) : State :=
  if s.2.1 = 0 then s else
    let q := s.1 / s.2.1
    (s.2.1, s.1 % s.2.1, s.2.2.2, (s.2.2.1 + n - (q * s.2.2.2) % n) % n)

def run (n u : ℕ) : State :=
  n.bits.foldl (fun s _ => step n (step n s)) (init n u)

def Inv (n u : ℕ) (s : State) : Prop :=
  Nat.gcd s.1 s.2.1 = Nat.gcd u n ∧
    (s.1 : ZMod n) = u * (s.2.2.1 : ZMod n) ∧
    (s.2.1 : ZMod n) = u * (s.2.2.2 : ZMod n)

theorem inv_init (n u : ℕ) : Inv n u (init n u) := by
  simp [Inv,init,Nat.gcd_comm]

theorem inv_step {n u : ℕ} (hn : 0 < n) (s : State) (hs : Inv n u s) : Inv n u (step n s) := by
  rcases s with ⟨a,b,c,e⟩
  by_cases hb : b = 0
  · simpa [step,hb] using hs
  rcases hs with ⟨hG,ha,he⟩
  change Nat.gcd a b = Nat.gcd u n at hG
  change (a : ZMod n) = u * c at ha
  change (b : ZMod n) = u * e at he
  have hle : (a / b * e) % n ≤ c + n := by have := Nat.mod_lt (a/b*e) hn; omega
  have hrel : (↑(a%b) : ZMod n) + (b : ZMod n) * ↑(a/b) = ↑a := by
    exact_mod_cast congrArg (fun h : ℕ => (h : ZMod n)) (Nat.mod_add_div a b)
  simp only [step,hb,if_false,Inv]
  refine ⟨?_,he,?_⟩
  · calc
      Nat.gcd b (a % b) = Nat.gcd (a % b) b := Nat.gcd_comm _ _
      _ = Nat.gcd b a := (Nat.gcd_rec b a).symm
      _ = Nat.gcd a b := Nat.gcd_comm _ _
      _ = Nat.gcd u n := hG
  · rw [ZMod.natCast_mod, Nat.cast_sub hle, Nat.cast_add, ZMod.natCast_self, add_zero,
      ZMod.natCast_mod, Nat.cast_mul]
    linear_combination hrel + ha - (↑(a/b) : ZMod n) * he

theorem inv_fold {n u : ℕ} (hn : 0 < n) (l : List Bool) (s : State) (hs : Inv n u s) :
    Inv n u (l.foldl (fun s _ => step n (step n s)) s) := by
  induction l generalizing s with
  | nil => exact hs
  | cons b l ih => exact ih _ (inv_step hn _ (inv_step hn _ hs))

theorem mod_half (a b : ℕ) (ha : 0 < a) : 2 * (b % a) < b ∨ b < a := by
  by_cases h : b < a
  · exact Or.inr h
  · left
    have hq : 1 ≤ b/a := (Nat.le_div_iff_mul_le ha).2 (by omega)
    have hh := Nat.mul_le_mul_left a hq
    have hm := Nat.mod_lt b ha
    have hh' := Nat.mod_add_div b a
    omega

theorem shrink (n : ℕ) (s : State) (h : s.2.1 ≠ 0) :
    2 * (step n (step n s)).2.1 < s.2.1 := by
  rcases s with ⟨a,b,c,e⟩
  change b ≠ 0 at h
  have hb : 0 < b := Nat.pos_of_ne_zero h
  cases hr : a % b with
  | zero => simp [step,h,hr,hb]
  | succ k =>
    have hk := Nat.mod_lt a hb
    have hh := mod_half (k+1) b (by omega)
    have hlt : 2 * (b % (k+1)) < b := by omega
    simpa [step,h,hr] using hlt

theorem finish (n : ℕ) (l : List Bool) (s : State) (hb : s.2.1 < 2^l.length) :
    (l.foldl (fun s _ => step n (step n s)) s).2.1 = 0 := by
  induction l generalizing s with
  | nil => simpa [Nat.lt_one_iff] using hb
  | cons bit l ih =>
    apply ih
    change (step n (step n s)).2.1 < 2^l.length
    by_cases hz : s.2.1 = 0
    · simp [step,hz]
    · have hlt := shrink n s hz
      simp only [List.length_cons,pow_succ] at hb
      omega

theorem result {n u : ℕ} (hn : 0 < n) (hu : u ≤ n) :
    (run n u).1 = Nat.gcd u n ∧
    (u : ℤ) * ((run n u).2.2.1 : ℤ) ≡ Nat.gcd u n [ZMOD (n : ℤ)] := by
  have hs := inv_fold hn n.bits (init n u) (inv_init n u)
  have hf : (run n u).2.1 = 0 := finish n n.bits (init n u) (by
    rw [Nat.size_eq_bits_len]; exact hu.trans_lt (Nat.lt_size_self n))
  change Inv n u (run n u) at hs
  rcases hs with ⟨hg,hc,_⟩
  rw [hf, Nat.gcd_zero_right] at hg
  refine ⟨hg, (ZMod.intCast_eq_intCast_iff _ _ _).1 ?_⟩
  simpa [← hg] using hc.symm

def answer (n u v : ℕ) : Option ℕ :=
  let s := run n u
  if v % s.1 = 0 then some ((s.2.2.1 * (v / s.1)) % (n / s.1)) else none

theorem answer_spec {n u v : ℕ} (hn : 0 < n) (hu : u ≤ n) :
    answer n u v = (if Nat.gcd u n ∣ v then
      some (((Nat.gcdA u n * ((v / Nat.gcd u n : ℕ) : ℤ)) % ((n / Nat.gcd u n : ℕ) : ℤ)).toNat)
      else none) := by
  obtain ⟨hg,hc⟩ := result hn hu
  unfold answer
  dsimp only
  simp only [hg, ← Nat.dvd_iff_mod_eq_zero]
  split_ifs with hd
  · congr 1
    have h := (hc.trans (Int.gcd_a_modEq u n).symm).cancel_left_div_gcd (by exact_mod_cast hn)
    rw [Int.gcd_natCast_natCast, Nat.gcd_comm n u, ← Int.natCast_ediv] at h
    have he := h.mul_right (↑(v / u.gcd n) : ℤ)
    have hval := congrArg Int.toNat (show _ % _ = _ % _ from he)
    simpa only [← Int.natCast_mul, ← Int.natCast_mod, Int.toNat_natCast] using hval
  · rfl

end DetDLP_W1_Euclid


