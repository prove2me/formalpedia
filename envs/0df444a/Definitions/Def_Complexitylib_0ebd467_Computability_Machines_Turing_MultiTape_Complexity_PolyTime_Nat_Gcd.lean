-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Nat_Gcd
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Nat_Gcd
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:59:01.504388+00:00
-- url     : https://prove2.me/theorems/f514d5fc-6b01-415f-a526-bf229ed7bdf4
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Gcd — Polynomial-time greatest common divisor on binary naturals
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Gcd` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   Euclid's algorithm on the binary encoding `Turing.MultiTapeTM.encNat`. Each step
--   `Turing.MultiTapeTM.BinaryGcd.gcdStep` replaces `(a, b)` by `(b, a % b)` when `b ≠ 0` and fixes
--   `(a, 0)`. After the first step the state satisfies `b ≤ a`, and every subsequent step with `0 < b`
--   at least halves the product `a * b` (`BinaryGcd.gcd_product_halving`). Because
--   `a * b < 2 ^ (a.size + b.size)`, iterating `gcdStep` for
--   `BinaryGcd.gcdCount (a, b) = a.bits.length + b.bits.length + 1` steps reaches `(Nat.gcd a b, 0)`
--   (`BinaryGcd.iterate_gcdStep_eq`). At every intermediate step both components are at most
--   `max a b`, so the encoded pair length never exceeds a linear bound in the input length.
--
--   ### Main definitions
--
--   * `Turing.MultiTapeTM.BinaryGcd.gcdStep`: one Euclidean remainder step on `ℕ × ℕ`.
--   * `Turing.MultiTapeTM.BinaryGcd.gcdCount`: the fuel `a.bits.length + b.bits.length + 1` sufficient
--     to reach a zero remainder.
--
--   ### Main results
--
--   * `Turing.MultiTapeTM.BinaryGcd.gcd_product_halving`: when `0 < a ≤ b`, `2 * (a * (b % a)) ≤ a * b`.
--   * `Turing.MultiTapeTM.BinaryGcd.iterate_gcdStep_eq`: iterating `gcdStep` for `gcdCount p` steps
--     produces `(Nat.gcd p.1 p.2, 0)`.
--   * `Turing.MultiTapeTM.ComputableInPolyTime.binary_gcd`, `.binary_gcd'`: polynomial-time
--     certificates for `Nat.gcd` on `encNat`.
--
--   ### References
--
--   * `gcd_product_halving` is adapted from OpenAI's formalization [OpenAI2026RationalHitting] at
--     revision adc7f1241b42e322a6451854ab7e4b4c146bf78a (file
--     lean/OAI/Computability/RationalHitting/BinaryFactorial.lean), via the complexitylib port
--     [Schlesinger2026RationalHitting] at revision add0aca8ee0d71e68969f2cb45cf91554a50f787.
--
--   **Contents.** The module is published as a whole: 16 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with library lemmas renamed back to their names in this Mathlib and a few proof steps adjusted; no statement is changed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Nat_Gcd`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Complexity/PolyTime/Nat/Gcd.lean

/-
Copyright (c) 2026 OpenAI, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Samuel Schlesinger, Karn Seth
-/

module
-- upstream: candidate

public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Nat_BinaryDiv
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_PolyTime
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Iteration
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Nat
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Plain

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Gcd` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Polynomial-time greatest common divisor on binary naturals

Euclid's algorithm on the binary encoding `Turing.MultiTapeTM.encNat`. Each step
`Turing.MultiTapeTM.BinaryGcd.gcdStep` replaces `(a, b)` by `(b, a % b)` when `b ≠ 0` and fixes
`(a, 0)`. After the first step the state satisfies `b ≤ a`, and every subsequent step with `0 < b`
at least halves the product `a * b` (`BinaryGcd.gcd_product_halving`). Because
`a * b < 2 ^ (a.size + b.size)`, iterating `gcdStep` for
`BinaryGcd.gcdCount (a, b) = a.bits.length + b.bits.length + 1` steps reaches `(Nat.gcd a b, 0)`
(`BinaryGcd.iterate_gcdStep_eq`). At every intermediate step both components are at most
`max a b`, so the encoded pair length never exceeds a linear bound in the input length.

## Main definitions

* `Turing.MultiTapeTM.BinaryGcd.gcdStep`: one Euclidean remainder step on `ℕ × ℕ`.
* `Turing.MultiTapeTM.BinaryGcd.gcdCount`: the fuel `a.bits.length + b.bits.length + 1` sufficient
  to reach a zero remainder.

## Main results

* `Turing.MultiTapeTM.BinaryGcd.gcd_product_halving`: when `0 < a ≤ b`, `2 * (a * (b % a)) ≤ a * b`.
* `Turing.MultiTapeTM.BinaryGcd.iterate_gcdStep_eq`: iterating `gcdStep` for `gcdCount p` steps
  produces `(Nat.gcd p.1 p.2, 0)`.
* `Turing.MultiTapeTM.ComputableInPolyTime.binary_gcd`, `.binary_gcd'`: polynomial-time
  certificates for `Nat.gcd` on `encNat`.

## References

* `gcd_product_halving` is adapted from OpenAI's formalization [OpenAI2026RationalHitting] at
  revision adc7f1241b42e322a6451854ab7e4b4c146bf78a (file
  lean/OAI/Computability/RationalHitting/BinaryFactorial.lean), via the complexitylib port
  [Schlesinger2026RationalHitting] at revision add0aca8ee0d71e68969f2cb45cf91554a50f787.
-/

@[expose] public section

namespace Turing.MultiTapeTM.BinaryGcd

/-- Euclid's product is halved at every ordered step. -/
theorem gcd_product_halving {a b : ℕ} (ha : 0 < a) (hab : a ≤ b) :
    2 * (a * (b % a)) ≤ a * b := by
  have hr := Nat.mod_lt b ha
  have hq : 1 ≤ b / a := (Nat.one_le_div_iff ha).mpr hab
  have hid := Nat.mod_add_div b a
  have hmul := Nat.mul_le_mul_left a hq
  have hhalf : 2 * (b % a) ≤ b := by lia
  nlinarith

/-- One step of Euclid's algorithm: replace `(a, b)` by `(b, a % b)` while `b ≠ 0`. -/
def gcdStep (state : ℕ × ℕ) : ℕ × ℕ :=
  if state.2 = 0 then state else (state.2, state.1 % state.2)

/-- Number of Euclidean steps sufficient to reduce `(p.1, p.2)` to `(Nat.gcd p.1 p.2, 0)`. -/
def gcdCount (p : ℕ × ℕ) : ℕ :=
  p.1.bits.length + p.2.bits.length + 1

lemma gcd_gcdStep (s : ℕ × ℕ) : Nat.gcd (gcdStep s).1 (gcdStep s).2 = Nat.gcd s.1 s.2 := by
  unfold gcdStep
  split_ifs with h
  · rfl
  · calc Nat.gcd s.2 (s.1 % s.2)
        = Nat.gcd (s.1 % s.2) s.2 := Nat.gcd_comm _ _
      _ = Nat.gcd s.2 s.1 := (Nat.gcd_rec s.2 s.1).symm
      _ = Nat.gcd s.1 s.2 := Nat.gcd_comm _ _

lemma gcd_iterate_gcdStep (s : ℕ × ℕ) (i : ℕ) :
    Nat.gcd (gcdStep^[i] s).1 (gcdStep^[i] s).2 = Nat.gcd s.1 s.2 := by
  induction i generalizing s with
  | zero => rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply, ih, gcd_gcdStep]

lemma max_gcdStep_le (s : ℕ × ℕ) : max (gcdStep s).1 (gcdStep s).2 ≤ max s.1 s.2 := by
  unfold gcdStep
  split_ifs with h
  · exact le_rfl
  · exact max_le (le_max_right s.1 s.2) ((Nat.mod_le s.1 s.2).trans (le_max_left s.1 s.2))

lemma max_iterate_gcdStep_le (s : ℕ × ℕ) (i : ℕ) :
    max (gcdStep^[i] s).1 (gcdStep^[i] s).2 ≤ max s.1 s.2 := by
  induction i generalizing s with
  | zero => exact le_rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply]
    exact (ih (gcdStep s)).trans (max_gcdStep_le s)

lemma snd_gcdStep_le_fst (s : ℕ × ℕ) : (gcdStep s).2 ≤ (gcdStep s).1 := by
  unfold gcdStep
  split_ifs with h
  · lia
  · exact (Nat.mod_lt s.1 (Nat.pos_of_ne_zero h)).le

lemma mul_gcdStep_le (s : ℕ × ℕ) : (gcdStep s).1 * (gcdStep s).2 ≤ s.1 * s.2 := by
  unfold gcdStep
  split_ifs with h
  · exact le_rfl
  · rw [Nat.mul_comm s.1 s.2]
    exact Nat.mul_le_mul_left s.2 (Nat.mod_le s.1 s.2)

lemma mul_gcdStep_two_le (s : ℕ × ℕ) (hs : s.2 ≤ s.1) :
    2 * ((gcdStep s).1 * (gcdStep s).2) ≤ s.1 * s.2 := by
  unfold gcdStep
  split_ifs with h
  · rw [h]
    simp
  · calc 2 * (s.2 * (s.1 % s.2))
        ≤ s.2 * s.1 := gcd_product_halving (Nat.pos_of_ne_zero h) hs
      _ = s.1 * s.2 := Nat.mul_comm s.2 s.1

lemma iterate_gcdStep_product_le (s : ℕ × ℕ) (hs : s.2 ≤ s.1) (k : ℕ) :
    (gcdStep^[k] s).2 ≤ (gcdStep^[k] s).1 ∧
      2 ^ k * ((gcdStep^[k] s).1 * (gcdStep^[k] s).2) ≤ s.1 * s.2 := by
  induction k generalizing s with
  | zero => simp [hs]
  | succ k ih =>
    rw [Function.iterate_succ_apply]
    obtain ⟨hord, hprod⟩ := ih (gcdStep s) (snd_gcdStep_le_fst s)
    refine ⟨hord, ?_⟩
    calc 2 ^ (k + 1) * ((gcdStep^[k] (gcdStep s)).1 * (gcdStep^[k] (gcdStep s)).2)
        = 2 * (2 ^ k * ((gcdStep^[k] (gcdStep s)).1 * (gcdStep^[k] (gcdStep s)).2)) := by ring
      _ ≤ 2 * ((gcdStep s).1 * (gcdStep s).2) := Nat.mul_le_mul_left 2 hprod
      _ ≤ s.1 * s.2 := mul_gcdStep_two_le s hs

lemma snd_iterate_gcdStep_gcdCount (p : ℕ × ℕ) :
    (gcdStep^[gcdCount p] p).2 = 0 := by
  unfold gcdCount
  rw [Function.iterate_add_apply, Function.iterate_one]
  set k := p.1.bits.length + p.2.bits.length
  obtain ⟨hord, hprod⟩ := iterate_gcdStep_product_le (gcdStep p) (snd_gcdStep_le_fst p) k
  have hmul : (gcdStep p).1 * (gcdStep p).2 < 2 ^ k := by
    refine (mul_gcdStep_le p).trans_lt ?_
    have h₁ : p.1 < 2 ^ p.1.bits.length :=
      Nat.size_eq_bits_len p.1 ▸ Nat.lt_size_self p.1
    have h₂ : p.2 < 2 ^ p.2.bits.length :=
      Nat.size_eq_bits_len p.2 ▸ Nat.lt_size_self p.2
    rw [show k = p.1.bits.length + p.2.bits.length from rfl, Nat.pow_add]
    exact Nat.mul_lt_mul'' h₁ h₂
  by_contra hne
  have hpos : 1 ≤ (gcdStep^[k] (gcdStep p)).1 * (gcdStep^[k] (gcdStep p)).2 := by
    have : 1 ≤ (gcdStep^[k] (gcdStep p)).2 := Nat.pos_of_ne_zero hne
    nlinarith
  have hge : 2 ^ k ≤ 2 ^ k * ((gcdStep^[k] (gcdStep p)).1 * (gcdStep^[k] (gcdStep p)).2) :=
    Nat.le_mul_of_pos_right (2 ^ k) hpos
  lia

/-- Iterating `gcdStep` for `gcdCount p` steps reaches `(Nat.gcd p.1 p.2, 0)`. -/
theorem iterate_gcdStep_eq (p : ℕ × ℕ) :
    gcdStep^[gcdCount p] p = (Nat.gcd p.1 p.2, 0) := by
  have hsnd := snd_iterate_gcdStep_gcdCount p
  have hgcd := gcd_iterate_gcdStep p (gcdCount p)
  rw [hsnd, Nat.gcd_zero_right] at hgcd
  exact Prod.ext hgcd hsnd

/-- At every Euclidean step, the encoded pair has length at most
`3 * (encPair encNat encNat p).length`. -/
theorem length_encPair_iterate_gcdStep_le (p : ℕ × ℕ) (i : ℕ) :
    (encPair encNat encNat (gcdStep^[i] p)).length ≤ 3 * (encPair encNat encNat p).length := by
  have hmax := max_iterate_gcdStep_le p i
  have h₁ : (gcdStep^[i] p).1 ≤ max p.1 p.2 := (le_max_left _ _).trans hmax
  have h₂ : (gcdStep^[i] p).2 ≤ max p.1 p.2 := (le_max_right _ _).trans hmax
  have hm : (max p.1 p.2).size ≤ p.1.size + p.2.size := by
    rcases le_total p.1 p.2 with h | h
    · rw [max_eq_right h]; lia
    · rw [max_eq_left h]; lia
  have hs₁ : ((gcdStep^[i] p).1).size ≤ p.1.size + p.2.size := (Nat.size_le_size h₁).trans hm
  have hs₂ : ((gcdStep^[i] p).2).size ≤ p.1.size + p.2.size := (Nat.size_le_size h₂).trans hm
  simp only [length_encPair, encNat_apply, Nat.size_eq_bits_len] at hs₁ hs₂ ⊢
  lia

end Turing.MultiTapeTM.BinaryGcd

namespace Turing.MultiTapeTM.ComputableInPolyTime

/-- Greatest common divisor of binary naturals via Euclid's algorithm. -/
@[fun_prop]
theorem binary_gcd : ComputableInPolyTime (fun p : ℕ × ℕ => Nat.gcd p.1 p.2)
    (encPair encNat encNat) encNat := by
  have hcount : ComputableInPolyTime BinaryGcd.gcdCount
      (encPair encNat encNat) encUnary := by
    unfold BinaryGcd.gcdCount
    fun_prop
  have hinit : ComputableInPolyTime (fun p => p)
      (encPair encNat encNat) (encPair encNat encNat) := by
    fun_prop
  have hstep : ComputableInPolyTime BinaryGcd.gcdStep
      (encPair encNat encNat) (encPair encNat encNat) := by
    unfold BinaryGcd.gcdStep
    fun_prop
  have hiter := iterate hcount hinit hstep
    (bound := fun p => 3 * (encPair encNat encNat p).length)
    ((PolyBounded.const 3).mul .self)
    (fun p i _ => BinaryGcd.length_encPair_iterate_gcdStep_le p i)
  have hfst := hiter.fst'
  simpa only [BinaryGcd.iterate_gcdStep_eq] using hfst

/-- Greatest common divisor of computed binary values, fixing their intermediate encodings for
proof search. -/
@[fun_prop]
theorem binary_gcd' {α : Type} {input : α ↪ List Bool} {left right : α → ℕ}
    (hleft : ComputableInPolyTime left input encNat)
    (hright : ComputableInPolyTime right input encNat) :
    ComputableInPolyTime (fun a => Nat.gcd (left a) (right a)) input encNat :=
  binary_gcd.comp (hleft.prod hright)

end Turing.MultiTapeTM.ComputableInPolyTime


