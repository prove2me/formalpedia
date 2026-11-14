-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_PolyTime_Int_ExactDiv
-- name    : Complexitylib_0ebd467_Computability_PolyTime_Int_ExactDiv
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T17:01:03.941771+00:00
-- url     : https://prove2.me/theorems/beb71209-4bca-4fe6-9ea9-727e5f255e3f
-- title:
--   Complexity.Computability.PolyTime.Int.ExactDiv — Plain polynomial-time signed integer division and modular reduction
-- statement:
--   This is module `Complexity.Computability.PolyTime.Int.ExactDiv` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   Plain `Turing.MultiTapeTM.ComputableInPolyTime` certificates, exact-division identities, and
--   sign-magnitude code-length bounds for signed binary integer division and remainder over
--   `Turing.MultiTapeTM.encIntBin`:
--
--   * truncated-toward-zero division and remainder (`Int.tdiv`, `Int.tmod`);
--   * Euclidean division and nonnegative remainder (`Int.ediv`, `Int.emod`, and the `/` and `%`
--     operators on `ℤ`);
--   * power-of-two modular reduction `Int.modPowTwo x ℓ = x % 2 ^ ℓ` with `ℓ` in unary
--     `Turing.MultiTapeTM.encUnary`, used to recover integer counts modulo `2 ^ ℓ` in Appendix B.3
--     of [OpenAI2026ETH].
--
--   All certificates are total (at divisor `0`, `a / 0 = 0`, `a.tdiv 0 = 0`, `a % 0 = a`, and
--   `a.tmod 0 = a`) and build on the binary natural division and modular reduction primitives of
--   `PolyTime/Nat/BinaryDiv` and `PolyTime/Int/BinaryDiv` without constructing new Turing machines.
--
--   ### Main definitions
--
--   * `Int.modPowTwo`: least nonnegative residue `x % (2 : ℤ) ^ ℓ` modulo `2 ^ ℓ`.
--
--   ### Main results
--
--   * `Int.ediv_mul_left_exact`, `Int.ediv_mul_right_exact`: exact Euclidean division of integer
--     multiples `(d * q).ediv d = q` and `(q * d).ediv d = q` for `d ≠ 0`.
--   * `Int.modPowTwo_eq_of_dvd_sub`: unique recovery of `z ∈ [0, 2 ^ ℓ)` from any `x` with
--     `2 ^ ℓ ∣ x - z`.
--   * `Int.size_natAbs_tdiv_le`, `Int.size_natAbs_ediv_le`, `Int.size_natAbs_emod_le_of_ne_zero`,
--     `Int.size_natAbs_modPowTwo_le`, `Turing.MultiTapeTM.length_encIntBin_tdiv_le`,
--     `Turing.MultiTapeTM.length_encIntBin_ediv_le`,
--     `Turing.MultiTapeTM.length_encIntBin_emod_le_of_ne_zero`,
--     `Turing.MultiTapeTM.length_encIntBin_emod_le_max`,
--     `Turing.MultiTapeTM.length_encIntBin_modPowTwo_le`: binary magnitude and `encIntBin` code-length
--     bounds.
--   * `Turing.MultiTapeTM.ComputableInPolyTime.intBin_tdiv`, `.intBin_tmod`, `.intBin_ediv`,
--     `.intBin_emod`, `.intBin_div`, `.intBin_mod`, `.intBin_modPowTwo`: plain polynomial-time
--     certificates and `@[fun_prop]` composition rules (`.intBin_tdiv'`, `.intBin_tmod'`,
--     `.intBin_ediv'`, `.intBin_emod'`, `.intBin_div'`, `.intBin_mod'`, `.intBin_modPowTwo'`).
--
--   ### References
--
--   * [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH]
--   * [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
--
--   **Contents.** The module is published as a whole: 39 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_PolyTime_Int_ExactDiv`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/PolyTime/Int/ExactDiv.lean

/-
Copyright (c) 2026 Anton Kovsharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anton Kovsharov
-/

module
-- upstream: candidate

public import Batteries.Tactic.Lint.Basic
public import Mathlib.Init
public import Mathlib.Tactic.Common
public import Definitions.Def_Cslib_254e30e_Tactic_GrindAttrs
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Int_BinaryDiv
public import Mathlib.Data.Nat.Size
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Plain

/- Prove2me definition bundle for `Complexity.Computability.PolyTime.Int.ExactDiv` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Plain polynomial-time signed integer division and modular reduction

Plain `Turing.MultiTapeTM.ComputableInPolyTime` certificates, exact-division identities, and
sign-magnitude code-length bounds for signed binary integer division and remainder over
`Turing.MultiTapeTM.encIntBin`:

* truncated-toward-zero division and remainder (`Int.tdiv`, `Int.tmod`);
* Euclidean division and nonnegative remainder (`Int.ediv`, `Int.emod`, and the `/` and `%`
  operators on `ℤ`);
* power-of-two modular reduction `Int.modPowTwo x ℓ = x % 2 ^ ℓ` with `ℓ` in unary
  `Turing.MultiTapeTM.encUnary`, used to recover integer counts modulo `2 ^ ℓ` in Appendix B.3
  of [OpenAI2026ETH].

All certificates are total (at divisor `0`, `a / 0 = 0`, `a.tdiv 0 = 0`, `a % 0 = a`, and
`a.tmod 0 = a`) and build on the binary natural division and modular reduction primitives of
`PolyTime/Nat/BinaryDiv` and `PolyTime/Int/BinaryDiv` without constructing new Turing machines.

## Main definitions

* `Int.modPowTwo`: least nonnegative residue `x % (2 : ℤ) ^ ℓ` modulo `2 ^ ℓ`.

## Main results

* `Int.ediv_mul_left_exact`, `Int.ediv_mul_right_exact`: exact Euclidean division of integer
  multiples `(d * q).ediv d = q` and `(q * d).ediv d = q` for `d ≠ 0`.
* `Int.modPowTwo_eq_of_dvd_sub`: unique recovery of `z ∈ [0, 2 ^ ℓ)` from any `x` with
  `2 ^ ℓ ∣ x - z`.
* `Int.size_natAbs_tdiv_le`, `Int.size_natAbs_ediv_le`, `Int.size_natAbs_emod_le_of_ne_zero`,
  `Int.size_natAbs_modPowTwo_le`, `Turing.MultiTapeTM.length_encIntBin_tdiv_le`,
  `Turing.MultiTapeTM.length_encIntBin_ediv_le`,
  `Turing.MultiTapeTM.length_encIntBin_emod_le_of_ne_zero`,
  `Turing.MultiTapeTM.length_encIntBin_emod_le_max`,
  `Turing.MultiTapeTM.length_encIntBin_modPowTwo_le`: binary magnitude and `encIntBin` code-length
  bounds.
* `Turing.MultiTapeTM.ComputableInPolyTime.intBin_tdiv`, `.intBin_tmod`, `.intBin_ediv`,
  `.intBin_emod`, `.intBin_div`, `.intBin_mod`, `.intBin_modPowTwo`: plain polynomial-time
  certificates and `@[fun_prop]` composition rules (`.intBin_tdiv'`, `.intBin_tmod'`,
  `.intBin_ediv'`, `.intBin_emod'`, `.intBin_div'`, `.intBin_mod'`, `.intBin_modPowTwo'`).

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Int

/-! ### Exact division and power-of-two modular reduction -/

/-- Least nonnegative residue of `x` modulo `2 ^ ℓ`, i.e., `x - 2 ^ ℓ * ⌊x / 2 ^ ℓ⌋`. -/
def modPowTwo (x : ℤ) (ℓ : ℕ) : ℤ :=
  x % (2 : ℤ) ^ ℓ

theorem modPowTwo_eq_emod (x : ℤ) (ℓ : ℕ) : x.modPowTwo ℓ = x.emod ((2 : ℤ) ^ ℓ) :=
  rfl

theorem modPowTwo_eq_sub_mul_ediv (x : ℤ) (ℓ : ℕ) :
    x.modPowTwo ℓ = x - (2 : ℤ) ^ ℓ * x.ediv ((2 : ℤ) ^ ℓ) :=
  Int.emod_def x ((2 : ℤ) ^ ℓ)

theorem modPowTwo_nonneg (x : ℤ) (ℓ : ℕ) : 0 ≤ x.modPowTwo ℓ :=
  Int.emod_nonneg x (by positivity)

theorem modPowTwo_lt (x : ℤ) (ℓ : ℕ) : x.modPowTwo ℓ < (2 : ℤ) ^ ℓ :=
  Int.emod_lt_of_pos x (by positivity)

theorem natAbs_modPowTwo_lt (x : ℤ) (ℓ : ℕ) : (x.modPowTwo ℓ).natAbs < 2 ^ ℓ := by
  have h₀ := modPowTwo_nonneg x ℓ
  have h₁ := modPowTwo_lt x ℓ
  have hcast : ((x.modPowTwo ℓ).natAbs : ℤ) < ((2 ^ ℓ : ℕ) : ℤ) := by
    rw [Int.natCast_natAbs, abs_of_nonneg h₀, Nat.cast_pow, Nat.cast_ofNat]
    exact h₁
  exact Int.ofNat_lt.mp hcast

/-- If `z ∈ [0, 2 ^ ℓ)` and `2 ^ ℓ` divides `x - z`, then `x.modPowTwo ℓ = z`. -/
theorem modPowTwo_eq_of_dvd_sub {x z : ℤ} {ℓ : ℕ} (hz₀ : 0 ≤ z) (hz₁ : z < (2 : ℤ) ^ ℓ)
    (hdvd : (2 : ℤ) ^ ℓ ∣ x - z) : x.modPowTwo ℓ = z := by
  obtain ⟨k, hk⟩ := hdvd
  have hx : x = z + (2 : ℤ) ^ ℓ * k := by lia
  rw [modPowTwo, hx, Int.add_mul_emod_self_left, Int.emod_eq_of_lt hz₀ hz₁]

/-- Exact Euclidean division of a left multiple `(d * q).ediv d = q` for `d ≠ 0`, stated directly
on `Int.ediv` for rewriting without folding to `/`. -/
theorem ediv_mul_left_exact {d : ℤ} (q : ℤ) (hd : d ≠ 0) : (d * q).ediv d = q :=
  Int.mul_ediv_cancel_left q hd

/-- Exact Euclidean division of a right multiple `(q * d).ediv d = q` for `d ≠ 0`, stated directly
on `Int.ediv` for rewriting without folding to `/`. -/
theorem ediv_mul_right_exact (q : ℤ) {d : ℤ} (hd : d ≠ 0) : (q * d).ediv d = q :=
  Int.mul_ediv_cancel q hd

/-! ### Sign-magnitude reductions and magnitude bounds -/

private theorem tdiv_eq_signMagnitude (a b : ℤ) :
    a.tdiv b =
      if (decide (a < 0) ^^ decide (b < 0)) then -((a.natAbs / b.natAbs : ℕ) : ℤ)
      else ((a.natAbs / b.natAbs : ℕ) : ℤ) := by
  cases a with
  | ofNat m =>
    cases b with
    | ofNat n => dsimp only [Int.tdiv, Int.natAbs]; split_ifs <;> lia
    | negSucc n => simp [Int.tdiv]
  | negSucc m =>
    cases b with
    | ofNat n =>
      cases n
      · simp [Int.tdiv]
      · dsimp only [Int.tdiv, Int.natAbs]; split_ifs <;> lia
    | negSucc n => simp [Int.tdiv]

private theorem tmod_eq_signMagnitude (a b : ℤ) :
    a.tmod b =
      if decide (a < 0) then -((a.natAbs % b.natAbs : ℕ) : ℤ)
      else ((a.natAbs % b.natAbs : ℕ) : ℤ) := by
  cases a with
  | ofNat m =>
    cases b with
    | ofNat n => simp [Int.tmod]
    | negSucc n => simp [Int.tmod]
  | negSucc m =>
    cases b with
    | ofNat n =>
      cases n <;> simp [Int.tmod]
    | negSucc n => simp [Int.tmod]

private theorem ediv_eq_signMagnitude (a b : ℤ) :
    a.ediv b =
      if b = 0 then 0
      else if a < 0 then
        if b < 0 then (((a.natAbs - 1) / b.natAbs + 1 : ℕ) : ℤ)
        else -(((a.natAbs - 1) / b.natAbs + 1 : ℕ) : ℤ)
      else
        if b < 0 then -((a.natAbs / b.natAbs : ℕ) : ℤ)
        else ((a.natAbs / b.natAbs : ℕ) : ℤ) := by
  cases a with
  | ofNat m =>
    cases b with
    | ofNat n =>
      cases n
      · simp [Int.ediv]
      · dsimp only [Int.ediv, Int.natAbs]; split_ifs <;> lia
    | negSucc n => simp [Int.ediv]
  | negSucc m =>
    cases b with
    | ofNat n =>
      cases n
      · simp [Int.ediv]
      · dsimp only [Int.ediv, Int.natAbs]; rw [Int.negSucc_eq]; split_ifs <;> lia
    | negSucc n => simp [Int.ediv]

private theorem emod_natAbs_eq (a b : ℤ) : a % (b.natAbs : ℤ) = a % b := by
  rcases le_or_gt 0 b with hb0 | hb0
  · rw [Int.natAbs_of_nonneg hb0]
  · have hbn : (b.natAbs : ℤ) = -b := by lia
    rw [hbn, Int.emod_neg]

private theorem emod_eq_emodNat (a b : ℤ) :
    a.emod b = if b = 0 then a else ((a % (b.natAbs : ℤ)).toNat : ℤ) := by
  change a % b = _
  by_cases hb : b = 0
  · simp [hb]
  · simp only [hb, ↓reduceIte, emod_natAbs_eq]
    exact (Int.toNat_of_nonneg (Int.emod_nonneg a hb)).symm

private theorem emod_eq_signMagnitude (a b : ℤ) :
    a.emod b =
      if b = 0 then a
      else if a < 0 then (((b.natAbs - a.natAbs % b.natAbs) % b.natAbs : ℕ) : ℤ)
      else ((a.natAbs % b.natAbs : ℕ) : ℤ) := by
  rw [emod_eq_emodNat]
  by_cases hb : b = 0
  · simp [hb]
  · have hq : b.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hb
    simp only [hb, ↓reduceIte]
    by_cases ha : a < 0
    · simp only [ha, ↓reduceIte, Int.emod_natAbs_of_neg ha hq]
      split_ifs with hdiv
      · rw [Int.emod_eq_zero_of_dvd hdiv]; simp
      · have hr_nonneg : 0 ≤ a % (b.natAbs : ℤ) := Int.emod_nonneg a (by positivity)
        have hr_lt : a % (b.natAbs : ℤ) < (b.natAbs : ℤ) := Int.emod_lt_of_pos a (by positivity)
        have hr_ne : a % (b.natAbs : ℤ) ≠ 0 := fun h0 => hdiv (Int.dvd_of_emod_eq_zero h0)
        have hlt : b.natAbs - (b.natAbs - (a % (b.natAbs : ℤ)).toNat) < b.natAbs := by lia
        rw [Nat.mod_eq_of_lt hlt]; lia
    · have ha0 : 0 ≤ a := not_lt.mp ha
      simp only [ha, ↓reduceIte, Int.emod_natAbs_of_nonneg ha0]

theorem natAbs_emod_lt_of_ne_zero (a : ℤ) {b : ℤ} (hb : b ≠ 0) :
    (a.emod b).natAbs < b.natAbs := by
  have hcast : ((a.emod b).natAbs : ℤ) < (b.natAbs : ℤ) := by
    change ((a % b).natAbs : ℤ) < (b.natAbs : ℤ)
    rw [Int.natCast_natAbs, abs_of_nonneg (Int.emod_nonneg a hb)]
    exact Int.emod_lt a hb
  exact Int.ofNat_lt.mp hcast

theorem size_natAbs_tdiv_le (a b : ℤ) : (a.tdiv b).natAbs.size ≤ a.natAbs.size :=
  Nat.size_le_size (Int.natAbs_tdiv_le_natAbs a b)

theorem size_natAbs_ediv_le (a b : ℤ) : (a.ediv b).natAbs.size ≤ a.natAbs.size :=
  Nat.size_le_size (Int.natAbs_ediv_le_natAbs a b)

theorem size_natAbs_emod_le_of_ne_zero (a : ℤ) {b : ℤ} (hb : b ≠ 0) :
    (a.emod b).natAbs.size ≤ b.natAbs.size :=
  Nat.size_le_size (natAbs_emod_lt_of_ne_zero a hb).le

theorem size_natAbs_modPowTwo_le (x : ℤ) (ℓ : ℕ) : (x.modPowTwo ℓ).natAbs.size ≤ ℓ :=
  Nat.size_le.mpr (natAbs_modPowTwo_lt x ℓ)

end Int

namespace Turing.MultiTapeTM

/-! ### Sign-magnitude `encIntBin` code-length bounds -/

/-- Truncated integer division never increases the `encIntBin` code length of the dividend. -/
theorem length_encIntBin_tdiv_le (a b : ℤ) :
    (encIntBin (a.tdiv b)).length ≤ (encIntBin a).length := by
  simp only [length_encIntBin]
  exact Nat.add_le_add_right (Int.size_natAbs_tdiv_le a b) 1

/-- Euclidean integer division never increases the `encIntBin` code length of the dividend. -/
theorem length_encIntBin_ediv_le (a b : ℤ) :
    (encIntBin (a.ediv b)).length ≤ (encIntBin a).length := by
  simp only [length_encIntBin]
  exact Nat.add_le_add_right (Int.size_natAbs_ediv_le a b) 1

/-- For `b ≠ 0`, the Euclidean remainder `a.emod b` has `encIntBin` code length at most
`(encIntBin b).length`. -/
theorem length_encIntBin_emod_le_of_ne_zero (a : ℤ) {b : ℤ} (hb : b ≠ 0) :
    (encIntBin (a.emod b)).length ≤ (encIntBin b).length := by
  simp only [length_encIntBin]
  exact Nat.add_le_add_right (Int.size_natAbs_emod_le_of_ne_zero a hb) 1

/-- Unconditionally on `b` (including `b = 0`),
`(encIntBin (a.emod b)).length ≤ max (encIntBin a).length (encIntBin b).length`. -/
theorem length_encIntBin_emod_le_max (a b : ℤ) :
    (encIntBin (a.emod b)).length ≤ max (encIntBin a).length (encIntBin b).length := by
  by_cases hb : b = 0
  · subst hb
    change (encIntBin (a % 0)).length ≤ _
    rw [Int.emod_zero]
    exact le_max_left _ _
  · exact (length_encIntBin_emod_le_of_ne_zero a hb).trans (le_max_right _ _)

/-- Reducing modulo `2 ^ ℓ` produces an `encIntBin` code of length at most `ℓ + 1`. -/
theorem length_encIntBin_modPowTwo_le (x : ℤ) (ℓ : ℕ) :
    (encIntBin (x.modPowTwo ℓ)).length ≤ ℓ + 1 := by
  rw [length_encIntBin]
  exact Nat.add_le_add_right (Int.size_natAbs_modPowTwo_le x ℓ) 1

end Turing.MultiTapeTM

namespace Turing.MultiTapeTM.ComputableInPolyTime

/-! ### Plain polynomial-time certificates -/

/-- Truncated-toward-zero division of signed binary integers is computable in polynomial time. -/
@[fun_prop]
theorem intBin_tdiv :
    ComputableInPolyTime (fun p : ℤ × ℤ => p.1.tdiv p.2)
      (encPair encIntBin encIntBin) encIntBin := by
  have h : ComputableInPolyTime
      (fun p : ℤ × ℤ =>
        if (decide (p.1 < 0) ^^ decide (p.2 < 0)) then -((p.1.natAbs / p.2.natAbs : ℕ) : ℤ)
        else ((p.1.natAbs / p.2.natAbs : ℕ) : ℤ))
      (encPair encIntBin encIntBin) encIntBin := by fun_prop
  exact h.of_enc_eq fun ⟨a, b⟩ => congrArg encIntBin (Int.tdiv_eq_signMagnitude a b)

/-- Truncated-toward-zero division of computed binary integers. -/
@[fun_prop]
theorem intBin_tdiv' {α : Type} {input : α ↪ List Bool} {left right : α → ℤ}
    (hleft : ComputableInPolyTime left input encIntBin)
    (hright : ComputableInPolyTime right input encIntBin) :
    ComputableInPolyTime (fun a => (left a).tdiv (right a)) input encIntBin :=
  intBin_tdiv.comp (hleft.prod hright)

/-- Truncated-toward-zero remainder of signed binary integers is computable in polynomial time. -/
@[fun_prop]
theorem intBin_tmod :
    ComputableInPolyTime (fun p : ℤ × ℤ => p.1.tmod p.2)
      (encPair encIntBin encIntBin) encIntBin := by
  have h : ComputableInPolyTime
      (fun p : ℤ × ℤ =>
        if decide (p.1 < 0) then -((p.1.natAbs % p.2.natAbs : ℕ) : ℤ)
        else ((p.1.natAbs % p.2.natAbs : ℕ) : ℤ))
      (encPair encIntBin encIntBin) encIntBin := by fun_prop
  exact h.of_enc_eq fun ⟨a, b⟩ => congrArg encIntBin (Int.tmod_eq_signMagnitude a b)

/-- Truncated-toward-zero remainder of computed binary integers. -/
@[fun_prop]
theorem intBin_tmod' {α : Type} {input : α ↪ List Bool} {left right : α → ℤ}
    (hleft : ComputableInPolyTime left input encIntBin)
    (hright : ComputableInPolyTime right input encIntBin) :
    ComputableInPolyTime (fun a => (left a).tmod (right a)) input encIntBin :=
  intBin_tmod.comp (hleft.prod hright)

/-- Euclidean division (`Int.ediv`) of signed binary integers is computable in polynomial time. -/
@[fun_prop]
theorem intBin_ediv :
    ComputableInPolyTime (fun p : ℤ × ℤ => p.1.ediv p.2)
      (encPair encIntBin encIntBin) encIntBin := by
  have hb0 : ComputableInPolyTime (fun p : ℤ × ℤ => decide (p.2 = 0))
      (encPair encIntBin encIntBin) encBool := by fun_prop
  have ha_neg : ComputableInPolyTime (fun p : ℤ × ℤ => decide (p.1 < 0))
      (encPair encIntBin encIntBin) encBool := by fun_prop
  have hb_neg : ComputableInPolyTime (fun p : ℤ × ℤ => decide (p.2 < 0))
      (encPair encIntBin encIntBin) encBool := by fun_prop
  have hq_neg : ComputableInPolyTime
      (fun p : ℤ × ℤ => (((p.1.natAbs - 1) / p.2.natAbs + 1 : ℕ) : ℤ))
      (encPair encIntBin encIntBin) encIntBin := by fun_prop
  have hq_nonneg : ComputableInPolyTime
      (fun p : ℤ × ℤ => ((p.1.natAbs / p.2.natAbs : ℕ) : ℤ))
      (encPair encIntBin encIntBin) encIntBin := by fun_prop
  have hneg : ComputableInPolyTime (fun z : ℤ => -z) encIntBin encIntBin := by fun_prop
  have h := hb0.ite (.const 0)
    (ha_neg.ite
      (hb_neg.ite hq_neg (hneg.comp hq_neg))
      (hb_neg.ite (hneg.comp hq_nonneg) hq_nonneg))
  refine h.of_enc_eq fun ⟨a, b⟩ => congrArg encIntBin ?_
  simpa only [Function.comp_apply, decide_eq_true_eq] using Int.ediv_eq_signMagnitude a b

/-- Euclidean division (`Int.ediv`) of computed binary integers. -/
@[fun_prop]
theorem intBin_ediv' {α : Type} {input : α ↪ List Bool} {left right : α → ℤ}
    (hleft : ComputableInPolyTime left input encIntBin)
    (hright : ComputableInPolyTime right input encIntBin) :
    ComputableInPolyTime (fun a => (left a).ediv (right a)) input encIntBin :=
  intBin_ediv.comp (hleft.prod hright)

/-- Euclidean division (`/`) of signed binary integers is computable in polynomial time. -/
@[fun_prop]
theorem intBin_div :
    ComputableInPolyTime (fun p : ℤ × ℤ => p.1 / p.2)
      (encPair encIntBin encIntBin) encIntBin :=
  intBin_ediv

/-- Euclidean division (`/`) of computed binary integers. -/
@[fun_prop]
theorem intBin_div' {α : Type} {input : α ↪ List Bool} {left right : α → ℤ}
    (hleft : ComputableInPolyTime left input encIntBin)
    (hright : ComputableInPolyTime right input encIntBin) :
    ComputableInPolyTime (fun a => left a / right a) input encIntBin :=
  intBin_div.comp (hleft.prod hright)

/-- Euclidean remainder (`Int.emod`) of signed binary integers is computable in polynomial time. -/
@[fun_prop]
theorem intBin_emod :
    ComputableInPolyTime (fun p : ℤ × ℤ => p.1.emod p.2)
      (encPair encIntBin encIntBin) encIntBin := by
  have hb0 : ComputableInPolyTime (fun p : ℤ × ℤ => decide (p.2 = 0))
      (encPair encIntBin encIntBin) encBool := by fun_prop
  have ha_neg : ComputableInPolyTime (fun p : ℤ × ℤ => decide (p.1 < 0))
      (encPair encIntBin encIntBin) encBool := by fun_prop
  have hneg : ComputableInPolyTime
      (fun p : ℤ × ℤ => (((p.2.natAbs - p.1.natAbs % p.2.natAbs) % p.2.natAbs : ℕ) : ℤ))
      (encPair encIntBin encIntBin) encIntBin := by fun_prop
  have hnonneg : ComputableInPolyTime
      (fun p : ℤ × ℤ => ((p.1.natAbs % p.2.natAbs : ℕ) : ℤ))
      (encPair encIntBin encIntBin) encIntBin := by fun_prop
  have h := hb0.ite (fst encIntBin encIntBin) (ha_neg.ite hneg hnonneg)
  refine h.of_enc_eq fun ⟨a, b⟩ => congrArg encIntBin ?_
  simpa only [Function.comp_apply, decide_eq_true_eq] using Int.emod_eq_signMagnitude a b

/-- Euclidean remainder (`Int.emod`) of computed binary integers. -/
@[fun_prop]
theorem intBin_emod' {α : Type} {input : α ↪ List Bool} {left right : α → ℤ}
    (hleft : ComputableInPolyTime left input encIntBin)
    (hright : ComputableInPolyTime right input encIntBin) :
    ComputableInPolyTime (fun a => (left a).emod (right a)) input encIntBin :=
  intBin_emod.comp (hleft.prod hright)

/-- Euclidean remainder (`%`) of signed binary integers is computable in polynomial time. -/
@[fun_prop]
theorem intBin_mod :
    ComputableInPolyTime (fun p : ℤ × ℤ => p.1 % p.2)
      (encPair encIntBin encIntBin) encIntBin :=
  intBin_emod

/-- Euclidean remainder (`%`) of computed binary integers. -/
@[fun_prop]
theorem intBin_mod' {α : Type} {input : α ↪ List Bool} {left right : α → ℤ}
    (hleft : ComputableInPolyTime left input encIntBin)
    (hright : ComputableInPolyTime right input encIntBin) :
    ComputableInPolyTime (fun a => left a % right a) input encIntBin :=
  intBin_mod.comp (hleft.prod hright)

/-- Reduction `Int.modPowTwo p.1 p.2 = p.1 % 2 ^ p.2` of a binary integer modulo `2 ^ ℓ` (with
`ℓ` in unary) is computable in polynomial time. -/
@[fun_prop]
theorem intBin_modPowTwo :
    ComputableInPolyTime (fun p : ℤ × ℕ => p.1.modPowTwo p.2)
      (encPair encIntBin encUnary) encIntBin := by
  have hpow : ComputableInPolyTime (fun p : ℤ × ℕ => ((2 : ℤ) ^ p.2))
      (encPair encIntBin encUnary) encIntBin := by fun_prop
  exact intBin_emod.comp ((fst encIntBin encUnary).prod hpow)

/-- Reduction `Int.modPowTwo (value a) (exponent a)` of a computed binary integer modulo a
computed unary power of two. -/
@[fun_prop]
theorem intBin_modPowTwo' {α : Type} {input : α ↪ List Bool} {value : α → ℤ} {exponent : α → ℕ}
    (hvalue : ComputableInPolyTime value input encIntBin)
    (hexponent : ComputableInPolyTime exponent input encUnary) :
    ComputableInPolyTime (fun a => (value a).modPowTwo (exponent a)) input encIntBin :=
  intBin_modPowTwo.comp (hvalue.prod hexponent)

end Turing.MultiTapeTM.ComputableInPolyTime


