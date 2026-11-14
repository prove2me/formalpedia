-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Nat_Log
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Nat_Log
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:56:22.788238+00:00
-- url     : https://prove2.me/theorems/11bace42-cc9b-45be-9d7b-528ad4950048
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log — Polynomial-time logarithms and bounded powers
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   The base-two logarithm is the binary representation's length minus one, with truncated
--   subtraction handling zero. Unary input first uses the certified unary-to-binary conversion.
--   Other fixed bases use repeated division with a linear bound on the encoded state. Ceiling
--   logarithms follow from floor logarithms; raising a fixed factor to a ceiling logarithm uses the
--   existing polynomial bound on logarithmically many multiplications. These latter certificates
--   charge unary counter lengths; the bounded-power rule also accepts any caller's encoding with
--   a certified unary size function.
--
--   ### Main results
--
--   * `Turing.MultiTapeTM.ComputableTidilyInPolyTime.binary_log_two`: compute the logarithm of a
--     binary natural, returning its unary value.
--   * `Turing.MultiTapeTM.ComputableTidilyInPolyTime.unary_log_two`: the unary-input version.
--   * `Turing.MultiTapeTM.ComputableTidilyInPolyTime.unary_log_const`, `.unary_clog_const`:
--     floor and ceiling logarithms in any fixed base on unary counters.
--   * `Turing.MultiTapeTM.ComputableTidilyInPolyTime.unary_pow_clog_const`: a fixed factor raised to
--     a fixed-base ceiling logarithm, with unary output and complete intermediate-size bounds.
--   * `Turing.MultiTapeTM.ComputableInPolyTime.unary_pow_clog_const`: the same bounded power for plain
--     certificates.
--
--   ### References
--
--   * [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
--
--   **Contents.** The module is published as a whole: 8 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Nat_Log`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Complexity/PolyTime/Nat/Log.lean

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Nat
public import Mathlib.Data.Nat.Log
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Iteration
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_List
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Nat_Div
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Plain
import Definitions.Def_Complexitylib_0ebd467_Foundations_Data_Nat_Log
import Mathlib.Data.Nat.Size

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Polynomial-time logarithms and bounded powers

The base-two logarithm is the binary representation's length minus one, with truncated
subtraction handling zero. Unary input first uses the certified unary-to-binary conversion.
Other fixed bases use repeated division with a linear bound on the encoded state. Ceiling
logarithms follow from floor logarithms; raising a fixed factor to a ceiling logarithm uses the
existing polynomial bound on logarithmically many multiplications. These latter certificates
charge unary counter lengths; the bounded-power rule also accepts any caller's encoding with
a certified unary size function.

## Main results

* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.binary_log_two`: compute the logarithm of a
  binary natural, returning its unary value.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.unary_log_two`: the unary-input version.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.unary_log_const`, `.unary_clog_const`:
  floor and ceiling logarithms in any fixed base on unary counters.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.unary_pow_clog_const`: a fixed factor raised to
  a fixed-base ceiling logarithm, with unary output and complete intermediate-size bounds.
* `Turing.MultiTapeTM.ComputableInPolyTime.unary_pow_clog_const`: the same bounded power for plain
  certificates.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Turing.MultiTapeTM.ComputableTidilyInPolyTime

/-- The base-two logarithm is polynomial-time on binary naturals, with its result in unary. -/
@[fun_prop]
theorem binary_log_two : ComputableTidilyInPolyTime (Nat.log 2) encNat encUnary := by
  have heq (n : ℕ) : (encNat n).length - 1 = Nat.log 2 n := by
    rw [encNat_apply, Nat.size_eq_bits_len]
    rcases n.eq_zero_or_pos with rfl | hn
    · simp
    · have hs := Nat.size_pos.mpr hn
      symm
      apply Nat.log_eq_of_pow_le_of_lt_pow
      · exact Nat.lt_size.mp (by lia)
      · simpa only [Nat.sub_add_cancel hs] using Nat.lt_size_self n
  simpa only [Function.comp_def, heq] using
    unary_sub.comp ((encoding_length encNat).prod (const 1))

/-- The base-two logarithm is polynomial-time with both input and output in unary. -/
@[fun_prop]
theorem unary_log_two : ComputableTidilyInPolyTime (Nat.log 2) encUnary encUnary :=
  binary_log_two.comp unary_to_binary

/-- Fixed-base logarithms are polynomial-time on unary counters, including bases zero and one.
The division loop maintains the logarithm identity and a linear bound on its complete state. -/
@[fun_prop]
theorem unary_log_const (base : ℕ) :
    ComputableTidilyInPolyTime (Nat.log base) encUnary encUnary := by
  rcases le_or_gt base 1 with hb | hb
  · convert (const (encIn := encUnary) (encMid := encUnary) 0) using 1
    exact funext (Nat.log_of_left_le_one hb)
  let step (state : ℕ × ℕ) :=
    if base ≤ state.1 then (state.1 / base, state.2 + 1) else state
  have hstep : ComputableTidilyInPolyTime step (encPair encUnary encUnary)
      (encPair encUnary encUnary) := by unfold step; fun_prop
  obtain ⟨hefficient, hspec⟩ := iterate_spec (count := id) (init := fun n => (n, 0))
    (encIn := encUnary) id' (by fun_prop) hstep
    (fun n i state => state.1 ≤ n ∧ state.2 ≤ i ∧
      (state.1 < base ∨ state.1 + i ≤ n) ∧
      Nat.log base state.1 + state.2 = Nat.log base n)
    (fun _ => by simp) (fun n i state _ h => by
      dsimp only [step]
      split
      · rename_i htest
        have hdrop := Nat.div_lt_self (lt_of_lt_of_le (by lia : 0 < base) htest) hb
        have hprogress : state.1 + i ≤ n := h.2.2.1.resolve_left (by lia)
        have hlog := Nat.log_of_one_lt_of_le hb htest
        exact ⟨(Nat.div_le_self _ _).trans h.1, by lia, Or.inr (by lia), by lia⟩
      · rename_i htest
        exact ⟨h.1, by lia, Or.inl (by lia), h.2.2.2⟩)
    (size := fun n => 3 * n + 1) (polyBounded (by fun_prop)) (fun _ _ _ hi h => by
      simp only [length_encPair, encUnary_apply, List.length_replicate]
      simp only [id_eq] at hi
      lia)
  have hresult (n : ℕ) : (step^[n] (n, 0)).2 = Nat.log base n := by
    have h := hspec n
    have hsmall : (step^[n] (n, 0)).1 < base := by
      rcases h.2.2.1 with hsmall | hsmall <;> simp only [id_eq] at * <;> lia
    simpa only [id_eq, Nat.log_of_lt hsmall, zero_add] using h.2.2.2
  simpa only [Function.comp_def, id_eq, hresult] using hefficient.snd'

/-- Ceiling logarithms in any fixed base are polynomial-time on unary counters. -/
@[fun_prop]
theorem unary_clog_const (base : ℕ) :
    ComputableTidilyInPolyTime (Nat.clog base) encUnary encUnary := by
  rcases le_or_gt base 1 with hb | hb
  · convert (const (encIn := encUnary) (encMid := encUnary) 0) using 1
    exact funext (Nat.clog_of_left_le_one hb)
  have heq (n : ℕ) : Nat.clog base n =
      if n ≤ 1 then 0 else Nat.log base (n - 1) + 1 := by
    split
    · rename_i hn
      exact Nat.clog_of_right_le_one hn base
    · rename_i hn
      apply le_antisymm
      · rw [Nat.clog_le_iff_le_pow hb]
        have h := Nat.lt_pow_succ_log_self hb (n - 1)
        lia
      · apply Nat.succ_le_of_lt
        rw [Nat.lt_clog_iff_pow_lt hb]
        exact (Nat.pow_log_le_self base (by lia : n - 1 ≠ 0)).trans_lt (by lia)
  convert (show ComputableTidilyInPolyTime
    (fun n : ℕ => if n ≤ 1 then 0 else Nat.log base (n - 1) + 1) encUnary encUnary
      from by fun_prop) using 1
  exact funext heq

/-- Given an efficient unary size function, a fixed factor raised to its fixed-base ceiling
logarithm has a polynomial-time unary output in the caller's original encoding. The bound charges
every intermediate power, including the initial one when the factor is zero. -/
@[fun_prop]
theorem unary_pow_clog_const {α : Type} {input : α ↪ List Bool} {size : α → ℕ}
    (hsize : ComputableTidilyInPolyTime size input encUnary) (factor base : ℕ) :
    ComputableTidilyInPolyTime (fun x => factor ^ Nat.clog base (size x)) input encUnary := by
  suffices ComputableTidilyInPolyTime (fun n : ℕ => factor ^ Nat.clog base n)
      encUnary encUnary from this.comp hsize
  rcases le_or_gt base 1 with hb | hb
  · simpa only [Nat.clog_of_left_le_one hb, pow_zero] using
      (const (encIn := encUnary) (encMid := encUnary) 1)
  obtain ⟨hefficient, hspec⟩ := iterate_spec (count := Nat.clog base) (init := fun _ => 1)
    (step := fun state => state * factor) (encIn := encUnary) (encState := encUnary)
    (unary_clog_const base) (by fun_prop) (by fun_prop)
    (fun _ i state => state = factor ^ i) (fun _ => rfl)
    (fun _ _ _ _ h => by rw [h, pow_succ])
    (size := fun n => base ^ Nat.clog base (max factor 1) *
      (n + 1) ^ Nat.clog base (max factor 1)) (polyBounded (by fun_prop)) (fun n i state hi h => by
      simp only [encUnary_apply, List.length_replicate, h]
      calc factor ^ i ≤ max factor 1 ^ i := Nat.pow_le_pow_left (Nat.le_max_left _ _) _
        _ ≤ max factor 1 ^ Nat.clog base (n + 1) :=
          Nat.pow_le_pow_right (Nat.le_max_right _ _)
            (hi.trans (Nat.clog_mono_right base (Nat.le_succ n)))
        _ ≤ _ := Nat.pow_clog_le_pow_clog_mul_pow_clog hb _ (Nat.succ_ne_zero n))
  simpa only [hspec] using hefficient

end Turing.MultiTapeTM.ComputableTidilyInPolyTime

namespace Turing.MultiTapeTM.ComputableInPolyTime

/-- `Turing.MultiTapeTM.ComputableTidilyInPolyTime.binary_log_two` for plain certificates. -/
theorem binary_log_two : ComputableInPolyTime (Nat.log 2) encNat encUnary :=
  .of_tidy ComputableTidilyInPolyTime.binary_log_two

/-- `Turing.MultiTapeTM.ComputableTidilyInPolyTime.unary_clog_const` for plain certificates. -/
theorem unary_clog_const (base : ℕ) :
    ComputableInPolyTime (Nat.clog base) encUnary encUnary :=
  .of_tidy (ComputableTidilyInPolyTime.unary_clog_const (base := base))

/-- `Turing.MultiTapeTM.ComputableTidilyInPolyTime.unary_pow_clog_const` for plain certificates. -/
@[fun_prop]
theorem unary_pow_clog_const {α : Type} {input : α ↪ List Bool} {size : α → ℕ}
    (hsize : ComputableInPolyTime size input encUnary) (factor base : ℕ) :
    ComputableInPolyTime (fun x => factor ^ Nat.clog base (size x)) input encUnary :=
  .of_tidy (ComputableTidilyInPolyTime.unary_pow_clog_const hsize.tidy factor base)

end Turing.MultiTapeTM.ComputableInPolyTime


