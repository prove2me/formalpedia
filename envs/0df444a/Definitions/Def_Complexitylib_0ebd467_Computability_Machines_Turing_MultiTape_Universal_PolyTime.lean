-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Universal_PolyTime
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Universal_PolyTime
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T17:08:08.993421+00:00
-- url     : https://prove2.me/theorems/b21dfacf-1a9a-4306-a0b5-85bc7cf5a20f
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Universal.PolyTime — Universal input coding and polynomial-time simulation
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Universal.PolyTime` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   The universal function `Turing.MultiTapeTM.Universal.universal` runs a described machine on an
--   input for a given number of steps. Its time and space are polynomial in the length of the
--   description, of the input and of the number of steps written in unary
--   (`Turing.MultiTapeTM.Universal.universal_bounds_unary`), so it is tidily computable in polynomial
--   time when the number of steps is written in unary
--   (`Turing.MultiTapeTM.Universal.computableTidilyInPolyTime_universal`). Written in binary, the
--   number of steps would be exponential in its length.
--
--   The input-coding API translates bits to unary symbols (`false ↦ 0`, `true ↦ 1`) in linear time
--   and output size. It also certifies polynomial-time decoding of descriptions and coding of a
--   single bit, independently of hierarchy theorems and Ladner's language.
--
--   ### Main definitions
--
--   * `Turing.MultiTapeTM.Universal.encTrueDoubled`: a bit-list encoding doubling every `true`.
--   * `Turing.MultiTapeTM.Universal.trueDoubleT`, `Turing.MultiTapeTM.Universal.symbolsT`: transducers
--     implementing the conversion from bit words to framed unary symbols.
--
--   ### Main results
--
--   * `Turing.MultiTapeTM.Universal.computableTidilyInDegree_map_eBit`: input symbols in linear time
--     and output size.
--   * `Turing.MultiTapeTM.Universal.computableTidilyInPolyTime_map_eBit`,
--     `Turing.MultiTapeTM.Universal.computableTidilyInPolyTime_eBit`,
--     `Turing.MultiTapeTM.Universal.computableInPolyTime_decodeDesc`,
--     `Turing.MultiTapeTM.Universal.computableInPolyTime_map_eBit`,
--     `Turing.MultiTapeTM.Universal.computableInPolyTime_eBit`,
--     `Turing.MultiTapeTM.Universal.computableInPolyTime_map_ne_zero`: polynomial-time description
--     decoding, bit coding, and output-symbol decoding.
--
--   * `Turing.MultiTapeTM.Universal.universal_bounds_unary`: the time and space of the universal
--     function, polynomially in the length of its input with the number of steps in unary.
--   * `Turing.MultiTapeTM.Universal.computableTidilyInPolyTime_universal`,
--     `Turing.MultiTapeTM.Universal.computableInPolyTime_universal`: the universal function,
--     with its number of steps in unary, is polynomial-time.
--
--   ### References
--
--   * [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
--
--   **Contents.** The module is published as a whole: 16 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Universal_PolyTime`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Universal/PolyTime.lean

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (local addition beside the vendored `Turing.MultiTapeTM.Universal` files)

public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Universal_ResourceBound
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Universal_Decode
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Universal_Bit
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Plain
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_BitString
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_List
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Nat

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Universal.PolyTime` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Universal input coding and polynomial-time simulation

The universal function `Turing.MultiTapeTM.Universal.universal` runs a described machine on an
input for a given number of steps. Its time and space are polynomial in the length of the
description, of the input and of the number of steps written in unary
(`Turing.MultiTapeTM.Universal.universal_bounds_unary`), so it is tidily computable in polynomial
time when the number of steps is written in unary
(`Turing.MultiTapeTM.Universal.computableTidilyInPolyTime_universal`). Written in binary, the
number of steps would be exponential in its length.

The input-coding API translates bits to unary symbols (`false ↦ 0`, `true ↦ 1`) in linear time
and output size. It also certifies polynomial-time decoding of descriptions and coding of a
single bit, independently of hierarchy theorems and Ladner's language.

## Main definitions

* `Turing.MultiTapeTM.Universal.encTrueDoubled`: a bit-list encoding doubling every `true`.
* `Turing.MultiTapeTM.Universal.trueDoubleT`, `Turing.MultiTapeTM.Universal.symbolsT`: transducers
  implementing the conversion from bit words to framed unary symbols.

## Main results

* `Turing.MultiTapeTM.Universal.computableTidilyInDegree_map_eBit`: input symbols in linear time
  and output size.
* `Turing.MultiTapeTM.Universal.computableTidilyInPolyTime_map_eBit`,
  `Turing.MultiTapeTM.Universal.computableTidilyInPolyTime_eBit`,
  `Turing.MultiTapeTM.Universal.computableInPolyTime_decodeDesc`,
  `Turing.MultiTapeTM.Universal.computableInPolyTime_map_eBit`,
  `Turing.MultiTapeTM.Universal.computableInPolyTime_eBit`,
  `Turing.MultiTapeTM.Universal.computableInPolyTime_map_ne_zero`: polynomial-time description
  decoding, bit coding, and output-symbol decoding.

* `Turing.MultiTapeTM.Universal.universal_bounds_unary`: the time and space of the universal
  function, polynomially in the length of its input with the number of steps in unary.
* `Turing.MultiTapeTM.Universal.computableTidilyInPolyTime_universal`,
  `Turing.MultiTapeTM.Universal.computableInPolyTime_universal`: the universal function,
  with its number of steps in unary, is polynomial-time.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Turing.MultiTapeTM.Universal

open ComputableTidilyInPolyTime

/-! ### The symbols of the input -/

/-- The code of a bit list with every `true` doubled: `false ↦ [false]`, `true ↦ [true, true]`. -/
def trueDoubled (b : Bool) : List Bool := if b then [true, true] else [false]

/-- Bit lists with every `true` doubled. -/
def encTrueDoubled : List Bool ↪ List Bool :=
  ⟨fun x => x.flatMap trueDoubled, fun x y h => by
    induction x generalizing y with
    | nil => cases y with
      | nil => rfl
      | cons b y => cases b <;> simp [trueDoubled] at h
    | cons a x ih => cases y with
      | nil => cases a <;> simp [trueDoubled] at h
      | cons b y =>
        cases a <;> cases b <;> simp only [trueDoubled, List.flatMap_cons, Bool.false_eq_true,
          ↓reduceIte, List.cons_append, List.nil_append, List.cons.injEq, true_and,
          reduceCtorEq, false_and] at h ⊢ <;> exact ih _ h⟩

/-- Doubles every `true`. -/
def trueDoubleT : Transducer Bool Unit where
  q₀ := ()
  step _ b := ((), trueDoubled b)
  final _ := []
  length_step_le _ b := by cases b <;> simp [trueDoubled]
  length_final_le _ := by simp

/-- Reads a doubled word as the framed unary symbols `0` for `false` and `1` for `true`. -/
def symbolsT : Transducer Bool Bool where
  q₀ := false
  step
    | false, false => (false, [false])
    | false, true => (true, [true, true])
    | true, _ => (false, [false])
  final _ := []
  length_step_le q b := by cases q <;> cases b <;> simp
  length_final_le _ := by simp

theorem trueDoubleT_run (x : List Bool) : trueDoubleT.run () x = encTrueDoubled x := by
  induction x with
  | nil => rfl
  | cons b x ih =>
    rw [Transducer.run_cons, ih]
    rfl

theorem symbolsT_run (x : List Bool) :
    symbolsT.run false (encTrueDoubled x) = encList encUnary (x.map eBit) := by
  induction x with
  | nil => rfl
  | cons b x ih =>
    cases b
    · change (false :: symbolsT.run false (encTrueDoubled x)) = _
      rw [ih]
      rfl
    · change (true :: true :: false :: symbolsT.run false (encTrueDoubled x)) = _
      rw [ih]
      rfl

/-- The input as symbols, in linear time and space. -/
theorem computableTidilyInDegree_map_eBit :
    ComputableTidilyInDegree (fun x : List Bool => x.map eBit) encBits (encList encUnary) 1 1 :=
  (ComputableTidilyInDegree.of_linear (encIn := encTrueDoubled)
    (symbolsT.computableTidilyInLinearTimeAndSpace fun x => (symbolsT_run x).symm)).comp
    (ComputableTidilyInDegree.of_linear (encIn := encBits) (encMid := encTrueDoubled) (f := id)
      (trueDoubleT.computableTidilyInLinearTimeAndSpace fun x => (trueDoubleT_run x).symm))

/-- The input of a machine as symbols is linear. -/
@[fun_prop]
theorem computableTidilyInPolyTime_map_eBit :
    ComputableTidilyInPolyTime (fun w : List Bool => w.map eBit) encBits (encList encUnary) :=
  computableTidilyInDegree_map_eBit.computableTidilyInPolyTime

/-- The coding of bits as symbols is a finite computation. -/
@[fun_prop]
theorem computableTidilyInPolyTime_eBit :
    ComputableTidilyInPolyTime (fun b : Bool => eBit b) encBool encUnary :=
  of_finite _

/-! ### Simulation with a unary clock -/

/-- The time and space of the universal function, polynomially in the length of its input with
the number of steps in unary. -/
theorem universal_bounds_unary (i : Desc × List ℕ × ℕ) :
    (i.2.2 + 1) * (stepBound (descLen i.1) (encList encUnary i.2.1).length i.2.2 +
        runBound (descLen i.1) (encList encUnary i.2.1).length i.2.2 +
          ((encNat i.2.2).length + 1) ^ 2) + ((eIn i).length + 1) ^ 2 ≤
      100025 * ((encPair eDesc (encPair (encList encUnary) encUnary) i).length + 1) ^ 6 ∧
    runBound (descLen i.1) (encList encUnary i.2.1).length i.2.2 + (eIn i).length ≤
      205 * ((encPair eDesc (encPair (encList encUnary) encUnary) i).length + 1) ^ 3 := by
  obtain ⟨d, x, t⟩ := i
  set n := (encPair eDesc (encPair (encList encUnary) encUnary) (d, x, t)).length with hn
  have hlen : n = 2 * descLen d + 1 + (2 * (encList encUnary x).length + 1 + t) := by
    simp [hn, descLen]
  have hL := length_encNat_le t
  have hIn : (eIn (d, x, t)).length ≤ 5 * n + 2 := by
    simp only [eIn, length_encPair]
    simp only [descLen] at hlen
    omega
  obtain ⟨h₁, h₂⟩ := universal_bounds_le (D := descLen d)
    (N := (encList encUnary x).length) (J := t + 1) (B := n) (L := (encNat t).length)
    (by omega) (by omega) (by omega) (by omega)
  have hstep := stepBound_mono (D := descLen d) (N := (encList encUnary x).length) le_rfl le_rfl
    (Nat.le_add_right t 1)
  have hrun := runBound_mono (D := descLen d) (N := (encList encUnary x).length)
    (Nat.le_add_right t 1)
  have ht : t + 1 ≤ n + 1 := by omega
  have hpow : (t + 1) ^ 2 ≤ (n + 1) ^ 2 := Nat.pow_le_pow_left ht 2
  simp only at h₁ h₂ hstep hrun ⊢
  constructor
  · have hA : (t + 1) * (stepBound (descLen d) (encList encUnary x).length t +
        runBound (descLen d) (encList encUnary x).length t + ((encNat t).length + 1) ^ 2) ≤
        100000 * (n + 1) ^ 4 * (n + 1) ^ 2 :=
      calc _ ≤ (t + 1 + 1) * (stepBound (descLen d) (encList encUnary x).length (t + 1) +
            runBound (descLen d) (encList encUnary x).length (t + 1) +
              ((encNat t).length + 1) ^ 2) := Nat.mul_le_mul (by omega) (by omega)
        _ ≤ _ := h₁
        _ ≤ _ := Nat.mul_le_mul_left _ hpow
    have hB : ((eIn (d, x, t)).length + 1) ^ 2 ≤ 25 * (n + 1) ^ 6 := by
      calc _ ≤ (5 * (n + 1)) ^ 2 := Nat.pow_le_pow_left (by omega) 2
        _ = 25 * (n + 1) ^ 2 := by ring
        _ ≤ 25 * (n + 1) ^ 6 := Nat.mul_le_mul_left _
            (Nat.pow_le_pow_right (by omega) (by omega))
    have : 100000 * (n + 1) ^ 4 * (n + 1) ^ 2 = 100000 * (n + 1) ^ 6 := by ring
    omega
  · have hA : runBound (descLen d) (encList encUnary x).length t ≤ 200 * (n + 1) ^ 3 :=
      calc _ ≤ _ := hrun
        _ ≤ 200 * (n + 1) ^ 2 * (t + 1) := h₂
        _ ≤ 200 * (n + 1) ^ 2 * (n + 1) := Nat.mul_le_mul_left _ ht
        _ = 200 * (n + 1) ^ 3 := by ring
    have hB : 5 * n + 2 ≤ 5 * (n + 1) ^ 3 := by
      have : n + 1 ≤ (n + 1) ^ 3 := Nat.le_self_pow (by omega) _
      omega
    omega

/-- **The universal function with a unary clock is polynomial-time**: written in unary, the number
of steps counts towards the length of the input. -/
@[fun_prop]
theorem computableTidilyInPolyTime_universal :
    ComputableTidilyInPolyTime universal
      (encPair eDesc (encPair (encList encUnary) encUnary)) eOut := by
  have hconv : ComputableTidilyInPolyTime (fun i : Desc × List ℕ × ℕ => i)
      (encPair eDesc (encPair (encList encUnary) encUnary)) eIn := by
    have : (fun i : Desc × List ℕ × ℕ => i) = fun i => (i.1, i.2.1, i.2.2) := rfl
    rw [this]
    fun_prop
  obtain ⟨d, e, hdeg⟩ := hconv.exists_degree
  exact (computableTidilyInO_universal.comp hdeg.inO).computableTidilyInPolyTime
    ((PolyBounded.of_forall_le 1 d fun _ => by simp).add
      (PolyBounded.of_forall_le 100025 6 fun i => (universal_bounds_unary i).1))
    ((PolyBounded.of_forall_le 1 d fun _ => by simp).add
      (PolyBounded.of_forall_le 205 3 fun i => (universal_bounds_unary i).2))

/-! ### Plain `ComputableInPolyTime` wrappers for the universal simulator -/

/-- Plain polynomial-time certificate for `decodeDesc`. -/
@[fun_prop]
theorem computableInPolyTime_decodeDesc :
    ComputableInPolyTime decodeDesc encBits eDesc :=
  let ⟨_, _, h⟩ := exists_computableInDegree_decodeDesc
  h.computableInPolyTime

/-- Plain polynomial-time certificate for coding a bit string as unary symbol numbers. -/
@[fun_prop]
theorem computableInPolyTime_map_eBit :
    ComputableInPolyTime (fun w : List Bool => w.map eBit) encBits (encList encUnary) :=
  .of_tidy computableTidilyInPolyTime_map_eBit

/-- Plain polynomial-time certificate for coding a single bit as a unary symbol number. -/
@[fun_prop]
theorem computableInPolyTime_eBit :
    ComputableInPolyTime (fun b : Bool => eBit b) encBool encUnary :=
  .of_tidy computableTidilyInPolyTime_eBit

/-- Decoding a list of unary symbol numbers to bits via `(· != 0)` is computable in polynomial
time. -/
@[fun_prop]
theorem computableInPolyTime_map_ne_zero :
    ComputableInPolyTime (fun l : List ℕ => l.map (· != 0)) (encList encUnary) encBits := by
  have hbit : ComputableInPolyTime (fun n : ℕ => n != 0) encUnary encBool :=
    .bne .id' (.const 0)
  exact ComputableInPolyTime.listToBits.comp (.map hbit)

/-- Plain polynomial-time certificate for the universal simulator with a unary step budget. -/
@[fun_prop]
theorem computableInPolyTime_universal :
    ComputableInPolyTime universal
      (encPair eDesc (encPair (encList encUnary) encUnary)) eOut :=
  .of_tidy computableTidilyInPolyTime_universal

end Turing.MultiTapeTM.Universal


