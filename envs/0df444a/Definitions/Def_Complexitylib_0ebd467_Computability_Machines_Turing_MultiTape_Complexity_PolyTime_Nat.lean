-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Nat
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Nat
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:53:34.452802+00:00
-- url     : https://prove2.me/theorems/927be938-fafa-43ec-9dae-286973453f7c
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat — Polynomial-time arithmetic on unary counters
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   Arithmetic on `encUnary`, built from Christian Reitwiessner's encodings and machine calculus.
--   Addition concatenates the unary words; multiplication folds addition while keeping a quadratic
--   bound on the accumulator. Fixed powers and fixed polynomials follow by composition. These
--   operations support polynomially bounded counters and list enumeration in reductions.
--
--   ### Main results
--
--   * `Turing.MultiTapeTM.ComputableTidilyInPolyTime.indexed_polynomial_bound`: a uniform polynomial
--     bound over a polynomially bounded range of indices, without computing the selected index.
--   * `Turing.MultiTapeTM.ComputableTidilyInPolyTime.unary_add`, `.unary_sub`, `.unary_mul`:
--     arithmetic on unary naturals.
--   * `Turing.MultiTapeTM.ComputableTidilyInPolyTime.unary_min`, `.unary_max`:
--     the smaller and larger of two unary naturals.
--   * `Turing.MultiTapeTM.ComputableTidilyInPolyTime.unary_le`, `.unary_lt`, `.unary_pair`:
--     comparisons and the natural-number pairing function.
--   * `Turing.MultiTapeTM.ComputableTidilyInPolyTime.unary_le'`, `.unary_lt'`: comparisons of computed
--     operands with the intermediate unary encodings fixed for automation.
--   * `Turing.MultiTapeTM.ComputableTidilyInPolyTime.unary_pow`, `.unary_eval`:
--     evaluation of a fixed power or polynomial, with input and output in unary.
--   * `Turing.MultiTapeTM.ComputableTidilyInPolyTime.unary_to_binary`:
--     conversion from unary to the binary encoding `encNat`.
--
--   ### References
--
--   * [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
--
--   The indexed bound is adapted from Cslib/Computability/Probabilistic/Encoding.lean on the cslib
--   `crypto` branch at `5ff69ca93402e7c947208dc56396d6d86203ccd8`.
--
--   **Contents.** The module is published as a whole: 24 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Nat`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Complexity/PolyTime/Nat.lean

/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_PolyTimeNatFrontends
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Fold
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_PolyTime
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Data.Nat.Pairing
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Plain

import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_Lists
import Mathlib.Data.Nat.Size

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Polynomial-time arithmetic on unary counters

Arithmetic on `encUnary`, built from Christian Reitwiessner's encodings and machine calculus.
Addition concatenates the unary words; multiplication folds addition while keeping a quadratic
bound on the accumulator. Fixed powers and fixed polynomials follow by composition. These
operations support polynomially bounded counters and list enumeration in reductions.

## Main results

* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.indexed_polynomial_bound`: a uniform polynomial
  bound over a polynomially bounded range of indices, without computing the selected index.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.unary_add`, `.unary_sub`, `.unary_mul`:
  arithmetic on unary naturals.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.unary_min`, `.unary_max`:
  the smaller and larger of two unary naturals.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.unary_le`, `.unary_lt`, `.unary_pair`:
  comparisons and the natural-number pairing function.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.unary_le'`, `.unary_lt'`: comparisons of computed
  operands with the intermediate unary encodings fixed for automation.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.unary_pow`, `.unary_eval`:
  evaluation of a fixed power or polynomial, with input and output in unary.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.unary_to_binary`:
  conversion from unary to the binary encoding `encNat`.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]

The indexed bound is adapted from Cslib/Computability/Probabilistic/Encoding.lean on the cslib
`crypto` branch at `5ff69ca93402e7c947208dc56396d6d86203ccd8`.
-/

@[expose] public section

namespace Turing.MultiTapeTM.ComputableTidilyInPolyTime

/-- Interpret one Boolean as a unary zero or one. -/
@[fun_prop]
theorem bool_toUnary : ComputableTidilyInPolyTime Bool.toNat encBool encUnary := of_finite _

/-- A unary-output polynomial-time function is polynomially bounded in its unary input. -/
theorem polynomiallyBounded {f : ℕ → ℕ} (hf : ComputableTidilyInPolyTime f encUnary encUnary) :
    Cslib.PolynomiallyBounded f :=
  (show PolyBounded (fun n : ℕ => n) f by
    simpa only [encUnary_apply, List.length_replicate] using hf.polyBounded).polynomiallyBounded

/-- Efficient unary values share a polynomial bound over a polynomially bounded range of
indices. Selecting an index does not require a computable choice. -/
theorem indexed_polynomial_bound {f : ℕ → ℕ → ℕ} {count : ℕ → ℕ}
    (hf : ComputableTidilyInPolyTime (fun input => f input.1 input.2)
      (encPair encUnary encUnary) encUnary)
    (hcount : Cslib.PolynomiallyBounded count) :
    ∃ c d : ℕ, ∀ n i, i < count n → f n i ≤ c * (n + 1) ^ d := by
  obtain ⟨c, d, hf⟩ := hf.polyBounded_length.exists_le
  have hpoly : Cslib.PolynomiallyBounded (fun n => c * (2 * n + count n + 2) ^ d) := by fun_prop
  obtain ⟨C, D, hpoly⟩ := Cslib.polynomiallyBounded_iff_le.mp hpoly
  refine ⟨C, D, fun n i hi => ?_⟩
  have h := hf (n, i)
  simp only [length_encPair, encUnary_apply, List.length_replicate] at h
  exact h.trans ((Nat.mul_le_mul_left c (Nat.pow_le_pow_left (by lia) d)).trans (hpoly n))

/-- Addition of unary naturals, by concatenating their encodings. -/
@[fun_prop]
theorem unary_add : ComputableTidilyInPolyTime (fun p : ℕ × ℕ => p.1 + p.2)
    (encPair encUnary encUnary) encUnary :=
  (fst encUnary encUnary).append (snd encUnary encUnary)
    (fun _ => by simp only [encUnary_apply, List.replicate_add])

/-- Truncated subtraction of unary naturals. -/
@[fun_prop]
theorem unary_sub : ComputableTidilyInPolyTime (fun p : ℕ × ℕ => p.1 - p.2)
    (encPair encUnary encUnary) encUnary :=
  ComputableTidilyInDegree.unary_sub.computableTidilyInPolyTime

/-- Multiplication of unary naturals, by repeated addition. -/
@[fun_prop]
theorem unary_mul : ComputableTidilyInPolyTime (fun p : ℕ × ℕ => p.1 * p.2)
    (encPair encUnary encUnary) encUnary := by
  have hq := fst (encPair encUnary encUnary) encBool
  have h := foldlWith_of_bounded_growth (encA := encBool) (encL := encBits) (encB := encUnary)
    (par := fun p : ℕ × ℕ => p.1) (list := fun p => List.replicate p.2 true)
    (step := fun a n _ => n + a) (fst encUnary encUnary)
    ((of_eq (encIn := encUnary) (encMid := encBits) fun _ => rfl).comp (snd encUnary encUnary))
    (const 0) (unary_add.comp (hq.snd'.prod hq.fst'))
    (growth := Prod.fst) (fst encUnary encUnary).polyBounded
    (by intros; simp)
  simpa [List.foldl_const, Nat.mul_comm] using h

/-- Take the smaller of two unary naturals. -/
@[fun_prop]
theorem unary_min : ComputableTidilyInPolyTime (fun p : ℕ × ℕ => min p.1 p.2)
    (encPair encUnary encUnary) encUnary :=
  ComputableTidilyInDegree.unary_min.computableTidilyInPolyTime

/-- Take the larger of two unary naturals. -/
@[fun_prop]
theorem unary_max : ComputableTidilyInPolyTime (fun p : ℕ × ℕ => max p.1 p.2)
    (encPair encUnary encUnary) encUnary := by
  have h : ComputableTidilyInPolyTime (fun p : ℕ × ℕ => p.1 + (p.2 - p.1))
      (encPair encUnary encUnary) encUnary := by fun_prop
  convert h using 1
  funext p
  omega

/-- Compare unary naturals. -/
@[fun_prop]
theorem unary_le : ComputableTidilyInPolyTime (fun p : ℕ × ℕ => decide (p.1 ≤ p.2))
    (encPair encUnary encUnary) encBool := by
  simpa only [Function.comp_def, Nat.sub_eq_zero_iff_le] using
    ComputableTidilyInDegree.unary_isZero.computableTidilyInPolyTime.comp unary_sub

/-- Strict comparison of unary naturals. -/
@[fun_prop]
theorem unary_lt : ComputableTidilyInPolyTime (fun p : ℕ × ℕ => decide (p.1 < p.2))
    (encPair encUnary encUnary) encBool := by
  simpa only [Function.comp_def, ← decide_not, Nat.not_le] using bool_not.comp
    (unary_le.comp ((snd encUnary encUnary).prod (fst encUnary encUnary)))

/-- Compare computed unary values, fixing their intermediate encodings before proof search. -/
@[fun_prop]
theorem unary_le' {α : Type} {input : α ↪ List Bool} {left right : α → ℕ}
    (hleft : ComputableTidilyInPolyTime left input encUnary)
    (hright : ComputableTidilyInPolyTime right input encUnary) :
    ComputableTidilyInPolyTime (fun a => decide (left a ≤ right a)) input encBool :=
  unary_le.comp (hleft.prod hright)

/-- Strictly compare computed unary values, with both operand encodings fixed. -/
@[fun_prop]
theorem unary_lt' {α : Type} {input : α ↪ List Bool} {left right : α → ℕ}
    (hleft : ComputableTidilyInPolyTime left input encUnary)
    (hright : ComputableTidilyInPolyTime right input encUnary) :
    ComputableTidilyInPolyTime (fun a => decide (left a < right a)) input encBool :=
  unary_lt.comp (hleft.prod hright)

/-- Equality of computed unary counters, fixing the intermediate encoding for proof search. -/
@[fun_prop]
theorem unary_beq {α : Type} {input : α ↪ List Bool} {left right : α → ℕ}
    (hleft : ComputableTidilyInPolyTime left input encUnary)
    (hright : ComputableTidilyInPolyTime right input encUnary) :
    ComputableTidilyInPolyTime (fun a => left a == right a) input encBool :=
  hleft.beq hright

/-- The natural-number pairing function, with both arguments and the result in unary. -/
@[fun_prop]
theorem unary_pair : ComputableTidilyInPolyTime (fun p : ℕ × ℕ => Nat.pair p.1 p.2)
    (encPair encUnary encUnary) encUnary := by
  have hleft : ComputableTidilyInPolyTime (fun p : ℕ × ℕ => p.2 * p.2 + p.1)
      (encPair encUnary encUnary) encUnary := by fun_prop
  have hright : ComputableTidilyInPolyTime (fun p : ℕ × ℕ => p.1 * p.1 + p.1 + p.2)
      (encPair encUnary encUnary) encUnary := by fun_prop
  simpa [Nat.pair] using unary_lt.ite' hleft hright

/-- A fixed power of a unary natural. -/
@[fun_prop]
theorem unary_pow (d : ℕ) : ComputableTidilyInPolyTime (fun n : ℕ => n ^ d)
    encUnary encUnary := by
  induction d with
  | zero => simpa using (const (encIn := encUnary) (encMid := encUnary) 1)
  | succ d ih => simpa only [pow_succ, Function.comp_def] using unary_mul.comp (ih.prod id')

/-- Evaluate a fixed polynomial on unary naturals, with its result also in unary. -/
@[fun_prop]
theorem unary_eval (p : Polynomial ℕ) : ComputableTidilyInPolyTime p.eval encUnary encUnary := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simpa only [Polynomial.eval_add, Function.comp_def] using unary_add.comp (hp.prod hq)
  | monomial d c =>
    simpa only [Polynomial.eval_monomial, Function.comp_def] using
      unary_mul.comp ((const c).prod (unary_pow d))

/-- Convert a unary natural to its binary encoding by incrementing a binary counter. -/
@[fun_prop]
theorem unary_to_binary : ComputableTidilyInPolyTime (fun n : ℕ => n) encUnary encNat := by
  have hsize (n : ℕ) : (encNat n).length ≤ n := by
    rw [encNat_apply, Nat.size_eq_bits_len]
    exact Nat.size_le.mpr Nat.lt_two_pow_self
  have h := foldl' (encA := encBool) (encL := encBits) (list := fun n => List.replicate n true)
    (step := fun n _ => n + 1)
    (of_eq (encIn := encUnary) (encMid := encBits) fun _ => rfl) (const 0)
    (computableTidilyInPolyTime_succ.comp (fst encNat encBool))
    (B := fun n => (encUnary n).length) .self (fun n i _ => by
      simpa [List.foldl_const] using (hsize (min i n)).trans (Nat.min_le_right i n))
  simpa [List.foldl_const] using h

end Turing.MultiTapeTM.ComputableTidilyInPolyTime

/-! ### Plain polynomial-time automation -/

namespace Turing.MultiTapeTM.ComputableInPolyTime

/-- Addition of unary naturals, by concatenating their encodings. -/
@[fun_prop]
theorem unary_add :
    ComputableInPolyTime (fun (p : ℕ × ℕ) => p.1 + p.2)
  (encPair encUnary encUnary)
  encUnary :=
  .of_tidy Turing.MultiTapeTM.ComputableTidilyInPolyTime.unary_add

/-- Evaluate a fixed polynomial on unary naturals, with its result also in unary. -/
@[fun_prop]
theorem unary_eval (p : Polynomial ℕ) :
    ComputableInPolyTime (fun (x : ℕ) => Polynomial.eval x p)
  encUnary encUnary :=
  .of_tidy (@Turing.MultiTapeTM.ComputableTidilyInPolyTime.unary_eval p)

/-- Multiplication of unary naturals, by repeated addition. -/
@[fun_prop]
theorem unary_mul :
    ComputableInPolyTime (fun (p : ℕ × ℕ) => p.1 * p.2)
  (encPair encUnary encUnary)
  encUnary :=
  .of_tidy Turing.MultiTapeTM.ComputableTidilyInPolyTime.unary_mul

/-- Add two computed unary naturals with the same full input context. -/
@[fun_prop]
theorem unary_add' {α : Type} {input : α ↪ List Bool} {left right : α → ℕ}
    (hleft : ComputableInPolyTime left input encUnary)
    (hright : ComputableInPolyTime right input encUnary) :
    ComputableInPolyTime (fun a => left a + right a) input encUnary :=
  unary_add.comp (hleft.prod hright)

/-- Subtract two computed unary naturals with the same full input context. -/
@[fun_prop]
theorem unary_sub' {α : Type} {input : α ↪ List Bool} {left right : α → ℕ}
    (hleft : ComputableInPolyTime left input encUnary)
    (hright : ComputableInPolyTime right input encUnary) :
    ComputableInPolyTime (fun a => left a - right a) input encUnary :=
  unary_sub.comp (hleft.prod hright)

/-- Multiply two computed unary naturals with the same full input context. -/
@[fun_prop]
theorem unary_mul' {α : Type} {input : α ↪ List Bool} {left right : α → ℕ}
    (hleft : ComputableInPolyTime left input encUnary)
    (hright : ComputableInPolyTime right input encUnary) :
    ComputableInPolyTime (fun a => left a * right a) input encUnary :=
  unary_mul.comp (hleft.prod hright)

/-- A fixed power of a unary natural. -/
@[fun_prop]
theorem unary_pow (d : ℕ) :
    ComputableInPolyTime (fun (n : ℕ) => n ^ d)
  encUnary encUnary :=
  .of_tidy (@Turing.MultiTapeTM.ComputableTidilyInPolyTime.unary_pow d)

end Turing.MultiTapeTM.ComputableInPolyTime


