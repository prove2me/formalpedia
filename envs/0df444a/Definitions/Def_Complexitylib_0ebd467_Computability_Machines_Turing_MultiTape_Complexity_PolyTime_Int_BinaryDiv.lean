-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Int_BinaryDiv
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Int_BinaryDiv
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:59:32.192397+00:00
-- url     : https://prove2.me/theorems/eaff704d-bad6-48ed-b312-724e4edd2ece
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.BinaryDiv — Polynomial-time reduction of signed binary integers
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.BinaryDiv` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   Reduce a signed binary integer modulo a binary natural and return the nonnegative residue.
--   The construction first computes `r = z.natAbs % q`. For a negative integer it returns
--   `(q - r) % q`; otherwise it returns `r`. This reuses binary natural division, subtraction
--   and the sign-magnitude interface, without enumerating the modulus or constructing a new machine.
--
--   The certificate is total: at modulus zero the result is `z.toNat`, matching Lean's integer
--   remainder convention followed by truncation at zero.
--
--   ### Main results
--
--   * `Turing.MultiTapeTM.ComputableInPolyTime.intBin_emodNat`: signed reduction with both
--     operands and the result encoded in binary.
--   * `Turing.MultiTapeTM.ComputableInPolyTime.intBin_emodNat'`: composition with computed inputs.
--
--   ### References
--
--   The proof uses Lean's `Int.emod_natAbs_of_nonneg` and `Int.emod_natAbs_of_neg` and the native
--   arithmetic certificates in `PolyTime/Int/Binary` and `PolyTime/Nat/BinaryDiv`.
--
--   **Contents.** The module is published as a whole: 3 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with library lemmas renamed back to their names in this Mathlib and a few proof steps adjusted; no statement is changed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Int_BinaryDiv`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Complexity/PolyTime/Int/BinaryDiv.lean

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Batteries.Tactic.Lint.Basic
public import Mathlib.Init
public import Mathlib.Tactic.Common
public import Definitions.Def_Cslib_254e30e_Tactic_GrindAttrs
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Int_Binary
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Nat_BinaryDiv
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_PolyTime
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Plain

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.BinaryDiv` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Polynomial-time reduction of signed binary integers

Reduce a signed binary integer modulo a binary natural and return the nonnegative residue.
The construction first computes `r = z.natAbs % q`. For a negative integer it returns
`(q - r) % q`; otherwise it returns `r`. This reuses binary natural division, subtraction
and the sign-magnitude interface, without enumerating the modulus or constructing a new machine.

The certificate is total: at modulus zero the result is `z.toNat`, matching Lean's integer
remainder convention followed by truncation at zero.

## Main results

* `Turing.MultiTapeTM.ComputableInPolyTime.intBin_emodNat`: signed reduction with both
  operands and the result encoded in binary.
* `Turing.MultiTapeTM.ComputableInPolyTime.intBin_emodNat'`: composition with computed inputs.

## References

The proof uses Lean's `Int.emod_natAbs_of_nonneg` and `Int.emod_natAbs_of_neg` and the native
arithmetic certificates in `PolyTime/Int/Binary` and `PolyTime/Nat/BinaryDiv`.
-/

@[expose] public section

namespace Turing.MultiTapeTM.ComputableInPolyTime

private theorem emodNat_eq (z : ℤ) (q : ℕ) :
    (z % (q : ℤ)).toNat =
      if z < 0 then (q - z.natAbs % q) % q else z.natAbs % q := by
  by_cases hz : z < 0
  · rw [if_pos hz]
    by_cases hq : q = 0
    · subst q
      simp only [Nat.cast_zero, Int.emod_zero, Nat.zero_sub, Nat.mod_zero]
      omega
    · rw [Int.emod_natAbs_of_neg hz hq]
      split_ifs with hdiv
      · simp [Int.emod_eq_zero_of_dvd hdiv]
      · have hrem : (z % (q : ℤ)).toNat < q := by
          have := Int.emod_lt_of_pos z (by omega : 0 < (q : ℤ))
          omega
        rw [Nat.sub_sub_self hrem.le, Nat.mod_eq_of_lt hrem]
  · rw [if_neg hz]
    exact (Int.emod_natAbs_of_nonneg (by omega : 0 ≤ z)).symm

/-- Reduce a signed binary integer modulo a binary natural. At modulus zero the result is
the integer truncated at zero; no positive-modulus hypothesis is required. -/
@[fun_prop]
theorem intBin_emodNat :
    ComputableInPolyTime (fun p : ℤ × ℕ => (p.1 % (p.2 : ℤ)).toNat)
      (encPair encIntBin encNat) encNat := by
  refine .of_tidy ?_
  have hsign := ComputableTidilyInPolyTime.intBin_isNeg.comp
    (ComputableTidilyInPolyTime.fst encIntBin encNat)
  have hmodulus := ComputableTidilyInPolyTime.snd encIntBin encNat
  have hremainder := ComputableTidilyInPolyTime.binary_mod.comp
    ((ComputableTidilyInPolyTime.intBin_natAbs.comp
      (ComputableTidilyInPolyTime.fst encIntBin encNat)).prod hmodulus)
  have h := hsign.ite'
    (ComputableTidilyInPolyTime.binary_mod.comp
      ((ComputableTidilyInPolyTime.binary_sub.comp (hmodulus.prod hremainder)).prod hmodulus))
    hremainder
  refine h.of_enc_eq fun p => congrArg encNat ?_
  simpa only [Function.comp_apply, decide_eq_true_eq] using emodNat_eq p.1 p.2

/-- Reduce computed signed integers by computed binary natural moduli, fixing the intermediate
encodings for proof search. -/
@[fun_prop]
theorem intBin_emodNat' {α : Type} {input : α ↪ List Bool} {value : α → ℤ} {modulus : α → ℕ}
    (hvalue : ComputableInPolyTime value input encIntBin)
    (hmodulus : ComputableInPolyTime modulus input encNat) :
    ComputableInPolyTime (fun a => (value a % (modulus a : ℤ)).toNat) input encNat :=
  intBin_emodNat.comp (hvalue.prod hmodulus)

end Turing.MultiTapeTM.ComputableInPolyTime


