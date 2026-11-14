-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_PolyTimeBinaryDivision
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_PolyTimeBinaryDivision
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:51:12.078454+00:00
-- url     : https://prove2.me/theorems/ec776fb0-647d-482d-bfd2-9fb00f67122f
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeBinaryDivision — Direct certificates for the existing binary subtraction and division algorithms
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeBinaryDivision` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   The word programs and their arithmetic laws are unchanged. Subtraction reuses the shared charged
--   schoolbook certificate. Division uses direct bit, pair, append and full-prefix fold primitives,
--   retaining binary magnitudes throughout.
--
--   **Contents.** The module is published as a whole: 5 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_PolyTimeBinaryDivision`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Internal/PolyTimeBinaryDivision.lean

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Karn Seth
-/

module
-- upstream: candidate

public import Batteries.Tactic.Lint.Basic
public import Mathlib.Init
public import Mathlib.Tactic.Common
public import Definitions.Def_Cslib_254e30e_Tactic_GrindAttrs
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Nat_Subtraction
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Nat_Division
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_PolyTimeBinaryPrimitives
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_BinaryComparison
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_PolyTimeListMap
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Decoder_Nat

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeBinaryDivision` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Direct certificates for the existing binary subtraction and division algorithms

The word programs and their arithmetic laws are unchanged. Subtraction reuses the shared charged
schoolbook certificate. Division uses direct bit, pair, append and full-prefix fold primitives,
retaining binary magnitudes throughout.
-/

@[expose] public section
namespace Turing.MultiTapeTM.ComputableInPolyTime

/-- Truncated binary subtraction, reusing the shared charged schoolbook certificate.
The quantitative interface takes the subtrahend first, so swap the two computed operands. -/
theorem binary_sub : ComputableInPolyTime (fun p : ℕ × ℕ => p.1 - p.2)
    (encPair encNat encNat) encNat := by
  have hsub := ComputableInO.natSub.computableInPolyTime
    (PolyBounded.of_forall_le 1 2 (fun _ => by simp))
    (PolyBounded.of_forall_le 1 1 (fun _ => by simp))
  exact hsub.comp ((snd encNat encNat).prod (fst encNat encNat))

private theorem divModStep_polyTime :
    ComputableInPolyTime (fun p : (ℕ × (ℕ × ℕ)) × Bool =>
      BinaryDiv.divModStep p.1.1 p.1.2 p.2)
      (encPair (encPair encNat (encPair encNat encNat)) encBool) (encPair encNat encNat) := by
  have hs := fst (encPair encNat (encPair encNat encNat)) encBool
  have hb := hs.fst'
  have hq := hs.snd'.fst'
  have hr := hs.snd'.snd'
  have hd := (of_finite (encIn := encBool) (encOut := encNat)
    fun bit : Bool => if bit then 1 else 0).comp
      (snd (encPair encNat (encPair encNat encNat)) encBool)
  have hr' := binary_add.comp ((binary_add.comp (hr.prod hr)).prod hd)
  have hq' := binary_add.comp (hq.prod hq)
  have hz : ComputableInPolyTime
      (fun p : (ℕ × (ℕ × ℕ)) × Bool => decide (p.1.1 = 0))
      (encPair (encPair encNat (encPair encNat encNat)) encBool) encBool := by
    convert binary_le.comp (hb.prod (const 0)) using 1
    funext p
    simp
  have hle := binary_le.comp (hb.prod hr')
  have hfit := (binary_add.comp (hq'.prod (const 1))).prod
    (binary_sub.comp (hr'.prod hb))
  have h := hz.ite ((const 0).prod hr') (hle.ite hfit (hq'.prod hr'))
  convert h using 1
  funext p
  simp only [BinaryDiv.divModStep, Function.comp_def, two_mul, decide_eq_true_eq]

/-- Quotient and remainder by the original shift-and-subtract binary long division.
The zero-divisor branch is retained; both outputs stay binary. -/
theorem binary_divMod : ComputableInPolyTime (fun p : ℕ × ℕ => (p.1 / p.2, p.1 % p.2))
    (encPair encNat encNat) (encPair encNat encNat) := by
  have hbits : ComputableInPolyTime Nat.bits encNat encBits := of_eq fun _ => rfl
  have hlist := bitsReverse.comp (hbits.comp (fst encNat encNat))
  have hfold := foldlWith (encP := encNat) (encA := encBool) (encL := encBits)
    (encB := encPair encNat encNat) (par := Prod.snd) (list := fun p : ℕ × ℕ => p.1.bits.reverse)
    (init := fun _ => (0, 0)) (step := BinaryDiv.divModStep)
    (snd encNat encNat) hlist (const (0, 0)) divModStep_polyTime
    (B := fun p => 3 * (encPair encNat encNat p).length + 1)
    (((PolyBounded.const 3).mul .self).add (.const 1)) (by
      intro p i _
      have hlen := BinaryDiv.length_encPair_foldl_divModStep_le p.2 (p.1.bits.reverse.take i)
      have htake : (p.1.bits.reverse.take i).length ≤ (encPair encNat encNat p).length := by
        calc (p.1.bits.reverse.take i).length
            ≤ p.1.bits.reverse.length := List.length_take_le' _ _
          _ = (encNat p.1).length := by simp
          _ ≤ (encPair encNat encNat p).length := length_le_encPair_left encNat encNat p
      omega)
  simpa only [BinaryDiv.divMod_eq] using hfold

/-- Binary quotient, with `a / 0 = 0`. This named rule adds no encoding-search alternative. -/
theorem binary_div : ComputableInPolyTime (fun p : ℕ × ℕ => p.1 / p.2)
    (encPair encNat encNat) encNat := binary_divMod.fst'

/-- Binary remainder, with `a % 0 = a`. This named rule adds no encoding-search alternative. -/
theorem binary_mod : ComputableInPolyTime (fun p : ℕ × ℕ => p.1 % p.2)
    (encPair encNat encNat) encNat := binary_divMod.snd'

end Turing.MultiTapeTM.ComputableInPolyTime


