-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_PolyTimeBinaryPrimitives
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_PolyTimeBinaryPrimitives
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:49:11.272654+00:00
-- url     : https://prove2.me/theorems/10c7591b-cfc6-4ba6-a394-6472dc701867
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeBinaryPrimitives — Direct polynomial-time binary arithmetic
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeBinaryPrimitives` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   Addition and comparison are the linear zip-transducer certificates of `BinaryAddition` and
--   `BinaryComparison`.
--   Multiplication weakens the cubic-time schoolbook certificate `ComputableInO.natMul`.
--
--   **Contents.** The module is published as a whole: 5 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_PolyTimeBinaryPrimitives`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Internal/PolyTimeBinaryPrimitives.lean

/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger, Karn Seth
-/
module
-- upstream: candidate

public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Nat_Arithmetic
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_PolyTimeNatFrontends
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_EqualityPrimitives
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_DegreeClosure
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_BinaryAddition
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_BinaryComparison

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeBinaryPrimitives` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Direct polynomial-time binary arithmetic

Addition and comparison are the linear zip-transducer certificates of `BinaryAddition` and
`BinaryComparison`.
Multiplication weakens the cubic-time schoolbook certificate `ComputableInO.natMul`.
-/

@[expose] public section
namespace Turing.MultiTapeTM
open Cslib

namespace ComputableInPolyTime

/-- Addition of binary naturals, from the linear zip-transducer certificate
`Turing.MultiTapeTM.computableInTimeAndSpace_natAdd`.
Compose this certificate with the producers' `.prod` certificate. Global automatic addition
remains separate from this named rule, since an unconstrained intermediate encoding can select
a binary branch where a surrounding computation needs a unary size. -/
theorem binary_add : ComputableInPolyTime (fun p : ℕ × ℕ => p.1 + p.2)
    (encPair encNat encNat) encNat :=
  ComputableInO.natAdd.computableInPolyTime
    (PolyBounded.of_forall_le 1 2 (fun _ => by simp))
    (PolyBounded.of_forall_le 1 1 (fun _ => by simp))

/-- Strict comparison of binary naturals, from the linear zip-transducer certificate
`Turing.MultiTapeTM.computableInTimeAndSpace_natLt`. -/
@[fun_prop]
theorem binary_lt : ComputableInPolyTime (fun p : ℕ × ℕ => decide (p.1 < p.2))
    (encPair encNat encNat) encBool :=
  (ComputableInO.of_linear ComputableInDegree.natLt).computableInPolyTime
    (PolyBounded.of_forall_le 1 1 (fun _ => by simp))
    (PolyBounded.of_forall_le 1 1 (fun _ => by simp))

/-- Multiply computed binary values, fixing their intermediate encodings for proof search. -/
theorem binary_mul' {α : Type} {input : α ↪ List Bool} {left right : α → ℕ}
    (hleft : ComputableInPolyTime left input encNat)
    (hright : ComputableInPolyTime right input encNat) :
    ComputableInPolyTime (fun a => left a * right a) input encNat :=
  (ComputableInO.natMul.computableInPolyTime (PolyBounded.of_forall_le 1 3 fun _ => by simp)
    (PolyBounded.of_forall_le 1 1 fun _ => by simp)).comp (hleft.prod hright)

/-- Non-strict binary comparison, from the linear zip-transducer certificate
`Turing.MultiTapeTM.computableInTimeAndSpace_natLe`. Automatic composition uses the
computed-operand rule `binary_le'`. -/
theorem binary_le : ComputableInPolyTime (fun p : ℕ × ℕ => decide (p.1 ≤ p.2))
    (encPair encNat encNat) encBool :=
  (ComputableInO.of_linear ComputableInDegree.natLe).computableInPolyTime
    (PolyBounded.of_forall_le 1 1 (fun _ => by simp))
    (PolyBounded.of_forall_le 1 1 (fun _ => by simp))

/-- Compare two binary naturals computed uniformly from the same encoded input. -/
@[fun_prop]
theorem binary_le' {α : Type} {input : α ↪ List Bool} {left right : α → ℕ}
    (hleft : ComputableInPolyTime left input encNat)
    (hright : ComputableInPolyTime right input encNat) :
    ComputableInPolyTime (fun a => decide (left a ≤ right a)) input encBool :=
  binary_le.comp (hleft.prod hright)

end ComputableInPolyTime
end Turing.MultiTapeTM


