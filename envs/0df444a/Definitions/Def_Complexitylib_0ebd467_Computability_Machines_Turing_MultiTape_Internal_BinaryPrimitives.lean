-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_BinaryPrimitives
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_BinaryPrimitives
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:46:37.010241+00:00
-- url     : https://prove2.me/theorems/311fbf53-fe14-400b-bf16-b61229eedf73
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Internal.BinaryPrimitives — Direct binary counter resource certificates
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Internal.BinaryPrimitives` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   The successor, predecessor and zero test certificates here are weakenings of the streaming
--   transducer certificates `computableInTimeAndSpace_succ`, `computableInTimeAndSpace_pred` and
--   `computableInTimeAndSpace_isZero`.
--
--   ### Main results
--
--   * `ComputableInO.natSucc`, `ComputableInO.natPred`: binary counters within the quadratic clock
--     and linear charged workspace used by their clients.
--   * `ComputableInO.natIsZero`: linear zero testing.
--
--   **Contents.** The module is published as a whole: 3 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_BinaryPrimitives`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Internal/BinaryPrimitives.lean

/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_OLoops
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Nat
import Mathlib.Tactic.Linarith

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Internal.BinaryPrimitives` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Direct binary counter resource certificates

The successor, predecessor and zero test certificates here are weakenings of the streaming
transducer certificates `computableInTimeAndSpace_succ`, `computableInTimeAndSpace_pred` and
`computableInTimeAndSpace_isZero`.

## Main results

* `ComputableInO.natSucc`, `ComputableInO.natPred`: binary counters within the quadratic clock
  and linear charged workspace used by their clients.
* `ComputableInO.natIsZero`: linear zero testing.
-/

@[expose] public section
namespace Turing.MultiTapeTM

namespace ComputableInO

/-- Binary successor within the quadratic clock and linear charged workspace used by its
clients, weakened from the linear-time, zero-work-space transducer certificate
`computableInTimeAndSpace_succ`. -/
theorem natSucc :
    ComputableInO (· + 1) encNat encNat (fun n => ((encNat n).length + 1) ^ 2)
      (fun n => (encNat n).length + 1) :=
  (of_linear .natSucc).mono_le (fun n => by simp only [encNat_apply]; nlinarith) fun _ => by omega

/-- Binary predecessor within the quadratic clock and linear charged workspace used by its
clients, weakened from the linear-time, zero-work-space transducer certificate
`computableInTimeAndSpace_pred`. -/
theorem natPred :
    ComputableInO (· - 1) encNat encNat (fun n => ((encNat n).length + 1) ^ 2)
      (fun n => (encNat n).length + 1) :=
  (of_linear .natPred).mono_le (fun n => by simp only [encNat_apply]; nlinarith) fun _ => by omega

/-- Zero testing is linear in both resources, weakened from the transducer certificate
`computableInTimeAndSpace_isZero`; the output charge remains explicit. -/
theorem natIsZero :
    ComputableInO (fun n => decide (n = 0)) encNat encBool
      (fun n => (encNat n).length) (fun n => (encNat n).length) :=
  of_linear .natIsZero

end ComputableInO
end Turing.MultiTapeTM


