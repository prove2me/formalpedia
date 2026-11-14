-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Foundations_Data_Fin_Tuple
-- name    : Complexitylib_0ebd467_Foundations_Data_Fin_Tuple
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:33:33.454953+00:00
-- url     : https://prove2.me/theorems/6647b6c4-1afc-49e9-b0d0-f28e13754ef2
-- title:
--   Complexity.Foundations.Data.Fin.Tuple — Appending constant tuples
-- statement:
--   This is module `Complexity.Foundations.Data.Fin.Tuple` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   The addition of Christian Reitwiessner's branch `crei/tidy-universal` (and of cslib PR #1112) to
--   `Cslib.Foundations.Data.Fin.Tuple`: appending constant tuples gives a constant tuple.
--
--   **Contents.** The module is published as a whole: 1 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Foundations_Data_Fin_Tuple`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Foundations/Data/Fin/Tuple.lean

/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: vendored crei:crei/tidy-universal @7f7c0696 (unsubmitted)
-- Also in cslib PR #1112 @0b9e55ce.

public import Definitions.Def_Cslib_254e30e_Foundations_Data_Fin_Tuple

/- Prove2me definition bundle for `Complexity.Foundations.Data.Fin.Tuple` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Appending constant tuples

The addition of Christian Reitwiessner's branch `crei/tidy-universal` (and of cslib PR #1112) to
`Cslib.Foundations.Data.Fin.Tuple`: appending constant tuples gives a constant tuple.
-/

@[expose] public section

namespace Fin

variable {α : Sort*} {m n : ℕ}

/-- Appending two constant tuples gives a constant tuple. -/
theorem append_const (x : α) : append (fun _ : Fin m => x) (fun _ : Fin n => x) = fun _ => x :=
  append_castAdd_natAdd (f := fun _ => x)

end Fin


