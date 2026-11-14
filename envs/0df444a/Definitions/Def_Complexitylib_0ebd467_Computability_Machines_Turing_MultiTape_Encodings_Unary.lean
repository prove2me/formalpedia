-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Unary
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Unary
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:42:45.294193+00:00
-- url     : https://prove2.me/theorems/07e0ae2c-7632-4374-b599-9e2968c32c97
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Encodings.Unary — Unary natural numbers
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Encodings.Unary` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   The encoding and its equation are moved unchanged from the former quantitative primitives.
--
--   **Contents.** The module is published as a whole: 2 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Unary`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Encodings/Unary.lean

/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: candidate

public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Words

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Encodings.Unary` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-! # Unary natural numbers

The encoding and its equation are moved unchanged from the former quantitative primitives.
-/

namespace Turing.MultiTapeTM

/-- Natural numbers in unary: `n` is encoded by `n` ones. -/
@[expose] public def encUnary : ℕ ↪ List Bool :=
  ⟨fun n => List.replicate n true, fun m n h => by simpa using congrArg List.length h⟩

@[simp]
public lemma encUnary_apply (n : ℕ) : encUnary n = List.replicate n true := rfl

end Turing.MultiTapeTM


