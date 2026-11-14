-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Combinators_Transducer
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Combinators_Transducer
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:38:19.497612+00:00
-- url     : https://prove2.me/theorems/e2f70fcf-9cd2-4388-a336-3eebf365c997
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Combinators.Transducer — Finite-state transducers
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Combinators.Transducer` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   A finite-state transducer reads its input once from left to right. In state `q`, on the symbol
--   `a`, it moves to state `(τ.step q a).1` and emits the word `(τ.step q a).2`; at the end of the
--   input it emits `τ.final q`. Every emitted word has length at most two.
--
--   `τ.toTM` runs a transducer as a Turing machine without work tapes, so every function computed by a
--   transducer is tidily computable in linear time and zero space.
--
--   ### Main definitions
--
--   * `Turing.MultiTapeTM.Transducer`: finite-state transducers.
--   * `Turing.MultiTapeTM.Transducer.run`: the word a transducer emits on a word.
--   * `Turing.MultiTapeTM.Transducer.toTM`: the transducer as a machine without work tapes.
--
--   ### Main results
--
--   * `Turing.MultiTapeTM.Transducer.computesInTimeAndSpace_toTM`: `τ.toTM` emits `τ.run τ.q₀ w` on
--     `w` within `2 * w.length + 3` steps and zero space.
--   * `Turing.MultiTapeTM.Transducer.computableTidilyInTimeAndSpace`: a function computed by a
--     transducer with finitely many states is tidily computable in linear time and zero space.
--
--   **Contents.** The module is published as a whole: 1 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Combinators_Transducer`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Combinators/Transducer.lean

/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

-- upstream: vendored crei:crei/tidy-universal @7f7c0696 (unsubmitted)

public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_KernelTransducer
public import Mathlib.Data.Finite.Prod
public import Mathlib.Data.Fintype.Option
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Combinators_TidyZeroSpace
import Mathlib.Data.Finite.Sum

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Combinators.Transducer` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Finite-state transducers

A finite-state transducer reads its input once from left to right. In state `q`, on the symbol
`a`, it moves to state `(τ.step q a).1` and emits the word `(τ.step q a).2`; at the end of the
input it emits `τ.final q`. Every emitted word has length at most two.

`τ.toTM` runs a transducer as a Turing machine without work tapes, so every function computed by a
transducer is tidily computable in linear time and zero space.

## Main definitions

* `Turing.MultiTapeTM.Transducer`: finite-state transducers.
* `Turing.MultiTapeTM.Transducer.run`: the word a transducer emits on a word.
* `Turing.MultiTapeTM.Transducer.toTM`: the transducer as a machine without work tapes.

## Main results

* `Turing.MultiTapeTM.Transducer.computesInTimeAndSpace_toTM`: `τ.toTM` emits `τ.run τ.q₀ w` on
  `w` within `2 * w.length + 3` steps and zero space.
* `Turing.MultiTapeTM.Transducer.computableTidilyInTimeAndSpace`: a function computed by a
  transducer with finitely many states is tidily computable in linear time and zero space.
-/

namespace Turing.MultiTapeTM

namespace Transducer

/-- A function computed by a transducer with finitely many states is tidily computable in linear
time and zero space. -/
public theorem computableTidilyInTimeAndSpace {Q : Type} [Finite Q] (τ : Transducer Bool Q)
    {α β : Type*} {encIn : α ↪ List Bool} {encOut : β ↪ List Bool} {f : α → β}
    (hf : ∀ a, encOut (f a) = τ.run τ.q₀ (encIn a)) :
    ComputableTidilyInTimeAndSpace f encIn encOut (fun a => 4 * (encIn a).length + 8)
      (fun _ => 0) :=
  ⟨0, _, inferInstance, τ.toTM.seq (rewindInput Bool), fun a =>
    hf a ▸ τ.computesTidily (encIn a)⟩

end Transducer

end Turing.MultiTapeTM


