-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Combinators_Transducer_Copy
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Combinators_Transducer_Copy
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:38:17.649204+00:00
-- url     : https://prove2.me/theorems/89380c4c-5087-4404-8a7e-90f53a3cf5a1
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Combinators.Transducer.Copy — Copying states of a finite-state transducer
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Combinators.Transducer.Copy` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   A state that emits each input symbol unchanged, stays in that state, and emits nothing at
--   end of input copies every word. This rule applies to arbitrary alphabets and state types;
--   it is shared by the binary predecessor and the unary-magnitude signed-integer transducers.
--
--   ### Main results
--
--   * `Turing.MultiTapeTM.Transducer.run_eq_self`: a copying state preserves the input word.
--
--   **Contents.** The module is published as a whole: 1 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Combinators_Transducer_Copy`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Combinators/Transducer/Copy.lean

/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_KernelTransducer

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Combinators.Transducer.Copy` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Copying states of a finite-state transducer

A state that emits each input symbol unchanged, stays in that state, and emits nothing at
end of input copies every word. This rule applies to arbitrary alphabets and state types;
it is shared by the binary predecessor and the unary-magnitude signed-integer transducers.

## Main results

* `Turing.MultiTapeTM.Transducer.run_eq_self`: a copying state preserves the input word.
-/

namespace Turing.MultiTapeTM.Transducer

/-- A transducer started in a copying state preserves every word, provided that state emits
nothing at the end of the input. -/
public theorem run_eq_self {Symbol Q : Type*} (T : Transducer Symbol Q) (q : Q)
    (hstep : ∀ a, T.step q a = (q, [a])) (hfinal : T.final q = []) (w : List Symbol) :
    T.run q w = w := by
  induction w with
  | nil => exact hfinal
  | cons a w ih => simp only [run_cons, hstep, List.singleton_append, ih]

end Turing.MultiTapeTM.Transducer


