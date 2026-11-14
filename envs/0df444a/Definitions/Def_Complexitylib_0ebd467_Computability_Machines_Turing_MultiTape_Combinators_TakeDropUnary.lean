-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Combinators_TakeDropUnary
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Combinators_TakeDropUnary
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:52:30.504731+00:00
-- url     : https://prove2.me/theorems/67eecac3-1cf5-430e-928a-0809a96ed586
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Combinators.TakeDropUnary — Taking and dropping list elements in linear time
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Combinators.TakeDropUnary` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   Taking or dropping the first `n` elements of a list encoded by `Turing.MultiTapeTM.encList`, with
--   `n` in unary, has cost and output degree one. Both are computed by the one-tape machine
--   `Turing.MultiTapeTM.TakeDropUnary.toTM`, which copies the count to its work tape and then streams
--   the encoded list once, moving the work head at every element boundary. Folding over the count or
--   over the list would cost quadratic time.
--
--   ### Main results
--
--   * `Turing.MultiTapeTM.ComputableInDegree.takeUnary`: the first `n` elements.
--   * `Turing.MultiTapeTM.ComputableInDegree.dropUnary`: all but the first `n` elements.
--
--   **Contents.** The module is published as a whole: 3 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Combinators_TakeDropUnary`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Combinators/TakeDropUnary.lean

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_Lists
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_Degree_Bounds
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_KernelTakeDropUnary

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Combinators.TakeDropUnary` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Taking and dropping list elements in linear time

Taking or dropping the first `n` elements of a list encoded by `Turing.MultiTapeTM.encList`, with
`n` in unary, has cost and output degree one. Both are computed by the one-tape machine
`Turing.MultiTapeTM.TakeDropUnary.toTM`, which copies the count to its work tape and then streams
the encoded list once, moving the work head at every element boundary. Folding over the count or
over the list would cost quadratic time.

## Main results

* `Turing.MultiTapeTM.ComputableInDegree.takeUnary`: the first `n` elements.
* `Turing.MultiTapeTM.ComputableInDegree.dropUnary`: all but the first `n` elements.
-/

namespace Turing.MultiTapeTM.ComputableInDegree

variable {α : Type}

/-- Taking (`keep = true`) or dropping (`keep = false`) a unary number of elements has cost and
output degree one. -/
private theorem cut (keep : Bool) (enc : α ↪ List Bool) :
    ComputableInDegree (fun p : List α × ℕ => if keep then p.1.take p.2 else p.1.drop p.2)
      (encPair (encList enc) encUnary) (encList enc) 1 1 :=
  of_bounds ⟨5, fun p => by
      dsimp only
      rw [pow_one]
      omega⟩
    ⟨2, fun p => by
      have h := length_le_encPair_right (encList enc) encUnary p
      rw [encUnary_apply, List.length_replicate] at h
      dsimp only
      rw [pow_one]
      omega⟩
    (TakeDropUnary.computableInTimeAndSpace keep enc)

/-- Taking the first `n` elements, with `n` in unary, in linear time. -/
public theorem takeUnary (enc : α ↪ List Bool) :
    ComputableInDegree (fun p : List α × ℕ => p.1.take p.2)
      (encPair (encList enc) encUnary) (encList enc) 1 1 :=
  cut true enc

/-- Dropping the first `n` elements, with `n` in unary, in linear time. -/
public theorem dropUnary (enc : α ↪ List Bool) :
    ComputableInDegree (fun p : List α × ℕ => p.1.drop p.2)
      (encPair (encList enc) encUnary) (encList enc) 1 1 :=
  cut false enc

end Turing.MultiTapeTM.ComputableInDegree


