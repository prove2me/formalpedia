-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Length
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Length
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:55:50.559382+00:00
-- url     : https://prove2.me/theorems/1355215a-402d-41ff-8ec3-cbf9c016f854
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Length — Binary list length in polynomial time
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Length` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   `Turing.MultiTapeTM.ComputableTidilyInPolyTime.length_list` computes the length of a framed list in
--   unary (`encUnary`), the representation required by bounded loops and `List.range`. Verifiers and
--   reductions that compare a list length against a binary parameter or add it to binary wire and
--   vertex indices instead need the length in the binary natural encoding `encNat`. Composing
--   `length_list` with `unary_to_binary` provides plain rules for `fun_prop` and `polytime`.
--
--   ### Main results
--
--   * `Turing.MultiTapeTM.ComputableInPolyTime.length_list_binary`: the length of a framed list in
--     the binary encoding `encNat`.
--   * `Turing.MultiTapeTM.ComputableInPolyTime.length_list_binary'`: the binary length of a computed
--     framed list, fixing the intermediate list encoding for proof search.
--
--   **Contents.** The module is published as a whole: 2 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Length`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Complexity/PolyTime/Length.lean

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_List
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Nat
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Plain
public import Definitions.Def_Complexitylib_0ebd467_Tactic_PolyTime_Init

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Length` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Binary list length in polynomial time

`Turing.MultiTapeTM.ComputableTidilyInPolyTime.length_list` computes the length of a framed list in
unary (`encUnary`), the representation required by bounded loops and `List.range`. Verifiers and
reductions that compare a list length against a binary parameter or add it to binary wire and
vertex indices instead need the length in the binary natural encoding `encNat`. Composing
`length_list` with `unary_to_binary` provides plain rules for `fun_prop` and `polytime`.

## Main results

* `Turing.MultiTapeTM.ComputableInPolyTime.length_list_binary`: the length of a framed list in
  the binary encoding `encNat`.
* `Turing.MultiTapeTM.ComputableInPolyTime.length_list_binary'`: the binary length of a computed
  framed list, fixing the intermediate list encoding for proof search.
-/

public section

namespace Turing.MultiTapeTM.ComputableInPolyTime

/-- Length of a framed list in binary (`encNat`); the element encoding is inferred from the list
encoding. -/
@[fun_prop, aesop safe -30 apply (rule_sets := [PolyTime])]
theorem length_list_binary {α : Type} (enc : α ↪ List Bool) :
    ComputableInPolyTime (fun l : List α => l.length) (encList enc) encNat :=
  .of_tidy (ComputableTidilyInPolyTime.unary_to_binary.comp (.length_list enc))

/-- Length of a computed framed list in binary (`encNat`), fixing the intermediate list encoding for
proof search. -/
@[fun_prop, aesop safe -30 apply (rule_sets := [PolyTime])]
theorem length_list_binary' {α β : Type} {input : α ↪ List Bool} {enc : β ↪ List Bool}
    {list : α → List β} (hlist : ComputableInPolyTime list input (encList enc)) :
    ComputableInPolyTime (fun a => (list a).length) input encNat :=
  (length_list_binary enc).comp hlist

end Turing.MultiTapeTM.ComputableInPolyTime


