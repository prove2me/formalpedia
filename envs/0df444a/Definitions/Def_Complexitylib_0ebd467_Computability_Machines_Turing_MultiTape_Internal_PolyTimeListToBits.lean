-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_PolyTimeListToBits
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_PolyTimeListToBits
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:48:48.158281+00:00
-- url     : https://prove2.me/theorems/9465c211-fe39-4ecf-bece-608001791ffe
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListToBits — Direct conversion of framed Boolean lists to raw words
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListToBits` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   The canonical `ComputableInPolyTime.listToBits` certificate keeps its original public contract
--   and registration. Its direct proof prepends into a raw word with a reachable-prefix bound and
--   then reverses that word. The higher bit-string facade reexports this same declaration.
--
--   **Contents.** The module is published as a whole: 1 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_PolyTimeListToBits`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Internal/PolyTimeListToBits.lean

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
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_PolyTimeListPrimitives
import Mathlib.Data.List.Fold

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListToBits` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Direct conversion of framed Boolean lists to raw words

The canonical `ComputableInPolyTime.listToBits` certificate keeps its original public contract
and registration. Its direct proof prepends into a raw word with a reachable-prefix bound and
then reverses that word. The higher bit-string facade reexports this same declaration.
-/

@[expose] public section

namespace Turing.MultiTapeTM.ComputableInPolyTime

/-- Convert framed Boolean lists to raw words without changing their contents. -/
@[fun_prop]
theorem listToBits :
    ComputableInPolyTime (fun l => l) (encList encBool) encBits := by
  have hstep : ComputableInPolyTime (fun p : List Bool × Bool => p.2 :: p.1)
      (encPair encBits encBool) encBits :=
    ComputableInPolyTime.bitsCons (ComputableInPolyTime.snd encBits encBool)
      (ComputableInPolyTime.fst encBits encBool)
  have hfold := ComputableInPolyTime.foldl' (encA := encBool) (encL := encList encBool)
    (encB := encBits) (list := id) (init := fun _ => []) (step := fun acc bit => bit :: acc)
    ComputableInPolyTime.id' (ComputableInPolyTime.const []) hstep
    (B := fun l => (encList encBool l).length) .self (by
      intro l i _
      change ((l.take i).foldl (flip List.cons) []).length ≤ _
      rw [List.foldl_cons_nil, List.length_reverse]
      exact (List.length_take_le' _ _).trans
        (SizedListEncoding.length_le (encA := encBool) (encL := encList encBool) l))
  have h := ComputableInPolyTime.bitsReverse.comp hfold
  simpa only [Function.comp_def, List.reverse_foldl, id_eq] using h

end Turing.MultiTapeTM.ComputableInPolyTime


