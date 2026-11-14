-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_WordEquality
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_WordEquality
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:32:41.0012+00:00
-- url     : https://prove2.me/theorems/6fdbb5f1-9bed-4869-a79a-b0b0be0e20c6
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Encodings.WordEquality — Word comparison by a left fold
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Encodings.WordEquality` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   The original comparison state and its all-word laws, independent of resource certificates.
--
--   **Contents.** The module is published as a whole: 3 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_WordEquality`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Encodings/WordEquality.lean

/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: candidate

public import Batteries.Tactic.Lint.Basic
public import Mathlib.Init
public import Mathlib.Tactic.Common
public import Definitions.Def_Cslib_254e30e_Tactic_GrindAttrs
public import Mathlib.Data.List.Basic

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Encodings.WordEquality` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-! # Word comparison by a left fold

The original comparison state and its all-word laws, independent of resource certificates.
-/

public section
namespace Turing.MultiTapeTM

namespace EqWords

/-- One step of comparing a word with `s.1`, the part of the other word still to be matched;
`s.2` records whether the words agree so far. -/
@[expose] public def step (s : List Bool × Bool) (b : Bool) : List Bool × Bool :=
  (s.1.tail, s.2 && !s.1.isEmpty && (s.1.headD false == b))

public lemma foldl_fst (l r : List Bool) (ok : Bool) :
    (l.foldl step (r, ok)).1 = r.drop l.length := by
  induction l generalizing r ok with
  | nil => rfl
  | cons b l ih =>
    cases r <;> simp [step, ih]

public lemma foldl_result (l r : List Bool) (ok : Bool) :
    ((l.foldl step (r, ok)).2 && (l.foldl step (r, ok)).1.isEmpty) = (ok && decide (l = r)) := by
  induction l generalizing r ok with
  | nil => cases r <;> simp
  | cons b l ih =>
    rw [List.foldl_cons, ih]
    cases r <;> grind [step]

end EqWords

end Turing.MultiTapeTM


