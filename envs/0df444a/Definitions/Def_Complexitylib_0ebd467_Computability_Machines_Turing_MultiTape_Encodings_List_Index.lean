-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_List_Index
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_List_Index
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:32:38.410195+00:00
-- url     : https://prove2.me/theorems/73b474f1-8f69-4e96-8a5e-d2bad81dc0ed
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Encodings.List.Index — The first-occurrence index fold
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Encodings.List.Index` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   Pure transition and invariant shared by the direct list certificate and its legacy client.
--
--   **Contents.** The module is published as a whole: 2 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_List_Index`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Encodings/List/Index.lean

/-
Copyright (c) 2026 Erik Demaine, Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Christian Reitwiessner, Samuel Schlesinger
-/
module
-- upstream: candidate

public import Batteries.Tactic.Lint.Basic
public import Mathlib.Init
public import Mathlib.Tactic.Common
public import Definitions.Def_Cslib_254e30e_Tactic_GrindAttrs
import Mathlib.Data.List.Basic

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Encodings.List.Index` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-! # The first-occurrence index fold

Pure transition and invariant shared by the direct list certificate and its legacy client.
-/

@[expose] public section
namespace Turing.MultiTapeTM.Internal.ListIndex
variable {α : Type*}

/-- Keep the first matching position, incrementing only while no match has appeared. -/
def idxStep [DecidableEq α] (v : α) (s : Bool × ℕ) (a : α) : Bool × ℕ :=
  if s.1 || decide (a = v) then (true, s.2) else (false, s.2 + 1)

/-- The original first-occurrence fold returns the starting count plus the first index. -/
theorem foldl_idxStep [DecidableEq α] (v : α) (l : List α) (s : Bool × ℕ) :
    (l.foldl (idxStep v) s).2 = s.2 + if s.1 then 0 else l.idxOf v := by
  induction l generalizing s with
  | nil => simp
  | cons a l ih =>
    rw [List.foldl_cons, ih]
    rcases s with ⟨b, n⟩
    cases b <;> by_cases ha : a = v <;>
      simp [idxStep, ha, Nat.add_comm, Nat.add_left_comm]

end Turing.MultiTapeTM.Internal.ListIndex


