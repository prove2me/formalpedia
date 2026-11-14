-- Prove2me | Definitions.Def_Cslib_254e30e_Foundations_Data_Fin_Tuple
-- name    : Cslib_254e30e_Foundations_Data_Fin_Tuple
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:33:16.900764+00:00
-- url     : https://prove2.me/theorems/7d70a615-6ae0-4d9c-bdc2-897fe1921613
-- title:
--   Cslib.Foundations.Data.Fin.Tuple — Appending tuples
-- statement:
--   This is module `Cslib.Foundations.Data.Fin.Tuple` of [CSLib](https://github.com/leanprover/cslib) (Apache-2.0), at commit `254e30e`: part of its development of multi-tape Turing machines. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states its running-time bounds on these machines.
--
--   Lemmas about `Fin.append` not (yet) in Mathlib: the two parts of an appended tuple never overlap
--   and appending commutes with post-composition and with updating an entry on either side.
--
--   **Contents.** The module is published as a whole: 4 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Cslib_254e30e_Foundations_Data_Fin_Tuple`.
-- source:
--   https://github.com/leanprover/cslib/blob/254e30e6d4299c51323aaeaf5f51a4763b375d4a/Cslib/Foundations/Data/Fin/Tuple.lean

/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Batteries.Tactic.Lint.Basic
public import Mathlib.Init
public import Mathlib.Tactic.Common
public import Definitions.Def_Cslib_254e30e_Tactic_GrindAttrs
public import Mathlib.Data.Fin.Tuple.Basic

set_option autoImplicit true
set_option relaxedAutoImplicit true

/- Prove2me definition bundle for `Cslib.Foundations.Data.Fin.Tuple` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Appending tuples

Lemmas about `Fin.append` not (yet) in Mathlib: the two parts of an appended tuple never overlap
and appending commutes with post-composition and with updating an entry on either side.
-/

@[expose] public section

namespace Fin

variable {α β : Sort*} {m n : ℕ}

/-- The two parts of `Fin.append` never overlap. -/
theorem castAdd_ne_natAdd (i : Fin m) (j : Fin n) : castAdd n i ≠ natAdd m j :=
  Fin.ne_of_lt ((castAdd_lt n i).trans_le (Nat.le_add_right m j))

/-- Post-composition commutes with `Fin.append`. -/
theorem comp_append (f : α → β) (a : Fin m → α) (b : Fin n → α) :
    f ∘ append a b = append (f ∘ a) (f ∘ b) := by
  funext i
  cases i using addCases <;> simp

/-- Updating an entry of the left tuple is updating the appended tuple at `castAdd`. -/
theorem append_update_left (a : Fin m → α) (b : Fin n → α) (i : Fin m) (x : α) :
    append (Function.update a i x) b = Function.update (append a b) (castAdd n i) x := by
  funext l
  cases l using addCases with
  | left j => simp [Function.update_apply]
  | right j => simp [Function.update_of_ne (castAdd_ne_natAdd i j).symm]

/-- Updating an entry of the right tuple is updating the appended tuple at `natAdd`. -/
theorem append_update_right (a : Fin m → α) (b : Fin n → α) (i : Fin n) (x : α) :
    append a (Function.update b i x) = Function.update (append a b) (natAdd m i) x := by
  funext l
  cases l using addCases with
  | left j => simp [Function.update_of_ne (castAdd_ne_natAdd j i)]
  | right j => simp [Function.update_apply]

end Fin


