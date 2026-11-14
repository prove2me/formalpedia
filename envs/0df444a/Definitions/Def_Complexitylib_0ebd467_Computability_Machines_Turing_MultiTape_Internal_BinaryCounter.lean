-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_BinaryCounter
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_BinaryCounter
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:32:40.586454+00:00
-- url     : https://prove2.me/theorems/e43c3f23-f920-47ad-a987-9b9a09d3b521
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Internal.BinaryCounter — Pure binary-counted iteration states
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Internal.BinaryCounter` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   The existing counter transition, iteration law and arithmetic bound are moved unchanged from the
--   legacy binary calculus. They store a binary counter with the current state, not a unary list.
--
--   **Contents.** The module is published as a whole: 5 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_BinaryCounter`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Internal/BinaryCounter.lean

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
public import Mathlib.Data.Nat.Basic
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Data.Nat.SuccPred
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Internal.BinaryCounter` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-! # Pure binary-counted iteration states

The existing counter transition, iteration law and arithmetic bound are moved unchanged from the
legacy binary calculus. They store a binary counter with the current state, not a unary list.
-/

public section
namespace Turing.MultiTapeTM.Internal.BinaryCounter

variable {β : Type} [Inhabited β]

/-- A round of the counted iteration: stop at zero, otherwise count down and apply `step`. -/
@[expose] public def countStep (step : β → β) : Option (ℕ × β) → Option (ℕ × β)
  | some (i + 1, b) => some (i, step b)
  | _ => none

lemma countStep_eq (step : β → β) (o : Option (ℕ × β)) : countStep step o =
    if o.isSome && !decide ((o.getD default).1 = 0) then
      some ((o.getD default).1 - 1, step (o.getD default).2) else none := by
  rcases o with _ | ⟨_ | i, b⟩ <;> rfl

omit [Inhabited β] in
lemma iterate_countStep (step : β → β) (t : ℕ) (b : β) {k : ℕ} (hk : k ≤ t) :
    (countStep step)^[k] (some (t, b)) = some (t - k, step^[k] b) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih (by omega), show t - k = t - (k + 1) + 1 by omega,
      countStep, Function.iterate_succ_apply']

lemma sum_le {c₀ c₁ k k' A M X Y : ℕ} (hX : X ≤ k * (M + 1)) (hY : Y ≤ c₀ * (A + 1)) :
    c₀ * (A + 1) + X + c₁ * (Y + 1) ≤ (c₀ + c₁ * (c₀ + 1) + k + k') * (A + M + 1) := by
  have h₁ : c₁ * (Y + 1) ≤ c₁ * (c₀ + 1) * (A + M + 1) :=
    calc c₁ * (Y + 1) ≤ c₁ * (c₀ * (A + 1) + 1) := Nat.mul_le_mul_left _ (by omega)
      _ ≤ c₁ * ((c₀ + 1) * (A + M + 1)) := Nat.mul_le_mul_left _ (by nlinarith)
      _ = _ := by ring
  have h₂ : X ≤ k * (A + M + 1) := hX.trans (Nat.mul_le_mul_left _ (by omega))
  have h₃ : c₀ * (A + 1) ≤ c₀ * (A + M + 1) := Nat.mul_le_mul_left _ (by omega)
  have : (c₀ + c₁ * (c₀ + 1) + k + k') * (A + M + 1) = c₀ * (A + M + 1) +
      c₁ * (c₀ + 1) * (A + M + 1) + k * (A + M + 1) + k' * (A + M + 1) := by ring
  omega

theorem iterate_sub_one (k n : ℕ) : (· - 1)^[k] n = n - k := Nat.pred_iterate n k

end Turing.MultiTapeTM.Internal.BinaryCounter


