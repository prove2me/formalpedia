-- Prove2me | Definitions.Def_ZZ_ProbeC
-- name    : ZZ_ProbeC
-- status  : Definition
-- author  : @WillR
-- created : 2026-09-26T13:36:53.827915+00:00
-- url     : https://prove2.me/theorems/40c3b625-7fc2-4d03-9db2-59415897ee3f
-- title:
--   probe C full region mod
-- statement:
--   probe

import Mathlib
import Definitions.Def_BraidsLinksMCG_ConfigSpace

open BraidsLinksMCG

namespace BraidsLinksMCG

/-!
# The two half-plane regions of the punctured plane, and their membership test

`leftRegion n` is the open half-plane `{z | z.re < n + 1}` with the punctures
`1, ..., n+1` removed, and `rightRegion n` is `{z | n + 1/2 < z.re}` with the same
punctures removed. Each is *defined* by its two defining conditions, so membership
is a single `Set.mem_setOf_eq` application after unfolding, with no range or
complement conversion anywhere.
-/

def leftRegion (n : ℕ) : Set ℂ :=
  {z : ℂ | z.re < (n : ℝ) + 1 ∧ ∀ j : Fin (n + 1), z ≠ ((j : ℕ) + 1 : ℂ)}

def rightRegion (n : ℕ) : Set ℂ :=
  {z : ℂ | (n : ℝ) + 1 / 2 < z.re ∧ ∀ j : Fin (n + 1), z ≠ ((j : ℕ) + 1 : ℂ)}

theorem leftRegion_mem_iff (n : ℕ) (z : ℂ) :
    z ∈ leftRegion n ↔
      z.re < (n : ℝ) + 1 ∧ (∀ j : Fin (n + 1), z ≠ ((j : ℕ) + 1 : ℂ)) := by
  -- The region `def` must be unfolded before the set-builder is visible: the remote
  -- reported the bare `Set.mem_setOf_eq` as "Type mismatch … `Set.mem_setOf_eq` has type
  -- `(?m.26 ∈ {y | ?m.27 y}) = ?m.27 ?m.26` but is expected to have type
  -- `z ∈ leftRegion n ↔ …`", i.e. the `def` was not reduced at the head of the goal.
  --
  -- `Set.mem_setOf_eq` is an `Eq` between propositions, while the goal is an `Iff`, so it
  -- cannot be applied directly. `show` restates the goal with the region unfolded; the
  -- resulting `Iff` between two definitionally equal propositions closes by `rfl`.
  --
  -- The bound variable is renamed from `z` to `w` deliberately. An earlier version reused
  -- `z` inside the `show` type ascription, which shadowed the theorem's own argument and
  -- produced "unexpected token 'theorem'; expected 'by' or 'from'", leaving the rest of the
  -- file unparsed. An even earlier version wrote
  -- `have h : z ∈ leftRegion n = (...)`, which makes Lean parse the `=` as a term of type
  -- `Set ℂ` applied to a `Prop` and was rejected with "has type `Prop` but is expected to
  -- have type `Set ℂ`".
  show z ∈ ({w : ℂ | w.re < (n : ℝ) + 1 ∧
      ∀ j : Fin (n + 1), w ≠ ((j : ℕ) + 1 : ℂ)} : Set ℂ) ↔ _
  rfl


theorem rightRegion_mem_iff (n : ℕ) (z : ℂ) :
    z ∈ rightRegion n ↔
      (n : ℝ) + 1 / 2 < z.re ∧ (∀ j : Fin (n + 1), z ≠ ((j : ℕ) + 1 : ℂ)) := by
  -- As in `leftRegion_mem_iff`: unfold the region `def`, then close the `Iff` by `rfl`.
  show z ∈ ({w : ℂ | (n : ℝ) + 1 / 2 < w.re ∧
      ∀ j : Fin (n + 1), w ≠ ((j : ℕ) + 1 : ℂ)} : Set ℂ) ↔ _
  rfl


end BraidsLinksMCG


