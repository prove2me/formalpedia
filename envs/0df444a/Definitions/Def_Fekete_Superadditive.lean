-- Prove2me | Definitions.Def_Fekete_Superadditive
-- name    : Fekete_Superadditive
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T19:25:37.063955+00:00
-- url     : https://prove2.me/theorems/2624367c-754a-5826-8e68-80361fad33d5
-- title:
--   Superadditive
-- statement:
--   Definitions and structural lemmas for Superadditive, from Brian Sanders (Egly443/lean-fekete; see pinned Apache-2.0 LICENSE and source headers)'s pinned Nearly subadditive sequences and Fekete's lemma beyond Mathlib development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Egly443/lean-fekete/blob/5faa67a2cbcf0d670bf2b8353336bab5818d6026/Fekete/Superadditive.lean

module
public import Mathlib.Analysis.Subadditive
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
set_option autoImplicit true
@[expose] public section
@[expose] public section
noncomputable section
open Filter Set
open scoped Topology
@[to_additive Superadditive /-- A sequence is superadditive if it satisfies the inequality
`u m + u n ≤ u (m + n)` for all `m, n`. -/]
def Supermultiplicative {α β : Type*} [Add α] [Mul β] [LE β] (u : α → β) : Prop :=
  ∀ m n, u m * u n ≤ u (m + n)
namespace Superadditive
variable {u : ℕ → ℝ} (h : Superadditive u)
@[irreducible]
protected def lim (u : ℕ → ℝ) : ℝ :=
  sSup ((fun n : ℕ ↦ u n / n) '' Ici 1)
end Superadditive
namespace Supermultiplicative
variable {u : ℕ → ℝ}
@[irreducible]
protected def lim (u : ℕ → ℝ) : ℝ :=
  sSup ((fun n : ℕ ↦ u n ^ (n : ℝ)⁻¹) '' Ici 1)
end Supermultiplicative


