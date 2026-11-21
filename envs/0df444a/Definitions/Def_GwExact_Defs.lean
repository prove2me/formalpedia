-- Prove2me | Definitions.Def_GwExact_Defs
-- name    : GwExact_Defs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-20T15:05:30.342357+00:00
-- url     : https://prove2.me/theorems/be174087-0ef9-4f43-8a23-c171245991db
-- title:
--   Defs
-- statement:
--   Definitions and structural lemmas for Defs, from arhancanli and contributors's pinned Exact Gallai–van der Waerden numbers development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/arhancanli/quantavane-gw-exact/blob/8df720c8181ada4313da2c7a1aa04cb72854a9ec/GwExact/Defs.lean

module
public import Mathlib.Order.Lattice.Nat
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace GwExact
def IsGoodExactColouring (r l n : ℕ) (c : ℕ → Fin r) : Prop :=
  (∀ col : Fin r, ∃ x, 1 ≤ x ∧ x ≤ n ∧ c x = col) ∧
  (∀ x d : ℕ, 1 ≤ x → 1 ≤ d → x + 2 * d ≤ n →
    ¬ (c x ≠ c (x + d) ∧ c x ≠ c (x + 2 * d) ∧ c (x + d) ≠ c (x + 2 * d))) ∧
  (∀ x d : ℕ, 1 ≤ x → 1 ≤ d → x + (l - 1) * d ≤ n → ¬ ∀ j < l, c (x + j * d) = c x)
def GWProperty (r l m : ℕ) : Prop :=
  ∀ n ≥ m, ∀ c : ℕ → Fin r, ¬ IsGoodExactColouring r l n c
noncomputable def GW (r l : ℕ) : ℕ := sInf {m | GWProperty r l m}
end GwExact


