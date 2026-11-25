-- Prove2me | Definitions.Def_Kac_Defs
-- name    : Kac_Defs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T12:57:56.424435+00:00
-- url     : https://prove2.me/theorems/af7f8d4f-71ac-557a-abd1-1490ed05b062
-- title:
--   Defs
-- statement:
--   Definitions and structural lemmas for Defs, from Zayn Blore (zblore/kac-lean; see pinned Apache-2.0 LICENSE and source headers)'s pinned Kac's return-time formula for measure-preserving maps development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/zblore/kac-lean/blob/bfeb867d5a9b469cb11139c296e9bd41706e0992/Kac/Defs.lean

module
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Data.ENat.Basic
set_option autoImplicit false
@[expose] public section
@[expose] public section
namespace Kac
open Classical in
/-- The first return time of `x` to `A` under `f`: the least `n ≥ 1` with `f^[n] x ∈ A`, and `⊤`
if there is none (for `x ∉ A`, the first hitting time at a time `n ≥ 1`). It is `ℕ∞`-valued so
that a point that never returns has infinite return time. -/
noncomputable def returnTime {α : Type*} (f : α → α) (A : Set α) (x : α) : ℕ∞ :=
  if h : ∃ n : ℕ, 1 ≤ n ∧ f^[n] x ∈ A then (Nat.find h : ℕ∞) else ⊤
end Kac


