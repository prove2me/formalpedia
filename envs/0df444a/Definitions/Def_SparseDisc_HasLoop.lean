-- Prove2me | Definitions.Def_SparseDisc_HasLoop
-- name    : SparseDisc_HasLoop
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:53:20.835885+00:00
-- url     : https://prove2.me/theorems/872fa9df-dbed-42fe-8c69-63fe129a09e0
-- title:
--   Set containing an $s$-loop
-- statement:
--   A set $A \subseteq \{\pm1\}^U$ **contains an $s$-loop** if it contains an antipodal $s$-path, an $s$-path $z_0, \dots, z_L$ in $A$ with $z_L = -z_0$.
-- source:
--   Zeng–Cao–Dai–Wang–Liao, Sparse Discrepancy Beyond Additive Functions: Acyclic, Bounded-Degree and Degenerate Sparsity Patterns, STOC 2027 submission (manuscript sha256 0f09ec60…25b81), Definition 2.9, p.14

import Mathlib
import Definitions.Def_SparseDisc_IsSPath

namespace SparseDisc

/-- `HasLoop s A`: the set `A` **contains an `s`-loop**, an antipodal `s`-path `z₀, …, z_L` in `A`
(`z_L = −z₀`) (Zeng–Cao–Dai–Wang–Liao, *Sparse Discrepancy Beyond Additive Functions*, STOC 2027
submission manuscript (sha256 0f09ec60…25b81), Definition 2.9, p.14; `U = ∅` as on p.29). -/
def HasLoop {U : Type} [Fintype U] (s : ℝ) (A : Set (Cube U)) : Prop :=
  ∃ (z : ℕ → Cube U) (L : ℕ), IsSPath s A z L ∧ z L = -(z 0)

end SparseDisc


