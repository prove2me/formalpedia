-- Prove2me | Definitions.Def_NisanRonen_Rounding_units
-- name    : NisanRonen_Rounding_units
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:17:35.648986+00:00
-- url     : https://prove2.me/theorems/383877a6-4cf1-4035-bf83-783119605235
-- title:
--   The rounded instance in $\delta$-units
-- statement:
--   For a grid step $\delta > 0$ and a matrix $d = (d^i_j)$ of declared times with positive entries, the **rounded instance in $\delta$-units** is the list of the $k$ task columns, column $j$ being the vector of natural numbers
--
--   $$
--   \left( \left\lceil d^1_j / \delta \right\rceil, \dots, \left\lceil d^n_j / \delta \right\rceil \right).
--   $$
--
--   Multiplying by $\delta$ gives the rounded entries $\hat d^i_j$. This is the input of the rounding algorithm, which "exactly solves this rounded problem".
--
--   **Formalization Note** The columns form a `List (Fin n → ℕ)`; negative ceilings would be truncated to $0$ by `Int.toNat`, but the entries used are at least $a > 0$. Since the allocation algorithm sees only this list, the allocation computed from $d$ equals the one computed from $\hat d$.
-- source:
--   Nisan, Ronen, Algorithmic Mechanism Design, Games and Economic Behavior 35 (2001) 166–196, doi:10.1006/game.1999.0790, p. 192 (PDF p. 27): "The entries t^i_j are first rounded up to integer multiples of δ … It then exactly solves this rounded problem"

import Mathlib

namespace NisanRonen.Rounding

/-- **The rounded instance in δ-units** (the input of the rounding algorithm, Nisan, Ronen, Algorithmic Mechanism Design, Games and Economic Behavior 35 (2001),
p. 192: "The entries t^i_j are first rounded up to integer multiples of δ … It then exactly
solves this rounded problem"). For a declaration matrix `d`, `units δ d` is the list of the
`k` task columns, column `j` being the vector `i ↦ ⌈d i j / δ⌉` of natural numbers, so that
`δ · (units δ d)[j] i` is the rounded entry `roundUp δ (d i j)`.

**Formalization Note** `Int.toNat` truncates negative ceilings to `0`; it is only applied to
positive entries (`d i j ≥ a > 0`), where it is exact. Because the allocation rule reads only
this list, the allocation computed from `d` equals the one computed from the rounded `d̂`
(`x(t) = x(t̂)`, Definition 34). -/
noncomputable def units {n k : ℕ} (δ : ℝ) (d : Fin n → Fin k → ℝ) : List (Fin n → ℕ) :=
  List.ofFn fun j : Fin k => fun i : Fin n => (⌈d i j / δ⌉).toNat

end NisanRonen.Rounding


