-- Prove2me | Definitions.Def_MemQueryFeas_advance
-- name    : MemQueryFeas_advance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:33:45.776507+00:00
-- url     : https://prove2.me/theorems/02d91074-21f1-4c1a-913f-1a7c5b60b4c0
-- title:
--   Leaf update of the transform oracle
-- statement:
--   Algorithm 4, line 3: while the current leaf's path oracle answers Success on the query and the last leaf has not been exceeded, move to the next leaf. Starting from the $n$-th leaf, the result is the first leaf index $m\ge n$ whose path oracle does not answer Success on $x$, or $N_1\cdots N_P$ (past the last leaf) if there is none.
-- source:
--   Yu–Blanchard, Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems, preprint (Nov. 3, 2026), Algorithm 4, line 3, p.9 (PDF p.10)

import Mathlib
import Definitions.Def_MemQueryFeas_Vec
import Definitions.Def_MemQueryFeas_leafOf
import Definitions.Def_MemQueryFeas_numLeaves

namespace MemQueryFeas

open Classical in
/-- **The leaf update of Algorithm 4, line 3.** Yu–Blanchard, *Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems*, preprint (Nov. 3, 2026), Algorithm 4, line 3, p.9 (PDF p.10): "while
`O_ℓ(x_t) = Success` and `ℓ ≤lex (N_1, …, N_P)` do Update `ℓ ← Succ(ℓ)`".

With leaves numbered lexicographically (`leafOf`), `advance O N P n x` is the first index `m ≥ n`
with `m < N_1⋯N_P` and `O_{leaf m}(x) ≠ Success`; if there is none (every remaining leaf answers
Success), it is `N_1⋯N_P`, meaning that the last leaf has been exhausted.

**Formalization Note.** `O ℓ x` is the path oracle of leaf `ℓ` (`none` = Success). -/
noncomputable def advance {d : ℕ} (O : List ℕ → Vec d → Option (Vec d)) (N : ℕ → ℕ) (P : ℕ)
    (n : ℕ) (x : Vec d) : ℕ :=
  if h : ∃ m, n ≤ m ∧ m < numLeaves N P ∧ O (leafOf N P m) x ≠ none then Nat.find h
  else numLeaves N P

end MemQueryFeas


