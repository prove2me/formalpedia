-- Prove2me | Definitions.Def_PermInvCC_AltCycle
-- name    : PermInvCC_AltCycle
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T20:23:09.252501+00:00
-- url     : https://prove2.me/theorems/b3f9df17-b39f-48af-ac94-6e925e7fe42d
-- title:
--   Simple alternating cycles and their signed matrices $v=v^+-v^-$
-- statement:
--   A **simple alternating cycle** of length $2r$, $r\ge2$, in the bipartite symbol graph runs through distinct rows $a_0,\dots,a_{r-1}$ and distinct columns $b_0,\dots,b_{r-1}$:
--   $$R_{a_0}K_{b_0}R_{a_1}K_{b_1}\cdots R_{a_{r-1}}K_{b_{r-1}}R_{a_0}.$$
--   Assigning alternating signs to its edges gives $v=v^+-v^-$, where $v^+$ is the $0/1$ table of the cells $(a_i,b_i)$ and $v^-$ that of the cells $(a_{i+1},b_i)$ (indices mod $r$). Every row and column sum of $v$ is zero.
--
--   Lemmas 4.4 and 4.5 move types along such cycles.
-- source:
--   Huang and Ye, Quantum Advantage of Permutation-Invariant Functions in Communication Complexity, arXiv:2609.40116 (held version, sha256 fe1797dd…), p.16

import Mathlib

namespace PermInvCC

/-- A **simple alternating cycle** in the bipartite symbol graph (Y. Huang and Z. Ye,
arXiv:2609.40116, held version sha256 fe1797dd…, p.16): distinct rows `a₀, …, a_{r−1}` and
distinct columns `b₀, …, b_{r−1}`, `r ≥ 2`, giving the cycle
`R_{a₀} K_{b₀} R_{a₁} K_{b₁} ⋯ R_{a_{r−1}} K_{b_{r−1}} R_{a₀}` of length `2r`. -/
structure AltCycle (q : ℕ) where
  /-- half the length of the cycle -/
  r : ℕ
  two_le : 2 ≤ r
  /-- the row symbols, in cyclic order -/
  rows : Fin r → Fin q
  /-- the column symbols, in cyclic order -/
  cols : Fin r → Fin q
  rows_inj : Function.Injective rows
  cols_inj : Function.Injective cols

namespace AltCycle

variable {q : ℕ}

open Classical in
/-- `v⁺`: the `0/1` table of the cells `(a_i, b_i)`. -/
noncomputable def vplus (v : AltCycle q) (a b : Fin q) : ℕ :=
  if ∃ i, v.rows i = a ∧ v.cols i = b then 1 else 0

open Classical in
/-- `v⁻`: the `0/1` table of the cells `(a_{i+1}, b_i)` (indices mod `r`). -/
noncomputable def vminus (v : AltCycle q) (a b : Fin q) : ℕ :=
  if ∃ i, v.rows (finRotate v.r i) = a ∧ v.cols i = b then 1 else 0

/-- The signed matrix `v = v⁺ − v⁻` of the cycle (p.16); its row and column sums vanish. -/
noncomputable def signed (v : AltCycle q) (a b : Fin q) : ℤ :=
  (v.vplus a b : ℤ) - v.vminus a b

/-- The `2r` edges (cells) of the cycle. -/
def edges (v : AltCycle q) : Finset (Fin q × Fin q) :=
  (Finset.univ.image fun i => (v.rows i, v.cols i)) ∪
    (Finset.univ.image fun i => (v.rows (finRotate v.r i), v.cols i))

end AltCycle

end PermInvCC


