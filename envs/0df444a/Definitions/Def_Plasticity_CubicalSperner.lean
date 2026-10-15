-- Prove2me | Definitions.Def_Plasticity_CubicalSperner
-- name    : Plasticity_CubicalSperner
-- status  : Definition
-- author  : @scanstone
-- created : 2026-10-14T09:30:27.153532+00:00
-- url     : https://prove2.me/theorems/689a601d-55e5-4e3f-81b1-7bf31019bb23
-- title:
--   Cubical Sperner: labelled grids, grid simplices and their faces
-- statement:
--   A **Sperner cube** is the grid $\{0,\dots,p\}^n$ with a labelling $L$ by numbers $0,\dots,n$ such that a point whose $k$-th coordinate is $0$ never carries label $k$, and a point whose $k$-th coordinate is $p$ carries a label at most $k$.
--   A **grid $m$-simplex** is an injective list $I_0,\dots,I_m$ of grid points that increase weakly in every coordinate, with $I_m$ exceeding $I_0$ by at most one in every coordinate.
--   An $(n-1)$-simplex $I$ is a **face** of an $n$-simplex $J$ when every vertex of $I$ is a vertex of $J$; deleting vertex $j$ of $J$ gives such a face.
--
--   These are the objects of Kuhn's cubical Sperner lemma, from which Brouwer's fixed-point theorem for the cube follows.
--
--   **Formalization Note** Ported from harfe, fixed-point-theorems-lean4 (MIT licence, notice reproduced in the file).
-- source:
--   H. W. Kuhn, Some combinatorial lemmas in topology, IBM J. Res. Dev. 4 (1960), 518–524; formalization ported from https://github.com/harfe/fixed-point-theorems-lean4 (FixedPointTheorems/cubical_sperner_prep.lean, MIT)

import Mathlib.Data.Fintype.Pi

/-!
# Cubical Sperner: grid, labellings, grid simplices, faces

Ported from harfe, *fixed-point-theorems-lean4*,
https://github.com/harfe/fixed-point-theorems-lean4 (file `FixedPointTheorems/cubical_sperner_prep.lean`),
MIT licence; the copyright and permission notice is reproduced below. The mathematics follows
H. W. Kuhn, *Some combinatorial lemmas in topology*, IBM J. Res. Dev. 4 (1960), 518–524.

A *Sperner cube* is the grid `{0,…,p}ⁿ` (points `Fin n → Fin (p+1)`) with a labelling
`RL` by natural numbers `0,…,n` such that a point with `k`-th coordinate `0` never carries
label `k`, and a point with `k`-th coordinate `p` carries a label `≤ k`.
A *grid `m`-simplex* is an injective list `I 0, …, I m` of grid points, increasing in every
coordinate, whose last point exceeds the first by at most one in every coordinate.
`is_face I J` says that the `n1`-simplex `I` is a facet (has all its vertices among those)
of the full-dimensional simplex `J`; `delete_vertex j J` removes vertex `j` from `J`, and
`insert_index j` is the order embedding `Fin (n1+1) → Fin (n+1)` that skips `j`.

Copyright (c) 2026 harfe

Permission is hereby granted, free of charge, to any person obtaining a copy of this software
and associated documentation files (the "Software"), to deal in the Software without
restriction, including without limitation the rights to use, copy, modify, merge, publish,
distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the
Software is furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or
substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING
BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
-/

namespace Plasticity.CubicalSperner

/-- A labelled grid `{0,…,p}ⁿ`: every label is at most `n`; a point whose `k`-th coordinate is
`0` does not carry label `k`; a point whose `k`-th coordinate is `p` carries a label `≤ k`. -/
structure SpernerCube where
  n : ℕ
  p : ℕ
  RL : (Fin n → Fin (p+1)) → ℕ
  rl_proper : ∀ (I : Fin n → Fin (p+1)), RL I ≤ n ∧
      ∀ (k : Fin n), (I k = 0 → RL I ≠ k.1) ∧ (I k = p → RL I ≤ k.1)

namespace SpernerCube

/-- The grid points `Fin n → Fin (p+1)`. -/
def G (SC : SpernerCube) := Fin SC.n → Fin (SC.p+1)

instance Gfin (SC : SpernerCube) : Fintype SC.G := Pi.instFintype

end SpernerCube

variable (SC : SpernerCube)
variable {n1 : ℕ}
variable {hn1 : n1 + 1 = SC.n}

/-- `I 0, …, I m` is a grid `m`-simplex: `I` is injective, consecutive vertices increase in every
coordinate, and the last vertex exceeds the first by at most one in every coordinate. -/
def simplex (m : ℕ) (I : Fin (m+1) → SC.G) := Function.Injective I
    ∧ ∀ i < m, ∀ j : Fin SC.n, (I (Fin.ofNat _ i) j).1 ≤ (I (Fin.ofNat _ (i+1)) j).1
    ∧ (I (Fin.last m) j).1 ≤ (I 0 j).1 + 1

/-- The `n1`-simplex `I` is a face of the full-dimensional simplex `J`: both are simplices and
every vertex of `I` is a vertex of `J`. -/
def is_face (I : Fin (n1+1) → SC.G) (J : Fin (SC.n+1) → SC.G) :=
    simplex SC n1 I ∧ simplex SC SC.n J ∧ Set.range I ⊆ Set.range J

/-- For `n1 + 1 = n`, the order embedding `Fin (n1+1) → Fin (n+1)` whose range misses `j`. -/
def insert_index (j : Fin (SC.n+1)) (a : Fin (n1+1)) : Fin (SC.n+1) :=
{ val := if a.val < j.val then a.val else a.val+1,
  isLt := by
    by_cases hlt : a.val < j.val
    · simp only [hlt, ↓reduceIte]
      exact Nat.lt_trans hlt j.2
    · simp only [hlt, ↓reduceIte, Nat.add_lt_add_iff_right]
      rw [← hn1]
      exact a.2 }

/-- The facet of `J` obtained by deleting vertex `j`. -/
def delete_vertex (j : Fin (SC.n+1)) (I : Fin (SC.n+1) → SC.G) : Fin (n1 + 1) → SC.G :=
  fun a ↦ I (@insert_index SC n1 hn1 j a)

end Plasticity.CubicalSperner


