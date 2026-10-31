-- Prove2me | Definitions.Def_ResistantSets_twist
-- name    : ResistantSets_twist
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:25:16.656987+00:00
-- url     : https://prove2.me/theorems/18c02fb8-14c6-4d39-bc67-9b30323ded66
-- title:
--   Twisting $S\triangle x$ and the point operations of $\{0,1\}^n$
-- statement:
--   Points of $\{0,1\}^n$ are functions $x:\{1,\dots,n\}\to\{0,1\}$ written as strings $x_1x_2\cdots x_n$; $x\triangle y$ is coordinate-wise addition modulo 2, $e_i$ is the $i$-th unit vector and $\mathbf 1$ the all-ones vector.
--
--   For a set $S\subseteq\{0,1\}^n$ and a point $x$, **twisting** $S$ by $x$ gives
--   $$
--   S\triangle x=\{\,y\triangle x : y\in S\,\}.
--   $$
--   Twisting at coordinate $i$ is twisting by $e_i$. The points of $S$ are the *feasible* points and the points of $\overline S=\{0,1\}^n\setminus S$ are the *infeasible* points. The module also fixes the incidence vector $\chi_C$ of a set $C$ of coordinates, the antipode $\mathbf 1-x$ of a point, and the last coordinate $n$.
--
--   Twists are the changes of variables $x_i\mapsto 1-x_i$; together with relabelings they generate the isomorphisms of subsets of the cube used throughout the mission.
--
--   **Formalization Note** A point is `Fin n → Bool`, and the paper's coordinate $i$ is the index $i-1$ (coordinate $n$ is `lastCoord n _`). A set is a `Finset (Fin n → Bool)`.
-- source:
--   Abdi, Cornuéjols, Lee, Resistant sets in the unit hypercube, accepted manuscript (Oct. 28, 2019), LSE Research Online 102397, pp.2–3 (feasible/infeasible points; twist S△eᵢ; incidence vector χ_C)

import Mathlib

namespace ResistantSets

/-- Coordinate-wise addition modulo 2 of two points of `{0,1}ⁿ` (the operation `x △ y` of
Abdi, Cornuéjols, Lee, *Resistant sets in the unit hypercube*, accepted manuscript (Oct. 28, 2019), §1, p.3).

**Formalization Note** A point of `{0,1}ⁿ` is a function `Fin n → Bool` (`false` = 0,
`true` = 1); the paper's coordinate `i ∈ [n]` is the index `i − 1`. -/
def vxor {n : ℕ} (x y : Fin n → Bool) : Fin n → Bool := fun i => xor (x i) (y i)

/-- The unit vector `eᵢ` of `{0,1}ⁿ` (Abdi, Cornuéjols, Lee, *Resistant sets in the unit hypercube*, accepted manuscript (Oct. 28, 2019), p.3). -/
def unitVec {n : ℕ} (i : Fin n) : Fin n → Bool := fun j => decide (j = i)

/-- The incidence vector `χ_C` of a set `C` of coordinates (Abdi, Cornuéjols, Lee, *Resistant sets in the unit hypercube*, accepted manuscript (Oct. 28, 2019), p.3). -/
def chi {n : ℕ} (C : Finset (Fin n)) : Fin n → Bool := fun j => decide (j ∈ C)

/-- The antipode `1 − x` of a point `x` (Abdi, Cornuéjols, Lee, *Resistant sets in the unit hypercube*, accepted manuscript (Oct. 28, 2019), p.5). -/
def cmpl {n : ℕ} (x : Fin n → Bool) : Fin n → Bool := fun i => !x i

/-- The paper's last coordinate `n`, which is the index `n − 1` of `Fin n`. -/
def lastCoord (n : ℕ) (h : 0 < n) : Fin n := ⟨n - 1, Nat.sub_lt h Nat.one_pos⟩

/-- **Twisting** (Abdi, Cornuéjols, Lee, *Resistant sets in the unit hypercube*, accepted manuscript (Oct. 28, 2019), §1, p.3): for `S ⊆ {0,1}ⁿ` and a point `x`,
`S △ x := {y △ x : y ∈ S}`. Twisting at coordinate `i` is `twist S (unitVec i)`.

**Formalization Note** A set `S ⊆ {0,1}ⁿ` is a `Finset (Fin n → Bool)`; its points are the
*feasible* points and the other points of `{0,1}ⁿ` are the *infeasible* ones (p.2). -/
def twist {n : ℕ} (S : Finset (Fin n → Bool)) (x : Fin n → Bool) : Finset (Fin n → Bool) :=
  S.image (fun y => vxor y x)

end ResistantSets


