-- Prove2me | Definitions.Def_EdmondsMatching65_Polyhedron_DualProgram
-- name    : EdmondsMatching65_Polyhedron_DualProgram
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T14:24:10.092742+00:00
-- url     : https://prove2.me/theorems/1a8d3e65-35dd-4f91-9a47-8f1097152fba
-- title:
--   The dual program: odd sets, U of (5), the inequalities (6)–(7) and the conditions (8)–(10)
-- statement:
--   Let $G$ be a finite graph with nodes $V$ and edges $E$, and let $c\in\mathbb R^E$ be edge weights. An **odd set** is a set $S$ of $2r+1$ nodes with $r$ a strictly positive integer; write $r_S=(|S|-1)/2$.
--
--   The dual program to maximizing $W$ over $C$ has a variable $y_v$ for every node $v$ and a variable $z_S$ for every odd set $S$. Its objective (5) is
--   $$U(y,z)=\sum_{v\in V}y_v+\sum_{S\text{ odd}}r_S\,z_S .$$
--
--   The pair $\langle y,z\rangle$ is **dual feasible** if
--
--   - (6) $y_v\ge 0$ for every node $v$ and $z_S\ge 0$ for every odd set $S$;
--   - (7) for every edge $e$ with ends $v_1,v_2$: $\displaystyle y_{v_1}+y_{v_2}+\sum_{S\ni v_1,v_2}z_S\ \ge\ c_e$, the sum over the odd sets containing both ends.
--
--   For a matching $M$, the **conditions (8)–(10)** are:
--
--   - (8) $y_v=0$ for each node $v$ which is not an endpoint of an edge in $M$;
--   - (9) equality holds in (7) for each $e\in M$;
--   - (10) for each odd set $S$ with $z_S>0$, $S$ contains both endpoints of exactly $r_S$ edges of $M$.
--
--   These are the complementary slackness conditions of the pair of linear programs; a matching together with a dual feasible $\langle y,z\rangle$ satisfying (8)–(10) certifies that the matching is maximum.
--
--   **Formalization Note** The dual variable $z$ is a function on all node sets, of which only the values on odd sets are read. $r_S$ is computed in the reals.
-- source:
--   Edmonds, Maximum Matching and a Polyhedron With 0,1-Vertices, J. Res. NBS 69B (1965), pp. 126–127, §3, (5)–(10)

import Mathlib
import Definitions.Def_EdmondsMatching65_Polyhedron_Graph

namespace EdmondsMatching65.Polyhedron

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- A node set `S` with `2r + 1` elements for a strictly positive integer `r` (§2–§3, p. 126). -/
def IsOddSet (S : Finset V) : Prop :=
  ∃ r : ℕ, 1 ≤ r ∧ S.card = 2 * r + 1

open Classical in
/-- The finite family of all odd node sets `S` (`|S| = 2r + 1`, `r ≥ 1`), which index the dual
variables `z` (§3, p. 126). -/
noncomputable def oddSets : Finset (Finset V) :=
  Finset.univ.filter (fun S : Finset V => IsOddSet S)

/-- The number `r` of an odd set, `r = (|S| - 1)/2`, computed in `ℝ`. -/
noncomputable def rOf (S : Finset V) : ℝ :=
  ((S.card : ℝ) - 1) / 2

/-- The dual objective (5) (§3, p. 126): `U = ∑_v y v + ∑_S r z S`, the second sum over all odd
sets `S`. -/
noncomputable def U (y : V → ℝ) (z : Finset V → ℝ) : ℝ :=
  ∑ v, y v + ∑ S ∈ oddSets, rOf S * z S

/-- The left side of inequality (7) for an edge `e` with ends `v₁, v₂` (§3, p. 126):
`y v₁ + y v₂ + ∑ z S`, the sum over the odd sets `S` containing both `v₁` and `v₂`. -/
noncomputable def edgeDual (G : Graph V E) (y : V → ℝ) (z : Finset V → ℝ) (e : E) : ℝ :=
  Sym2.lift ⟨fun a b => y a + y b, fun a b => add_comm (y a) (y b)⟩ (G.ends e) +
    ∑ S ∈ oddSets.filter (fun S : Finset V => G.ends e ∈ S.sym2), z S

/-- Dual feasibility (6)–(7) (§3, p. 126): `y ≥ 0`, `z ≥ 0` on every odd set, and for every edge
`e`, `y v₁ + y v₂ + ∑_{S ∋ v₁, v₂} z S ≥ c e`. -/
def DualFeasible (G : Graph V E) (c : E → ℝ) (y : V → ℝ) (z : Finset V → ℝ) : Prop :=
  (∀ v, 0 ≤ y v) ∧ (∀ S ∈ (oddSets : Finset (Finset V)), 0 ≤ z S) ∧
    ∀ e, c e ≤ edgeDual G y z e

/-- The conditions (8)–(10) (§3, p. 127) for a matching `M` and a dual vector `⟨y, z⟩`:
(8) `y v = 0` for each node `v` which is not an endpoint of an edge in `M`;
(9) equality holds in (7) for each `e ∈ M`;
(10) for each odd set `S` with `z S > 0`, `S` contains both endpoints of `r` edges of `M`. -/
noncomputable def CompSlack (G : Graph V E) (c : E → ℝ) (M : Finset E) (y : V → ℝ)
    (z : Finset V → ℝ) : Prop :=
  (∀ v, (∀ e ∈ M, v ∉ G.ends e) → y v = 0) ∧
  (∀ e ∈ M, edgeDual G y z e = c e) ∧
  (∀ S ∈ (oddSets : Finset (Finset V)), 0 < z S →
    ((M.filter (fun e => G.ends e ∈ S.sym2)).card : ℝ) = rOf S)

end EdmondsMatching65.Polyhedron


