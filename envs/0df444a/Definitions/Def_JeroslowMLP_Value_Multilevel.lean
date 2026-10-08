-- Prove2me | Definitions.Def_JeroslowMLP_Value_Multilevel
-- name    : JeroslowMLP_Value_Multilevel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T09:38:29.148769+00:00
-- url     : https://prove2.me/theorems/e792110b-9f62-4944-957f-2cdffd3dcd21
-- title:
--   §2, p. 148 and (3.7), p. 152 — multi-level programs, the solution sets S_j and the value
-- statement:
--   A **multi-level program** on a finite set $V$ of real variables consists of a feasible set $S_0\subseteq\mathbb R^V$, an owner map assigning each variable to a player, and for each player $i$ a linear criterion
--   $$c^i x=\sum_{v\in V} c^i_v\,x_v ,$$
--   which that player minimises. Players are indexed from $0$ here: player $i$ optimises at level $i+1$, so the player with the largest index moves first and player $0$ moves last (Jeroslow's players $p,\dots,1$ move in that order).
--
--   For a level $j$ write $x\sim_j x'$ when $x$ and $x'$ agree on every variable owned by a player with index $>j$, i.e. on all variables of the players who have already moved. The **solution sets** are defined by
--   $$S_{j+1}=\bigl\{x\in S_j:\ c^j x\le c^j x' \text{ for every } x'\in S_j \text{ with } x\sim_j x'\bigr\}.$$
--   So $S_{j+1}$ keeps the points of $S_j$ at which player $j$'s criterion is minimal given the choices of the earlier movers; it may be empty (unbounded criterion, unattained infimum, or $S_j=\emptyset$). An $N$-player program **has value** $w$ when $N\ge1$, $S_N\neq\emptyset$ and the last mover's criterion $c^{N-1}x$ equals $w$ at every $x\in S_N$.
--
--   The file also defines the polyhedron $\{x: Ax\ge b\}$ of the constraint system (2.1) and the predicate "$t$ is binary" ($t\in\{0,1\}$).
--
--   This is the solution concept of Candler and Townsley used throughout the paper; every game of the mission is an instance.
--
--   **Formalization Note** The paper's informal "minimise $c^jx$ over $S_{j-1}$, players $p,\dots,j+1$ having moved" is the conditional minimisation made precise by (3.7), p. 152, which is what is encoded (a global minimum over $S_j$ would be a lexicographic program, a different notion). The paper's value $+\infty$ for $S_N=\emptyset$ is not modelled: `HasValue` requires $S_N\neq\emptyset$. Criteria are linear with real coefficients (the paper's data are rational; only the remark that all constructions stay rational depends on that).
-- source:
--   Jeroslow, The polynomial hierarchy and a simple model for competitive analysis, Math. Programming 32 (1985), pp. 147–148, §2, (2.1), (2.3), and p. 152, (3.7)

import Mathlib

namespace JeroslowMLP.Value

/-- A multi-level (linear) program on the variable set `V` (Jeroslow 1985, §2, pp. 147–148).
Players are indexed from `0`; player `i` optimises at level `i + 1`, so player `0` moves last.
`feasible` is the set `S₀`, `owner v` is the player controlling variable `v`, and player `i`
minimises the linear criterion `∑ v, cost i v * x v`. -/
structure MultilevelProgram (V : Type) where
  feasible : Set (V → ℝ)
  owner : V → ℕ
  cost : ℕ → V → ℝ

namespace MultilevelProgram

variable {V : Type} [Fintype V] (G : MultilevelProgram V)

/-- Player `i`'s criterion `cⁱx`. -/
def crit (i : ℕ) (x : V → ℝ) : ℝ := ∑ v, G.cost i v * x v

/-- `x` and `x'` agree on every variable owned by a player `> j`, i.e. by every player who moved
before player `j` (the paper's `Agr_{j+1}`, (3.7), p. 152, with 0-based players). -/
def AgreeAbove (j : ℕ) (x x' : V → ℝ) : Prop := ∀ v, j < G.owner v → x' v = x v

/-- The solution sets `S_j` (§2, p. 148, made precise by (3.7), p. 152): `S₀` is the feasible
set, and `S_{j+1}` consists of the `x ∈ S_j` minimising player `j`'s criterion among the points
of `S_j` that agree with `x` on the variables of all earlier movers. -/
def solSet : ℕ → Set (V → ℝ)
  | 0 => G.feasible
  | j + 1 => {x | x ∈ solSet j ∧
      ∀ x' ∈ solSet j, G.AgreeAbove j x x' → G.crit j x ≤ G.crit j x'}

/-- An `N`-player program has value `val`: `0 < N`, `S_N ≠ ∅`, and the last mover's criterion
(player `N - 1`) equals `val` at every point of `S_N`. -/
def HasValue (N : ℕ) (val : ℝ) : Prop :=
  0 < N ∧ (G.solSet N).Nonempty ∧ ∀ x ∈ G.solSet N, G.crit (N - 1) x = val

end MultilevelProgram

/-- The polyhedron `{x | A x ≥ b}` of (2.1). -/
def polyhedron {V : Type} [Fintype V] {m : ℕ} (A : Matrix (Fin m) V ℝ) (b : Fin m → ℝ) :
    Set (V → ℝ) :=
  {x | ∀ r, b r ≤ ∑ v, A r v * x v}

/-- A real number is binary when it is `0` or `1`. -/
def IsBinary (t : ℝ) : Prop := t = 0 ∨ t = 1

end JeroslowMLP.Value


