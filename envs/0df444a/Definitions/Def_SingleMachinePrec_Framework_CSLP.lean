-- Prove2me | Definitions.Def_SingleMachinePrec_Framework_CSLP
-- name    : SingleMachinePrec_Framework_CSLP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T14:29:16.18396+00:00
-- url     : https://prove2.me/theorems/e3ad4255-c649-4b95-a783-d97f6510c5c7
-- title:
--   §2.2, §5: the LP relaxation [CS-LP], half-integral solutions, V_0, V_{1/2}, V_1, I_{1/2} and the rounded cover
-- statement:
--   Fix an instance $S$ with precedence order $P$ and its vertex cover graph $G^S_P$ with node weights $w_{(i,j)} = p_i w_j$.
--
--   The linear relaxation [CS-LP] of [CS-IP] has one variable $x_u$ per incomparable pair $u$. A vector $x$ is **feasible** when $0 \le x_u \le 1$ for every $u$ and $x_u + x_v \ge 1$ for every edge $uv$ of $G^S_P$ (these edges are the constraints (1)–(3) of [CS-IP]). Its objective is
--   $$\sum_{u} w_u\, x_u,$$
--   and $x$ is **optimal** when it is feasible and no feasible vector has a smaller objective. The vector $x$ is **half-integral** when every $x_u$ lies in $\{0, \tfrac12, 1\}$.
--
--   For a value $a$, $V_a = \{u : x_u = a\}$; the proof of Theorem 5.1 uses $V_0, V_{1/2}, V_1$. For a linear extension $L$ of $P$, $I_{1/2}(L)$ is the set of incomparable pairs of $V_{1/2}$ that $L$ reverses, and the **rounded cover** is
--   $$V_1 \cup C, \qquad C = V_{1/2} \setminus I_{1/2}(L).$$
--
--   These are the objects of the rounding argument of §5.
--
--   **Formalization Note** The constant term $\sum_j p_j w_j + \sum_{(i,j) \in P} p_i w_j$ of the [CS-IP] objective is dropped: it does not depend on $x$, so it changes neither feasibility nor optimality.
-- source:
--   Ambühl, Mastrolilli, Mutsanas, Svensson, On the Approximability of Single-Machine Scheduling with Precedence Constraints, Math. Oper. Res. 36(4) (2011), p. 656, §2.2 ([CS-IP], [CS-LP]); p. 659, proof of Theorem 5.1 (V_i, I_{1/2}, C = V_{1/2}\I_{1/2})

import Mathlib
import Definitions.Def_SingleMachinePrec_Framework_VertexCoverGraph

namespace SingleMachinePrec.Framework

variable {N : Type*}

/-- Feasibility for [CS-LP], the linear relaxation of [CS-IP] (p. 656), read as the vertex cover
LP of `G^S_P`: one variable `x_u ∈ [0, 1]` per incomparable pair, and `x_u + x_v ≥ 1` for every
edge `uv` of `G^S_P` (these edges are the constraints (1)–(3)). -/
def IsCSLPFeasible (S : Instance N) (x : IncPair S.P → ℝ) : Prop :=
  (∀ u, 0 ≤ x u ∧ x u ≤ 1) ∧ ∀ u v, (vertexCoverGraph S.P).Adj u v → 1 ≤ x u + x v

/-- The variable part `∑_{(i,j)} p_i w_j x_{(i,j)}` of the [CS-LP] objective; the constant
`∑_j p_j w_j + ∑_{(i,j) ∈ P} p_i w_j` of [CS-IP] is dropped (it does not depend on `x`). -/
noncomputable def csLPValue [Fintype N] (S : Instance N) (x : IncPair S.P → ℝ) : ℝ :=
  ∑ u, vertexWeight S u * x u

/-- `x` is an optimal solution of [CS-LP]. -/
def IsCSLPOptimal [Fintype N] (S : Instance N) (x : IncPair S.P → ℝ) : Prop :=
  IsCSLPFeasible S x ∧ ∀ y, IsCSLPFeasible S y → csLPValue S x ≤ csLPValue S y

/-- `x` is half-integral: every value lies in `{0, 1/2, 1}`. -/
def IsHalfIntegral {P : N → N → Prop} (x : IncPair P → ℝ) : Prop :=
  ∀ u, x u = 0 ∨ x u = 1 / 2 ∨ x u = 1

open Classical in
/-- `V_a = {u : x_u = a}` (p. 659), used for `a ∈ {0, 1/2, 1}`. -/
noncomputable def levelSet [Fintype N] {P : N → N → Prop} (x : IncPair P → ℝ) (a : ℝ) :
    Finset (IncPair P) :=
  Finset.univ.filter (fun u => x u = a)

open Classical in
/-- `I_{1/2}` for a linear extension `L` (p. 659): the incomparable pairs of `V_{1/2}` that `L`
reverses. -/
noncomputable def reversedHalf [Fintype N] {P : N → N → Prop} (x : IncPair P → ℝ)
    (L : LinearExtension P) : Finset (IncPair P) :=
  (levelSet x (1 / 2)).filter (fun u => L.Reverses u)

/-- The cover `V_1 ∪ C` with `C = V_{1/2} \ I_{1/2}` that the proof of Theorem 5.1 (p. 659)
builds from a half-integral [CS-LP] solution `x` and a linear extension `L`. -/
noncomputable def roundedCover [Fintype N] [DecidableEq N] {P : N → N → Prop}
    (x : IncPair P → ℝ) (L : LinearExtension P) : Finset (IncPair P) :=
  levelSet x 1 ∪ (levelSet x (1 / 2) \ reversedHalf x L)

end SingleMachinePrec.Framework


