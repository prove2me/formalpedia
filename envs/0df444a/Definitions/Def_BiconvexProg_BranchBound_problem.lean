-- Prove2me | Definitions.Def_BiconvexProg_BranchBound_problem
-- name    : BiconvexProg_BranchBound_problem
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T17:52:21.674988+00:00
-- url     : https://prove2.me/theorems/f6b88ceb-a45b-4ddb-9c04-5d6861784243
-- title:
--   Problem $\mathcal P$: the objective $\varphi = f(x) + x^\top y + g(y)$, the node functions $\psi^{B}$, the branching gap, and the standing hypotheses
-- statement:
--   Fix $n \ge 1$. For $x, y \in \mathbb{R}^n$ write $x^\top y = \sum_{i=1}^n x_i y_i$. **Problem $\mathcal P$** of Al-Khayyal and Falk is
--
--   $$\min_{(x,y)} \ \varphi(x,y) = f(x) + x^\top y + g(y) \quad \text{subject to } (x,y) \in S \cap \Omega,$$
--
--   where $\Omega = \{(x,y) : l \le x \le L,\ m \le y \le M\}$ is a box. Its **standing hypotheses** are:
--
--   1. $n > 0$, and the box is nonempty: $l \le L$ and $m \le M$;
--   2. $f$ is convex and continuous on $\{x : l \le x \le L\}$, and $g$ is convex and continuous on $\{y : m \le y \le M\}$;
--   3. $S$ is closed and convex;
--   4. the feasible set $S \cap \Omega$ is nonempty.
--
--   For a box $B$, the **node function** is
--
--   $$\psi^B(x,y) = f(x) + \mathrm{Vex}_B\, x^\top y + g(y),$$
--
--   a convex underestimator of $\varphi$ on $B$. For a coordinate $i$ and a point $(x, y)$, the **branching gap** of $B$ is $x_i y_i - \mathrm{Vex}_{B_i}\, x_i y_i$, where the envelope is taken over the $i$-th rectangle $B_i$ of $B$. It measures how far the node's underestimate falls below $x_i y_i$ in coordinate $i$.
--
--   These are the objects of the convex-envelope branch-and-bound algorithm. Problem $\mathcal P_{B}$, "minimize $\psi^B$ over $S \cap B$", is the convex subproblem solved at node $B$.
--
--   **Formalization Note** The paper states hypothesis 2 as "$f$ and $g$ are convex over $S \cap \Omega$" on p. 274 and as convexity over the two boxes on p. 276. The box form is used. **Continuity of $f$ and $g$ is an addition**: the paper takes it for granted ("there is a continuous function $\psi^k$", p. 276; "the continuous function $\varphi$", p. 279), and without it the subproblems need not have solutions. The positivity of $n$ is the paper's implicit setting.
-- source:
--   Al-Khayyal, Falk, Jointly Constrained Biconvex Programming, Math. Oper. Res. 8(2), 1983, p. 274 (Problem 𝒫, (a)–(c)); p. 276 (ψ^{kj}, restatement of 𝒫); p. 277 (branching inequality)

import Mathlib
import Definitions.Def_BiconvexProg_BranchBound_convexEnvelope
import Definitions.Def_BiconvexProg_BranchBound_Box

namespace BiconvexProg.BranchBound

variable {n : ℕ}

/-- The bilinear form `xᵀy = ∑ᵢ xᵢ yᵢ` on `ℝⁿ × ℝⁿ`. -/
def bilin (z : (Fin n → ℝ) × (Fin n → ℝ)) : ℝ :=
  ∑ i, z.1 i * z.2 i

/-- The objective of Problem 𝒫 (p. 274): `φ(x, y) = f(x) + xᵀy + g(y)`. -/
def objective (f g : (Fin n → ℝ) → ℝ) (z : (Fin n → ℝ) × (Fin n → ℝ)) : ℝ :=
  f z.1 + bilin z + g z.2

/-- The node function of a box `B` (p. 276):
`ψ^B(x, y) = f(x) + Vex_B xᵀy + g(y)`, with `Vex_B` the convex envelope over the box. -/
noncomputable def nodeFun (f g : (Fin n → ℝ) → ℝ) (B : Box n)
    (z : (Fin n → ℝ) × (Fin n → ℝ)) : ℝ :=
  f z.1 + convexEnvelope B.toSet bilin z + g z.2

/-- The branching gap of coordinate `i` of box `B` at the point `z` (p. 277):
`x_i y_i − Vex_{B_i} x_i y_i`, the envelope taken over the `i`-th rectangle of `B`. -/
noncomputable def gap (B : Box n) (i : Fin n) (z : (Fin n → ℝ) × (Fin n → ℝ)) : ℝ :=
  z.1 i * z.2 i - convexEnvelope (B.rect i) (fun p : ℝ × ℝ => p.1 * p.2) (z.1 i, z.2 i)

/-- The standing hypotheses of Problem 𝒫 (pp. 274, 276): the dimension `n` is positive; the box
`Ω` is nonempty (`l ≤ L`, `m ≤ M`); `f` and `g` are convex and continuous on
`{x : l ≤ x ≤ L}` and `{y : m ≤ y ≤ M}` respectively; `S` is closed and convex; and the feasible
set `S ∩ Ω` is nonempty. (Continuity of `f`, `g` is taken for granted in the paper.) -/
structure IsProblemP (S : Set ((Fin n → ℝ) × (Fin n → ℝ))) (f g : (Fin n → ℝ) → ℝ)
    (Ω : Box n) : Prop where
  pos_dim : 0 < n
  lL : Ω.l ≤ Ω.L
  mM : Ω.m ≤ Ω.M
  f_convex : ConvexOn ℝ (Set.Icc Ω.l Ω.L) f
  g_convex : ConvexOn ℝ (Set.Icc Ω.m Ω.M) g
  f_cont : ContinuousOn f (Set.Icc Ω.l Ω.L)
  g_cont : ContinuousOn g (Set.Icc Ω.m Ω.M)
  S_closed : IsClosed S
  S_convex : Convex ℝ S
  feasible : (S ∩ Ω.toSet).Nonempty

end BiconvexProg.BranchBound


