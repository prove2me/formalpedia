-- Prove2me | Definitions.Def_FastCLO_ERM_Polytope
-- name    : FastCLO_ERM_Polytope
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T04:17:46.044985+00:00
-- url     : https://prove2.me/theorems/750425c4-c6d7-4215-8854-9b234c2b02e6
-- title:
--   The feasible polytope Z = {z : Az ≤ b} with norm bound B, and its extreme points Z∠
-- statement:
--   Let $d \ge 0$. Write $\mathbb R^d$ for Euclidean space with its inner product $z^\top z'$ and norm $\|z\|$.
--
--   A **polytope** in this mission is given by finitely many linear constraints: rows $a_1, \dots, a_m \in \mathbb R^d$ and right-hand sides $b_1, \dots, b_m \in \mathbb R$, which cut out the feasible set
--
--   $$\mathcal Z = \{z \in \mathbb R^d : a_i^\top z \le b_i \text{ for } i = 1, \dots, m\}.$$
--
--   The data also carry a number $B > 0$, and two standing assumptions are recorded as part of the structure: $\mathcal Z$ is nonempty, and every $z \in \mathcal Z$ satisfies $\|z\| \le B$. The set $\mathcal Z^\angle$ is the set of extreme points of $\mathcal Z$; it is finite, and the paper's policies take values in it.
--
--   This is the decision set of contextual linear optimization, shared by every statement of the mission.
--
--   **Formalization Note** The module also fixes the carrier `Vec k` $= \mathbb R^k$ (Mathlib's `EuclideanSpace ℝ (Fin k)`, with the Euclidean inner product and norm), used for features and decisions alike. $B > 0$ is implicit in the paper, whose noise condition divides by $B$. Nonemptiness is part of the paper's reading of "polytope" (its policies minimize over $\mathcal Z$). Finiteness of $\mathcal Z^\angle$ is a provable fact, not an assumption.
-- source:
--   Hu, Kallus, Mao, Fast Rates for Contextual Linear Optimization, arXiv:2011.03030v3, Eq. (1), p. 1, and the standing assumptions on p. 2

import Mathlib
open scoped InnerProductSpace

namespace FastCLO.ERM

/-- `Vec k` is Euclidean space `ℝ^k` with its inner product and norm. Features live in `Vec p`,
cost vectors and decisions in `Vec d` (Hu, Kallus, Mao, *Fast Rates for Contextual Linear
Optimization*, arXiv:2011.03030v3, §1, p. 1). -/
abbrev Vec (k : ℕ) := EuclideanSpace ℝ (Fin k)

/-- The feasible region of contextual linear optimization (arXiv:2011.03030v3, Eq. (1), p. 1, and
the standing assumption on p. 2: "We assume throughout that Z is a polytope (sup_{z∈Z} ‖z‖ ≤ B)").
A polytope is given by its constraint rows `A i` and right-hand sides `b i`; `B > 0` bounds the norm
of every feasible point. The fields record the standing assumptions: the region is nonempty and
bounded by `B`.

Formalization Note: `0 < B` is implicit on the page (Assumption 2, p. 8, divides by `B`). -/
structure Polytope (d : ℕ) where
  /-- number of linear constraints -/
  m : ℕ
  /-- the rows `a_i` of the constraint matrix `A` -/
  A : Fin m → Vec d
  /-- the right-hand side `b` -/
  b : Fin m → ℝ
  /-- the norm bound `B` -/
  B : ℝ
  hB : 0 < B
  nonempty : {z : Vec d | ∀ i, ⟪A i, z⟫_ℝ ≤ b i}.Nonempty
  bounded : ∀ z ∈ {z : Vec d | ∀ i, ⟪A i, z⟫_ℝ ≤ b i}, ‖z‖ ≤ B

/-- The feasible set `Z = {z : Az ≤ b}` of a polytope (arXiv:2011.03030v3, Eq. (1), p. 1). -/
def Polytope.Z {d : ℕ} (P : Polytope d) : Set (Vec d) := {z | ∀ i, ⟪P.A i, z⟫_ℝ ≤ P.b i}

/-- The set `Z∠` of extreme points of `Z` (arXiv:2011.03030v3, p. 2). It is finite because `Z`
is a polytope; that is a provable fact, not an assumption. -/
def Polytope.ext {d : ℕ} (P : Polytope d) : Set (Vec d) := Set.extremePoints ℝ P.Z

end FastCLO.ERM


