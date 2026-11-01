-- Prove2me | Definitions.Def_ExpConMinimax_Problem
-- name    : ExpConMinimax_Problem
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:50:44.209229+00:00
-- url     : https://prove2.me/theorems/3e2b7f26-15ca-41c9-96cb-8496ba8d1cf7
-- title:
--   The expectation-constrained minimax problem (1.2), its Lagrangian (2.1) and the gap function (3.5)
-- statement:
--   The problem of the paper is
--   $$\min_{x\in\mathcal X}\max_{y\in\mathcal Y}F(x,y)\quad\text{s.t.}\quad H(x)\le0,\ \ G(y)\le0,$$
--   where $\mathcal X\subseteq\mathbb R^{d_x}$, $\mathcal Y\subseteq\mathbb R^{d_y}$, $F(x,y)=\mathbb E_\omega[f(x,y,\omega)]$, $H(x)=\mathbb E_\xi[h(x,\xi)]\in\mathbb R^{m_1}$ and $G(y)=\mathbb E_\zeta[g(y,\zeta)]\in\mathbb R^{m_2}$. The definition records:
--
--   1. the data $(\mathcal X,\mathcal Y,F,H,G)$;
--   2. the **standing assumptions**: $\mathcal X$ and $\mathcal Y$ are nonempty, closed and convex; $F(\cdot,y)$ is convex on $\mathcal X$ for $y\in\mathcal Y$, $F(x,\cdot)$ is concave on $\mathcal Y$ for $x\in\mathcal X$, every $H_i$ is convex on $\mathcal X$ and every $G_j$ is convex on $\mathcal Y$;
--   3. the **Lagrangian** $\mathcal L(x,y,\gamma,\lambda)=F(x,y)+\gamma^\top H(x)-\lambda^\top G(y)$;
--   4. the **gap function** $Q(z',z)=\mathcal L(x',y,\gamma,\lambda')-\mathcal L(x,y',\gamma',\lambda)$ for $z'=(x',y',\gamma',\lambda')$ and $z=(x,y,\gamma,\lambda)$;
--   5. the **feasible sets** $\widetilde{\mathcal X}=\{x\in\mathcal X\mid H(x)\le0\}$ and $\widetilde{\mathcal Y}=\{y\in\mathcal Y\mid G(y)\le0\}$.
--
--   Every result of the mission is about this problem and its saddle-point reformulation.
--
--   **Formalization Note** $F$, $H$, $G$ are given as functions; the integrands $f$, $h$, $g$ appear only through the sampling oracle. Convexity is required on $\mathcal X$, resp. $\mathcal Y$.
-- source:
--   Yang, Li, Lan, Data-Driven Minimax Optimization with Expectation Constraints, arXiv:2202.07868v2, (1.2), p.2; standing assumptions, pp.2–3; (2.1), p.8; feasible sets, p.8; (3.5), p.11

import Mathlib
import Definitions.Def_ExpConMinimax_Vec

namespace ExpConMinimax

/-- **The expectation-constrained minimax problem (1.2) and its Lagrangian (2.1).**
Yang, Li, Lan, *Data-Driven Minimax Optimization with Expectation Constraints*,
arXiv:2202.07868v2, (1.2), p.2, and (2.1), p.8:

  `min_{x∈X} max_{y∈Y} F(x,y)  s.t.  H(x) ≤ 0,  G(y) ≤ 0`,

with `F(x,y) = E_ω[f(x,y,ω)]`, `H(x) = E_ξ[h(x,ξ)] ∈ ℝ^{m₁}`, `G(y) = E_ζ[g(y,ζ)] ∈ ℝ^{m₂}`.

**Formalization Note.** The expected-value functions `F`, `H`, `G` are taken as primitive
real/vector-valued functions on the whole spaces; the integrands `f`, `h`, `g` enter only
through the sampling oracle (`Oracle`), whose means are tied to `F`, `H`, `G` by
Assumptions 2.1–2.2. -/
structure Problem (dx dy m₁ m₂ : ℕ) where
  /-- The feasible region `X ⊂ ℝ^{d_x}` of the minimizing player. -/
  X : Set (Vec dx)
  /-- The feasible region `Y ⊂ ℝ^{d_y}` of the maximizing player. -/
  Y : Set (Vec dy)
  /-- The objective `F(x,y) = E[f(x,y,ω)]`. -/
  F : Vec dx → Vec dy → ℝ
  /-- The constraint map `H(x) = E[h(x,ξ)] ∈ ℝ^{m₁}` (constraint `H(x) ≤ 0`). -/
  H : Vec dx → Vec m₁
  /-- The constraint map `G(y) = E[g(y,ζ)] ∈ ℝ^{m₂}` (constraint `G(y) ≤ 0`). -/
  G : Vec dy → Vec m₂

namespace Problem

variable {dx dy m₁ m₂ : ℕ}

/-- **Standing assumptions of the paper** (arXiv:2202.07868v2, p.2 and p.3): "`X ⊂ ℝ^{d_x}`
and `Y ⊂ ℝ^{d_y}` are nonempty closed convex sets", "`F` is convex in `x` and concave in `y`
and expected value functions `Hᵢ`, `Gⱼ` are convex functions".

**Formalization Note.** Convexity is required on `X` (resp. `Y`), the sets where the paper
evaluates these functions. -/
def Standing (P : Problem dx dy m₁ m₂) : Prop :=
  P.X.Nonempty ∧ IsClosed P.X ∧ Convex ℝ P.X ∧
  P.Y.Nonempty ∧ IsClosed P.Y ∧ Convex ℝ P.Y ∧
  (∀ y ∈ P.Y, ConvexOn ℝ P.X (fun x => P.F x y)) ∧
  (∀ x ∈ P.X, ConcaveOn ℝ P.Y (fun y => P.F x y)) ∧
  (∀ i, ConvexOn ℝ P.X (fun x => P.H x i)) ∧
  (∀ j, ConvexOn ℝ P.Y (fun y => P.G y j))

/-- **The Lagrangian (2.1)**, p.8: `𝓛(x,y,γ,λ) = F(x,y) + γᵀH(x) − λᵀG(y)`. -/
noncomputable def lagrangian (P : Problem dx dy m₁ m₂) (x : Vec dx) (y : Vec dy) (γ : Vec m₁)
    (lam : Vec m₂) : ℝ :=
  P.F x y + inner ℝ γ (P.H x) - inner ℝ lam (P.G y)

/-- **The gap function (3.5)**, p.11: for `z' = (x',y',γ',λ')` and a reference point
`z = (x,y,γ,λ)`, `Q(z', z) = 𝓛(x', y, γ, λ') − 𝓛(x, y', γ', λ)`. -/
noncomputable def gap (P : Problem dx dy m₁ m₂) (x' : Vec dx) (y' : Vec dy) (γ' : Vec m₁) (lam' : Vec m₂)
    (x : Vec dx) (y : Vec dy) (γ : Vec m₁) (lam : Vec m₂) : ℝ :=
  P.lagrangian x' y γ lam' - P.lagrangian x y' γ' lam

/-- **The feasible set `X̃ = {x ∈ X | H(x) ≤ 0}`** (p.8). -/
def feasX (P : Problem dx dy m₁ m₂) : Set (Vec dx) := {x | x ∈ P.X ∧ ∀ i, P.H x i ≤ 0}

/-- **The feasible set `Ỹ = {y ∈ Y | G(y) ≤ 0}`** (p.8). -/
def feasY (P : Problem dx dy m₁ m₂) : Set (Vec dy) := {y | y ∈ P.Y ∧ ∀ j, P.G y j ≤ 0}

end Problem

end ExpConMinimax


