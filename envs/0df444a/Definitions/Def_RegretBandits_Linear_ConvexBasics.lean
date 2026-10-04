-- Prove2me | Definitions.Def_RegretBandits_Linear_ConvexBasics
-- name    : RegretBandits_Linear_ConvexBasics
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T09:50:55.094398+00:00
-- url     : https://prove2.me/theorems/687a4b81-43cf-4e53-bc17-5c79e623a6a7
-- title:
--   Legendre functions, Bregman divergences and the Legendre–Fenchel transform (Definitions 5.1–5.3)
-- statement:
--   This file fixes the convex-analysis vocabulary of Chapter 5. Throughout, $\mathbb R^d$ is the space of real vectors indexed by $\{1,\dots,d\}$ and $x^\top y$ is the usual scalar product.
--
--   1. **Gradient.** For $F:\mathbb R^d\to\mathbb R$, $\nabla F(x)=(\partial_1F(x),\dots,\partial_dF(x))$ is the vector of partial derivatives.
--   2. **Legendre function** (Definition 5.3). Let $D\subset\mathbb R^d$ be a nonempty open convex set with closure $\bar D$. A function $F:\bar D\to\mathbb R$ is Legendre if it is continuous on $\bar D$, strictly convex with continuous first partial derivatives on $D$, and
--   $$\lim_{x\to \bar D\setminus D}\|\nabla F(x)\|=+\infty .$$
--   3. **Bregman divergence.** For $x\in\bar D$ and $y\in D$,
--   $$D_F(x,y)=F(x)-F(y)-(x-y)^\top\nabla F(y).$$
--   4. **Legendre–Fenchel transform** (Definition 5.2). $F^*(u)=\sup_{x\in\bar D}\bigl(x^\top u-F(x)\bigr)\in\mathbb R\cup\{+\infty\}$, and the biconjugate $F^{**}(x)=\sup_{u\in\mathbb R^d}\bigl(x^\top u-F^*(u)\bigr)$.
--   5. **Dual Bregman divergence.** For $u,v$ in the dual space $D^*=\nabla F(D)$, where $F^*$ is finite,
--   $$D_{F^*}(u,v)=F^*(u)-F^*(v)-(u-v)^\top\nabla F^*(v).$$
--   6. **Bregman projection.** $z$ is a Bregman projection of $w$ onto $K$ if $z\in K$ and $D_F(z,w)\le D_F(y,w)$ for every $y\in K$, i.e. $z\in\arg\min_{y\in K}D_F(y,w)$.
--   7. **Norms.** A norm $\|\cdot\|$ on $\mathbb R^d$ and its dual norm $\|g\|_*=\sup\{g^\top x:\|x\|\le1\}$.
--
--   These objects are used by every result of the chapter: the OMD and OSMD algorithms, their regret bounds and the potential-based Legendre functions.
--
--   **Formalization Note** The norm in the blow-up condition is Lean's sup norm on `Fin d → ℝ`; the book's footnote 1 notes that the choice of norm does not matter. $F^*$ is valued in `EReal`; the real-valued conjugate `conjReal` is its `toReal`, which equals $F^*$ on the open set $D^*$, the only place where the mission evaluates $F^*$, $\nabla F^*$ or $D_{F^*}$. The gradient is Lean's Fréchet derivative applied to basis vectors, and is used only at points of $D$. The dual-norm supremum is over a nonempty set that is bounded above for every norm on $\mathbb R^d$.
-- source:
--   Bubeck, Cesa-Bianchi, Regret Analysis of Stochastic and Nonstochastic Multi-armed Bandit Problems, arXiv:1204.5721v2, pp. 69–71, Definitions 5.1, 5.2, 5.3, Lemma 5.2 (Bregman projection), Theorem 5.5 (norm and dual norm)

import Mathlib

open Filter Topology

namespace RegretBandits.Linear

/-- The gradient `∇F(x) ∈ ℝ^d` of `F : ℝ^d → ℝ` at `x`, as the vector of partial derivatives
`(∂F/∂x_1 (x), …, ∂F/∂x_d (x))` (Bubeck, Cesa-Bianchi, arXiv:1204.5721v2, p. 70, Definition 5.3).
It is meaningful where `F` is differentiable; elsewhere Lean's `fderiv` is `0`. Every statement
of the mission evaluates it only at points of the open set `D` on which `F` is `C¹`. -/
noncomputable def grad {d : ℕ} (F : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) : Fin d → ℝ :=
  fun i => fderiv ℝ F x (Pi.single i 1)

/-- Definition 5.3 (p. 70): `F` is a **Legendre function** on `D̄`, where `D ⊂ ℝ^d` is a nonempty
open convex set: `F` is continuous on the closure `D̄`, strictly convex and with continuous first
partial derivatives on `D`, and `‖∇F(x)‖ → +∞` as `x ∈ D` tends to a point of `D̄ \ D`.
(The norm on `ℝ^d` is Lean's sup norm; by the book's footnote 1 the choice of norm does not
matter.) Values of `F` outside `D̄` are irrelevant. -/
structure IsLegendre {d : ℕ} (F : (Fin d → ℝ) → ℝ) (D : Set (Fin d → ℝ)) : Prop where
  isOpen : IsOpen D
  convex : Convex ℝ D
  nonempty : D.Nonempty
  continuousOn : ContinuousOn F (closure D)
  strictConvexOn : StrictConvexOn ℝ D F
  contDiffOn : ContDiffOn ℝ 1 F D
  grad_tendsto : ∀ x ∈ closure D \ D, Tendsto (fun y => ‖grad F y‖) (𝓝[D] x) atTop

/-- The Bregman divergence `D_F(x, y) = F(x) - F(y) - (x - y)ᵀ ∇F(y)` (p. 70, Definition 5.3),
for `x ∈ D̄` and `y ∈ D`. -/
noncomputable def bregman {d : ℕ} (F : (Fin d → ℝ) → ℝ) (x y : Fin d → ℝ) : ℝ :=
  F x - F y - (x - y) ⬝ᵥ grad F y

/-- The Legendre–Fenchel transform of `F : D̄ → ℝ` (p. 69, Definition 5.2, with `X = D̄`):
`F*(u) = sup_{x ∈ D̄} (xᵀu - F(x))`, valued in `EReal` because the supremum may be `+∞`. -/
noncomputable def legendreConj {d : ℕ} (F : (Fin d → ℝ) → ℝ) (D : Set (Fin d → ℝ))
    (u : Fin d → ℝ) : EReal :=
  ⨆ x ∈ closure D, ((x ⬝ᵥ u - F x : ℝ) : EReal)

/-- The biconjugate `F**(x) = sup_{u ∈ ℝ^d} (xᵀu - F*(u))` (p. 70, Lemma 5.1), in `EReal`
(`r - ⊤ = ⊥` for real `r`, which is the correct value `-∞` of a term with `F*(u) = +∞`). -/
noncomputable def legendreBiconj {d : ℕ} (F : (Fin d → ℝ) → ℝ) (D : Set (Fin d → ℝ))
    (x : Fin d → ℝ) : EReal :=
  ⨆ u : Fin d → ℝ, ((x ⬝ᵥ u : ℝ) : EReal) - legendreConj F D u

/-- The real-valued conjugate `u ↦ F*(u)`, equal to `legendreConj F D u` wherever that is finite.
For a Legendre `F` it is finite on the open dual space `D* = ∇F(D)`, which is the only place the
mission evaluates it or its gradient. -/
noncomputable def conjReal {d : ℕ} (F : (Fin d → ℝ) → ℝ) (D : Set (Fin d → ℝ))
    (u : Fin d → ℝ) : ℝ :=
  (legendreConj F D u).toReal

/-- The Bregman divergence of the conjugate,
`D_{F*}(u, v) = F*(u) - F*(v) - (u - v)ᵀ ∇F*(v)` (p. 70, Eq. (5.2)), for `u, v ∈ D* = ∇F(D)`. -/
noncomputable def dualBregman {d : ℕ} (F : (Fin d → ℝ) → ℝ) (D : Set (Fin d → ℝ))
    (u v : Fin d → ℝ) : ℝ :=
  conjReal F D u - conjReal F D v - (u - v) ⬝ᵥ grad (conjReal F D) v

/-- `z` is a Bregman projection of `w` onto `K`: `z ∈ argmin_{y ∈ K} D_F(y, w)`
(p. 70, Lemma 5.2; step (3) of OMD, p. 71). -/
def IsBregmanProjection {d : ℕ} (F : (Fin d → ℝ) → ℝ) (K : Set (Fin d → ℝ))
    (w z : Fin d → ℝ) : Prop :=
  z ∈ K ∧ ∀ y ∈ K, bregman F z w ≤ bregman F y w

/-- `N` is a norm on `ℝ^d` (p. 76, Theorem 5.5: "for any norm ‖·‖"). -/
structure IsNorm {d : ℕ} (N : (Fin d → ℝ) → ℝ) : Prop where
  add_le : ∀ x y, N (x + y) ≤ N x + N y
  smul : ∀ (c : ℝ) x, N (c • x) = |c| * N x
  eq_zero : ∀ x, N x = 0 → x = 0

/-- The dual norm `‖g‖_* = sup {gᵀx : ‖x‖ ≤ 1}` of a norm `N` on `ℝ^d`. The set is nonempty
(it contains `0`) and bounded above for every norm on `ℝ^d`, so the real supremum is the
book's value. -/
noncomputable def dualNorm {d : ℕ} (N : (Fin d → ℝ) → ℝ) (g : Fin d → ℝ) : ℝ :=
  sSup ((fun x => g ⬝ᵥ x) '' {x | N x ≤ 1})

end RegretBandits.Linear


