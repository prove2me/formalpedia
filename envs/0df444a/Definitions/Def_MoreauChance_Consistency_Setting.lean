-- Prove2me | Definitions.Def_MoreauChance_Consistency_Setting
-- name    : MoreauChance_Consistency_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T17:22:32.733992+00:00
-- url     : https://prove2.me/theorems/426b8c09-fcf3-44d2-875a-24edfd1567ed
-- title:
--   §2.4, §5, pp. 2, 8–9, 19 — conic setting (9)–(10), S^h_Φ (11), ϕ (1), ϕλ (13), M(p), Mλ(p), v(P), v(Pλ)
-- statement:
--   This file fixes the chance-constrained model of van Ackooij, Pérez-Aros, Soto and Vilches. Let $\mathcal H$ be a real Hilbert space, $\mathcal Y$ a real Banach space with dual $\mathcal Y^*$, $(\Omega,\mathbb P)$ a probability space, $\xi:\Omega\to\mathbb R^m$ a random vector, and $\Phi:\mathcal H\times\mathbb R^m\to\mathcal Y$.
--
--   1. **Conic setting (§2.4).** $\mathcal K\subseteq\mathcal Y$ is a nonempty closed convex cone; $\mathcal C\subseteq\mathcal Y^*$ is convex and weak$^*$-compact and generates the positive polar cone $\mathcal K^+ := \{v^*\in\mathcal Y^*:\langle v^*,v\rangle\ge0\ \forall v\in\mathcal K\}$:
--   $$
--   \operatorname{cl}^{w^*}\operatorname{cone}\mathcal C = \mathcal K^+ . \tag{9}
--   $$
--   The function $h:\mathcal H\to\mathbb R$ is convex and continuously differentiable, and for every $v^*\in\mathcal C$ the map $(x,z)\mapsto\langle v^*,\Phi(x,z)\rangle+h(x)$ is jointly convex (10).
--   2. **Supremum function (11).** $S^h_\Phi(x,z) := \sup\{\langle v^*,\Phi(x,z)\rangle+h(x):v^*\in\mathcal C\}$ on $\mathcal H\times\mathbb R^m$ with the Hilbert norm $\|(x,z)\|^2=\|x\|^2+\|z\|^2$.
--   3. **Probability function (1)** and its **inner regularization (13)**, for $\lambda>0$:
--   $$
--   \varphi(x) := \mathbb P\big(\omega:\Phi(x,\xi(\omega))\in-\mathcal K\big),\qquad
--   \varphi_\lambda(x) := \mathbb P\big(\omega:\mathrm e_\lambda S^h_\Phi(x,\xi(\omega))\le h(x)\big).
--   $$
--   4. **Problems (P) and (Pλ) (§5).** For $p\in[0,1]$, $M(p) := \{x:\varphi(x)\ge p\}$ and $M_\lambda(p) := \{x:\varphi_\lambda(x)\ge p\}$. For $\psi:\mathcal H\to\mathbb R_\infty$, problem (P) minimizes $\psi$ over $M(p)$ and problem (Pλ) minimizes $\mathrm e_\lambda\psi$ over $M_\lambda(p)$; their values are $v(P) := \inf_{M(p)}\psi$ and $v(P_\lambda) := \inf_{M_\lambda(p)}\mathrm e_\lambda\psi$. A point is an optimal solution of (P) if it lies in $M(p)$ and minimizes $\psi$ there; likewise for (Pλ).
--
--   The regularization replaces the nonsmooth event $\{\Phi\in-\mathcal K\}$ by a sublevel event of a Moreau envelope, which is what makes $\varphi_\lambda$ amenable to the variational and differentiability analysis of the paper.
--
--   **Formalization Note** $\mathcal Y^*$ is `StrongDual ℝ Y`; weak$^*$ topology is that of `WeakDual ℝ Y`, and "cone C" is $\{t v^*:t\ge0,\ v^*\in\mathcal C\}$. Closedness of $\mathcal K$ is an addition to the page (p. 8), needed for the bipolar step of Proposition 2.6. With this encoding (9) forces $\mathcal C\ne\emptyset$ (since $0\in\mathcal K^+$), so $S^h_\Phi$ is real-valued as (11) declares; it is computed as an extended-real supremum, so no default value enters. The product $\mathcal H\times\mathbb R^m$ is `WithLp 2 (H × EuclideanSpace ℝ (Fin m))`, so the envelope uses the Hilbert norm. Probabilities are `ℝ≥0∞`-valued and values of problems are `EReal` infima. The parameter λ is unrestricted in the definitions; every theorem assumes $\lambda>0$.
-- source:
--   van Ackooij, Pérez-Aros, Soto & Vilches, Inner Moreau envelope of nonsmooth conic chance constrained optimization problems, arXiv:2301.09803v1, p. 2 Equation (1); p. 8 §2.4, Equations (9)–(11); p. 9 Equation (13); p. 19 §5, problems (P), (Pλ), M(p), Mλ(p), v(P), v(Pλ)

import Mathlib
import Definitions.Def_MoreauChance_Consistency_Basic

open MeasureTheory
open scoped ENNReal

namespace MoreauChance.Consistency

/-- The conic setting of §2.4 (p. 8): `K` a nonempty closed convex cone of `Y`; `C ⊆ Y*` convex and
weak*-compact with `cl^{w*} cone C = K⁺` (9); `h : H → ℝ` convex and `C¹`; and, for every `v* ∈ C`,
`(x, z) ↦ ⟨v*, Φ(x, z)⟩ + h(x)` convex (10). -/
structure IsConicSetting {H Y : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] {m : ℕ}
    (K : Set Y) (C : Set (StrongDual ℝ Y)) (h : H → ℝ)
    (Φ : H → EuclideanSpace ℝ (Fin m) → Y) : Prop where
  K_nonempty : K.Nonempty
  K_convex : Convex ℝ K
  K_cone : ∀ t : ℝ, 0 ≤ t → ∀ y ∈ K, t • y ∈ K
  K_closed : IsClosed K
  C_convex : Convex ℝ C
  C_weakStarCompact : IsCompact (StrongDual.toWeakDual '' C)
  C_generates_polar :
    closure (StrongDual.toWeakDual '' {w | ∃ t : ℝ, 0 ≤ t ∧ ∃ v ∈ C, w = t • v}) =
      StrongDual.toWeakDual '' {v | ∀ y ∈ K, 0 ≤ v y}
  h_convex : ConvexOn ℝ Set.univ h
  h_C1 : ContDiff ℝ 1 h
  scalarization_convex : ∀ v ∈ C,
    ConvexOn ℝ Set.univ (fun q : H × EuclideanSpace ℝ (Fin m) => v (Φ q.1 q.2) + h q.1)

/-- Supremum function `S^h_Φ(x, z) := sup {⟨v*, Φ(x, z)⟩ + h(x) : v* ∈ C}` (11), on the Hilbert
product `H × ℝ^m` (ℓ² norm). -/
noncomputable def supFun {H Y : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] {m : ℕ}
    (C : Set (StrongDual ℝ Y)) (h : H → ℝ) (Φ : H → EuclideanSpace ℝ (Fin m) → Y)
    (q : WithLp 2 (H × EuclideanSpace ℝ (Fin m))) : EReal :=
  ⨆ v ∈ C, ((v (Φ (WithLp.ofLp q).1 (WithLp.ofLp q).2) + h (WithLp.ofLp q).1 : ℝ) : EReal)

/-- Probability function `ϕ(x) := ℙ(ω : Φ(x, ξ(ω)) ∈ −K)` (1). -/
noncomputable def probFun {H Y Ω : Type*} [NormedAddCommGroup Y] [MeasurableSpace Ω] {m : ℕ}
    (K : Set Y) (Φ : H → EuclideanSpace ℝ (Fin m) → Y) (μ : Measure Ω)
    (ξ : Ω → EuclideanSpace ℝ (Fin m)) (x : H) : ℝ≥0∞ :=
  μ {ω | -(Φ x (ξ ω)) ∈ K}

/-- Inner regularization `ϕ_λ(x) := ℙ(ω : e_λ S^h_Φ(x, ξ(ω)) ≤ h(x))` (13). -/
noncomputable def probFunReg {H Y Ω : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [MeasurableSpace Ω] {m : ℕ}
    (C : Set (StrongDual ℝ Y)) (h : H → ℝ) (Φ : H → EuclideanSpace ℝ (Fin m) → Y)
    (μ : Measure Ω) (ξ : Ω → EuclideanSpace ℝ (Fin m)) (lam : ℝ) (x : H) : ℝ≥0∞ :=
  μ {ω | moreauEnv (supFun C h Φ) lam (WithLp.toLp 2 (x, ξ ω)) ≤ (h x : EReal)}

/-- Feasible set `M(p) := {x : ϕ(x) ≥ p}` of (P) (p. 19). -/
def feasSet {H Y Ω : Type*} [NormedAddCommGroup Y] [MeasurableSpace Ω] {m : ℕ}
    (K : Set Y) (Φ : H → EuclideanSpace ℝ (Fin m) → Y) (μ : Measure Ω)
    (ξ : Ω → EuclideanSpace ℝ (Fin m)) (p : ℝ) : Set H :=
  {x | ENNReal.ofReal p ≤ probFun K Φ μ ξ x}

/-- Feasible set `M_λ(p) := {x : ϕ_λ(x) ≥ p}` of (P_λ) (p. 19). -/
def feasSetReg {H Y Ω : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [MeasurableSpace Ω] {m : ℕ}
    (C : Set (StrongDual ℝ Y)) (h : H → ℝ) (Φ : H → EuclideanSpace ℝ (Fin m) → Y)
    (μ : Measure Ω) (ξ : Ω → EuclideanSpace ℝ (Fin m)) (lam p : ℝ) : Set H :=
  {x | ENNReal.ofReal p ≤ probFunReg C h Φ μ ξ lam x}

/-- Value `v(P) := inf {ψ(x) : x ∈ M(p)}` (p. 19). -/
noncomputable def valP {H Y Ω : Type*} [NormedAddCommGroup Y] [MeasurableSpace Ω] {m : ℕ}
    (ψ : H → EReal) (K : Set Y) (Φ : H → EuclideanSpace ℝ (Fin m) → Y) (μ : Measure Ω)
    (ξ : Ω → EuclideanSpace ℝ (Fin m)) (p : ℝ) : EReal :=
  ⨅ x ∈ feasSet K Φ μ ξ p, ψ x

/-- Value `v(P_λ) := inf {e_λψ(x) : x ∈ M_λ(p)}` (p. 19). -/
noncomputable def valPReg {H Y Ω : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [MeasurableSpace Ω] {m : ℕ}
    (ψ : H → EReal) (C : Set (StrongDual ℝ Y)) (h : H → ℝ)
    (Φ : H → EuclideanSpace ℝ (Fin m) → Y) (μ : Measure Ω) (ξ : Ω → EuclideanSpace ℝ (Fin m))
    (lam p : ℝ) : EReal :=
  ⨅ x ∈ feasSetReg C h Φ μ ξ lam p, moreauEnv ψ lam x

/-- `x0` is an optimal solution of (P): feasible, and `ψ x0 ≤ ψ y` for every feasible `y`. -/
def IsOptimalP {H Y Ω : Type*} [NormedAddCommGroup Y] [MeasurableSpace Ω] {m : ℕ}
    (ψ : H → EReal) (K : Set Y) (Φ : H → EuclideanSpace ℝ (Fin m) → Y) (μ : Measure Ω)
    (ξ : Ω → EuclideanSpace ℝ (Fin m)) (p : ℝ) (x0 : H) : Prop :=
  x0 ∈ feasSet K Φ μ ξ p ∧ ∀ y ∈ feasSet K Φ μ ξ p, ψ x0 ≤ ψ y

/-- `x` is an optimal solution of (P_λ): feasible, and `e_λψ x ≤ e_λψ y` for every feasible `y`. -/
def IsOptimalPReg {H Y Ω : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [MeasurableSpace Ω] {m : ℕ}
    (ψ : H → EReal) (C : Set (StrongDual ℝ Y)) (h : H → ℝ)
    (Φ : H → EuclideanSpace ℝ (Fin m) → Y) (μ : Measure Ω) (ξ : Ω → EuclideanSpace ℝ (Fin m))
    (lam p : ℝ) (x : H) : Prop :=
  x ∈ feasSetReg C h Φ μ ξ lam p ∧
    ∀ y ∈ feasSetReg C h Φ μ ξ lam p, moreauEnv ψ lam x ≤ moreauEnv ψ lam y

end MoreauChance.Consistency


