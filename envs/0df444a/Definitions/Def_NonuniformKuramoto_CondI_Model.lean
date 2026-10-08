-- Prove2me | Definitions.Def_NonuniformKuramoto_CondI_Model
-- name    : NonuniformKuramoto_CondI_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T11:23:22.253901+00:00
-- url     : https://prove2.me/theorems/d2d0c332-447a-474f-9c0e-021a89bdec75
-- title:
--   Non-uniform Kuramoto model (8): $D_i\dot\theta_i = \omega_i - \sum_j P_{ij}\sin(\theta_i-\theta_j+\varphi_{ij})$, arc sets $\Delta(\gamma)$, $\bar\Delta(\gamma)$, solutions, positive invariance
-- statement:
--   This file fixes the dynamical system studied in the mission and the vocabulary used to state its synchronization properties.
--
--   **The model.** Consider $n$ oscillators with phases $\theta_1,\dots,\theta_n$, time constants $D_i>0$, natural frequencies $\omega_i\in\mathbb R$, coupling weights $P_{ij}\ge 0$ and phase shifts $\varphi_{ij}\in[0,\pi/2[$ (with $P_{ii}=\varphi_{ii}=0$). The **non-uniform Kuramoto model** is
--
--   $$D_i\,\dot\theta_i = \omega_i - \sum_{j=1}^n P_{ij}\sin(\theta_i-\theta_j+\varphi_{ij}),\qquad i\in\{1,\dots,n\}. \tag{8}$$
--
--   The function `field` is the right-hand side of (8) divided by $D_i$, i.e. the velocity $\dot\theta_i$ at the configuration $\theta$.
--
--   **Arc sets.** For $\gamma\in[0,\pi]$, $\Delta(\gamma)$ is the set of configurations all of whose angles lie in the interior of an arc of length $\gamma$, and $\bar\Delta(\gamma)$ is its closure together with the synchronized configurations. A configuration lies in $\bar\Delta(\gamma)$ (resp. $\Delta(\gamma)$) iff it has a real lift $\theta\in\mathbb R^n$ with
--
--   $$\theta_i-\theta_j\le\gamma\ \ \forall i,j\qquad(\text{resp. } \theta_i-\theta_j<\gamma\ \ \forall i,j),$$
--
--   and the predicates `ArcClosed γ θ` and `ArcOpen γ θ` state these inequalities for a given lift $\theta$.
--
--   **Solutions and invariance.** A solution on $[0,\infty)$ is a curve $t\mapsto\theta(t)\in\mathbb R^n$ whose derivative (one-sided at $t=0$) equals the right-hand side of (8) for every $t\ge0$. A set $S$ of configurations is **positively invariant** if every solution with $\theta(0)\in S$ satisfies $\theta(t)\in S$ for all $t\ge0$.
--
--   **Graphs.** The graph induced by $P$ has a directed edge $(i,j)$ iff $P_{ij}>0$. A node $k$ is **globally reachable** if every node $i$ has a directed path from $i$ to $k$.
--
--   These are the objects of Sections I, III.A and V of the paper, used by every statement of the mission.
--
--   **Formalization Note** Angles on the torus $\mathbb T^n$ are represented by real lifts $\theta:\{1,\dots,n\}\to\mathbb R$; the right-hand side of (8) is $2\pi$-periodic in each coordinate, so solutions on $\mathbb T^n$ are exactly the projections of solutions on $\mathbb R^n$, and a configuration lies in $\bar\Delta(\gamma)$ iff it has a lift of spread at most $\gamma$. The velocity $\dot\theta$ in all statements is the value of `field` along the solution, never Lean's `deriv`. The parameter ranges are hypotheses of each theorem, not part of the definitions.
-- source:
--   Dörfler & Bullo, Synchronization and Transient Stability in Power Networks and Nonuniform Kuramoto Oscillators, arXiv:0910.5673v4, p. 8, (8); p. 5, ∆(γ) and ∆̄(γ); pp. 4–6 (graph theory, solutions); p. 16 (globally reachable node)

import Mathlib

namespace NonuniformKuramoto.CondI

/-- The right-hand side of the non-uniform Kuramoto model (8), divided by `D i` as in (18):
`θ̇_i = (ω_i − ∑_j P_ij sin(θ_i − θ_j + ϕ_ij)) / D_i` (Dörfler–Bullo, arXiv:0910.5673v4, p. 8, (8)).
Angles are represented by a real lift `θ : Fin n → ℝ` of a point of the torus. -/
noncomputable def field {n : ℕ} (D ω : Fin n → ℝ) (P ϕ : Fin n → Fin n → ℝ) (θ : Fin n → ℝ)
    (i : Fin n) : ℝ :=
  (ω i - ∑ j, P i j * Real.sin (θ i - θ j + ϕ i j)) / D i

/-- `∆̄(γ)` on lifts: all pairwise differences of the lift are at most `γ`, i.e. all angles lie in a
closed arc of length `γ` (p. 5). -/
def ArcClosed {n : ℕ} (γ : ℝ) (θ : Fin n → ℝ) : Prop :=
  ∀ i j, θ i - θ j ≤ γ

/-- `∆(γ)` on lifts: all pairwise differences of the lift are strictly less than `γ`, i.e. all angles
lie in the interior of an arc of length `γ` (p. 5). -/
def ArcOpen {n : ℕ} (γ : ℝ) (θ : Fin n → ℝ) : Prop :=
  ∀ i j, θ i - θ j < γ

/-- `θ : ℝ → (Fin n → ℝ)` is a solution of (8) on `[0, ∞)`: for every `t ≥ 0` it has derivative
`field D ω P ϕ (θ t)` within `[0, ∞)` at `t` (a one-sided derivative at `t = 0`). -/
def IsSolution {n : ℕ} (D ω : Fin n → ℝ) (P ϕ : Fin n → Fin n → ℝ) (θ : ℝ → Fin n → ℝ) : Prop :=
  ∀ t : ℝ, 0 ≤ t → HasDerivWithinAt θ (field D ω P ϕ (θ t)) (Set.Ici 0) t

/-- A set `S` of (lifted) configurations is positively invariant for (8): every solution on `[0, ∞)`
that starts in `S` stays in `S` for all `t ≥ 0`. -/
def IsPosInvariant {n : ℕ} (D ω : Fin n → ℝ) (P ϕ : Fin n → Fin n → ℝ)
    (S : (Fin n → ℝ) → Prop) : Prop :=
  ∀ θ : ℝ → Fin n → ℝ, IsSolution D ω P ϕ θ → S (θ 0) → ∀ t : ℝ, 0 ≤ t → S (θ t)

/-- The graph induced by `P` (an edge `(i, j)` iff `P i j > 0`, p. 4) has a globally reachable node:
some node `k` is reachable from every node along directed edges (p. 16). -/
def HasGloballyReachableNode {n : ℕ} (P : Fin n → Fin n → ℝ) : Prop :=
  ∃ k : Fin n, ∀ i : Fin n, Relation.ReflTransGen (fun a b => 0 < P a b) i k

end NonuniformKuramoto.CondI


