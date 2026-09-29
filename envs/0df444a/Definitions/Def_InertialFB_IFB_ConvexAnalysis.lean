-- Prove2me | Definitions.Def_InertialFB_IFB_ConvexAnalysis
-- name    : InertialFB_IFB_ConvexAnalysis
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T17:44:50.066919+00:00
-- url     : https://prove2.me/theorems/a084b362-39a2-4a82-b1de-a555ebb96b6a
-- title:
--   Proper, convex and subdifferentiable extended-valued functions; weak convergence in a Hilbert space
-- statement:
--   Let $H$ be a real inner-product space and let $\Phi : H \to \mathbb R \cup \{+\infty\}$ be an extended-valued function. This file fixes the basic vocabulary of convex analysis used throughout the mission.
--
--   1. $\Phi$ is **proper** if it never takes the value $-\infty$ and is not identically $+\infty$.
--   2. $\Phi$ is **convex** if its epigraph
--   $$\operatorname{epi}\Phi = \{(x,t) \in H \times \mathbb R : \Phi(x) \le t\}$$
--   is a convex subset of $H \times \mathbb R$.
--   3. A vector $g \in H$ is a **subgradient** of $\Phi$ at $u$, written $g \in \partial\Phi(u)$, if $\Phi(u) < +\infty$ and
--   $$\Phi(u) + \langle g, v - u\rangle \le \Phi(v) \qquad \text{for every } v \in H.$$
--   In particular $\partial\Phi(u) = \emptyset$ whenever $u \notin \operatorname{dom}\Phi$.
--   4. A sequence $(u_k)$ in $H$ **converges weakly** to $p$, written $u_k \rightharpoonup p$, if $\langle u_k, v\rangle \to \langle p, v\rangle$ for every $v \in H$.
--   5. A map $F : H \to H$ is **weak-to-weak sequentially continuous** if $x_k \rightharpoonup p$ implies $F(x_k) \rightharpoonup F(p)$.
--
--   These are the notions in which Hypothesis H, algorithm (IFB) and the convergence statements of Attouch, Peypouquet and Redont are phrased.
--
--   **Formalization Note** The value set $\mathbb R \cup \{+\infty\}$ is encoded as `EReal`; properness excludes $-\infty$. Mathlib's `ConvexOn` cannot be used for `EReal`-valued functions (there is no scalar action of $\mathbb R$ on `EReal`), so convexity is the epigraph definition. The condition $\Phi(u) \ne +\infty$ in the subgradient predicate is essential: without it, every $g$ would be a subgradient at a point where $\Phi = +\infty$.
-- source:
--   Attouch, Peypouquet & Redont, A Dynamical Approach to an Inertial Forward-Backward Algorithm for Convex Minimization, authors' manuscript (Aug 2013) of SIAM J. Optim. (2014), DOI 10.1137/130910294, pp. 1-4 (setting, (IFB), Hypothesis H), p. 4 (Theorem 1: weak convergence, weak-to-weak sequential continuity)

import Mathlib

open Filter Topology

namespace InertialFB.IFB

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- A function `Φ : H → ℝ ∪ {+∞}` (encoded as `EReal`) is *proper* if it never takes the value
`-∞` and is not identically `+∞`. -/
def IsProperFn (Φ : H → EReal) : Prop :=
  (∀ x, Φ x ≠ ⊥) ∧ ∃ x, Φ x ≠ ⊤

/-- An extended-valued function `Φ : H → EReal` is *convex* if its epigraph
`{(x, t) ∈ H × ℝ | Φ x ≤ t}` is a convex subset of `H × ℝ`. -/
def IsConvexFn (Φ : H → EReal) : Prop :=
  Convex ℝ {p : H × ℝ | Φ p.1 ≤ (p.2 : EReal)}

/-- `g` is a subgradient of `Φ` at `u` (that is, `g ∈ ∂Φ(u)`, the convex subdifferential):
`Φ u` is finite from above (`u ∈ dom Φ`) and `Φ u + ⟪g, v - u⟫ ≤ Φ v` for every `v ∈ H`. -/
def IsSubgradient (Φ : H → EReal) (u g : H) : Prop :=
  Φ u ≠ ⊤ ∧ ∀ v : H, Φ u + ((inner ℝ g (v - u) : ℝ) : EReal) ≤ Φ v

/-- Weak convergence `u k ⇀ p` in the Hilbert space `H`: `⟪u k, v⟫ → ⟪p, v⟫` for every `v ∈ H`. -/
def WeakTendsto (u : ℕ → H) (p : H) : Prop :=
  ∀ v : H, Tendsto (fun k => inner ℝ (u k) v) atTop (𝓝 (inner ℝ p v))

/-- A map `F : H → H` is weak-to-weak sequentially continuous: whenever `x k ⇀ p`,
also `F (x k) ⇀ F p`. -/
def WeakSeqContinuous (F : H → H) : Prop :=
  ∀ (x : ℕ → H) (p : H), WeakTendsto x p → WeakTendsto (F ∘ x) (F p)

end InertialFB.IFB


