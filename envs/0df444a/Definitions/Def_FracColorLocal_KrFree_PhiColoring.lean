-- Prove2me | Definitions.Def_FracColorLocal_KrFree_PhiColoring
-- name    : FracColorLocal_KrFree_PhiColoring
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T07:11:36.052097+00:00
-- url     : https://prove2.me/theorems/aa0d4bd4-c927-4079-b2ee-85b94a10034c
-- title:
--   Demand functions, φ-colorings and the weighted independence number α_u(G)
-- statement:
--   Let $G$ be a finite simple graph on a vertex set $V$. A set $I\subseteq V$ is **independent** if no two of its vertices are adjacent; $\mathcal I(G)$ denotes the family of independent sets (it contains $\emptyset$).
--
--   A **demand function** for $G$ is a function $\varphi:V\to[0,1]$. A **$\varphi$-coloring** of $G$ is a probability distribution $\mu$ on $\mathcal I(G)$ such that a set $I$ sampled from it satisfies $\mathbb P(v\in I)\ge\varphi(v)$ for every vertex $v$:
--
--   $$\mu\ge 0,\qquad \mu(I)=0\ \text{unless}\ I\in\mathcal I(G),\qquad \sum_{I\subseteq V}\mu(I)=1,\qquad \sum_{I\ni v}\mu(I)\ge\varphi(v)\ \ (v\in V).$$
--
--   For a vertex weight $u:V\to\mathbb R$, the **weighted independence number** is $\alpha_u(G)=\max\{u(I):I\in\mathcal I(G)\}$ with $u(I)=\sum_{v\in I}u(v)$.
--
--   **Formalization Note** The distribution is a function `μ : Finset V → ℝ` on all subsets of the finite vertex type, nonnegative, zero off the independent sets and of total mass one (`IsPhiColoring`); `inclusionProb μ v` is $\sum_{I\ni v}\mu(I)$. `HasPhiColoring G φ` asserts that some such `μ` exists. `IsDemandFunction φ` is $0\le\varphi(v)\le 1$ for all $v$. `weightedIndepNumber G u` is the real `sSup` of the finite, nonempty set $\{u(I):I\in\mathcal I(G)\}$, hence its maximum.
-- source:
--   Davies, Dhawan, Methuku, Nguyen, Seo, Fractional colorings of K_r-free graphs with local demands, arXiv:2611.04297 (PDF sha256 b3f2dcce…), p. 3 (PDF 4), Definition 1.2; p. 4 (PDF 5), §1.2 (α_u)

import Mathlib

namespace FracColorLocal.KrFree

variable {V : Type*} [Fintype V]

/-- A demand function for a graph on `V` (Definition 1.2): a function `φ : V → [0, 1]`. -/
def IsDemandFunction (φ : V → ℝ) : Prop :=
  ∀ v, 0 ≤ φ v ∧ φ v ≤ 1

/-- The weighted independence number `α_u(G) := max {u(I) : I ∈ I(G)}`, where `u(I) = ∑_{v ∈ I} u v`
and `I(G)` is the (finite, nonempty: it contains `∅`) family of independent sets of `G`. -/
noncomputable def weightedIndepNumber (G : SimpleGraph V) (u : V → ℝ) : ℝ :=
  sSup ((fun I : Finset V => ∑ v ∈ I, u v) '' {I : Finset V | G.IsIndepSet (I : Set V)})

/-- The probability `P(v ∈ I)` that a set `I` drawn from the weights `μ` on subsets contains `v`:
`∑_{I ∋ v} μ(I)`. -/
noncomputable def inclusionProb (μ : Finset V → ℝ) (v : V) : ℝ := by
  classical
  exact ∑ I : Finset V, if v ∈ I then μ I else 0

/-- `μ` is a `φ`-coloring of `G` (Definition 1.2): a probability distribution on the independent
sets of `G` (nonnegative weights on subsets of `V`, zero off the independent sets, total mass one)
under which every vertex `v` lies in the sampled set with probability at least `φ v`. -/
def IsPhiColoring (G : SimpleGraph V) (φ : V → ℝ) (μ : Finset V → ℝ) : Prop :=
  (∀ I, 0 ≤ μ I) ∧ (∀ I, μ I ≠ 0 → G.IsIndepSet (I : Set V)) ∧ (∑ I, μ I = 1) ∧
    ∀ v, φ v ≤ inclusionProb μ v

/-- `G` admits a `φ`-coloring. -/
def HasPhiColoring (G : SimpleGraph V) (φ : V → ℝ) : Prop :=
  ∃ μ : Finset V → ℝ, IsPhiColoring G φ μ

end FracColorLocal.KrFree


