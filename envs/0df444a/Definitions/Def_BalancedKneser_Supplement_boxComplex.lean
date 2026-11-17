-- Prove2me | Definitions.Def_BalancedKneser_Supplement_boxComplex
-- name    : BalancedKneser_Supplement_boxComplex
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:13:33.94661+00:00
-- url     : https://prove2.me/theorems/4902fce2-5d52-42ae-bf0e-8e0ddf28102e
-- title:
--   Box complex $B(G)$ (weighted-pair model of $\mathrm{Hom}(K_2,G)$), its swap involution and the $\mathbb Z_2$-index
-- statement:
--   Let $G$ be a finite simple graph with vertex set $V$. The **box complex** $B(G)$, in the weighted-pair model of $\mathrm{Hom}(K_2,G)$, is the space of pairs $(\lambda,\mu)$ of probability distributions on $V$ such that every vertex in the positive support of $\lambda$ is adjacent to every vertex in the positive support of $\mu$:
--   $$
--   B(G)=\Bigl\{(\lambda,\mu)\in\mathbb R^V\times\mathbb R^V:\ \lambda,\mu\ge0,\ \textstyle\sum_v\lambda_v=\sum_v\mu_v=1,\ \lambda_v>0,\ \mu_w>0\ \Rightarrow\ vw\in E(G)\Bigr\}.
--   $$
--   Each complete bipartite subgraph of $G$ contributes the cell formed by the product of the two simplices of weights on its sides. The involution $\nu(\lambda,\mu)=(\mu,\lambda)$ exchanges the two sides.
--
--   A map $f:B(G)\to S^d$ to the unit sphere $S^d\subset\mathbb R^{d+1}$ is **equivariant** if exchanging the two sides sends its value to its negative, $f(\mu,\lambda)=-f(\lambda,\mu)$. The **$\mathbb Z_2$-index** $\operatorname{ind}_{\mathbb Z_2}B(G)$ is the least $d$ for which a continuous equivariant map $B(G)\to S^d$ exists.
--
--   The index gives Lovász's topological lower bound $\chi(G)\ge\operatorname{ind}_{\mathbb Z_2}B(G)+2$; Theorem 1.3 computes how far this bound reaches for the balanced graphs $G_{n,r}$.
--
--   **Formalization Note** A probability distribution on the finite type $V$ is a function $V\to\mathbb R$ with nonnegative values summing to $1$, and $B(G)$ (`boxComplex G`) is a subset of $(V\to\mathbb R)\times(V\to\mathbb R)$ with the subspace topology. `HasEquivSphereMap G d` asserts a continuous $f:B(G)\to\mathbb R^{d+1}$ (`EuclideanSpace ℝ (Fin (d+1))`) with $\|f\|=1$ everywhere and $f\circ\nu=-f$. The index `z2Index G` is valued in $\mathbb N\cup\{\infty\}$ (`ℕ∞`) and equals $\infty$ when no such map exists, so an upper bound on it is never vacuous.
-- source:
--   Alipour, Jafari, Balanced Fair Division and Generalized Kneser Graphs, arXiv:2611.04486v1, §9.1, p.17 (PDF p.19): weighted-pair model of B(G); §1, p.2 (PDF p.4): Z2-index; §10.1, p.24 (PDF p.26): equivariance

import Mathlib

namespace BalancedKneser.Supplement

/-- **Box complex** `B(G)` of a finite simple graph, in the weighted-pair model of
`Hom(K₂, G)` (Alipour–Jafari, *Balanced Fair Division and Generalized Kneser Graphs*,
arXiv:2611.04486v1, §9.1, p.17 (PDF p.19); used in §1, p.2 (PDF p.4) and §10.1, p.24
(PDF p.26)): its points are pairs `(λ, μ)` of probability distributions on `V(G)` such that every
vertex in the positive support of `λ` is adjacent to every vertex in the positive support of `μ`.

Formalization Note: a probability distribution on the finite vertex type `V` is a function
`V → ℝ` with nonnegative values summing to `1`; `B(G)` is the subset of `(V → ℝ) × (V → ℝ)` and
carries the subspace topology of the product (Euclidean) topology, which is the topology of the
geometric realization of this finite cell complex. -/
def boxComplex {V : Type*} [Fintype V] (G : SimpleGraph V) : Set ((V → ℝ) × (V → ℝ)) :=
  {p | (∀ v, 0 ≤ p.1 v) ∧ (∀ v, 0 ≤ p.2 v) ∧ ∑ v, p.1 v = 1 ∧ ∑ v, p.2 v = 1 ∧
    ∀ v w, 0 < p.1 v → 0 < p.2 w → G.Adj v w}

/-- The free involution of `B(G)` exchanging the two distributions, `(λ, μ) ↦ (μ, λ)`
(arXiv:2611.04486v1, §9.1, p.17 (PDF p.19)). -/
def boxSwap {V : Type*} [Fintype V] (G : SimpleGraph V) (p : boxComplex G) : boxComplex G :=
  ⟨(p.1.2, p.1.1), by
    obtain ⟨h1, h2, h3, h4, h5⟩ := p.2
    exact ⟨h2, h1, h4, h3, fun v w hv hw => (h5 w v hw hv).symm⟩⟩

/-- `B(G)` admits an **equivariant map to the sphere** `S^d` (arXiv:2611.04486v1, §1, p.2
(PDF p.4) and §10.1, p.24 (PDF p.26)): a continuous map `f` from `B(G)` to the unit sphere `S^d`
of `ℝ^{d+1}` that sends the exchange of the two sides to the antipodal map,
`f(μ, λ) = −f(λ, μ)`.

Formalization Note: `S^d` is `Metric.sphere 0 1` in `EuclideanSpace ℝ (Fin (d + 1))`; the map is
written into the ambient space together with the condition that every value lies on the sphere,
which is the same as a continuous map into the sphere with its subspace topology. -/
def HasEquivSphereMap {V : Type*} [Fintype V] (G : SimpleGraph V) (d : ℕ) : Prop :=
  ∃ f : boxComplex G → EuclideanSpace ℝ (Fin (d + 1)),
    Continuous f ∧ (∀ p, f p ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin (d + 1))) 1) ∧
      ∀ p, f (boxSwap G p) = -f p

/-- The **`ℤ₂`-index** `ind_{ℤ₂} B(G)` (arXiv:2611.04486v1, §1, p.2 (PDF p.4)): the least `d`
for which there is a continuous map `B(G) → S^d` sending the exchange of the two sides to
`x ↦ −x`.

Formalization Note: the index is valued in `ℕ∞` and is the infimum of the set of such `d`; when
no such `d` exists the infimum of the empty set is `⊤ = ∞`, so a bound `ind ≤ D` asserts that an
equivariant map to some `S^d` with `d ≤ D` exists. -/
noncomputable def z2Index {V : Type*} [Fintype V] (G : SimpleGraph V) : ℕ∞ :=
  sInf ((fun d : ℕ => (d : ℕ∞)) '' {d | HasEquivSphereMap G d})

end BalancedKneser.Supplement


