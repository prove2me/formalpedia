-- Prove2me | Definitions.Def_MetricMatchingDistortion_IsFlowDecomp
-- name    : MetricMatchingDistortion_IsFlowDecomp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:15:41.435121+00:00
-- url     : https://prove2.me/theorems/61bad5ca-3f39-416f-ad18-c0207a2504b8
-- title:
--   The flow $f$ of §6.2.1, its path–cycle decompositions, and the matrix $F(t)$
-- statement:
--   Fix a matrix $X$ (on the page $X(t)$) and a perfect matching $\pi^*$ (on the page $M^*$). The **flow** $f$ on the complete directed graph on agents and items sends $X_{a,b}$ along every arc $(b,a)$ from an item to an agent and $1$ along every arc $(a,\pi^*(a))$; every other arc carries $0$.
--
--   A **path–cycle decomposition** of a flow $f$ is a finite family of weighted walks $(\alpha_P,P)$, each starting at an agent and ending at an item, and of weighted closed walks $(\beta_Q,Q)$, with all weights nonnegative, such that $f=\sum_P\alpha_P\mathbf 1_P+\sum_Q\beta_Q\mathbf 1_Q$, where $\mathbf 1_W(u,v)$ counts the traversals of the arc $(u,v)$ by $W$.
--
--   The matrix of the decomposition is $F_{ab}=\sum_{P\text{ from }a\text{ to }b}\alpha_P$.
--
--   **Formalization Note** Paths and cycles are walks and may repeat vertices. The page's decomposition into simple paths and simple cycles is one of these.
-- source:
--   Charikar, Haqi, Hastings, Huang, Ramakrishnan, Sublinear Metric Distortion for Matching, arXiv:2611.05777 (held version, sha256 fdf3452b105082d6ff680c8a762ec950298417efdebeb216b721705a9802e0da), §6.2.1, pp.51–52 (PDF pp.53–54)

import Mathlib

namespace MetricMatchingDistortion

variable {n : ℕ}

/-- **The flow `f` of §6.2.1.** Charikar et al., *Sublinear Metric Distortion for Matching*,
arXiv:2611.05777 (held version, sha256 fdf3452b…), §6.2.1, p.51 (PDF p.53): "Fix t ∈ [0, 1). We
consider a flow f on the directed graph on vertices A ∪ B such that the following hold: 1. Each item
b sends X_{a,b}(t) units of flow along edge (b, a) for every a ∈ A. 2. Each agent a sends 1 unit of
flow along edge (a, M∗(a))."

`psFlow X πstar u v` is the flow on the arc `u → v` of the complete directed graph on agents
(`Sum.inl a`) and items (`Sum.inr b`), for the matrix `X` (on the page `X(t)`) and the perfect
matching `πstar` (on the page `M∗`); arcs not listed carry `0`. -/
def psFlow (X : Fin n → Fin n → ℝ) (πstar : Equiv.Perm (Fin n)) :
    Fin n ⊕ Fin n → Fin n ⊕ Fin n → ℝ
  | Sum.inr b, Sum.inl a => X a b
  | Sum.inl a, Sum.inr b => if πstar a = b then 1 else 0
  | _, _ => 0

/-- The arcs `v₀ → v₁ → ⋯ → v_k` of a walk written as its vertex list `[v₀, …, v_k]`, with
multiplicity. -/
def walkArcs (w : List (Fin n ⊕ Fin n)) : List ((Fin n ⊕ Fin n) × (Fin n ⊕ Fin n)) :=
  w.zip w.tail

/-- The arcs of the closed walk `v₀ → ⋯ → v_k → v₀` written as `[v₀, …, v_k]`, with multiplicity. -/
def cycleArcs : List (Fin n ⊕ Fin n) → List ((Fin n ⊕ Fin n) × (Fin n ⊕ Fin n))
  | [] => []
  | x :: w => walkArcs (x :: w ++ [x])

/-- **A path–cycle decomposition of a flow** (§6.2.1, pp.51–52 = PDF pp.53–54): "By the flow
decomposition theorem, we can write f = ∑_{P∈𝒫} α_P 1_P + ∑_{Q∈𝒬} β_Q 1_Q, α_P, β_Q ≥ 0, where 𝒫 is
a set of directed paths, each from an agent to an item, 𝒬 is a set of directed cycles, and 1_P and
1_Q are the arc-incidence vectors of P and Q".

`paths` and `cycles` are lists of weighted walks `(weight, vertex list)`. Every path starts at an
agent and ends at an item, every weight is nonnegative, and on every arc `(u, v)` the flow `f u v`
is the weighted number of traversals of `(u, v)` by the paths and the closed walks.

**Formalization Note.** Paths and cycles are walks: they may repeat vertices. Every decomposition
into simple paths and simple cycles, the page's, is one of these. -/
def IsFlowDecomp (f : Fin n ⊕ Fin n → Fin n ⊕ Fin n → ℝ)
    (paths cycles : List (ℝ × List (Fin n ⊕ Fin n))) : Prop :=
  (∀ p ∈ paths, 0 ≤ p.1 ∧ (∃ a, p.2.head? = some (Sum.inl a)) ∧
      ∃ b, p.2.getLast? = some (Sum.inr b)) ∧
    (∀ q ∈ cycles, 0 ≤ q.1) ∧
    ∀ u v, f u v = (paths.map fun p => p.1 * ((walkArcs p.2).count (u, v) : ℝ)).sum +
      (cycles.map fun q => q.1 * ((cycleArcs q.2).count (u, v) : ℝ)).sum

/-- **The matrix `F(t)`** (§6.2.1, p.52 = PDF p.54): "For an agent a and an item b, let 𝒫_{ab} ⊆ 𝒫
be the paths from a to b, and define F_{ab}(t) = ∑_{P∈𝒫_{ab}} α_P." -/
def pathMatrix (paths : List (ℝ × List (Fin n ⊕ Fin n))) : Fin n → Fin n → ℝ :=
  fun a b => ((paths.filter fun p =>
    decide (p.2.head? = some (Sum.inl a) ∧ p.2.getLast? = some (Sum.inr b))).map Prod.fst).sum

end MetricMatchingDistortion


