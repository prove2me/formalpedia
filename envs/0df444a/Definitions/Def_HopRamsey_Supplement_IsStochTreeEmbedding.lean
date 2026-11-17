-- Prove2me | Definitions.Def_HopRamsey_Supplement_IsStochTreeEmbedding
-- name    : HopRamsey_Supplement_IsStochTreeEmbedding
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:07:25.114831+00:00
-- url     : https://prove2.me/theorems/414421a2-9bf9-47e2-b968-7836332697b0
-- title:
--   Stochastic dominating embeddings into arbitrary trees: tree metrics, exclusion probability, expected distortion
-- statement:
--   Let $G=(V,E,w)$ be a weighted graph with shortest-path distance $d_G$. A function $d:V\times V\to[0,\infty]$ is a **tree metric** if there are a weighted tree $T$ (any vertex set, positive edge weights) and a map $f:V\to V(T)$ with $d(u,v)=d_T(f(u),f(v))$ for all $u,v$.
--
--   A **stochastic dominating embedding of $G$ into trees** is given by a probability space $(\Omega,\mu)$ and, for each sample $\omega$, a distance $d_\omega$ on $V$ and a saved set $M_\omega\subseteq V$, such that
--
--   1. $\omega\mapsto d_\omega(u,v)$ and the events $\{v\in M_\omega\}$ are measurable;
--   2. almost surely, $d_\omega$ is a tree metric;
--   3. almost surely, $d_G(u,v)\le d_\omega(u,v)$ for all saved $u,v\in M_\omega$.
--
--   It has **exclusion probability** $\varepsilon$ if $\Pr[v\notin M]\le\varepsilon$ for every $v\in V$, and **expected distortion** $t$ if for all $u,v\in V$
--   $$\mathbb E\big[d_{T,M}(u,v)\big]\le t\cdot d_G(u,v),\qquad d_{T,M}(u,v)=d_T(u,v)\cdot\mathbf 1_{u,v\in M}.$$
--
--   These are the objects of the expected-distortion lower bound (Theorem 3): the classical notion of stochastic tree embedding of §3, combined with the saved sets, exclusion probability and nullified expected distortion of Definition 2, with hop constraints disregarded.
--
--   **Formalization Note** Only the pulled-back distances are recorded, so the measure lives on an arbitrary sample type. Domination is required on saved pairs only, which is what the lower-bound proof uses. The expectation is the lower Lebesgue integral in $[0,\infty]$, and a negative $t$ counts as $0$.
-- source:
--   Filtser, Zuzic, Trees with Benefits: Stochastic Hop-Constrained Ramsey-Type Embeddings with Logarithmic Expected Distortion, STOC 2027 submission (manuscript sha256 1ee73385…), §3 "Metric Embeddings", p.13 (PDF p.15); Definition 2, pp.13–14 (PDF pp.15–16); §5.2, p.27 (PDF p.29)

import Mathlib
import Definitions.Def_ARTreeCover_WGraph

open scoped ENNReal
open MeasureTheory

namespace HopRamsey

namespace Supplement

open ARTreeCover

/-- A distance function `d : V → V → [0, ∞]` is a **tree metric** if it is the pull-back of the
shortest-path distance of an arbitrary weighted tree: there are a vertex type `W`, a weighted graph
`T` on `W` whose underlying simple graph is a tree, and a map `f : V → W` with
`d u v = d_T(f u, f v)`.

Filtser, Zuzic, *Trees with Benefits: Stochastic Hop-Constrained Ramsey-Type Embeddings with
Logarithmic Expected Distortion*, STOC 2027 submission (manuscript sha256 1ee73385…), §3 "Metric
Embeddings", p.13 (PDF p.15), and §5.2, p.27 (PDF p.29): "every stochastic embedding of G into
trees".

**Formalization Note.** The tree is arbitrary: `W` is any type (finite or infinite), the edge weights
are positive reals (`ARTreeCover.WGraph`, the paper's convention on p.12), and `IsTree` is Mathlib's
`SimpleGraph.IsTree` (connected, hence nonempty, and acyclic). Only the distances the embedding
induces on `V` are recorded. -/
def IsTreeMetric {V : Type} (d : V → V → ℝ≥0∞) : Prop :=
  ∃ (W : Type) (T : WGraph W), T.graph.IsTree ∧
    ∃ f : V → W, d = fun u v => T.dist (f u) (f v)

/-- A **stochastic dominating embedding of `G` into trees with saved sets** (§3, p.13, PDF p.15, and
Definition 2, pp.13–14, PDF pp.15–16, with the hop constraints disregarded as in §5.2, p.27, PDF
p.29). The randomness is a probability space `(Ω, μ)`; a sample `ω` yields the pulled-back tree
distance `d ω` on `V` and the saved set `M ω ⊆ V`.

1. `μ` is a probability measure, and the sample is measurable: each `ω ↦ d ω u v` is measurable and
   each event `{ω | v ∈ M ω}` is measurable.
2. Almost every sample is a tree metric (`IsTreeMetric`).
3. Almost every sample is dominating on its saved set: `d_G(u, v) ≤ d ω u v` for `u, v ∈ M ω`.

**Formalization Note.** The paper's distribution is over dominating embeddings. Domination is
required on saved pairs only, which is all the paper's lower-bound proof uses ("As the embedding is
dominating, every cluster will have diameter at most ∆ also w.r.t. the graph G distances", p.28);
requiring it on all pairs would only shrink the class of embeddings. Measurability makes the
probabilities and expectations of `HasExclusionProb` and `HasExpectedDistortion` the usual ones;
every distribution with countable support (a `PMF`) is an instance with `Ω` its sample type. -/
structure IsStochTreeEmbedding {V : Type} (G : WGraph V) {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) (d : Ω → V → V → ℝ≥0∞) (M : Ω → Finset V) : Prop where
  /-- `μ` is a probability measure. -/
  isProbability : IsProbabilityMeasure μ
  /-- Each sampled distance is a measurable function of the sample. -/
  measurable_dist : ∀ u v : V, Measurable fun ω => d ω u v
  /-- Each event "v is saved" is measurable. -/
  measurableSet_mem : ∀ v : V, MeasurableSet {ω | v ∈ M ω}
  /-- Almost every sample is a tree metric. -/
  tree : ∀ᵐ ω ∂μ, IsTreeMetric (d ω)
  /-- Almost every sample dominates `d_G` on its saved pairs. -/
  dominating : ∀ᵐ ω ∂μ, ∀ u ∈ M ω, ∀ v ∈ M ω, G.dist u v ≤ d ω u v

/-- **Exclusion probability** `ε` (Definition 2, third bullet, p.14, PDF p.16):
`Pr[v ∉ M] ≤ ε` for every vertex `v`. -/
def HasExclusionProb {V : Type} {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (M : Ω → Finset V) (ε : ℝ) : Prop :=
  ∀ v : V, μ {ω | v ∉ M ω} ≤ ENNReal.ofReal ε

/-- **Expected distortion** `t` (Definition 2, fourth bullet, p.14, PDF p.16, with `d_G` in place of
`d^{(h)}_G`): for all `u, v`, `E[d_{T,M}(u, v)] ≤ t · d_G(u, v)`, where the sampled distance is
nullified unless both endpoints are saved, `d_{T,M}(u, v) = d_T(u, v) · 1_{u, v ∈ M}` (p.2).

**Formalization Note.** The expectation is the lower Lebesgue integral in `[0, ∞]`; a negative `t`
is read as `0` (`ENNReal.ofReal`). -/
def HasExpectedDistortion {V : Type} [DecidableEq V] (G : WGraph V) {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) (d : Ω → V → V → ℝ≥0∞) (M : Ω → Finset V) (t : ℝ) : Prop :=
  ∀ u v : V, ∫⁻ ω, (if u ∈ M ω ∧ v ∈ M ω then d ω u v else 0) ∂μ ≤ ENNReal.ofReal t * G.dist u v

end Supplement

end HopRamsey


