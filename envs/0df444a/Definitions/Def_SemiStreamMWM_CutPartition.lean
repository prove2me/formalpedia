-- Prove2me | Definitions.Def_SemiStreamMWM_CutPartition
-- name    : SemiStreamMWM_CutPartition
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:19:21.638357+00:00
-- url     : https://prove2.me/theorems/1749ad48-83c4-4829-9d10-2fbb2f480be6
-- title:
--   §2.3, §3.1 — internal and crossing edges, the odd-set guarantee, and the cut partition $\mathcal Q$
-- statement:
--   Given a partition $\mathcal Q$ of $V$, an edge is **internal** if its endpoints lie in the same part and **crossing** otherwise; a matching is crossing if all its edges are. The **odd-set guarantee** of $\mathcal Q$ for $x$ and $\delta$ (property 2 of Lemma 3.1) is: for every crossing matching $J$, every odd set $S$ and every $0\le\eta\le\delta/4$, $(x+\eta\vec1_J)(S)\le(|S|-1)/2$.
--
--   §3.1 builds $\mathcal Q$ from $x\in\mathcal P_{G,\delta}$. Set $\gamma=(1-\delta)/\lceil16(1-\delta)/\delta^2\rceil$ and $\tilde x_e=\gamma\lfloor x_e/\gamma\rfloor$. In the rooted graph $G_{\tilde x,\delta}$ every edge $e$ has capacity $\tilde x_e$ and a new root $r$ is joined to each $v$ with capacity $1-\delta-\tilde x_v$. For $S\subseteq V$ the cut capacity is
--
--   $$f(S)=\sum_{e\in E:\,|e\cap S|=1}\tilde x_e+\sum_{v\in S}(1-\delta-\tilde x_v).$$
--
--   $Q_v$ is an inclusion-minimal minimum $v$–$r$ cut side containing $v$, and $\mathcal Q$ consists of the members $Q_v$ that no $Q_u$ strictly contains.
--
--   This partition is what makes a crossing matching a safe step: Lemma 3.3 bounds its internal edges and Lemma 3.4 proves its odd-set guarantee.
--
--   **Formalization Note** A partition is given by its family of parts. A choice of the sides $Q_v$ is a function $V\to$ `Finset V`; cut sides never contain the root.
-- source:
--   J. Chen, Faster Semi-Streaming and Dynamic Approximate Maximum Weight Matchings in General Graphs: A Unified Framework (STOC 2027 submission, preprint, arXiv:2611.02105, sha256 83213124981525da907e0f2f9e1e9da47f70f80b9aa72c30767fb094e3bf6934), §2.3 p.13; Lemma 3.1 p.14; §3.1 p.14

import Mathlib
import Definitions.Def_SemiStreamMWM_Graph

open Classical

namespace SemiStreamMWM

/-! # Partitions, internal and crossing edges, and the cut partition of §3.1

J. Chen (STOC 2027 submission, arXiv:2611.02105, sha256 83213124…), §2.3 p.13 ("We call an edge
internal if its endpoints lie in the same part, and crossing otherwise"), Lemma 3.1 p.14 (the
odd-set guarantee, property 2), §3.1 p.14 (`γ`, `x̃`, the rooted graph `G_{x̃,δ}`, its cut function
`f`, the sides `Q_v`, and the partition `Q` of inclusion-maximal `Q_v`).

**Formalization Note.** A partition is given by its family of parts (`Set (Finset V)`). The rooted
graph `G_{x̃,δ}` adds a root `r` joined to every vertex `v` with capacity `1 − δ − x̃_v`; a cut side
of a `v–r` cut is a set `S ⊆ V` with `v ∈ S` (it never contains `r`), and its capacity `f(S)` is the
sum of `x̃_e` over the edges with exactly one endpoint in `S` plus the root capacities of the
vertices of `S`, as on p.14. `x̃_e = γ⌊x_e/γ⌋` uses the integer floor. A choice `Q_v` of an
inclusion-minimal minimum `v–r` cut side for every `v` is a function `Qf : V → Finset V`; the parts
are the `Q_v` not strictly contained in any `Q_u`, each counted once as a set. -/

variable {V : Type*} [Fintype V]

/-- The edge `e` is internal for the family of parts `Q`: both endpoints lie in one part. -/
def IsInternal (Q : Set (Finset V)) (e : Sym2 V) : Prop :=
  ∃ P ∈ Q, ∀ u ∈ e, u ∈ P

/-- The internal edges of `G`: the edge set of the internal graph `H = (V, ⋃_{Q∈Q} E[Q])`. -/
noncomputable def internalEdges (G : SimpleGraph V) (Q : Set (Finset V)) : Finset G.edgeSet :=
  Finset.univ.filter fun e => IsInternal Q e.1

/-- Property 2 of Lemma 3.1, the odd-set guarantee of the parts `Q` for `x` and `δ`: for every
crossing matching `J`, odd set `S ∈ O_G` and `0 ≤ η ≤ δ/4`, `(x + η1_J)(S) ≤ (|S| − 1)/2`. -/
def OddSetGuarantee (G : SimpleGraph V) (Q : Set (Finset V)) (δ : ℝ) (x : G.edgeSet → ℝ) : Prop :=
  ∀ J : Finset G.edgeSet, IsMatching G J → (∀ e ∈ J, ¬ IsInternal Q e.1) →
    ∀ S : Finset V, Odd S.card → ∀ η : ℝ, 0 ≤ η → η ≤ δ / 4 →
      inside G (x + η • ind G J) S ≤ ((S.card : ℝ) - 1) / 2

/-- `γ = (1 − δ)/⌈16(1 − δ)/δ²⌉` (p.14). -/
noncomputable def gam (δ : ℝ) : ℝ := (1 - δ) / (⌈16 * (1 - δ) / δ ^ 2⌉₊ : ℝ)

/-- `x̃_e = γ⌊x_e/γ⌋` (p.14). -/
noncomputable def xt (G : SimpleGraph V) (δ : ℝ) (x : G.edgeSet → ℝ) : G.edgeSet → ℝ :=
  fun e => gam δ * (⌊x e / gam δ⌋ : ℝ)

/-- The edge `e` has exactly one endpoint in `S` (`|e ∩ S| = 1` for a non-loop edge). -/
def Crosses (S : Finset V) (e : Sym2 V) : Prop :=
  (∃ u ∈ e, u ∈ S) ∧ ∃ u ∈ e, u ∉ S

/-- The cut capacity of `S ⊆ V` in `G_{x̃,δ}` (p.14):
`f(S) = Σ_{e∈E : |e∩S|=1} x̃_e + Σ_{v∈S} x̃_{vr}`, with `x̃_{vr} = 1 − δ − x̃_v`. -/
noncomputable def cutCap (G : SimpleGraph V) (δ : ℝ) (x : G.edgeSet → ℝ) (S : Finset V) : ℝ :=
  (∑ e : G.edgeSet, if Crosses S (e : Sym2 V) then xt G δ x e else 0) +
    ∑ v ∈ S, (1 - δ - deg G (xt G δ x) v)

/-- `S` is a minimum `v–r` cut side containing `v` in `G_{x̃,δ}`. -/
def IsMinCutSide (G : SimpleGraph V) (δ : ℝ) (x : G.edgeSet → ℝ) (v : V) (S : Finset V) : Prop :=
  v ∈ S ∧ ∀ S' : Finset V, v ∈ S' → cutCap G δ x S ≤ cutCap G δ x S'

/-- `S` is an inclusion-minimal minimum `v–r` cut side containing `v` (p.14): no proper subset of `S`
containing `v` is also a minimum cut side. -/
def IsMinimalMinCutSide (G : SimpleGraph V) (δ : ℝ) (x : G.edgeSet → ℝ) (v : V) (S : Finset V) :
    Prop :=
  IsMinCutSide G δ x v S ∧ ∀ S' : Finset V, S' ⊂ S → v ∈ S' → ¬ IsMinCutSide G δ x v S'

/-- The partition `Q` of §3.1 (p.14): the members `Q_v` that no `Q_u` strictly contains. -/
def partsOf (Qf : V → Finset V) : Set (Finset V) :=
  {P | ∃ v, P = Qf v ∧ ∀ u, ¬ Qf v ⊂ Qf u}

end SemiStreamMWM


