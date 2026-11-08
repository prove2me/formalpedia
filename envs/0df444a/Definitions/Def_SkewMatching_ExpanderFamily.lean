-- Prove2me | Definitions.Def_SkewMatching_ExpanderFamily
-- name    : SkewMatching_ExpanderFamily
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:07:51.388179+00:00
-- url     : https://prove2.me/theorems/8e2da4dc-b994-4a57-abe8-157f4034770f
-- title:
--   Definition 17 — expanders, and the trial of the sampling step in §3.6
-- statement:
--   A family of edge-disjoint unweighted graphs $A_i$ on a vertex set $V$ has loopless edges with weights $w_e$, and the edges of $A_i$ have weights in $(2^{j_i-1},2^{j_i}]$ with $j_i\in\mathbb Z$. Here $\deg_{A}(v)$ counts the edges of $A$ at $v$ and $\mathrm{vol}_A(T)=\sum_{v\in T}\deg_A(v)$. The graph $A_i$ is a **$\phi$-expander** if $|\partial T|\ge\phi\min\{\mathrm{vol}(T),\mathrm{vol}(V\setminus T)\}$ for every cut $T$.
--
--   For a vertex set $S$, one **trial** of the sampling step chooses $A_i$ with probability proportional to $2^{j_i}\min\{\mathrm{vol}_{A_i}(S),\mathrm{vol}_{A_i}(V\setminus S)\}$, then a vertex $v$ of the smaller side with probability proportional to its degree, then an edge at $v$ uniformly; it rejects an edge outside $\partial S$, and accepts an edge $e\in\partial S$ with probability $w_e/2^{j_i}$. This definition gives the probability that one trial outputs a given edge as the explicit product of these factors.
--
--   **Formalization Note** Vertices off the support of $A_i$ have degree $0$, so cuts of $V$ and of the support give the same volumes. On a tie the smaller side is $V\setminus S$, as on p.11.
-- source:
--   Li, Li, Zhang, Maximum Cardinality Matching in n^{2+o(1)} Time, STOC 2027 submission (manuscript sha256 3fc151f5…), Definition 17, p.12; §3.6, proof of Lemma 16, pp.11–12

import Mathlib

namespace SkewMatching

open scoped Classical

/-- A finite family of edge-disjoint unweighted expanders on the vertex set `V`, as in the proof of Lemma 16, p.12: every edge `e` has endpoints and a
weight `w_e`, and the edges of the graph `A_i` have weights in `(2^{j_i − 1}, 2^{j_i}]`.

Li, Li, Zhang, *Maximum Cardinality Matching in n^{2+o(1)} Time*, STOC 2027 submission (manuscript sha256 3fc151f5…), §3.6, proof of Lemma 16, p.12.

**Formalization Note.** Expanders are taken in the paper from a decomposition of the unweighted graph `G_j` (Definition 18, p.12), so `deg`, `vol` and the
cut in Definition 17 count edges. -/
structure ExpanderFamily (V E ι : Type*) [Fintype ι] where
  ends : E → V × V
  ends_ne : ∀ e, (ends e).1 ≠ (ends e).2
  weight : E → ℝ
  edges : ι → Finset E
  level : ι → ℤ
  disjoint : ∀ i i', i ≠ i' → Disjoint (edges i) (edges i')
  weight_gt : ∀ i, ∀ e ∈ edges i, (2 : ℝ) ^ (level i - 1) < weight e
  weight_le : ∀ i, ∀ e ∈ edges i, weight e ≤ (2 : ℝ) ^ level i

namespace ExpanderFamily

variable {V E ι : Type*} [Fintype V] [Fintype E] [Fintype ι] (F : ExpanderFamily V E ι)

/-- `v` is an endpoint of `e`. -/
def IsEnd (v : V) (e : E) : Prop := (F.ends e).1 = v ∨ (F.ends e).2 = v

/-- The edges of `A_i` adjacent to `v`. -/
noncomputable def adj (i : ι) (v : V) : Finset E := (F.edges i).filter (F.IsEnd v)

/-- The degree `deg_{A_i}(v)`. -/
noncomputable def deg (i : ι) (v : V) : ℕ := (F.adj i v).card

/-- The volume `vol_{A_i}(T) = Σ_{v ∈ T} deg_{A_i}(v)`. -/
noncomputable def vol (i : ι) (T : Finset V) : ℕ := ∑ v ∈ T, F.deg i v

/-- `e ∈ ∂S`: exactly one endpoint of `e` lies in `S`. -/
def InCut (S : Finset V) (e : E) : Prop := ((F.ends e).1 ∈ S) ≠ ((F.ends e).2 ∈ S)

/-- **Definition 17 (ϕ-expander)**, p.12, for the unweighted graph `A_i`: for any cut `T`, `|∂T| ≥ ϕ min{vol(T), vol(V \ T)}`.
Vertices off the support of `A_i` have degree `0`, so testing all `T ⊆ V` is testing all cuts of the support. -/
def IsExpander (φ : ℝ) (i : ι) : Prop :=
  ∀ T : Finset V, φ * (min (F.vol i T) (F.vol i Tᶜ) : ℕ) ≤ (((F.edges i).filter (F.InCut T)).card : ℝ)

/-- The weight `2^{j_i} min{vol_{A_i}(U ∩ S), vol_{A_i}(U \ S)}` of the expander `A_i` (p.12). -/
noncomputable def expanderWeight (S : Finset V) (i : ι) : ℝ :=
  (2 : ℝ) ^ F.level i * (min (F.vol i S) (F.vol i Sᶜ) : ℕ)

/-- The total of the expander weights. -/
noncomputable def totalWeight (S : Finset V) : ℝ := ∑ i, F.expanderWeight S i

/-- The smaller side `B` of the cut, `V \ S` on ties as on p.11. -/
noncomputable def side (S : Finset V) (i : ι) : Finset V :=
  if F.vol i S < F.vol i Sᶜ then S else Sᶜ

/-- The sampling step on p.12, as a formula: the probability that one trial **outputs** the edge `e`. A trial samples the expander `i` with probability
proportional to its weight, then a vertex `v` of the smaller side `B` with probability proportional to its degree, then an edge `e′` adjacent to `v`
uniformly, rejects if `e′ ∉ ∂S`, and otherwise accepts with probability `w_{e′} / 2^{j_i}`. -/
noncomputable def trialProb (S : Finset V) (e : E) : ℝ :=
  ∑ i, F.expanderWeight S i / F.totalWeight S *
    ∑ v ∈ F.side S i, ((F.deg i v : ℝ) / (F.vol i (F.side S i) : ℝ)) *
      ∑ e' ∈ F.adj i v, (1 / (F.deg i v : ℝ)) *
        (if e' = e ∧ F.InCut S e then F.weight e / (2 : ℝ) ^ F.level i else 0)

end ExpanderFamily

end SkewMatching


