-- Prove2me | Definitions.Def_BootstrapRecolorVerify_MetricGap_Construction
-- name    : BootstrapRecolorVerify_MetricGap_Construction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T03:37:24.509005+00:00
-- url     : https://prove2.me/theorems/bc071559-ebd3-4ea2-aeb5-c6b9c0c71900
-- title:
--   The augmented terminal instance and merging objective edges
-- statement:
--   Given the final labeled hierarchy $G_r$, attach a terminal leaf $\widetilde u$ to each vertex $u$, with length $L$ and weight $1/L$. The terminal metric is zero on the diagonal and
--
--   $$d_T(\widetilde u,\widetilde v)=2L+d_r(u,v)\quad(u\ne v).$$
--
--   The augmented graph is represented on $V(G_r)\sqcup V(G_r)$, with terminals in the second copy. Its terminal distances are computed in the original multigraph before parallel objective edges are merged. The weight of a merged objective edge is the sum of all its constituent weights; lengths are never summed. Thus every assignment cost and every metric-extension objective is preserved.
--
--   This constructor supplies the paper's instance using the published generic 0-extension interface. It has no lower-bound field or distinguished solution. Validity holds in the sufficiently-large accepted regime where the hierarchy is connected.
-- source:
--   Konstantin Makarychev, STOC 2027 submission #1436 (October 2026), §3 pp.7–8; §6.1 p.22; final merging representation of the same instance, p.7; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1436.pdf#page=7; PDF SHA-256 c6f69cddcebf9bb51692e022b1f2a1c3ca49babeba005dc1d6ce05e954bea358.

import Mathlib
import Definitions.Def_BootstrapRecolorVerify_MetricGap_Hierarchy
import Definitions.Def_BootstrapRecolorVerify_MetricGap_MetricLP

open scoped Classical

namespace BootstrapRecolorVerify.MetricGap

/-- The augmented graph, §§3,6.1 pp.7,22, with one new terminal leaf per
vertex. Only the final objective graph merges parallel edges; all lengths and
terminal distances have already been computed on the labeled multigraph. -/
def augmentedGraph {r : ℕ} (H : History r r) :
    SimpleGraph (Vertex r r ⊕ Vertex r r) where
  Adj
    | Sum.inl u, Sum.inl v => u ≠ v ∧ ∃ e, Joins H e u v
    | Sum.inl u, Sum.inr v => u = v
    | Sum.inr u, Sum.inl v => u = v
    | Sum.inr _, Sum.inr _ => False
  symm := ⟨by
    rintro (u | u) (v | v) h
    · rcases h with ⟨hne, e, he⟩
      exact ⟨Ne.symm hne, e, he.elim Or.inr Or.inl⟩
    · exact h.symm
    · exact h.symm
    · exact h⟩
  loopless := ⟨by
    rintro (u | u) h
    · exact h.1 rfl
    · exact h⟩

/-- Objective weights are SUMMED over parallel edges; metric lengths are never
summed. Pendant edges retain weight 1/L, including vertices fixed by a map. -/
noncomputable def augmentedWeight {r : ℕ} (H : History r r)
    (e : Sym2 (Vertex r r ⊕ Vertex r r)) : ℝ :=
  (∑ f : Edge r r,
    if s(Sum.inl (endpoints H f).1, Sum.inl (endpoints H f).2) = e then
      edgeWeight r (edgeLevel f) else 0) +
  ∑ u : Vertex r r, if s(Sum.inl u, Sum.inr u) = e then (L r : ℝ)⁻¹ else 0

/-- Forget whether an augmented vertex is a terminal. -/
def underlyingVertex {V : Type*} : V ⊕ V → V := Sum.elim id id

/-- The source instance as the compatible published generic instance, with the
terminal shortest-path metric computed BEFORE merging parallel objective edges.
It is valid in the source's sufficiently-large accepted regime; the data type
itself does not assume any cost bound or any gap. -/
noncomputable def hierarchyInstance {r : ℕ} (H : History r r) :
    ZeroExtensionGap.Instance (Vertex r r ⊕ Vertex r r) where
  G := augmentedGraph H
  w := augmentedWeight H
  T := Finset.univ.map ⟨Sum.inr, Sum.inr_injective⟩
  D u v := terminalDistance H (underlyingVertex u) (underlyingVertex v)

end BootstrapRecolorVerify.MetricGap


