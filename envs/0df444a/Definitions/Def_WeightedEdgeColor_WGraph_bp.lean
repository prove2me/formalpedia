-- Prove2me | Definitions.Def_WeightedEdgeColor_WGraph_bp
-- name    : WeightedEdgeColor_WGraph_bp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:47:09.824263+00:00
-- url     : https://prove2.me/theorems/77906877-244f-4dc2-ae38-50832d75e3b8
-- title:
--   Local bin-packing number $\mathrm{bp}(G)=\max_v \mathrm{bp}_v(G)$
-- statement:
--   Let $G=(V,E)$ be an edge-weighted graph with weights in $(0,1]$. For a vertex $v$, $\mathrm{bp}_v(G)$ is the minimum number of unit-capacity bins needed to pack the weights of the edges incident with $v$: the least $m$ such that $E(v)$ can be split into $m$ parts, each of total weight at most one. The **local bin-packing number** is
--   $$
--   \mathrm{bp}(G)=\max_{v\in V}\mathrm{bp}_v(G).
--   $$
--   Every proper weighted coloring induces a feasible bin packing at each vertex, so $\lceil\Delta_w(G)\rceil\le\mathrm{bp}(G)\le\chi'_w(G)$.
--
--   The local bin-packing number is the lower bound against which the main theorem measures $\chi'_w(G)$.
--
--   **Formalization Note** $\mathrm{bp}(G)$ is defined as the least $m$ such that every vertex, separately, admits a packing of its incident edges into $m$ bins; since a packing into $m$ bins is also one into more bins, this equals the maximum of the local optima. The packing is chosen independently at each vertex (one packing shared by all vertices would be a proper coloring). A graph with no vertices has $\mathrm{bp}(G)=0$. A short lemma in the module shows that $|E|$ bins always suffice, so the least such $m$ exists.
-- source:
--   Gajjala, Khan, Asymptotically Optimal Weighted Edge Colorings via Local Bin Packing, preprint (arXiv:2611.03190, version not stamped), §1, p.1; Appendix A, p.24

import Mathlib
import Definitions.Def_WeightedEdgeColor_WGraph

set_option autoImplicit false

namespace WeightedEdgeColor

namespace WGraph

variable {V E : Type} [Fintype E] [DecidableEq V]

/-- The edges incident with `v` can be packed into `m` unit-capacity bins: some assignment
`f : E → Fin m` of bins puts total weight at most one of the edges at `v` into each bin.
(Only the edges at `v` matter; the assignment is chosen for this vertex alone.) -/
def PacksInto (G : WGraph V E) (v : V) (m : ℕ) : Prop :=
  ∃ f : E → Fin m, ∀ j : Fin m, ∑ e ∈ (G.inc v).filter (fun e => f e = j), G.w e ≤ 1

/-- With `|E|` bins, one edge per bin, every vertex can be packed (weights are at most one). -/
theorem exists_packsInto (G : WGraph V E) : ∃ m : ℕ, ∀ v, G.PacksInto v m := by
  classical
  refine ⟨Fintype.card E, fun v => ⟨Fintype.equivFin E, fun j => ?_⟩⟩
  calc ∑ e ∈ (G.inc v).filter (fun e => Fintype.equivFin E e = j), G.w e
      ≤ ∑ e ∈ ({(Fintype.equivFin E).symm j} : Finset E), G.w e := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro e he
          rw [Finset.mem_filter] at he
          rw [Finset.mem_singleton, ← he.2]
          simp
        · intro e _ _
          exact (G.w_pos e).le
    _ = G.w ((Fintype.equivFin E).symm j) := Finset.sum_singleton _ _
    _ ≤ 1 := G.w_le_one _

open Classical in
/-- The local bin-packing number `bp(G) = max_v bp_v(G)`, where `bp_v(G)` is the minimum number
of unit-capacity bins needed to pack the weights of the edges incident with `v`. It is the least
`m` such that **every** vertex, separately, can be packed into `m` bins.

Source: Gajjala, Khan, preprint of November 2, 2026 (arXiv:2611.03190, version not stamped),
§1, p.1; Appendix A, p.24.

**Formalization Note.** The packing is chosen per vertex (`∃ f` inside `∀ v` in `PacksInto`);
one packing shared by all vertices would be a proper coloring. Because a packing into `m` bins
is also one into any `m' ≥ m` bins, the least common `m` equals the maximum over vertices of
the local optima. For a graph with no vertices, `bp(G) = 0`. -/
noncomputable def bp (G : WGraph V E) : ℕ := Nat.find G.exists_packsInto

end WGraph

end WeightedEdgeColor


