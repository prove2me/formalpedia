-- Prove2me | Definitions.Def_TwoConnSS_IsInitialCover
-- name    : TwoConnSS_IsInitialCover
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:46:30.563181+00:00
-- url     : https://prove2.me/theorems/4662eed3-be14-459c-9090-07d2dab6e2d6
-- title:
--   The initial cover $S_0$ of the 2ECSS algorithms
-- statement:
--   Let $G$ be a graph. An edge set $S_0$ is an **initial cover** of $G$ if:
--
--   1. $S_0$ is a triangle-free 2-edge-cover of $G$;
--   2. $|S_0| \le |F|$ for every triangle-free 2-edge-cover $F$ of $G$;
--   3. every 2EC component of $S_0$ with fewer than nine edges is a cycle;
--   4. every 2EC block of a complex component of $S_0$ has at least five vertices;
--   5. some component of $S_0$ has at least $32$ vertices;
--   6. for any two distinct 4-cycle components $C, C'$ of $S_0$, the graph $G$ has no cycle whose vertex set is $V(C) \cup V(C')$ (no spanning 8-cycle on their union).
--
--   Both algorithms of the paper start from this cover, and the counts $m_4$, $m_{\ne 4}$ are taken from it.
--
--   **Formalization Note** The paper obtains $S_0$ by a cited local-search canonicalization followed by 4-cycle merging; the definition lists the properties of the result that the paper states, not the procedure.
-- source:
--   A. Jabal Ameli, Improved Approximations for Two-Edge-Connected and Two-Vertex-Connected Spanning Subgraphs, STOC 2027 submission (manuscript sha256 22d0f2a8…2ae6a), §8.1, pp.32–33 (with Lemma 8.3 and "Initial 4-cycle merging")

import Mathlib
import Definitions.Def_TwoConnSS_IsTwoEdgeCover

namespace TwoConnSS

open Classical

variable {V : Type*} [Fintype V]

/-- **The initial cover `S₀` of §8.1.**
Jabal Ameli, *Improved Approximations for Two-Edge-Connected and Two-Vertex-Connected Spanning
Subgraphs*, STOC 2027 submission (manuscript sha256 22d0f2a8…), §8.1, pp.32–33: "This construction
gives a minimum triangle-free canonical cover S̃ containing a component with at least 32 vertices.
… Every 2EC component with fewer than nine edges is a cycle"; Lemma 8.3, p.32: "every block of a
complex component has at least five vertices"; p.33, "Initial 4-cycle merging": "We exhaustively
merge two 4-cycle components whenever their union admits a spanning 8-cycle in G … This preserves
the size of the cover and its other canonical properties … We denote the resulting cover by S0."

`IsInitialCover G S₀` lists the properties of `S₀`:
1. `S₀` is a triangle-free 2-edge-cover of `G`;
2. `|S₀| ≤ |F|` for every triangle-free 2-edge-cover `F` of `G`;
3. every 2EC component of `S₀` with fewer than nine edges is a cycle;
4. every 2EC block of a complex component of `S₀` has at least five vertices;
5. some component of `S₀` has at least 32 vertices;
6. for two distinct 4-cycle components `C, C'` of `S₀`, `G` has no cycle with vertex set
   `V(C) ∪ V(C')` (no spanning 8-cycle on their union).

**Formalization Note.** The cited procedure ([20, Appendix B]) is replaced by the properties of
its output that the paper states; this is the procedure-free reading recorded with Lemma 8.3. -/
def IsInitialCover (G : SimpleGraph V) (S₀ : Finset (Sym2 V)) : Prop :=
  IsTwoEdgeCover G S₀ ∧ IsTriangleFree S₀ ∧
  (∀ F, IsTwoEdgeCover G F → IsTriangleFree F → S₀.card ≤ F.card) ∧
  (∀ C, IsTwoECComp S₀ C → (edgesIn S₀ C).card < 9 → ∀ v ∈ C, deg S₀ v = 2) ∧
  (∀ C, IsComplexComp S₀ C → ∀ B ∈ blocksIn S₀ C, 5 ≤ B.card) ∧
  (∃ C ∈ comps S₀, 32 ≤ C.card) ∧
  (∀ C C', IsCycleComp S₀ C 4 → IsCycleComp S₀ C' 4 → C ≠ C' →
    ¬ ∃ (v : V) (w : G.Walk v v), w.IsCycle ∧ ∀ x, x ∈ w.support ↔ x ∈ C ∪ C')

end TwoConnSS


