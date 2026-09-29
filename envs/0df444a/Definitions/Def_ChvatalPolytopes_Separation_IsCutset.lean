-- Prove2me | Definitions.Def_ChvatalPolytopes_Separation_IsCutset
-- name    : ChvatalPolytopes_Separation_IsCutset
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T20:17:25.25772+00:00
-- url     : https://prove2.me/theorems/d9fb26ab-bb5f-438b-a8cb-ce198b3f3ed5
-- title:
--   Cutset of a graph (§4, proof of Corollary 4.3)
-- statement:
--   Let $G=(V,E)$ be a graph and $K\subseteq V$. Write $G-K$ for the subgraph of $G$ induced by $V\setminus K$. The set $K$ is a **cutset** of $G$ if there are two vertices $x,y\notin K$ that are joined by no path of $G-K$.
--
--   Equivalently, $G=G_1\cup G_2$ for graphs $G_1=(V_1,E_1)$, $G_2=(V_2,E_2)$ with $V_1\cap V_2=K$, $V_1-V_2\neq\emptyset$ and $V_2-V_1\neq\emptyset$; this is the form in which the proof of Corollary 4.3 uses the notion.
--
--   **Formalization Note** The paper does not define "cutset"; the definition above is the reading its proof of Corollary 4.3 uses. It is deliberately not "$G-K$ is disconnected" in Mathlib's sense, which would count $K=V$ as a cutset (Mathlib's connectedness requires a vertex) and make Corollary 4.3 false for $K_1$ and $K_2$. With this definition, $K=V$ and any $K$ with $|V\setminus K|\le1$ are never cutsets.
-- source:
--   Chvátal, On certain polytopes associated with graphs, J. Combin. Theory Ser. B 18 (1975), p. 144, §4, Corollary 4.3 and its proof (cutset)

import Mathlib

namespace ChvatalPolytopes.Separation

/-- **Cutset** (the notion used in the proof of Corollary 4.3, Chvátal 1975, p. 144): a vertex
set `K` of `G` is a *cutset* if there are two vertices `x, y` outside `K` that are not joined by
any path of `G − K`, the subgraph of `G` induced on the complement of `K`.

Equivalently, `G = G₁ ∪ G₂` with `V₁ ∩ V₂ = K`, `V₁ − V₂ ≠ ∅`, `V₂ − V₁ ≠ ∅` and no edge
between `V₁ − V₂` and `V₂ − V₁`. In particular `K = V` is never a cutset. -/
def IsCutset {V : Type*} (G : SimpleGraph V) (K : Set V) : Prop :=
  ∃ (x y : V) (hx : x ∉ K) (hy : y ∉ K),
    ¬ (G.induce Kᶜ).Reachable ⟨x, hx⟩ ⟨y, hy⟩

end ChvatalPolytopes.Separation


