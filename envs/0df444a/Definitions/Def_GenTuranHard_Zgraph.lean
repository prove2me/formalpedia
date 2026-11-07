-- Prove2me | Definitions.Def_GenTuranHard_Zgraph
-- name    : GenTuranHard_Zgraph
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:35:14.147006+00:00
-- url     : https://prove2.me/theorems/776fc510-8646-4275-a28f-697ba2d73caa
-- title:
--   The graph $Z = L_{\mathbf x}(G)(B)$, $J^+$, $J^-$, the transversal graph $R_J$ and $\mathbb E[e(R_J)]$
-- statement:
--   Let $G$ be a graph on $n$ vertices, $\mathbf x$ a vector of positive integers and $B$ a positive integer. Then (§4.2, pp.17–20)
--
--   1. $Z = L_{\mathbf x}(G)(B)$ is the $B$-blow-up of $L_{\mathbf x}(G)$; the clusters $C_v$ of the original vertices $v \in V(G)$ induce a copy of $G(B)$;
--   2. for a subgraph $J \subseteq Z$, $J^+$ has vertex set $V(Z)$ and edge set $(E(J) \cap E(G(B))) \cup (E(Z) \setminus E(G(B)))$ (p.17);
--   3. $J^-$ is the subgraph of $J$ induced by $V(J) \cap \bigcup_{v \in V(G)} C_v$ (p.20);
--   4. for a choice of one vertex $v' \in C_v$ for each $v \in V(G)$, $R_J$ is the spanning subgraph of $G$ with $E(R_J) = \{uv \in E(G) : u', v' \in V(J),\ u'v' \in E(J)\}$ (p.18);
--   5. $\mathbb E[e(R_J)]$ is the expected number of edges of $R_J$ when the vertices $v'$ are chosen independently and uniformly.
--
--   $Z$ is the host graph produced by the reduction, and $\mathbb E[e(R_J)]$ is the quantity of the random-transversal bound (Lemma 4.7).
--
--   **Formalization Note** Vertex $i$ of $Z$ lies in the cluster of vertex $\lfloor i/B \rfloor$ of $L_{\mathbf x}(G)$, and the clusters of $V(G)$ are those with index $< n$ (the original graph occupies the first $n$ vertices of $L_{\mathbf x}(G)$). A transversal is a map $\sigma : V(G) \to \{0,\dots,B-1\}$ with $v' = vB + \sigma(v)$, and the expectation is the average over all $B^n$ maps.
-- source:
--   Chen, He, Li, Ma, Xie, NP-hardness of additive approximation for generalized Turán problems, arXiv:2610.16358 (sha256 dc85633a…), §4.2, p.17 (Z, J⁺), p.18 (R_J), p.20 (J⁻)

import Mathlib
import Definitions.Def_GenTuranHard_blowUp
import Definitions.Def_GenTuranHard_leafAdd

set_option autoImplicit false

namespace GenTuranHard

/-- The graph **Z = L_x(G)(B)** (Chen, He, Li, Ma, Xie, arXiv:2610.16358, sha256 dc85633a…, §4.2,
p.17): the `B`-blow-up of the iterated leaf addition `L_x(G)`. Vertex `i` lies in the cluster of vertex
`i / B` of `L_x(G)`; the clusters `C_v` of the original vertices `v < v(G)` induce `G(B)`. -/
noncomputable def Zgraph (x : List ℕ) (G : FinGraph) (B : ℕ) : FinGraph :=
  uBlowUp (iterLeaf x G) B

/-- A vertex of `Z` lies in one of the clusters `C_v`, `v ∈ V(G)` (its cluster index is `< v(G)`). -/
def InGCluster (x : List ℕ) (G : FinGraph) (B : ℕ) (a : Fin (Zgraph x G B).1) : Prop :=
  a.val / B < G.1

/-- **J⁺** (p.17) for a subgraph `J ⊆ Z`: vertex set `V(Z)` and edge set
`(E(J) ∩ E(G(B))) ∪ (E(Z) ∖ E(G(B)))`, i.e. the edges of `Z` between two clusters of `V(G)` are kept only
if they are edges of `J`, and every other edge of `Z` is kept. -/
noncomputable def JPlus (x : List ℕ) (G : FinGraph) (B : ℕ) (J : (Zgraph x G B).2.Subgraph) :
    SimpleGraph (Fin (Zgraph x G B).1) where
  Adj a b := (Zgraph x G B).2.Adj a b ∧ (InGCluster x G B a ∧ InGCluster x G B b → J.Adj a b)
  symm := ⟨fun _ _ h => ⟨h.1.symm, fun hab => (h.2 ⟨hab.2, hab.1⟩).symm⟩⟩
  loopless := ⟨fun a h => (Zgraph x G B).2.loopless.irrefl a h.1⟩

/-- **J⁻** (p.20): the subgraph of `J` induced by `V(J) ∩ ⋃_{v ∈ V(G)} C_v`. -/
noncomputable def JMinus (x : List ℕ) (G : FinGraph) (B : ℕ) (J : (Zgraph x G B).2.Subgraph) :
    (Zgraph x G B).2.Subgraph :=
  J.induce {a | a ∈ J.verts ∧ InGCluster x G B a}

/-- The graph **R_J** of a transversal (p.18): for a choice `σ v ∈ Fin B` of one vertex
`v′ = v·B + σ v` of each cluster `C_v`, `v ∈ V(G)`, `R_J` is the spanning subgraph of `G` with
`E(R_J) = {uv ∈ E(G) : u′, v′ ∈ V(J), u′v′ ∈ E(J)}` (an edge of `J` implies both ends lie in `V(J)`). -/
noncomputable def RJ (x : List ℕ) (G : FinGraph) (B : ℕ) (J : (Zgraph x G B).2.Subgraph) (σ : Fin G.1 → Fin B) :
    SimpleGraph (Fin G.1) where
  Adj u v := G.2.Adj u v ∧ ∃ a b : Fin (Zgraph x G B).1,
    a.val = u.val * B + (σ u).val ∧ b.val = v.val * B + (σ v).val ∧ J.Adj a b
  symm := ⟨fun _ _ h => by
    obtain ⟨huv, a, b, ha, hb, hab⟩ := h
    exact ⟨huv.symm, b, a, hb, ha, hab.symm⟩⟩
  loopless := ⟨fun u h => G.2.loopless.irrefl u h.1⟩

/-- **E[e(R_J)]** (p.18): the average number of edges of `R_J` over the uniform random transversal,
i.e. over all `B^{v(G)}` choices `σ : V(G) → Fin B`, each equally likely. -/
noncomputable def avgEdges (x : List ℕ) (G : FinGraph) (B : ℕ) (J : (Zgraph x G B).2.Subgraph) : ℝ :=
  (∑ σ : Fin G.1 → Fin B, (edgeCount (RJ x G B J σ) : ℝ)) / (B : ℝ) ^ G.1

end GenTuranHard


