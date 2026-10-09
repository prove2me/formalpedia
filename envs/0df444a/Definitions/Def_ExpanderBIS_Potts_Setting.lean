-- Prove2me | Definitions.Def_ExpanderBIS_Potts_Setting
-- name    : ExpanderBIS_Potts_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T03:33:36.491413+00:00
-- url     : https://prove2.me/theorems/acbf9576-8ec7-4e0a-a6d6-3d740de7d342
-- title:
--   Potts partition sums, edge expansion, and the polymer model
-- statement:
--   Let $G=(V,E)$ be a finite simple graph with $n=|V|$. The **edge boundary** $\partial_e S$ of $S\subseteq V$ consists of edges with one endpoint in $S$ and one outside; $\nabla(S)$ consists of all edges incident to $S$. The graph is an **$\alpha$-expander** when $|\partial_e S|\ge\alpha|S|$ for every $S$ with $2|S|\le n$.
--
--   For a coloring $\omega:V\to[q]$, let $m(G,\omega)$ count its monochromatic edges. The **Potts partition sum** and the strict-majority sum for color $j$ are
--
--   $$
--   Z_{G,q}(\beta)=\sum_\omega e^{\beta m(G,\omega)},\qquad
--   Z_G^j(\beta)=\sum_{\omega:\,2|\omega^{-1}(j)|>n} e^{\beta m(G,\omega)},\qquad
--   Z_G^*(\beta)=\sum_{j\in[q]}Z_G^j(\beta).
--   $$
--
--   A **polymer** is a nonempty connected induced vertex set $\gamma$ with $2|\gamma|\le n$. Two polymers are compatible when every pair of their vertices has graph distance greater than one. Its weight and the polymer partition sum are
--
--   $$
--   w_\gamma=e^{-\beta|\nabla(\gamma)|}Z_{G[\gamma],q-1}(\beta),\qquad
--   \Xi(G)=\sum_{\Gamma\text{ pairwise compatible}}\prod_{\gamma\in\Gamma}w_\gamma.
--   $$
--
--   These definitions provide the shared mathematical objects for the reduction and the Kotecký–Preiss condition. An $\varepsilon$-relative approximation $\widehat Z$ to $Z$ means $e^{-\varepsilon}\widehat Z\le Z\le e^\varepsilon\widehat Z$.
--
--   **Formalization Note** The graph distance is extended distance, so vertices in different components have infinite distance. The empty compatible family contributes one to $\Xi(G)$. The vertex type is finite; sets and color palettes are finite. The edge boundary uses one ordered orientation per crossing edge, so its size is the number of undirected crossing edges.
-- source:
--   Jenssen, Keevash and Perkins, Algorithms for #BIS-hard problems on expander graphs, SIAM J. Comput. 49(4) (2020), author accepted manuscript, pp. 4, 7, 12–14, §1.1, §2.1, Definitions 10–11, §3.1

import Mathlib

namespace ExpanderBIS.Potts

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Definition 10, p. 12. -/
def IsRelApprox (ε Zhat Z : ℝ) : Prop :=
  Real.exp (-ε) * Zhat ≤ Z ∧ Z ≤ Real.exp ε * Zhat

/-- The vertex boundary ∂S, p. 12. -/
def vertexBoundary (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : Finset V :=
  (univ \ S).filter (fun v => ∃ u ∈ S, G.Adj u v)

/-- The edge boundary ∂ₑS, with the endpoint in S listed first, p. 12. -/
def edgeBoundary (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : Finset (V × V) :=
  (S ×ˢ (univ \ S)).filter (fun p => G.Adj p.1 p.2)

/-- S⁺ = S ∪ ∂S, p. 12. -/
def expandedSet (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : Finset V :=
  S ∪ vertexBoundary G S

/-- ∇S, the edges incident to S, p. 12. -/
noncomputable def incidentEdges (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) : Finset (Sym2 V) := by
  classical
  exact G.edgeFinset.filter (fun e => ∃ v ∈ S, v ∈ e)

/-- Definition 11, p. 12. -/
def IsExpander (G : SimpleGraph V) [DecidableRel G.Adj] (α : ℝ) : Prop :=
  ∀ S : Finset V, 2 * #S ≤ Fintype.card V →
    α * (#S : ℝ) ≤ (#(edgeBoundary G S) : ℝ)

/-- The number of monochromatic edges, §1.1, p. 4. -/
noncomputable def monoEdges {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] {k : ℕ} (ω : W → Fin k) : ℕ := by
  classical
  exact #(H.edgeFinset.filter (fun e => ∀ a ∈ e, ∀ b ∈ e, ω a = ω b))

/-- The q-colour Potts partition function, §1.1, p. 4. -/
noncomputable def pottsZ {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] (k : ℕ) (β : ℝ) : ℝ := by
  classical
  exact ∑ ω : W → Fin k, Real.exp (β * monoEdges H ω)

/-- The partition sum over colourings in which j has a strict majority, p. 13. -/
noncomputable def pottsZj (G : SimpleGraph V) [DecidableRel G.Adj]
    (q : ℕ) (β : ℝ) (j : Fin q) : ℝ := by
  classical
  exact ∑ ω ∈ (univ : Finset (V → Fin q)).filter
      (fun ω => Fintype.card V < 2 * #((univ : Finset V).filter (fun v => ω v = j))),
    Real.exp (β * monoEdges G ω)

/-- The sum of the strict-majority partition sums, p. 13. -/
noncomputable def pottsZstar (G : SimpleGraph V) [DecidableRel G.Adj]
    (q : ℕ) (β : ℝ) : ℝ := by
  classical
  exact ∑ j : Fin q, pottsZj G q β j

/-- A polymer is a connected induced vertex set of size at most half the graph, pp. 13–14. -/
noncomputable def polymers (G : SimpleGraph V) [DecidableRel G.Adj] : Finset (Finset V) := by
  classical
  exact univ.filter (fun γ : Finset V =>
    (G.induce (γ : Set V)).Connected ∧ 2 * #γ ≤ Fintype.card V)

/-- Two polymers are compatible when their graph distance exceeds one, pp. 7, 13. -/
def Compat (G : SimpleGraph V) (γ₁ γ₂ : Finset V) : Prop :=
  ∀ u ∈ γ₁, ∀ v ∈ γ₂, (1 : ℕ∞) < G.edist u v

/-- Polymers at graph distance at most one from γ, including γ itself. -/
noncomputable def incompatiblePolymers (G : SimpleGraph V) [DecidableRel G.Adj]
    (γ : Finset V) : Finset (Finset V) := by
  classical
  exact (polymers G).filter (fun γ' => ¬ Compat G γ' γ)

/-- The Potts polymer weight, pp. 13–14. -/
noncomputable def weight (G : SimpleGraph V) [DecidableRel G.Adj]
    (q : ℕ) (β : ℝ) (γ : Finset V) : ℝ :=
  Real.exp (-β * #(incidentEdges G γ)) *
    pottsZ (G.induce (γ : Set V)) (q - 1) β

/-- The polymer partition function, pp. 7, 14. -/
noncomputable def polymerXi (G : SimpleGraph V) [DecidableRel G.Adj]
    (q : ℕ) (β : ℝ) : ℝ := by
  classical
  exact ∑ Γ ∈ (polymers G).powerset.filter
      (fun Γ => ∀ γ ∈ Γ, ∀ γ' ∈ Γ, γ ≠ γ' → Compat G γ γ'),
    ∏ γ ∈ Γ, weight G q β γ

end ExpanderBIS.Potts


