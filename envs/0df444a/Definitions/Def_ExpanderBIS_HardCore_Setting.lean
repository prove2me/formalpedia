-- Prove2me | Definitions.Def_ExpanderBIS_HardCore_Setting
-- name    : ExpanderBIS_HardCore_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T04:33:10.334351+00:00
-- url     : https://prove2.me/theorems/7bc27bfb-363d-4dd0-8ac4-3393ee6cbb50
-- title:
--   pp. 1–2, 12, 18–20 — hard-core partition function, bipartite α-expander, G², the even and odd polymer models
-- statement:
--   This file fixes the objects of §4 of Jenssen, Keevash and Perkins on the hard-core model on bipartite expanders.
--
--   Let $G$ be a finite simple graph on a vertex set $V$, $n = |V|$, and let $\mathcal O \subseteq V$, with $\mathcal E = V \setminus \mathcal O$.
--
--   1. **Bipartition.** $G$ is bipartite with classes $\mathcal O$ (odd vertices) and $\mathcal E$ (even vertices) if every edge has one endpoint in each class.
--   2. **Vertex boundary.** For $S \subseteq V$, $\partial S$ is the set of vertices of $V \setminus S$ with a neighbour in $S$.
--   3. **Bipartite $\alpha$-expander** (Definition 17). $|\partial S| \ge (1+\alpha)|S|$ for every $S \subseteq \mathcal O$ with $|S| \le |\mathcal O|/2$ and every $S \subseteq \mathcal E$ with $|S| \le |\mathcal E|/2$.
--   4. **Hard-core partition function.** With $\mathcal I(G)$ the independent sets of $G$ and fugacity $\lambda$,
--   $$Z_G(\lambda) = \sum_{I \in \mathcal I(G)} \lambda^{|I|}.$$
--   5. **Relative approximation** (Definition 10). $\hat Z$ is an $\varepsilon$-relative approximation to $Z$ if $e^{-\varepsilon}\hat Z \le Z \le e^{\varepsilon}\hat Z$.
--   6. **Graph power.** $G^k$ joins two distinct vertices when their distance in $G$ is at most $k$; a set $S$ is $G^k$-connected when $G^k[S]$ is connected (Definition 19).
--   7. **Sparse sets.** A set $A$ inside one class is sparse if each of its $G^2$-connected components is small, i.e. has at most half as many vertices as that class.
--   8. **Polymers.** An even (odd) polymer is a nonempty small $G^2$-connected set $\gamma \subseteq \mathcal E$ ($\subseteq \mathcal O$). Two polymers are compatible if $d_G(\gamma_1,\gamma_2) > 2$. The weight of a polymer is
--   $$w_\gamma = \frac{\lambda^{|\gamma|}}{(1+\lambda)^{|\partial\gamma|}}.$$
--   9. **Polymer partition functions.** $\Xi^{\mathcal E}(G) = \sum_{\Gamma} \prod_{\gamma \in \Gamma} w_\gamma$, summed over all families $\Gamma$ (the empty family included) of pairwise compatible even polymers; $\Xi^{\mathcal O}(G)$ likewise.
--   10. **Sparse independent sets.** $\sum_{I \text{ sparse}} \lambda^{|I|}$ is the sum over independent sets $I$ with both $I \cap \mathcal O$ and $I \cap \mathcal E$ sparse.
--
--   These are the objects of Theorem 1, Lemmas 18 and 20 and the Kotecký–Preiss verification of §4.2.
--
--   **Formalization Note** The fugacity $\lambda$ is called `lam` (`λ` is a Lean keyword). Distances use the extended distance `SimpleGraph.edist` (value $\infty$ between different components), so vertices in different components are never adjacent in $G^k$ and polymers in different components are compatible. `Connected` includes nonemptiness, so every polymer is nonempty. "$|S| \le |\mathcal O|/2$" is written `2 * #S ≤ #O` in $\mathbb N$. The set-valued definitions use classical decidability. The sparse condition is stated through the $G^2[A]$-component of each vertex of $A$.
-- source:
--   Jenssen, Keevash and Perkins, Algorithms for #BIS-hard problems on expander graphs, SIAM J. Comput. 49(4) (2020), author accepted manuscript, pp. 1–2 (§1, Z_G(λ), bipartite α-expander, ∂S), p. 12 (Definition 10), pp. 18–20 (§4.1, Definitions 17, 19, polymers, w_γ, Ξ^ℰ, Ξ^𝒪, sparse sets)

import Mathlib
import Definitions.Def_ExpanderBIS_Potts_Setting

namespace ExpanderBIS.HardCore

open Finset Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `O` and its complement `univ \ O` are the two partition classes of `G`: every edge joins a vertex of
`O` (the odd vertices `𝒪`) to a vertex outside `O` (the even vertices `ℰ`). -/
def IsBipartiteWrt (G : SimpleGraph V) (O : Finset V) : Prop :=
  ∀ u v, G.Adj u v → (u ∈ O ↔ v ∉ O)

/-- The vertex boundary `∂S`: the vertices outside `S` with a neighbour in `S`. -/
noncomputable def vertexBoundary (G : SimpleGraph V) (S : Finset V) : Finset V :=
  (univ \ S).filter (fun v => ∃ u ∈ S, G.Adj u v)

/-- Definition 17: `G` (bipartite with classes `O`, `univ \ O`) is a bipartite `α`-expander if
`|∂S| ≥ (1 + α)|S|` for every `S ⊆ 𝒪` with `|S| ≤ |𝒪|/2` and every `S ⊆ ℰ` with `|S| ≤ |ℰ|/2`. -/
def IsBipExpander (G : SimpleGraph V) (O : Finset V) (α : ℝ) : Prop :=
  (∀ S ⊆ O, 2 * #S ≤ #O → (1 + α) * (#S : ℝ) ≤ (#(vertexBoundary G S) : ℝ)) ∧
  (∀ S ⊆ univ \ O, 2 * #S ≤ #(univ \ O) → (1 + α) * (#S : ℝ) ≤ (#(vertexBoundary G S) : ℝ))

/-- `I` is an independent set of `G`. -/
def IsIndep (G : SimpleGraph V) (I : Finset V) : Prop :=
  ∀ u ∈ I, ∀ v ∈ I, ¬ G.Adj u v

/-- The hard-core partition function `Z_G(λ) = ∑_{I ∈ ℐ(G)} λ^{|I|}` (the fugacity is called `lam`). -/
noncomputable def hardcoreZ (G : SimpleGraph V) (lam : ℝ) : ℝ :=
  ∑ I ∈ univ.filter (fun I : Finset V => IsIndep G I), lam ^ #I

/-- The `k`-th power `G^k`: distinct vertices are adjacent iff their distance in `G` is at most `k`
(extended distance, so vertices in different components are never adjacent). -/
def distLE (G : SimpleGraph V) (k : ℕ) : SimpleGraph V where
  Adj u v := u ≠ v ∧ G.edist u v ≤ k
  symm := ⟨fun u v h => ⟨h.1.symm, by rw [SimpleGraph.edist_comm]; exact h.2⟩⟩
  loopless := ⟨fun u h => h.1 rfl⟩

/-- The `G²`-connected component of `v` inside `A`: the vertices `u ∈ A` joined to `v` by a path of
`G²[A]` (empty if `v ∉ A`). -/
noncomputable def comp2 (G : SimpleGraph V) (A : Finset V) (v : V) : Finset V :=
  A.filter (fun u => ∃ (hv : v ∈ A) (hu : u ∈ A),
    ((distLE G 2).induce (A : Set V)).Reachable ⟨v, hv⟩ ⟨u, hu⟩)

/-- `A` is a sparse subset of the side `side` (p. 19): `A ⊆ side` and every `G²`-connected component of
`A` is small, i.e. has at most `|side|/2` vertices. -/
def IsSparse (G : SimpleGraph V) (side A : Finset V) : Prop :=
  A ⊆ side ∧ ∀ v ∈ A, 2 * #(comp2 G A v) ≤ #side

/-- The polymers of one side (p. 19): the small (`|γ| ≤ |side|/2`) `G²`-connected sets `γ ⊆ side`.
`Connected` includes nonemptiness, so polymers are nonempty. -/
noncomputable def sidePolymers (G : SimpleGraph V) (side : Finset V) : Finset (Finset V) :=
  univ.filter (fun γ : Finset V =>
    γ ⊆ side ∧ 2 * #γ ≤ #side ∧ ((distLE G 2).induce (γ : Set V)).Connected)

/-- Compatibility of polymers (p. 19): `d_G(γ₁, γ₂) > 2`. -/
def Compat2 (G : SimpleGraph V) (γ₁ γ₂ : Finset V) : Prop :=
  ∀ u ∈ γ₁, ∀ v ∈ γ₂, (2 : ℕ∞) < G.edist u v

/-- The polymer weight `w_γ = λ^{|γ|} / (1 + λ)^{|∂γ|}` (p. 19). -/
noncomputable def hcWeight (G : SimpleGraph V) (lam : ℝ) (γ : Finset V) : ℝ :=
  lam ^ #γ / (1 + lam) ^ #(vertexBoundary G γ)

/-- The polymer partition function of one side, `Ξ = ∑_{Γ} ∏_{γ ∈ Γ} w_γ`, summed over all families `Γ`
(including the empty one) of pairwise compatible polymers of that side. `Ξ^ℰ(G) = sideXi G (univ \ O) lam`
and `Ξ^𝒪(G) = sideXi G O lam`. -/
noncomputable def sideXi (G : SimpleGraph V) (side : Finset V) (lam : ℝ) : ℝ :=
  ∑ Γ ∈ (sidePolymers G side).powerset.filter
      (fun Γ => ∀ γ ∈ Γ, ∀ γ' ∈ Γ, γ ≠ γ' → Compat2 G γ γ'),
    ∏ γ ∈ Γ, hcWeight G lam γ

/-- The sum of `λ^{|I|}` over the sparse independent sets (p. 20): independent `I` with `I ∩ 𝒪` sparse in
`𝒪` and `I ∩ ℰ` sparse in `ℰ`. -/
noncomputable def sparseIndepSum (G : SimpleGraph V) (O : Finset V) (lam : ℝ) : ℝ :=
  ∑ I ∈ univ.filter (fun I : Finset V =>
      IsIndep G I ∧ IsSparse G O (I ∩ O) ∧ IsSparse G (univ \ O) (I \ O)), lam ^ #I

end ExpanderBIS.HardCore


