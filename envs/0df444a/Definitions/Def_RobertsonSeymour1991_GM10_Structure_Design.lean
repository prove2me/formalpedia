-- Prove2me | Definitions.Def_RobertsonSeymour1991_GM10_Structure_Design
-- name    : RobertsonSeymour1991_GM10_Structure_Design
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:06:12.027592+00:00
-- url     : https://prove2.me/theorems/1db2fc5a-06c5-4e8b-aaad-a7338926d170
-- title:
--   §11, pp. 185–186 — designs, node designs, enlargements 𝒮ⁿ, ℛₙ, locations, θ-pervasive classes, Z-extension
-- statement:
--   Fix a hypergraph $G$. A **design** is a pair $(H, M)$ where $H$ is a hypergraph and $M$ is a set of subsets of $V(H)$.
--
--   1. **Design of a node.** If $(T, \tau)$ is a tree-decomposition of $G$ and $t_0 \in V(T)$ has neighbours $t_1, \dots, t_k$, the design of $t_0$ in $(T,\tau)$ is $(\tau(t_0), \{V(\tau(t_0) \cap \tau(t_i)) : 1 \le i \le k\})$. For a class $\mathcal S$ of designs, $(T,\tau)$ is **over $\mathcal S$** if $\mathcal S$ contains the design of every $t_0 \in V(T)$.
--   2. **Enlargements.** Let $(H, M)$, $(H', M')$ be designs and $Z \subseteq V(H')$ such that (i) $H$ is a subhypergraph of $H'$ and $V(H') - V(H) \subseteq Z$, (ii) every edge of $H'$ is an edge of $H$, (iii) for every $X \in M'$ with $X \ne Z$, $X \cap V(H) \in M$. Then $(H', M')$ is an **$n$-enlargement** of $(H, M)$ for every integer $n \ge |Z|$. $\mathcal S^n$ is the class of all $n$-enlargements of members of $\mathcal S$, and $\mathcal R_n$ is the class of all designs $(H, M)$ with $|V(H)| \le n$.
--   3. **Locations.** A location in a hypergraph $G'$ is a set $\{(A_1,B_1),\dots,(A_k,B_k)\}$ of separations of $G'$ with $A_i \subseteq B_j$ for all distinct $i, j$; its design is $(G' \cap B_1 \cap \dots \cap B_k, \{V(A_i \cap B_i) : 1 \le i \le k\})$.
--   4. **Pervasiveness.** For $\theta \ge 1$, a class $\mathcal S$ is **$\theta$-pervasive in $G$** if for every subhypergraph $G'$ of $G$ and every tangle $\mathcal T$ in $G'$ of order $\ge \theta$ there is a location $\mathcal L$ in $G'$ with $\mathcal L \subseteq \mathcal T$ whose design belongs to $\mathcal S$.
--   5. **Z-extension.** If $(H, M)$ is a design and $Z \subseteq V(H)$, then $(H, M \cup \{Z\})$ is its $Z$-extension.
--
--   In short, with $\mathcal S$ $\theta$-pervasive the hypothesis of the main theorem reads
--   $$\forall\, G' \subseteq G,\ \forall\, \mathcal T \text{ tangle in } G' \text{ of order} \ge \theta:\ \exists\, \mathcal L \subseteq \mathcal T \text{ location in } G' \text{ with design in } \mathcal S.$$
--   These notions express "relative to every high-order tangle, $G$ has a local structure from $\mathcal S$", the input to the structure theorem (11.1).
--
--   **Formalization Note** Every design that the paper's §11 statements query has as hypergraph a subhypergraph of the fixed $G$ (node designs, location designs in subhypergraphs $G' \subseteq G$, and their enlargements, since an enlargement $H'$ contains $H$). So a design is encoded as a *$G$-design* `G.Design := G.Sub × Set (Set V)`, and a class of designs as a `Set G.Design`; such a class is not required to be closed under isomorphism, which the paper never uses. The type does not force the members of $M$ to lie in $V(H)$; every design built here satisfies this. Separations, tangles and locations in a subhypergraph $G'$ are pairs of subhypergraphs of $G$ whose union is $G'$ (`IsSeparationIn`, `IsTangleIn`, `IsLocationIn`); for $G' = G$ they coincide with the absolute notions. A location is a `Set` of pairs (automatically finite); the empty set is a location, with design $(G', \emptyset)$. "Order $\ge \theta$" is every order $\theta' \ge \theta$. $\mathcal S^n$ is `enlarge 𝒮 n` (with $|Z| \le n$ via `Set.ncard`, meaningful because $V$ is finite in every theorem), $\mathcal R_n$ is `smallDesigns n`.
-- source:
--   Robertson, Seymour, Graph Minors. X. Obstructions to Tree-Decomposition, J. Combin. Theory Ser. B 52 (1991), p. 185 (design, design of t₀, over 𝒮, n-enlargement, 𝒮ⁿ, ℛₙ, location, design of a location, θ-pervasive), p. 186 (Z-extension)

import Mathlib
import Definitions.Def_RobertsonSeymour1991_GM10_Structure_Hypergraph
import Definitions.Def_RobertsonSeymour1991_GM10_Structure_TreeDecomposition

namespace RobertsonSeymour1991.GM10.Structure

variable {V E : Type}

namespace Hypergraph

/-- p. 185: a design `(H, M)`, with `H` a hypergraph and `M` a set of subsets of `V(H)`. Every design
the paper uses in §11 has as its hypergraph a subhypergraph of the fixed hypergraph `G`, so a design is
encoded as a pair of a subhypergraph of `G` and a set of vertex sets (a *`G`-design*). -/
abbrev Design (G : Hypergraph V E) : Type := G.Sub × Set (Set V)

variable {G : Hypergraph V E}

/-- p. 154 (relative to a subhypergraph `G'` of `G`): `(A, B)` is a separation of `G'`, i.e.
`A ∪ B = G'` and `E(A ∩ B) = ∅` (so `A, B ⊆ G'`). For `G' = G` this is `IsSeparation A B`. -/
def IsSeparationIn (G' A B : G.Sub) : Prop :=
  A.union B = G' ∧ A.edges ∩ B.edges = ∅

/-- p. 154 (relative to a subhypergraph `G'` of `G`): `𝒯` is a tangle in `G'` of order `θ`. Same
clauses, in the same order, as `IsTangle`, with `G` replaced by `G'`. -/
def IsTangleIn (G' : G.Sub) (θ : ℕ) (𝒯 : Set (G.Sub × G.Sub)) : Prop :=
  1 ≤ θ ∧
  (∀ p ∈ 𝒯, IsSeparationIn G' p.1 p.2 ∧ order p.1 p.2 < θ) ∧
  (∀ A B : G.Sub, IsSeparationIn G' A B → order A B < θ → (A, B) ∈ 𝒯 ∨ (B, A) ∈ 𝒯) ∧
  (∀ p₁ ∈ 𝒯, ∀ p₂ ∈ 𝒯, ∀ p₃ ∈ 𝒯, (p₁.1.union p₂.1).union p₃.1 ≠ G') ∧
  (∀ p ∈ 𝒯, p.1.verts ≠ G'.verts)

/-- p. 185: a location in `G'`: a set `{(A₁, B₁), …, (A_k, B_k)}` of separations of `G'` with
`Aᵢ ⊆ Bⱼ` for all distinct `i, j`. The empty set is a location. -/
def IsLocationIn (G' : G.Sub) (L : Set (G.Sub × G.Sub)) : Prop :=
  (∀ p ∈ L, IsSeparationIn G' p.1 p.2) ∧ ∀ p ∈ L, ∀ q ∈ L, p ≠ q → p.1.le q.2

/-- p. 185: the hypergraph `G' ∩ B₁ ∩ ⋯ ∩ B_k` of a location `L` in `G'` (equal to `G'` if `L = ∅`). -/
def locationHypergraph (G' : G.Sub) (L : Set (G.Sub × G.Sub)) : G.Sub where
  verts := G'.verts ∩ ⋂ p ∈ L, p.2.verts
  edges := G'.edges ∩ ⋂ p ∈ L, p.2.edges
  ends_subset := fun e he _ hv =>
    ⟨G'.ends_subset e he.1 hv,
      Set.mem_iInter₂.2 fun p hp => p.2.ends_subset e (Set.mem_iInter₂.1 he.2 p hp) hv⟩

/-- p. 185: the design of a location `L` in `G'`,
`(G' ∩ B₁ ∩ ⋯ ∩ B_k, {V(Aᵢ ∩ Bᵢ) : 1 ≤ i ≤ k})`. -/
def locationDesign (G' : G.Sub) (L : Set (G.Sub × G.Sub)) : G.Design :=
  (locationHypergraph G' L, {X | ∃ p ∈ L, X = p.1.verts ∩ p.2.verts})

/-- p. 185: `(H', M')` is an `n`-enlargement of `(H, M)`: there is `Z ⊆ V(H')` with `|Z| ≤ n` such that
(i) `H ⊆ H'` and `V(H') − V(H) ⊆ Z`, (ii) every edge of `H'` is an edge of `H`, and
(iii) `X ∩ V(H) ∈ M` for every `X ∈ M'` with `X ≠ Z`. -/
def IsEnlargement (n : ℕ) (d d' : G.Design) : Prop :=
  ∃ Z : Set V, Z ⊆ d'.1.verts ∧ Z.ncard ≤ n ∧ d.1.le d'.1 ∧ d'.1.verts \ d.1.verts ⊆ Z ∧
    d'.1.edges ⊆ d.1.edges ∧ ∀ X ∈ d'.2, X ≠ Z → X ∩ d.1.verts ∈ d.2

/-- p. 185: `𝒮ⁿ`, the class of all `n`-enlargements of members of `𝒮`. -/
def enlarge (𝒮 : Set G.Design) (n : ℕ) : Set G.Design :=
  {d' | ∃ d ∈ 𝒮, IsEnlargement n d d'}

/-- p. 185: `ℛₙ`, the class of all designs `(H, M)` with `|V(H)| ≤ n`. -/
def smallDesigns (G : Hypergraph V E) (n : ℕ) : Set G.Design :=
  {d | d.1.verts.ncard ≤ n}

/-- p. 186: the `Z`-extension `(H, M ∪ {Z})` of a design `(H, M)`. -/
def zExtension (d : G.Design) (Z : Set V) : G.Design :=
  (d.1, insert Z d.2)

/-- p. 185: `𝒮` is `θ`-pervasive in `G`: for every subhypergraph `G'` of `G` and every tangle `𝒯` in
`G'` of order `≥ θ` there is a location `ℒ` in `G'` with `ℒ ⊆ 𝒯` whose design belongs to `𝒮`. -/
def IsPervasive (θ : ℕ) (𝒮 : Set G.Design) : Prop :=
  ∀ G' : G.Sub, ∀ θ' : ℕ, θ ≤ θ' → ∀ 𝒯 : Set (G.Sub × G.Sub), IsTangleIn G' θ' 𝒯 →
    ∃ L ⊆ 𝒯, IsLocationIn G' L ∧ locationDesign G' L ∈ 𝒮

end Hypergraph

namespace TreeDecomposition

variable {G : Hypergraph V E} {n : ℕ}

/-- p. 185: the design of `t₀` in `(T, τ)`: `(τ(t₀), {V(τ(t₀) ∩ τ(tᵢ)) : 1 ≤ i ≤ k})`, where
`t₁, …, t_k` are the neighbours of `t₀` in `T`. -/
def nodeDesign (D : TreeDecomposition G n) (t₀ : Fin n) : G.Design :=
  (D.τ t₀, {X | ∃ t, D.T.Adj t₀ t ∧ X = (D.τ t₀).verts ∩ (D.τ t).verts})

/-- p. 185: `(T, τ)` is over the class `𝒮`: `𝒮` contains the design of every `t₀ ∈ V(T)`. -/
def IsOver (D : TreeDecomposition G n) (𝒮 : Set G.Design) : Prop :=
  ∀ t₀, D.nodeDesign t₀ ∈ 𝒮

end TreeDecomposition

end RobertsonSeymour1991.GM10.Structure


