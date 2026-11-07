-- Prove2me | Definitions.Def_PlantedSubgraphLD_Tri
-- name    : PlantedSubgraphLD_Tri
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:19:39.256407+00:00
-- url     : https://prove2.me/theorems/f0d2b69a-fc44-4950-b189-9e09ba462ca2
-- title:
--   Isomorphism triples $\mathrm{Tri}(F)$
-- statement:
--   Let $\Gamma$ be a finite simple graph and $F$ a nonempty abstract graph with $N_\Gamma(F)>0$. The set of **isomorphism triples** of $F$ is
--
--   $$
--   \mathrm{Tri}(F)=\big\{(F^\circ_1,F^\circ_2,\psi):\ F^\circ_1,F^\circ_2\in C_\Gamma(F),\ \psi:F^\circ_1\xrightarrow{\ \simeq\ }F^\circ_2\big\},
--   $$
--
--   where $\psi:V(F^\circ_1)\to V(F^\circ_2)$ is a graph isomorphism: a bijection with $\{u,v\}\in E(F^\circ_1)\Leftrightarrow\{\psi(u),\psi(v)\}\in E(F^\circ_2)$. It turns $\beta_n(F)$ into a count (Lemma 4.1), so that $\beta_n(F)$ can be compared with the weights of the pieces of a decomposition of $F$.
--
--   **Formalization Note** A copy is an edge subset of $\Gamma$ in the class $F$ (`Copy Γ F`), and $\psi$ is an isomorphism of the spanned graphs. The type is finite and $|\mathrm{Tri}(F)|$ is `Nat.card (Tri Γ F)`.
-- source:
--   Chen, Li, Rigorous Low-Degree Implications for Planted Subgraph Detection: Noise and Treewidth (manuscript of Nov. 3, 2026, arXiv:2608.06279, sha256 405d09c0…), §4.1, p.18 (PDF p.20)

import Mathlib
import Definitions.Def_PlantedSubgraphLD_AbsGraph

namespace PlantedSubgraphLD

/-- A concrete copy `F° ∈ C_Γ(F)` of the abstract graph `F` in `Γ`. -/
def Copy {V : Type} [Fintype V] [DecidableEq V] (Γ : SimpleGraph V) (F : AbsGraph Γ) : Type :=
  {S : EdgeSub Γ // (Quotient.mk (isoSetoid Γ) S : AbsGraph Γ) = F}

/-- The isomorphism triples `Tri(F) = {(F°₁, F°₂, ψ) : F°₁, F°₂ ∈ C_Γ(F), ψ : F°₁ ≃ F°₂}`.

Chen, Li, *Rigorous Low-Degree Implications for Planted Subgraph Detection* (manuscript of
Nov. 3, 2026, arXiv:2608.06279, sha256 405d09c0…), §4.1, p.18: "For F°1, F°2 ∈ CΓn(F), let
ψ : V(F°1) → V(F°2) be a graph isomorphism […] We then define the set of isomorphism triples
associated with the abstract graph F by Tri(F) := {(F°1, F°2, ψ) : F°1, F°2 ∈ CΓn(F),
ψ : F°1 ≃ F°2}."

**Formalization Note** A copy is an edge subset of `Γ` in the class `F`; `ψ` is a graph
isomorphism between the spanned graphs (a bijection of the incident vertices with
`{u, v} ∈ E(F°₁) ⇔ {ψ u, ψ v} ∈ E(F°₂)`). The type is finite; its size is `Nat.card`. -/
def Tri {V : Type} [Fintype V] [DecidableEq V] (Γ : SimpleGraph V) (F : AbsGraph Γ) : Type :=
  Σ p : Copy Γ F × Copy Γ F, (spanned p.1.1.1 ≃g spanned p.2.1.1)

end PlantedSubgraphLD


