-- Prove2me | Definitions.Def_BalancedKneser_inclusionMap
-- name    : BalancedKneser_inclusionMap
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:44:25.413193+00:00
-- url     : https://prove2.me/theorems/a2bd2d1c-48df-4b66-82ad-fda1fe3219b7
-- title:
--   Induced subcomplexes and the inclusion $|K|\hookrightarrow|L|$ of geometric realizations
-- statement:
--   A finite simplicial complex on a finite vertex set $V$ is given by its family $K$ of nonempty faces (closed under nonempty subsets); its **geometric realization** $|K|$ is the referenced platform definition `TreeCoverLB.realization`,
--   $$
--   |K|=\Big\{x\in\mathbb R^V:\ x_v\ge 0\ \text{for all } v,\ \sum_{v}x_v=1,\ \{v: x_v> 0\}\in K\Big\},
--   $$
--   with the subspace topology of $\mathbb R^V$: each face is filled by a simplex. This module defines:
--
--   1. the **induced subcomplex** $K[S]=\{\sigma\in K:\sigma\subseteq S\}$ of $K$ on a vertex set $S\subseteq V$;
--   2. for complexes $K\subseteq L$, the continuous **inclusion** $|K|\hookrightarrow|L|$ (with the structural lemmas $|K|\subseteq|L|$ and $K[S]\subseteq K$).
--
--   These are the spaces and maps whose homology the topological statements of the mission compute (for example the inclusion $i_c : C_c(N,k)\hookrightarrow Y_c$ of §9.4).
--
--   **Formalization Note** The empty complex has empty realization. Mathlib's `AbstractSimplicialComplex` is not used, because it requires every singleton to be a face, which fails for the neighborhood complex of a graph with an isolated vertex.
-- source:
--   Alipour, Jafari, Balanced Fair Division and Generalized Kneser Graphs, arXiv:2611.04486v1, §3.1, p.5 (PDF p.7): geometric realization; §9.4, p.20 (PDF p.22): the inclusion i_c

import Mathlib
import Definitions.Def_TreeCoverLB_realization

namespace BalancedKneser

/-- The **induced subcomplex** of a complex `K` on a vertex set `S` (Alipour–Jafari, *Balanced
Fair Division and Generalized Kneser Graphs*, arXiv:2611.04486v1, §3.2, p.6 (PDF p.8): the
cycles "supported on" a configuration): the faces of `K` contained in `S`. -/
def restrict {V : Type} (K : Set (Finset V)) (S : Finset V) : Set (Finset V) :=
  {σ | σ ∈ K ∧ σ ⊆ S}

theorem restrict_subset {V : Type} (K : Set (Finset V)) (S : Finset V) : restrict K S ⊆ K :=
  fun _ h => h.1

theorem realization_mono {V : Type} [Fintype V] {K L : Set (Finset V)} (h : K ⊆ L) :
    TreeCoverLB.realization K ⊆ TreeCoverLB.realization L :=
  fun _ hx => ⟨hx.1, hx.2.1, h hx.2.2⟩

/-- The continuous **inclusion** `|K| ↪ |L|` of geometric realizations induced by an inclusion of
complexes `K ⊆ L` (Alipour–Jafari, arXiv:2611.04486v1, §3.1, p.5 (PDF p.7), and §9.4, p.20
(PDF p.22): the inclusion `i_c : C_c(N, k) ↪ Y_c`).

Formalization Note: a complex on a finite vertex type `V` is its family `K` of nonempty faces;
its geometric realization `|K|` is the referenced platform definition `TreeCoverLB.realization`
(probability vectors on `V` supported on a face, with the subspace topology of `V → ℝ`). All
complexes of the mission are closed under nonempty subsets, so this is the usual realization;
the empty complex has empty realization. -/
def inclusionMap {V : Type} [Fintype V] {K L : Set (Finset V)} (h : K ⊆ L) :
    C(TreeCoverLB.realization K, TreeCoverLB.realization L) :=
  ⟨Set.inclusion (realization_mono h), continuous_inclusion (realization_mono h)⟩

end BalancedKneser


