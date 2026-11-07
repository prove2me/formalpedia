-- Prove2me | Definitions.Def_TreeCoverLB_realization
-- name    : TreeCoverLB_realization
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:22:00.623137+00:00
-- url     : https://prove2.me/theorems/9ab8ade5-5f08-4f9b-a727-b7e51c154229
-- title:
--   Abstract simplicial complex, support, geometric realization $|K|$ and induced action
-- statement:
--   Let $V$ be a finite set. A family $K$ of subsets of $V$ is an **abstract simplicial complex** if $\emptyset\in K$ and every subset of a member of $K$ is in $K$.
--
--   For $\mu\in\mathbb R^V$ let $\operatorname{supp}(\mu)=\{v:\mu_v>0\}$. The **geometric realization** of $K$ is
--   $$
--   |K|=\Big\{\mu\in\mathbb R^V:\ \mu_v\ge 0,\ \sum_{v\in V}\mu_v=1,\ \operatorname{supp}(\mu)\in K\Big\},
--   $$
--   the probability vectors supported on a face, with the subspace topology of $\mathbb R^V$.
--
--   If a group $H$ acts on $V$, the action extends linearly to $\mathbb R^V$ (and to $|K|$): $(h\cdot\mu)_v=\mu_{h^{-1}v}$, i.e. $h\cdot\sum_v\mu_v e_v=\sum_v\mu_v e_{hv}$.
--
--   **Formalization Note** Groups are written additively (not necessarily commutative), so $h^{-1}v$ is $(-h)+v$. Continuity of a map on $|K|$ means continuity on this subset of the finite-dimensional space $\mathbb R^V$.
-- source:
--   Chen, Huang, Tan, Xu, Improved Lower Bounds on Tree Covers, arXiv:2607.27264 (version of October 31, 2026), Definitions 3.2 (p.8, PDF p.10), 3.3 (p.9, PDF p.11) and 3.8 (p.10, PDF p.12)

import Mathlib

open Classical

namespace TreeCoverLB

/-- **Abstract simplicial complex** on a finite vertex type `V` (Chen, Huang, Tan, Xu, *Improved Lower Bounds on Tree Covers*, arXiv:2607.27264 (version of October 31, 2026), Definition 3.2, p.8
(PDF p.10)): a family `K` of finite subsets of `V` that contains `∅` and is closed under subsets. -/
def IsASC {V : Type*} (K : Set (Finset V)) : Prop :=
  ∅ ∈ K ∧ ∀ σ ∈ K, ∀ τ, τ ⊆ σ → τ ∈ K

/-- The **support** `supp(µ) = {v : µ_v > 0}` of a vector `µ ∈ ℝ^V` (Chen, Huang, Tan, Xu, *Improved Lower Bounds on Tree Covers*, arXiv:2607.27264 (version of October 31, 2026), Definition 3.3,
p.9 (PDF p.11)). -/
noncomputable def supp {V : Type*} [Fintype V] (μ : V → ℝ) : Finset V :=
  Finset.univ.filter fun v => 0 < μ v

/-- The **geometric realization** of a family `K` of faces on a finite vertex type `V`
(Chen, Huang, Tan, Xu, *Improved Lower Bounds on Tree Covers*, arXiv:2607.27264 (version of October 31, 2026), Definition 3.3, p.9 (PDF p.11)):
`|K| = {µ ∈ ℝ^V : µ_v ≥ 0, Σ_v µ_v = 1, supp(µ) ∈ K}`.

**Formalization Note** `|K|` is a subset of `V → ℝ` and carries the subspace topology of the
finite-dimensional space `V → ℝ` (product topology, equal to the Euclidean one). Continuity of a
map on `|K|` is `ContinuousOn` on this set. -/
def realization {V : Type*} [Fintype V] (K : Set (Finset V)) : Set (V → ℝ) :=
  {μ | (∀ v, 0 ≤ μ v) ∧ ∑ v, μ v = 1 ∧ supp μ ∈ K}

/-- The extension to `ℝ^V` (in particular to `|K|`) of an action of a group `H` on the vertex
set `V` (Chen, Huang, Tan, Xu, *Improved Lower Bounds on Tree Covers*, arXiv:2607.27264 (version of October 31, 2026), Definition 3.8, p.10 (PDF p.12): "This action can be naturally extended to |K|"):
`(h · µ) = Σ_v µ_v e_{h·v}`, i.e. `(h · µ)_v = µ_{h⁻¹·v}`.

**Formalization Note** The group is written additively (`AddGroup`, not necessarily
commutative), so `h⁻¹ · v` is `(-h) +ᵥ v`. -/
def ptAct {H V : Type*} [AddGroup H] [AddAction H V] (h : H) (μ : V → ℝ) : V → ℝ :=
  fun v => μ ((-h) +ᵥ v)

end TreeCoverLB


