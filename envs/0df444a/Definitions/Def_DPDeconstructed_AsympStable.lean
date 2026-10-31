-- Prove2me | Definitions.Def_DPDeconstructed_AsympStable
-- name    : DPDeconstructed_AsympStable
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:46:34.915695+00:00
-- url     : https://prove2.me/theorems/2cdf7a65-4aac-44cc-b01c-2b17652ae128
-- title:
--   Asymptotic stability and the standing order-closed Hausdorff topology
-- statement:
--   Let $s$ be a set of a partially ordered space $\alpha$ (in the paper, $\alpha=\mathbb R^{\mathsf F}$ with the pointwise order and $s=\mathcal G$), and let $\tau$ be a topology on $s$.
--
--   1. A sequence $(f_n)$ of $\alpha$ **converges to $y$ under $\tau$** if every $f_n$ and $y$ lie in $s$ and $f_n\to y$ in $(s,\tau)$.
--   2. A self-map $A$ of a subset $U\subseteq s$ is **asymptotically stable on $U$** if $A$ maps $U$ into $U$, has a fixed point $\bar u\in U$, has no other fixed point in $U$, and $A^n u\to\bar u$ under $\tau$ for every $u\in U$. Here $U$ carries the subspace topology of $\tau$.
--   3. $\tau$ is **Hausdorff with closed order** if $(s,\tau)$ is Hausdorff and the graph $\{(f,g)\in s\times s: f\le g\}$ of the partial order is closed in the product topology on $s\times s$.
--
--   These are the notions of §3.2 used by Theorem 3.3: the refactored Bellman operator $S$ is asked to be asymptotically stable on $\mathbb G$ and each policy operator $S_\sigma$ on $\mathcal G$, both with respect to one Hausdorff, order-closed topology $\tau$ on $\mathcal G$. The closed order is what lets inequalities $f_n\le g_n$ pass to the limit.
--
--   **Formalization Note** The topology lives on the subtype $\mathcal G$ only, as in the paper. Convergence in the subspace topology of $U\subseteq\mathcal G$ coincides with convergence in $(\mathcal G,\tau)$ for sequences and limits in $U$, so it is stated in $(\mathcal G,\tau)$; the membership of every term is part of the definition.
-- source:
--   Ma and Stachurski, Dynamic Programming Deconstructed: Transformations of the Bellman Equation and Computational Efficiency, arXiv:1811.01940v2, §3.2, p.15 (asymptotic stability; Hausdorff topology τ on 𝒢 with closed pointwise order)

import Mathlib

open Filter Topology

namespace DPDeconstructed

/-- Convergence of a sequence `f` in `α` to a point `y` of `α`, inside a subset `s ⊆ α` that
carries its own topology `τ` (the topology of `↥s`, which need not come from a topology on `α`).
It holds iff every `f n` and `y` lie in `s` and the sequence `n ↦ ⟨f n, _⟩` converges to
`⟨y, _⟩` in `(↥s, τ)`.

Used for the statement "`Aⁿu → ū` under `τ`" of Ma and Stachurski, *Dynamic Programming
Deconstructed*, arXiv:1811.01940v2, §3.2, p.15, where `τ` is a topology on the set `𝒢` only.

**Formalization Note** Membership of every term and of the limit is part of the definition, so
the statement never needs membership proofs inside its own terms. -/
def TendstoIn {α : Type*} {s : Set α} (τ : TopologicalSpace s) (f : ℕ → α) (y : α) : Prop :=
  ∃ (hf : ∀ n, f n ∈ s) (hy : y ∈ s),
    Tendsto (fun n => (⟨f n, hf n⟩ : s)) atTop (@nhds s τ ⟨y, hy⟩)

/-- Asymptotic stability, Ma and Stachurski, *Dynamic Programming Deconstructed*,
arXiv:1811.01940v2, §3.2, p.15: "a self-mapping `A` on a topological space `U` is called
asymptotically stable on `U` if `A` has a unique fixed point `ū` in `U` and `Aⁿu → ū` as
`n → ∞` for all `u ∈ U`."

Here `U ⊆ s` is a subset of a set `s ⊆ α` carrying a topology `τ`, and `U` has the subspace
topology induced by `τ` (as for `𝔾 ⊆ 𝒢` in the paper). `A : α → α` is a self-map of `U`
(`Set.MapsTo A U U`), it has a fixed point `ū ∈ U`, every fixed point of `A` in `U` equals
`ū`, and for every `u ∈ U` the iterates `A^[n] u` converge to `ū` under `τ`.

**Formalization Note** Convergence in the subspace topology of `U ⊆ s` is the same as
convergence in `(↥s, τ)` for a sequence of `U` and a limit in `U` (the inclusion is an
embedding), so convergence is stated in `(↥s, τ)` through `TendstoIn`; it also forces `U ⊆ s`
along every orbit. `A` is a map on all of `α` whose values off `U` are irrelevant. -/
def AsympStableOn {α : Type*} {s : Set α} (τ : TopologicalSpace s) (A : α → α) (U : Set α) :
    Prop :=
  Set.MapsTo A U U ∧
    ∃ ū ∈ U, A ū = ū ∧ (∀ u ∈ U, A u = u → u = ū) ∧
      ∀ u ∈ U, TendstoIn τ (fun n => A^[n] u) ū

/-- The standing topology of Ma and Stachurski, *Dynamic Programming Deconstructed*,
arXiv:1811.01940v2, §3.2, p.15: "a Hausdorff topology `τ` on `𝒢` under which the pointwise
partial order is closed (i.e., its graph is closed in the product topology on `𝒢 × 𝒢`)".

For a set `s` of a partially ordered type `α` (functions with the pointwise order, in the
paper), `τ` is a topology on `↥s` that is Hausdorff and for which
`{(f, g) ∈ s × s : f ≤ g}` is closed in the product topology `τ × τ`. -/
def IsHausdorffOrderClosed {α : Type*} [PartialOrder α] {s : Set α}
    (τ : TopologicalSpace s) : Prop :=
  @T2Space s τ ∧
    @IsClosed (s × s) (@instTopologicalSpaceProd s s τ τ) {q | (q.1 : α) ≤ (q.2 : α)}

end DPDeconstructed


