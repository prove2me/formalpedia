-- Prove2me | Definitions.Def_LocalPush_PageRank
-- name    : LocalPush_PageRank
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T23:04:18.386624+00:00
-- url     : https://prove2.me/theorems/61f450ab-63f7-4952-86ff-4d532361ffef
-- title:
--   PageRank vector $\mathrm{pr}_\alpha(s)$ and ACL $\varepsilon$-approximate PageRank vectors (Definition 1.1)
-- statement:
--   For a source vector $s\in\mathbb R^V$ and $\alpha\in(0,1)$, the PageRank vector $\mathrm{pr}_\alpha(s)$ is the unique solution of
--   $$\mathrm{pr}_\alpha(s)=\alpha s+(1-\alpha)AD^{-1}\mathrm{pr}_\alpha(s),\tag{1}$$
--   and $\mathrm{pr}_\alpha(u,v):=\mathrm{pr}_\alpha(e_u)(v)$. A vector $p\in\mathbb R^V_{\ge0}$ is an ACL $\varepsilon$-approximate PageRank vector for the source $s$ if there is a vector $r$ with
--   $$p=\mathrm{pr}_\alpha(s-r)\quad\text{and}\quad 0\le r\le\varepsilon d\ \text{entrywise}.$$
--   For a seed node $s$ the source vector is $e_s$.
--
--   This is the approximation notion of Andersen, Chung and Lang that the local push primitive computes.
--
--   **Formalization Note** $\mathrm{pr}_\alpha(\sigma)$ is defined as $\alpha(I-(1-\alpha)AD^{-1})^{-1}\sigma$; that this is the unique solution of (1) for $\alpha\in(0,1)$ on a graph without isolated nodes is the milestone `LocalPush.eq_1_unique`. The condition $p\ge0$ of Definition 1.1 is part of the predicate.
-- source:
--   Cui, Wei, Yang, Revisiting Local Push, STOC 2027 submission (manuscript sha256 4c36279a…), §1.1, eq. (1), p.4 (PDF p.4); Definition 1.1, p.5 (PDF p.5)

import Mathlib
import Definitions.Def_LocalPush_GraphMatrices

open Finset Matrix

namespace LocalPush

/-!
# The PageRank vector `pr_α(s)` and ACL ε-approximate PageRank vectors

Cui, Wei, Yang, *Revisiting Local Push: Faster Algorithms and Optimal Query Complexity for PageRank and
Effective Resistance*, STOC 2027 submission (manuscript sha256 4c36279a…), §1.1, eq. (1), p.4 (PDF p.4), and
Definition 1.1, p.5 (PDF p.5).

"For any source vector s ∈ ℝ^V and a teleportation parameter α ∈ (0, 1), we use pr_α(s) ∈ ℝ^V to denote its
PageRank vector, which is defined as the unique solution to the linear system pr_α(s) = αs + (1 − α)AD⁻¹pr_α(s).
(1)" — "a vector p ∈ ℝ^V_{≥0} is called an ε-approximate PageRank vector if there exists a vector r such that
p = pr_α(s − r) and 0 ≤ r ≤ εd entrywise."

**Formalization Note.**
* `pr G α σ := α (I − (1 − α)AD⁻¹)⁻¹ σ`, the solution of (1) written through the matrix inverse. For
  `α ∈ (0, 1)` and a graph without isolated nodes the matrix is invertible and this is the unique solution of
  (1); that is the milestone `LocalPush.eq_1_unique`. Every statement of the mission uses `pr` only for
  `α ∈ (0, 1)` and `NoIsolated G`, so Mathlib's junk value of a singular inverse never arises.
* `pr_α(u, v)` of the paper is `pr G α (e u) v`.
* `IsACL G α σ ε p` is Definition 1.1 with source vector `σ`, including `p ≥ 0` (the paper's `p ∈ ℝ^V_{≥0}`);
  for a seed node `s` the source is `e s`.
-/

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The PageRank vector `pr_α(σ)`, the solution of `p = ασ + (1 − α)AD⁻¹p` (eq. (1), p.4). -/
noncomputable def pr (G : SimpleGraph V) [DecidableRel G.Adj] (α : ℝ) (σ : V → ℝ) : V → ℝ :=
  α • (((1 : Matrix V V ℝ) - (1 - α) • (adjM G * Dinv G))⁻¹ *ᵥ σ)

/-- Definition 1.1 (p.5): `p` is an ACL `ε`-approximate PageRank vector for the source vector `σ`:
`p ≥ 0`, and some `r` with `0 ≤ r ≤ εd` entrywise has `p = pr_α(σ − r)`. -/
def IsACL (G : SimpleGraph V) [DecidableRel G.Adj] (α : ℝ) (σ : V → ℝ) (ε : ℝ) (p : V → ℝ) : Prop :=
  (∀ v, 0 ≤ p v) ∧ ∃ r : V → ℝ, p = pr G α (σ - r) ∧ ∀ v, 0 ≤ r v ∧ r v ≤ ε * deg G v

end LocalPush


