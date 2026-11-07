-- Prove2me | Definitions.Def_ChoresEFX_IsAlphaEFX
-- name    : ChoresEFX_IsAlphaEFX
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:05:33.883204+00:00
-- url     : https://prove2.me/theorems/fadd8192-03e5-467c-b08e-828c290e0610
-- title:
--   Additive costs, complete allocations, $\alpha$-EFX, the residual cost $R^k_i$ and $\alpha$-EFkX
-- statement:
--   Let $\iota$ be a set of agents and $\kappa$ a finite set of chores, with additive costs $c_i(S)=\sum_{g\in S}c_i(g)$. A complete allocation is a map $\sigma:\kappa\to\iota$; its bundles are $X_i=\sigma^{-1}(i)$, a partition of the chores into possibly empty bundles.
--
--   The allocation is **$\alpha$-EFX** if for all agents $i,j$ and every $g\in X_i$,
--
--   $$c_i(X_i\setminus\{g\})\le\alpha\,c_i(X_j).$$
--
--   The **residual cost** of a bundle is
--
--   $$R^k_i(S)=\max\{c_i(S\setminus T):T\subseteq S,\ |T|=\min\{k,|S|\}\},$$
--
--   and a family $X$ is **$\alpha$-EFkX** if $R^k_i(X_i)\le\alpha\,c_i(X_j)$ for all $i,j$.
--
--   These notions are the fairness targets of every statement of the mission.
--
--   **Formalization Note** Costs are real, because the milestones use real working costs; the input costs of the main theorem are rationals cast to the reals. The EFkX predicate takes a family of bundles because the procedures APR and BRBI work with families; `IsPartition` says the family is a complete allocation.
-- source:
--   Qin, Fang, Li, Liu, Chen, Polynomial-Time Approximate EFX for Chores via Flow and Matching, STOC 2027 submission (manuscript sha256 b26d14cf…), §1 p.2; §2 p.5; Definition 2.1, p.5

import Mathlib

namespace ChoresEFX

open Finset

variable {ι κ : Type*} [Fintype κ] [DecidableEq κ] [DecidableEq ι]

/-- **Additive cost of a bundle**, `c_i(S) = ∑_{g ∈ S} c_i(g)`.

Qin, Fang, Li, Liu, Chen, *Polynomial-Time Approximate EFX for Chores via Flow and Matching*, STOC
2027 submission (manuscript sha256 b26d14cf…), §1, p.2 and §2, p.5.

**Formalization Note.** The costs are real here because the milestones use the real working costs
`Ĉ` and because the fairness notions do not depend on the number type; the input costs of the goal
are rationals cast to `ℝ` (`Inst.realCost`). -/
def cost (c : ι → κ → ℝ) (i : ι) (S : Finset κ) : ℝ := ∑ g ∈ S, c i g

/-- The bundle `X_i = σ⁻¹(i)` of the complete allocation `σ : κ → ι`, §2, p.5 (Qin et al., STOC 2027
submission).

**Formalization Note.** A function `σ : κ → ι` is exactly a partition of the chores into `|ι|`
possibly empty bundles: "A complete allocation assigns every chore to exactly one agent". -/
def bundle (σ : κ → ι) (i : ι) : Finset κ := univ.filter (fun g => σ g = i)

/-- **Definition 2.1 (α-EFX)**, p.5 (Qin et al., STOC 2027 submission): for every `i, j` and every
`g ∈ X_i`, `c_i(X_i \ {g}) ≤ α · c_i(X_j)`.

**Formalization Note.** The quantifier runs over every `i, j`, including `i = j`, as printed. -/
def IsAlphaEFX (c : ι → κ → ℝ) (α : ℝ) (σ : κ → ι) : Prop :=
  ∀ i j, ∀ g ∈ bundle σ i, cost c i (bundle σ i \ {g}) ≤ α * cost c i (bundle σ j)

/-- **The residual cost** `R^k_i(S) = max{c_i(S \ T) : T ⊆ S, |T| = min{k, |S|}}`, §2, p.5 (Qin et
al., STOC 2027 submission).

**Formalization Note.** A `Finset.sup'` over the subsets of `S` of size `min{k, |S|}`; that family is
never empty. `R^k_i(S) = 0` when `|S| ≤ k` (proved in `Solutions/verification/ChoresEFX_Sanity.lean`). -/
def resid (c : ι → κ → ℝ) (k : ℕ) (i : ι) (S : Finset κ) : ℝ :=
  (S.powersetCard (min k S.card)).sup' (Finset.powersetCard_nonempty.2 (min_le_right _ _))
    (fun T => cost c i (S \ T))

/-- **α-EFkX**, §2, p.5 (Qin et al., STOC 2027 submission): `R^k_i(X_i) ≤ α · c_i(X_j)` for all
`i, j`.

**Formalization Note.** Stated for a family of bundles `X : ι → Finset κ`, because the procedures APR
and BRBI work with families; `IsPartition` says that the family is a complete allocation. -/
def IsAlphaEFkX (c : ι → κ → ℝ) (k : ℕ) (α : ℝ) (X : ι → Finset κ) : Prop :=
  ∀ i j, resid c k i (X i) ≤ α * cost c i (X j)

/-- The family `X` is a complete allocation: every chore lies in exactly one bundle, §2, p.5 (Qin et
al., STOC 2027 submission). -/
def IsPartition (X : ι → Finset κ) : Prop := ∀ g, ∃! i, g ∈ X i

end ChoresEFX


