-- Prove2me | Definitions.Def_TwoStageMatch_Bipartite
-- name    : TwoStageMatch_Bipartite
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:29:56.752545+00:00
-- url     : https://prove2.me/theorems/c409670f-2b9d-4a4e-9b90-1106e59d9642
-- title:
--   Bipartite matchings, $\mathrm{Max\text{-}WeightMatch}^w(X,Y)$ and the matching LP (LP-1)
-- statement:
--   Let $U$ (demands) and $S$ (supplies) be finite sets and $E\subseteq U\times S$ an edge relation. For $X\subseteq U$ and $Y\subseteq S$:
--
--   1. A **matching** between $X$ and $Y$ is a set $M$ of edges $(i,j)$ with $i\in X$, $j\in Y$, no two of which share a demand vertex or a supply vertex. $S(M)$ denotes the set of supply vertices it matches.
--   2. Given supply weights $w:S\to\mathbb R$, the **weight** of $M$ is $\sum_{j\in S} w_j\,\mathbb 1\{j \text{ is matched in } M\}=\sum_{j\in S(M)}w_j$.
--   3. $\mathrm{Max\text{-}WeightMatch}^w(X,Y)$ is the weight of a supply-weighted maximum matching between $X$ and $Y$:
--   $$\mathrm{Max\text{-}WeightMatch}^w(X,Y)=\max\{\,w(M) : M \text{ a matching between } X \text{ and } Y\,\}.$$
--   4. A **fractional matching** of $G[X,Y]$ is $x\ge 0$, vanishing off the edges of $G[X,Y]$, with $\sum_j x_{ij}\le 1$ for every $i$ and $\sum_i x_{ij}\le 1$ for every $j$; its value is $\sum_i\sum_j x_{ij}w_j$ (the primal of (LP-1)).
--   5. A **dual-feasible** pair $(\alpha,\beta)$ has $\alpha_i\ge 0$ ($i\in X$), $\beta_j\ge 0$ ($j\in Y$) and $\alpha_i+\beta_j\ge w_j$ for every edge $(i,j)$ of $G[X,Y]$; its objective is $\sum_{i\in X}\alpha_i+\sum_{j\in Y}\beta_j$ (the dual of (LP-1)).
--
--   These are the general bipartite-matching objects on which the two-stage model is built.
--
--   **Formalization Note** The maximum is a finite maximum over the nonempty set of matchings (the empty matching always qualifies). Decidability is supplied classically.
-- source:
--   Y. Feng, R. Niazadeh, A. Saberi, Two-stage Stochastic Matching and Pricing with Applications to Ride Hailing, arXiv:2210.11648v1 [cs.DS] (preprint, 21 Oct 2022), https://arxiv.org/abs/2210.11648v1, §2, p.10 (Max-WeightMatch^w(X, Y), below eq. (1)); proof of Theorem 1, p.14 (LP-1)

import Mathlib

open Finset

namespace TwoStageMatch

/-!
# Bipartite matchings, supply-weighted maximum matchings and the matching LP

Feng, Niazadeh & Saberi, *Two-stage Stochastic Matching and Pricing with Applications to Ride
Hailing*, arXiv:2210.11648v1, §2, pp.8–10 (matchings, `Max-WeightMatch^w(X, Y)` below (1)) and
the linear program (LP-1), p.14.

These are general objects on a bipartite graph with demand side `U`, supply side `S` and edge
relation `E : U → S → Prop`; the two-stage model of the paper builds on them.

**Formalization Note.** A matching is a `Finset` of pairs `(i, j)` that are edges, with `i ∈ X`,
`j ∈ Y`, and no two distinct pairs sharing a demand vertex or a supply vertex. Weights live on
supply vertices (`w : S → ℝ`), and the weight of a matching is the total weight of its matched
supply vertices. `Max-WeightMatch` is a maximum over the finite, nonempty set of matchings (the
empty matching is always one), taken with `Finset.sup'`. Decidability is supplied classically.
-/

variable {U S : Type*}

/-- `M` is a matching between `X ⊆ U` and `Y ⊆ S` in the bipartite graph with edge relation `E`
(arXiv:2210.11648v1, §2, p.8): every pair of `M` is an edge `(i, j)` with `i ∈ X` and `j ∈ Y`, and
two pairs of `M` sharing their demand vertex or their supply vertex are equal. -/
def IsMatching (E : U → S → Prop) (X : Finset U) (Y : Finset S) (M : Finset (U × S)) : Prop :=
  (∀ e ∈ M, E e.1 e.2 ∧ e.1 ∈ X ∧ e.2 ∈ Y) ∧
  (∀ e ∈ M, ∀ e' ∈ M, e.1 = e'.1 → e = e') ∧
  (∀ e ∈ M, ∀ e' ∈ M, e.2 = e'.2 → e = e')

/-- The set of supply vertices matched by `M` (the set `S₁` of (2), p.10, when `M = M₁`). -/
def matchedSupply [DecidableEq S] (M : Finset (U × S)) : Finset S :=
  M.image Prod.snd

/-- The supply weight `Σ_{j ∈ S} w_j 𝟙{j is matched in M}` of `M` (p.9). -/
def weight [DecidableEq S] (w : S → ℝ) (M : Finset (U × S)) : ℝ :=
  ∑ j ∈ matchedSupply M, w j

/-- The empty set is a matching between any `X` and `Y`. -/
theorem isMatching_empty (E : U → S → Prop) (X : Finset U) (Y : Finset S) :
    IsMatching E X Y ∅ := by
  simp [IsMatching]

open Classical in
/-- The finite set of all matchings between `X` and `Y`. -/
noncomputable def matchings [Fintype U] [Fintype S] (E : U → S → Prop) (X : Finset U)
    (Y : Finset S) : Finset (Finset (U × S)) :=
  (Finset.univ : Finset (Finset (U × S))).filter (IsMatching E X Y)

open Classical in
/-- The set of matchings is nonempty: it contains the empty matching. -/
theorem matchings_nonempty [Fintype U] [Fintype S] (E : U → S → Prop) (X : Finset U)
    (Y : Finset S) : (matchings E X Y).Nonempty :=
  ⟨∅, by simp [matchings, isMatching_empty]⟩

/-- `Max-WeightMatch^w(X, Y)` (arXiv:2210.11648v1, p.10, below (1)): the weight of a
supply-weighted maximum matching between `X ⊆ U` and `Y ⊆ S`, i.e. the maximum of `weight w M`
over all matchings `M` between `X` and `Y`. -/
noncomputable def maxWeightMatch [Fintype U] [Fintype S] [DecidableEq S] (E : U → S → Prop)
    (w : S → ℝ) (X : Finset U) (Y : Finset S) : ℝ :=
  (matchings E X Y).sup' (matchings_nonempty E X Y) (weight w)

/-- A fractional matching between `X` and `Y`: a feasible point of the primal of (LP-1), p.14.
`x i j ≥ 0`, `x` vanishes off the edges of `G[X, Y]`, and every vertex has total load at most 1. -/
def IsFracMatching [Fintype U] [Fintype S] (E : U → S → Prop) (X : Finset U) (Y : Finset S)
    (x : U → S → ℝ) : Prop :=
  (∀ i j, 0 ≤ x i j) ∧
  (∀ i j, x i j ≠ 0 → E i j ∧ i ∈ X ∧ j ∈ Y) ∧
  (∀ i, ∑ j, x i j ≤ 1) ∧
  (∀ j, ∑ i, x i j ≤ 1)

/-- The primal objective `Σ_i Σ_{j ∈ N(i)} x_{ij} w_j` of (LP-1), p.14. -/
def fracWeight [Fintype U] [Fintype S] (w : S → ℝ) (x : U → S → ℝ) : ℝ :=
  ∑ i, ∑ j, x i j * w j

/-- A feasible point `(α, β)` of the dual of (LP-1), p.14, for the graph `G[X, Y]`:
`α_i ≥ 0` for `i ∈ X`, `β_j ≥ 0` for `j ∈ Y`, and `α_i + β_j ≥ w_j` for every edge `(i, j)` with
`i ∈ X`, `j ∈ Y`. Values of `α` off `X` and of `β` off `Y` play no role. -/
def IsDualFeasible (E : U → S → Prop) (w : S → ℝ) (X : Finset U) (Y : Finset S)
    (α : U → ℝ) (β : S → ℝ) : Prop :=
  (∀ i ∈ X, 0 ≤ α i) ∧ (∀ j ∈ Y, 0 ≤ β j) ∧
  (∀ i ∈ X, ∀ j ∈ Y, E i j → w j ≤ α i + β j)

/-- The dual objective `Σ_{i ∈ X} α_i + Σ_{j ∈ Y} β_j` of (LP-1), p.14. -/
def dualObj (X : Finset U) (Y : Finset S) (α : U → ℝ) (β : S → ℝ) : ℝ :=
  ∑ i ∈ X, α i + ∑ j ∈ Y, β j

end TwoStageMatch


