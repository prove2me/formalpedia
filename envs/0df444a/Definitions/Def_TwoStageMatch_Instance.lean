-- Prove2me | Definitions.Def_TwoStageMatch_Instance
-- name    : TwoStageMatch_Instance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:30:44.433267+00:00
-- url     : https://prove2.me/theorems/e4572f71-490d-4986-aa1f-8f6dd8e449ec
-- title:
--   Two-stage stochastic matching instances, $\mathsf{OPT}_{\mathrm{offline}}$ (1) and $\mathsf{OPT}_{\mathrm{online}}$ (2)
-- statement:
--   An **instance** of the (vertex-)weighted two-stage stochastic matching problem consists of finite sets $D_1$ (first-stage demands), $D_2$ (potential second-stage demands) and $S$ (supplies), a bipartite edge relation $E\subseteq (D_1\cup D_2)\times S$, supply weights $w_j\ge 0$ and availability probabilities $\pi_i\in[0,1]$ for $i\in D_2$.
--
--   Each $i\in D_2$ is available independently with probability $\pi_i$; the random set $\tilde D_2$ of available second-stage demands has law
--   $$\Pr[\tilde D_2=A]=\prod_{i\in A}\pi_i\prod_{i\in D_2\setminus A}(1-\pi_i),\qquad A\subseteq D_2 .$$
--   A first-stage matching $M_1$ is a matching between $D_1$ and $S$, with matched supplies $S_1$. If $\tilde D_2=A$ and the second stage picks a maximum supply-weighted matching between $A$ and $S\setminus S_1$, the collected weight is $w(S_1)+\mathrm{Max\text{-}WeightMatch}^w(A,S\setminus S_1)$.
--
--   The two benchmarks are
--   $$\mathsf{OPT}_{\mathrm{offline}}=\mathbb E_{\tilde D_2}\big[\mathrm{Max\text{-}WeightMatch}^w(D_1\cup\tilde D_2,S)\big] \qquad (1)$$
--   $$\mathsf{OPT}_{\mathrm{online}}=\max_{M_1}\Big(\sum_{j\in S}w_j\mathbb 1\{j\text{ is matched in }M_1\}+\mathbb E_{\tilde D_2}\big[\mathrm{Max\text{-}WeightMatch}^w(\tilde D_2,S\setminus S_1)\big]\Big). \qquad (2)$$
--   The offline benchmark knows the realization of $\tilde D_2$; the online benchmark commits to the best first-stage matching before seeing it.
--
--   **Formalization Note** The demand side is the disjoint union $D_1\oplus D_2$. Values $v_i$ and prices $p_i$ do not enter the matching problem; $\pi$ is given directly (p.9). Expectations over $\tilde D_2$ are finite sums over subsets of $D_2$.
-- source:
--   Y. Feng, R. Niazadeh, A. Saberi, Two-stage Stochastic Matching and Pricing with Applications to Ride Hailing, arXiv:2210.11648v1 [cs.DS] (preprint, 21 Oct 2022), https://arxiv.org/abs/2210.11648v1, §2, pp.8–9 (graph, Definition 1, weights), p.10 (benchmarks (1), (2))

import Mathlib
import Definitions.Def_TwoStageMatch_Bipartite

open Finset

namespace TwoStageMatch

/-!
# The two-stage stochastic matching model and its two benchmarks

Feng, Niazadeh & Saberi, arXiv:2210.11648v1, §2, pp.8–10: the graph `G = (D, S, E)` with
`D = D₁ ∪ D₂`, the supply weights `w_j ≥ 0` (p.9), the availability probabilities `π_i` of the
second-stage demands (p.8), the law of the available set `D̃₂`, and the benchmarks
`OPT_offline` (1) and `OPT_online` (2), p.10.

**Formalization Note.** The demand side is the disjoint union `D₁ ⊕ D₂`; first-stage demands are
`Sum.inl i`, second-stage demands `Sum.inr i`. The edge set is a relation
`E : D₁ ⊕ D₂ → S → Prop`. The availability probabilities `π_i ∈ [0, 1]` are taken as given
parameters (p.9: "the probabilities {π_i} are known and given parameters"); values and prices
play no role here. `D̃₂` is a random `Finset D₂` with the product law
`P(A) = Π_{i ∈ A} π_i · Π_{i ∉ A} (1 − π_i)` (independent coins, Definition 1), and
`𝔼_{D̃₂}[f] = Σ_A P(A) f(A)`.
-/

/-- An instance of the (vertex-)weighted two-stage stochastic matching problem
(arXiv:2210.11648v1, §2, pp.8–9): a bipartite graph between demands `D₁ ⊕ D₂` and supplies `S`,
non-negative supply weights `w`, and availability probabilities `π_i ∈ [0, 1]` of the
second-stage demands. -/
structure Instance (D₁ D₂ S : Type*) where
  /-- the edge relation `E`: `(i, j) ∈ E` iff demand `i` can be matched to supply `j` -/
  E : D₁ ⊕ D₂ → S → Prop
  /-- the supply weights `w_j` -/
  w : S → ℝ
  /-- the availability probabilities `π_i` of the second-stage demands -/
  π : D₂ → ℝ
  w_nonneg : ∀ j, 0 ≤ w j
  π_nonneg : ∀ i, 0 ≤ π i
  π_le_one : ∀ i, π i ≤ 1

variable {D₁ D₂ S : Type*}

/-- The first-stage demand set `D₁`, as a subset of `D₁ ⊕ D₂`. -/
def firstStage [Fintype D₁] [DecidableEq D₁] [DecidableEq D₂] : Finset (D₁ ⊕ D₂) :=
  (Finset.univ : Finset D₁).image Sum.inl

/-- A set `A ⊆ D₂` of available second-stage demands, as a subset of `D₁ ⊕ D₂`. -/
def secondStage [DecidableEq D₁] [DecidableEq D₂] (A : Finset D₂) : Finset (D₁ ⊕ D₂) :=
  A.image Sum.inr

/-- `Pr[D̃₂ = A] = Π_{i ∈ A} π_i · Π_{i ∉ A} (1 − π_i)`: each `i ∈ D₂` is available independently
with probability `π_i` (Definition 1, p.9). -/
def arrivalProb [Fintype D₂] [DecidableEq D₂] (I : Instance D₁ D₂ S) (A : Finset D₂) : ℝ :=
  (∏ i ∈ A, I.π i) * ∏ i ∈ Aᶜ, (1 - I.π i)

/-- The expectation `𝔼_{D̃₂}[f(D̃₂)] = Σ_{A ⊆ D₂} Pr[D̃₂ = A] f(A)`. -/
def expect [Fintype D₂] [DecidableEq D₂] (I : Instance D₁ D₂ S) (f : Finset D₂ → ℝ) : ℝ :=
  ∑ A : Finset D₂, arrivalProb I A * f A

/-- `M₁` is a first-stage matching: a matching between `D₁` and `S` (Definition 1, I.). -/
def IsFirstStageMatching [Fintype D₁] [Fintype S] [DecidableEq D₁] [DecidableEq D₂]
    (I : Instance D₁ D₂ S) (M : Finset ((D₁ ⊕ D₂) × S)) : Prop :=
  IsMatching I.E firstStage Finset.univ M

/-- The total supply weight `Σ_{j ∈ S} w_j 𝟙{j matched in M₁ ∪ M₂}` collected by a first-stage
matching `M₁` when `D̃₂ = A` and the second stage picks a maximum supply-weighted matching between
`A` and the unmatched supplies `S \ S₁` (p.10, "the platform should always pick a maximum
supply-weighted matching M₂ between D̃₂ and unmatched supplies left by M₁"). -/
noncomputable def twoStageWeight [Fintype D₁] [Fintype D₂] [Fintype S] [DecidableEq D₁]
    [DecidableEq D₂] [DecidableEq S] (I : Instance D₁ D₂ S) (M : Finset ((D₁ ⊕ D₂) × S))
    (A : Finset D₂) : ℝ :=
  weight I.w M + maxWeightMatch I.E I.w (secondStage A) (Finset.univ \ matchedSupply M)

/-- `OPT_offline ≜ 𝔼_{D̃₂}[Max-WeightMatch^w(D₁ ∪ D̃₂, S)]`, equation (1), p.10. -/
noncomputable def optOffline [Fintype D₁] [Fintype D₂] [Fintype S] [DecidableEq D₁]
    [DecidableEq D₂] [DecidableEq S] (I : Instance D₁ D₂ S) : ℝ :=
  expect I fun A => maxWeightMatch I.E I.w (firstStage ∪ secondStage A) Finset.univ

/-- `OPT_online ≜ max_{M₁} (Σ_{j ∈ S} w_j 𝟙{j matched in M₁} +
𝔼_{D̃₂}[Max-WeightMatch^w(D̃₂, S \ S₁)])`, equation (2), p.10: the maximum over all first-stage
matchings `M₁` (a finite nonempty set). -/
noncomputable def optOnline [Fintype D₁] [Fintype D₂] [Fintype S] [DecidableEq D₁]
    [DecidableEq D₂] [DecidableEq S] (I : Instance D₁ D₂ S) : ℝ :=
  (matchings I.E firstStage Finset.univ).sup' (matchings_nonempty _ _ _)
    fun M => weight I.w M +
      expect I fun A => maxWeightMatch I.E I.w (secondStage A) (Finset.univ \ matchedSupply M)

end TwoStageMatch


