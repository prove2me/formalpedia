-- Prove2me | Definitions.Def_TwoStageMatch_Supplement_Algorithm2
-- name    : TwoStageMatch_Supplement_Algorithm2
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T22:08:07.186948+00:00
-- url     : https://prove2.me/theorems/ca9aee67-4136-50b3-918c-067c737691c0
-- title:
--   Algorithm 2 (Hedge-and-Greed) and its runs
-- statement:
--   A **run of Algorithm 2** (Hedge-and-Greed) for a differentiable, increasing, strictly convex $g$ on an instance consists of
--
--   1. a run $(x^*,\rho)$ of Algorithm 1 for $g$: an optimal solution $x^*$ of $\mathcal P^g$ and a distribution $\rho$ of the first-stage matching with edge marginals $x^*$ (used with probability $\lambda$);
--   2. a set $\bar T\in\bar{\mathcal B}$ returned by the greedy-style algorithm, satisfying for every $T\in\bar{\mathcal B}$
--   $$f^w(\bar T)+\sum_{j\in S\setminus\bar T}w_j\ \ge\ \Big(1-\frac1e\Big)f^w(T)+\sum_{j\in S\setminus T}w_j;$$
--   3. a maximum unweighted matching $M_1$ between $D_1$ and $S\setminus\bar T$ (used with probability $1-\lambda$).
--
--   In both branches the second stage takes a maximum supply-weighted matching between $\tilde D_2$ and the remaining supplies. The value of the run with mixing probability $\lambda$ is $\lambda$ times the expected weight of the Algorithm 1 run plus $1-\lambda$ times $\mathbb E_{\tilde D_2}[w(S_1)+\text{Max-WeightMatch}^w(\tilde D_2,S\setminus S_1)]$ for the greedy $M_1$.
--
--   This is the algorithm whose competitive ratio against the optimum online Theorem 3 bounds.
--
--   **Formalization Note** The greedy branch is any $\bar T$ meeting the guarantee of Proposition 3 with the constant $1-1/e$ that the proof of Proposition 4 uses (eq. (13)); an exact maximizer of (9) qualifies.
-- source:
--   Feng, Niazadeh & Saberi, Two-stage Stochastic Matching and Pricing with Applications to Ride Hailing, arXiv:2210.11648v1, Algorithm 2, p.19; Proposition 3, p.18; eq. (13), p.21

import Mathlib
import Definitions.Def_TwoStageMatch_Algorithm1
import Definitions.Def_TwoStageMatch_Supplement_Matroid

open Finset

namespace TwoStageMatch.Supplement

/-!
# Algorithm 2 (Hedge-and-Greed) and its runs

Feng, Niazadeh & Saberi, arXiv:2210.11648v1, Algorithm 2, p.19, with the greedy-style guarantee
of Proposition 3, p.18.

**Formalization Note.**
* A *run* of Algorithm 2 for `g` consists of a run `(x*, ρ)` of Algorithm 1 for `g` (the published
  `TwoStageMatch.Run`: every optimal `x*` of `𝒫^g`, every rounding with marginals `x*`), a set
  `T̄ ∈ B̄` returned by the greedy branch, and a maximum unweighted matching `M₁` between `D₁` and
  `S \ T̄` (step 4). The second stage of both branches takes a maximum supply-weighted matching
  (step 5), as in `TwoStageMatch.twoStageWeight`.
* The greedy branch is any `T̄ ∈ B̄` with
  `f^w(T̄) + Σ_{j ∈ S \ T̄} w_j ≥ (1 − 1/e) f^w(T) + Σ_{j ∈ S \ T} w_j` for every `T ∈ B̄`: the
  guarantee of Proposition 3 with the constant `1 − 1/e` that the proof of Proposition 4 uses
  (eq. (13), p.21); an exact maximizer of (9) qualifies.
* The value of a run with mixing probability `λ` is
  `λ · (value of the Algorithm 1 run) + (1 − λ) · 𝔼_{D̃₂}[w(S₁) + Max-WeightMatch^w(D̃₂, S \ S₁)]`
  for the greedy `M₁`: Algorithm 2 flips a `λ`-coin, independent of `D̃₂`.
-/

variable {D₁ D₂ S : Type*}
variable [Fintype D₁] [Fintype D₂] [Fintype S] [DecidableEq D₁] [DecidableEq D₂] [DecidableEq S]

/-- A run of Algorithm 2 (Hedge-and-Greed, p.19) for the function `g` on the instance `I`. -/
structure Run2 (I : Instance D₁ D₂ S) (g : ℝ → ℝ) where
  /-- the run of Algorithm 1 used with probability `λ` (step 3) -/
  alg1 : Run I g
  /-- the set `T̄ ∈ B̄` returned by the greedy-style algorithm (step 4) -/
  Tbar : Finset S
  Tbar_mem : IsDualBase I Tbar
  /-- the guarantee of Proposition 3 (with constant `1 − 1/e`) -/
  Tbar_greedy : ∀ T, IsDualBase I T →
    (1 - 1 / Real.exp 1) * fw I T + ∑ j ∈ Finset.univ \ T, I.w j ≤
      fw I Tbar + ∑ j ∈ Finset.univ \ Tbar, I.w j
  /-- the maximum unweighted matching `M₁` between `D₁` and `S \ T̄` (step 4) -/
  M₁ : Finset ((D₁ ⊕ D₂) × S)
  M₁_max : IsMaxCardMatching I.E firstStage (Finset.univ \ Tbar) M₁

/-- The expected total supply weight `𝔼[Σ_j w_j 𝟙{j matched in M₁ ∪ M₂}]` of a run of Algorithm 2
with mixing probability `lam` (the `λ` of Algorithm 2). -/
noncomputable def Run2.value {I : Instance D₁ D₂ S} {g : ℝ → ℝ} (r : Run2 I g) (lam : ℝ) : ℝ :=
  lam * r.alg1.value + (1 - lam) * expect I (twoStageWeight I r.M₁)

end TwoStageMatch.Supplement


