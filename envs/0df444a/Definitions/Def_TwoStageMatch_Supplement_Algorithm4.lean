-- Prove2me | Definitions.Def_TwoStageMatch_Supplement_Algorithm4
-- name    : TwoStageMatch_Supplement_Algorithm4
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T22:08:41.588941+00:00
-- url     : https://prove2.me/theorems/51c00fce-2d86-55dc-a050-e0bfb5936fb2
-- title:
--   Assumption EC.1 and Algorithm 4 ($\beta$-approximate second stage)
-- statement:
--   **Assumption EC.1** with parameter $\gamma$: for each realization $A$ of $\tilde D_2$ (each $A\subseteq D_2$ of positive probability), the size $|M_1^*|$ of a maximum matching between $D_1$ and $S$ and the size $|M^*|$ of a maximum matching between $D_1\cup A$ and $S$ satisfy
--   $$\gamma\,|M^*|\le|M_1^*|,$$
--   i.e. $|M_1^*|/|M^*|\ge\gamma$ whenever $|M^*|>0$.
--
--   A **run of Algorithm 4** with approximation factor $\beta$ is a run $(x^*,\rho)$ of Algorithm 1 together with a rule that, for every first-stage matching $M_1$ and every realization $A$, returns a matching $M_2$ between $A$ and the supplies left unmatched by $M_1$ with
--   $$|M_2|\ \ge\ \beta\cdot\nu(A,S\setminus S_1).$$
--   Its value is $\mathbb E[\sum_j w_j\mathbb 1\{j\text{ matched in }M_1\cup M_2\}]$, the expected size of $M_1\cup M_2$ on unweighted instances.
--
--   These are the objects of Theorem EC.2.
--
--   **Formalization Note** The ratio of Assumption EC.1 is written without division, so the case $|M^*|=0$ imposes nothing.
-- source:
--   Feng, Niazadeh & Saberi, Two-stage Stochastic Matching and Pricing with Applications to Ride Hailing, arXiv:2210.11648v1, Assumption EC.1, p.ec9; Algorithm 4, p.ec10

import Mathlib
import Definitions.Def_TwoStageMatch_Algorithm1
import Definitions.Def_TwoStageMatch_Supplement_Matroid

open Finset

namespace TwoStageMatch.Supplement

/-!
# Assumption EC.1 and Algorithm 4 (β-approximate second stage)

Feng, Niazadeh & Saberi, arXiv:2210.11648v1, §EC.4.1, pp.ec9–ec10: Assumption EC.1 and
Algorithm 4 (Weighted-Balanced-Utilization with β-approximation in second stage).

**Formalization Note.**
* Assumption EC.1 compares maximum-matching *sizes*: `|M₁*| ≥ γ |M*|`, written without division
  (`γ · |M*| ≤ |M₁*|`), for every realization `A` of `D̃₂`, i.e. every `A ⊆ D₂` of positive
  probability. When `|M*| = 0` the inequality holds trivially.
* A run of Algorithm 4 is a run `(x*, ρ)` of Algorithm 1 (steps 3–4) together with a rule `M₂`
  that, for every first-stage matching `M₁` and every realization `A`, returns a matching between
  `A` and the supplies left unmatched by `M₁` whose size is at least `β` times the maximum
  (step 5). Every such rule is allowed.
* The value of a run is `𝔼[Σ_j w_j 𝟙{j matched in M₁ ∪ M₂}]`; on unweighted instances
  (`w_j = 1`) this is the expected size of `M₁ ∪ M₂`.
-/

variable {D₁ D₂ S : Type*}
variable [Fintype D₁] [Fintype D₂] [Fintype S] [DecidableEq D₁] [DecidableEq D₂] [DecidableEq S]

/-- Assumption EC.1 (p.ec9) with parameter `γ`: for each realization `D̃₂ = A`, the maximum
matching `M₁*` between `D₁` and `S` and the maximum matching `M*` between `D₁ ∪ D̃₂` and `S` satisfy
`|M₁*| / |M*| ≥ γ`. -/
def AssumptionEC1 (I : Instance D₁ D₂ S) (γ : ℝ) : Prop :=
  ∀ A : Finset D₂, 0 < arrivalProb I A →
    γ * maxCard I.E (firstStage ∪ secondStage A) Finset.univ ≤
      maxCard I.E firstStage Finset.univ

/-- A run of Algorithm 4 (p.ec10) for the function `g` and the approximation factor `β`. -/
structure Run4 (I : Instance D₁ D₂ S) (g : ℝ → ℝ) (β : ℝ) where
  /-- steps 3–4: the optimal `x*` of `𝒫^g` and the rounding `ρ` of Algorithm 1 -/
  alg1 : Run I g
  /-- step 5: the second-stage matching chosen for `M₁` and the realization `A` -/
  M₂ : Finset ((D₁ ⊕ D₂) × S) → Finset D₂ → Finset ((D₁ ⊕ D₂) × S)
  M₂_matching : ∀ M, IsFirstStageMatching I M → ∀ A,
    IsMatching I.E (secondStage A) (Finset.univ \ matchedSupply M) (M₂ M A)
  M₂_approx : ∀ M, IsFirstStageMatching I M → ∀ A,
    β * maxCard I.E (secondStage A) (Finset.univ \ matchedSupply M) ≤ ((M₂ M A).card : ℝ)

/-- The expected total supply weight `𝔼_{M₁ ∼ ρ} 𝔼_{D̃₂}[w(S₁) + w(S₂)]` of a run of Algorithm 4. -/
noncomputable def Run4.value {I : Instance D₁ D₂ S} {g : ℝ → ℝ} {β : ℝ} (r : Run4 I g β) : ℝ :=
  ∑ M, r.alg1.ρ M * expect I fun A => weight I.w M + weight I.w (r.M₂ M A)

end TwoStageMatch.Supplement


