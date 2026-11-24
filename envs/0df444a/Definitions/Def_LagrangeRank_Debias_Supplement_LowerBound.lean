-- Prove2me | Definitions.Def_LagrangeRank_Debias_Supplement_LowerBound
-- name    : LagrangeRank_Debias_Supplement_LowerBound
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T03:49:07.719925+00:00
-- url     : https://prove2.me/theorems/6da8199d-a4df-47a3-91cd-b6a8cf66c142
-- title:
--   Selection procedures, minimax risk (5.1), swap-closed parameter sets and divider sets (Definition 5.1)
-- statement:
--   Lower-bound objects of Section 5 (pp. 28–29). A **selection procedure** $\psi$ maps the data to a vector in $\{0,1\}^n$, $\psi_i=1$ meaning that $H_{0i}$ is rejected; it is applied to the *observed* data `observe s`: the comparison graph and the comparison outcomes on observed edges (outcomes of unobserved pairs are overwritten by a fixed value), so that a procedure uses only what is observed. The true selection vector is $\psi^*_i=\mathbb 1\{\gamma(\theta)\in R_i\}$.
--
--   A parameter set $\Xi$ is **swap-closed** if swapping the scores of any two items keeps it in $\Xi$. The **minimax risk** (5.1) is
--   $$\mathfrak R=\inf_\psi\sup_{\theta^*\in\Xi}P_{\theta^*}\big(\#\text{false positives}+\#\text{false negatives}\ge1\big)=\inf_\psi\sup_{\theta^*\in\Xi}P_{\theta^*}(\psi\ne\psi^*),$$
--   the infimum over every function of the observed data. The supremum is a real supremum of probabilities, bounded by 1, over a set that is nonempty wherever it is used.
--
--   **Definition 5.1.** $M\subseteq[n]\times[n]$ is a **divider set** for $\theta$ if every $(i,i')\in M$ has $\gamma(\theta)\in R_i$, is a legal pair (Definition 3.1) and attains $|\theta_i-\theta_{i'}|=\Delta(\theta)$ of (4.2); and for two distinct pairs of $M$, the score vectors obtained by swapping them give different sets $\{i:\gamma\in R_i\}$.
-- source:
--   Liu, Fang, Lu, Lagrangian Inference for Ranking Problems, arXiv:2110.00151v1, p. 28, (5.1) and Definition 5.1; p. 29

import Mathlib
import Definitions.Def_LagrangeRank_Debias_Supplement_Ranking

namespace LagrangeRank.Debias.Supplement

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped BigOperators ENNReal
attribute [local instance] Classical.propDecidable

/-- The observed part of a data point: the comparison graph, and the comparison outcomes on
observed edges only (outcomes of unobserved pairs are overwritten by `false`). A selection
procedure is applied to this, so it uses only the data the source observes. -/
def observe {n L : ℕ} (s : Data n L) : Data n L :=
  (s.1, fun le => s.1 le.2 && s.2 le)

/-- The true selection vector ψ* of Section 5: coordinate i is `true` iff the induced ranking
of θ has property Rᵢ. -/
noncomputable def trueSelection {n : ℕ} (θ : Vec n) (R : Fin n → Set (Ranking n)) : Fin n → Bool :=
  fun i => decide (ranking θ ∈ R i)

/-- Definition 5.1 (divider set), p. 28: every pair (i,i') in M has γ(θ) ∈ Rᵢ, is legal, and
attains |θᵢ − θᵢ'| = Δ(θ) of (4.2); two distinct pairs of M, once swapped, give different sets
{i : γ ∈ Rᵢ}. -/
def IsDividerSet {n : ℕ} (θ : Vec n) (R : Fin n → Set (Ranking n))
    (M : Finset (Fin n × Fin n)) : Prop :=
  (∀ ij ∈ M, ranking θ ∈ R ij.1 ∧ ij.2 ∈ legalPairs θ ij.1 (R ij.1) ∧
      ENNReal.ofReal |θ ij.1 - θ ij.2| = familySignal θ R) ∧
  (∀ ij ∈ M, ∀ kl ∈ M, ij ≠ kl →
      trueSelection (swapScores θ ij.1 ij.2) R ≠ trueSelection (swapScores θ kl.1 kl.2) R)

/-- A parameter space closed under swapping the scores of any two items (p. 28). -/
def SwapClosed {n : ℕ} (Ξ : Set (Vec n)) : Prop :=
  ∀ θ ∈ Ξ, ∀ i j, swapScores θ i j ∈ Ξ

/-- Worst case over Ξ of the probability that the selection procedure ψ makes at least one
Type I or Type II error. Bounded by 1; Ξ is nonempty wherever it is used. -/
noncomputable def worstRisk {n L : ℕ} (p : unitInterval) (R : Fin n → Set (Ranking n))
    (Ξ : Set (Vec n)) (ψ : Data n L → Fin n → Bool) : ℝ :=
  ⨆ θ : Ξ, (dataLaw L p θ.1 {s | ψ (observe s) ≠ trueSelection θ.1 R}).toReal

/-- The minimax risk (5.1): infimum over every selection procedure ψ (a function of the
observed data) of the worst-case error probability over Ξ. -/
noncomputable def minimaxRisk {n : ℕ} (L : ℕ) (p : unitInterval) (R : Fin n → Set (Ranking n))
    (Ξ : Set (Vec n)) : ℝ :=
  ⨅ ψ : Data n L → Fin n → Bool, worstRisk p R Ξ ψ

end LagrangeRank.Debias.Supplement


