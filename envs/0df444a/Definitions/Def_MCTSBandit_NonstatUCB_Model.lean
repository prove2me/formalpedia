-- Prove2me | Definitions.Def_MCTSBandit_NonstatUCB_Model
-- name    : MCTSBandit_NonstatUCB_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T00:30:28.632047+00:00
-- url     : https://prove2.me/theorems/50b0b881-8ed5-495f-bb36-f830338741bf
-- title:
--   Non-stationary reward-table bandit and empirical statistics
-- statement:
--   A bandit has $K\ge1$ arms and a reward table $X_{i,t}$, where $X_{i,t}$ is the reward on the $t$th play of arm $i$. The empirical arm mean is
--
--   $$\bar X_{i,s}=\frac{1}{s}\sum_{t=1}^{s}X_{i,t}.$$
--
--   The model requires measurable rewards in $[-R,R]$, convergence of $\mathbb E[\bar X_{i,s}]$ to $\mu_i$, and both tails of $s\bar X_{i,s}-s\mu_i$ to be at most $\beta/z^\xi$ beyond $s^\eta z$, for $s,z\ge1$. The same file defines play counts $T_i(n)$ and the run average $\bar X_n$. These objects support non-stationary bandit arguments without independence assumptions.
--
--   **Formalization Note** Plays start at one. A run's arm-selection events are required to be measurable when a theorem takes their probabilities or expectations. The surrounding theorems impose $K\ge1$ and the paper's parameter ranges.
-- source:
--   Shah, Xie & Xu, arXiv:1902.05213v4, pp. 15–16, §5, (12)–(13); p. 16, §5.2

import Mathlib

open MeasureTheory Filter

namespace MCTSBandit.NonstatUCB

universe u

/-- The average of the first `s` rewards from arm `i`. Plays are numbered from one. -/
noncomputable def empMean {Ω : Type u} {K : ℕ} (X : Fin K → ℕ → Ω → ℝ)
    (i : Fin K) (s : ℕ) (ω : Ω) : ℝ :=
  (∑ t ∈ Finset.Icc 1 s, X i t ω) / (s : ℝ)

/-- The number of times arm `i` has been selected through round `t`. -/
def pullCount {Ω : Type u} {K : ℕ} (I : ℕ → Ω → Fin K)
    (i : Fin K) (t : ℕ) (ω : Ω) : ℕ :=
  ((Finset.Icc 1 t).filter (fun l => I l ω = i)).card

/-- The sample average of rewards earned by a run through round `n`. -/
noncomputable def runAvg {Ω : Type u} {K : ℕ} (X : Fin K → ℕ → Ω → ℝ)
    (I : ℕ → Ω → Fin K) (n : ℕ) (ω : Ω) : ℝ :=
  (∑ i : Fin K, (pullCount I i n ω : ℝ) *
    empMean X i (pullCount I i n ω) ω) / (n : ℝ)

/-- Measurable arm choices, needed for probabilities and expectations of run statistics. -/
def RunMeasurable {Ω : Type u} [MeasurableSpace Ω] {K : ℕ}
    (I : ℕ → Ω → Fin K) : Prop :=
  ∀ t i, MeasurableSet {ω | I t ω = i}

/-- Conditions (12) and (13), with the bounded reward and measurability conventions. -/
structure IsNonstatMAB {Ω : Type u} [MeasurableSpace Ω] {K : ℕ}
    (P : Measure Ω) (X : Fin K → ℕ → Ω → ℝ)
    (μ : Fin K → ℝ) (R β ξ η : ℝ) : Prop where
  meas : ∀ i t, 1 ≤ t → Measurable (X i t)
  bdd : ∀ i t, 1 ≤ t → ∀ ω, X i t ω ∈ Set.Icc (-R) R
  conv : ∀ i, Tendsto (fun n => ∫ ω, empMean X i n ω ∂P) atTop (nhds (μ i))
  upper : ∀ i (n : ℕ), 1 ≤ n → ∀ z : ℝ, 1 ≤ z →
    P {ω | (n : ℝ) ^ η * z ≤ (n : ℝ) * empMean X i n ω - (n : ℝ) * μ i}
      ≤ ENNReal.ofReal (β / z ^ ξ)
  lower : ∀ i (n : ℕ), 1 ≤ n → ∀ z : ℝ, 1 ≤ z →
    P {ω | (n : ℝ) * empMean X i n ω - (n : ℝ) * μ i
      ≤ -((n : ℝ) ^ η * z)} ≤ ENNReal.ofReal (β / z ^ ξ)

/-- The designated arm has strictly larger limiting mean than every other arm. -/
def IsUniqueOpt {K : ℕ} (μ : Fin K → ℝ) (istar : Fin K) : Prop :=
  ∀ i, i ≠ istar → μ i < μ istar

/-- A positive lower bound for every suboptimality gap. -/
def GapLB {K : ℕ} (μ : Fin K → ℝ) (istar : Fin K) (Δ : ℝ) : Prop :=
  0 < Δ ∧ ∀ i, i ≠ istar → Δ ≤ μ istar - μ i

end MCTSBandit.NonstatUCB


