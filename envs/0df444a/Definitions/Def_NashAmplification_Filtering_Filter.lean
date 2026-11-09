-- Prove2me | Definitions.Def_NashAmplification_Filtering_Filter
-- name    : NashAmplification_Filtering_Filter
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T08:14:28.332037+00:00
-- url     : https://prove2.me/theorems/b423a765-2f75-434b-b6ca-d8849055f974
-- title:
--   Smallest-threshold filtering round
-- statement:
--   For a finite index set $Z$, initial masses $\rho$, incoming weights $w$, assigned values $v$, and parameters $q,h$, let $m=\sum_z\rho(z)w(z)$. Define
--   $$\phi(v,\theta)=\begin{cases}0&v\le\theta,\\(v-\theta)/h&\theta<v<\theta+h,\\1&v\ge\theta+h.\end{cases}$$
--   The threshold is the infimum of the solutions $\theta\in[-h,1]$ to $\sum_z\rho(z)w(z)\phi(v(z),\theta)=qm$, and $w^+(z)=w(z)\phi(v(z),\theta)$. Lemma 2.2 separately asserts that this infimum is the smallest solution under the source's admissibility conditions; well-definedness is not assumed by this definition. Every sequence is updated, including those of zero mass.
--
--   This is the common subroutine of the payoff and recovery calculations. Values on inadmissible input use Lean's total-function conventions and are never relied on by the admissible statements.
-- source:
--   Deng, Li, Wang and Zhang, Hardness Amplification for Approximate Nash Equilibrium with a Constant Number of Players, STOC 2027 submission #120 (October 2026), SHA-256 c201a27da9b9920a924945f1a30c7919ae6b922c99430223ee9bbcdec5b0ffa8, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/120.pdf, (2.6)–(2.8), PDF pp. 8–9 (printed pp. 7–8)

import Mathlib

open scoped BigOperators
noncomputable section

namespace NashAmplification.Filtering

/-- (2.6), with the source's branch priority; only h > 0 is used. -/
def phi (h v θ : ℝ) : ℝ := if v ≤ θ then 0 else if v < θ + h then (v - θ) / h else 1

def mass {Z : Type} [Fintype Z] (ρ w : Z → ℝ) : ℝ := ∑ z, ρ z * w z

def thresholdSet {Z : Type} [Fintype Z] (q h : ℝ) (ρ w v : Z → ℝ) : Set ℝ :=
  {θ | θ ∈ Set.Icc (-h) 1 ∧ mass ρ (fun z => w z * phi h (v z) θ) = q * mass ρ w}

/-- The smallest solution of (2.7). Lemma 2.2 asserts IsLeast, including existence.
On invalid data (e.g. empty solution set) the real sInf has its usual default. -/
def threshold {Z : Type} [Fintype Z] (q h : ℝ) (ρ w v : Z → ℝ) : ℝ :=
  sInf (thresholdSet q h ρ w v)

/-- (2.8), including sequences of zero initial mass. -/
def filterWeights {Z : Type} [Fintype Z] (q h : ℝ) (ρ w v : Z → ℝ) : Z → ℝ :=
  fun z => w z * phi h (v z) (threshold q h ρ w v)
end NashAmplification.Filtering


