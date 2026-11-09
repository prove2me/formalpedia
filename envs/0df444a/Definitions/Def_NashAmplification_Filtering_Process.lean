-- Prove2me | Definitions.Def_NashAmplification_Filtering_Process
-- name    : NashAmplification_Filtering_Process
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T08:22:10.892111+00:00
-- url     : https://prove2.me/theorems/367e4152-58b4-49cd-8cad-e7408bdbbdbc
-- title:
--   Payoff, recovery and deviation calculations
-- statement:
--   A sequence is $z\in A^t$. For initial masses $\rho$, start with $W_0=1$ and, in round $s$, form
--   $$Q_s(a)=q^{-(s-1)}\sum_{z:z_s=a}\rho(z)W_{s-1}(z).$$
--   Update every weight by Filter using $v(z)=V_{Q_s}(z_s)$. Empirical masses $\widehat P(z)=C^{-1}\sum_j\mathbf1\{y_j=z\}$ define the payoff calculation; its payoff is exactly $U_i(y)=\mathbf1\{\widehat W_t(y_i)=1\}$. For a mixed profile $\sigma$, recovery uses the original mixture $P=C^{-1}\sum_j\sigma_j$, computes the rounds, and selects the first passing score test, or reports failure. Its output is the marginals of that round. Use $q=1-\beta/2$, $h=\Delta/4$.
--
--   Choose the first score maximizer in each round according to mixed-radix rank to form $z^*$. Expectations with a set $I$ of coordinates fixed are finite sums over only the unfixed coordinates, weighted by their independent component laws. In the deviation experiment $Y_i=z^*$; the original $\sigma_i$ stays in $P$.
--
--   This shared calculation defines the objects in (2.11)–(2.22) and (3.1). Round coordinate $r$ is zero based, so its source index is $r+1$. Weights after the last round are kept constant solely to make the recursion total.
-- source:
--   Deng, Li, Wang and Zhang, Hardness Amplification for Approximate Nash Equilibrium with a Constant Number of Players, STOC 2027 submission #120 (October 2026), SHA-256 c201a27da9b9920a924945f1a30c7919ae6b922c99430223ee9bbcdec5b0ffa8, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/120.pdf, (2.11)–(2.22), (3.1), PDF pp. 10–14 (printed pp. 9–13)

import Definitions.Def_NashAmplification_Filtering_Model
import Definitions.Def_NashAmplification_Filtering_Filter

open scoped BigOperators
noncomputable section

namespace NashAmplification.Filtering

/-- Current-tuple law (2.12)/(2.18), with the prescribed q^r denominator. -/
def currentLaw {k t : ℕ} {n : Fin k → ℕ} (q : ℝ) (ρ w : Seq n t → ℝ)
    (r : Fin t) : Tuple n → ℝ :=
  fun a => (∑ z, if z r = a then ρ z * w z else 0) / q ^ r.val

/-- All t rounds are run. Round r.val+1 uses coordinate r. Values after t stay fixed. -/
def weights {k t : ℕ} {n : Fin k → ℕ} (u : Utility n) (q h : ℝ)
    (ρ : Seq n t → ℝ) : ℕ → Seq n t → ℝ
  | 0 => fun _ => 1
  | s + 1 =>
    let w := weights u q h ρ s
    if hs : s < t then
      let r : Fin t := ⟨s, hs⟩
      filterWeights q h ρ w (fun z => score u (currentLaw q ρ w r) (z r))
    else w

def roundLaw {k t : ℕ} {n : Fin k → ℕ} (u : Utility n) (q h : ℝ)
    (ρ : Seq n t → ℝ) (r : Fin t) : Tuple n → ℝ :=
  currentLaw q ρ (weights u q h ρ r.val) r

def empirical {C : ℕ} {Z : Type} [DecidableEq Z] (y : Fin C → Z) : Z → ℝ :=
  fun z => (∑ j, if y j = z then (1 : ℝ) else 0) / C

def mixture {C : ℕ} {Z : Type} (σ : Fin C → Z → ℝ) : Z → ℝ :=
  fun z => (∑ j, σ j z) / C

/-- Exact equality test in (2.15). -/
def payoff {k C t : ℕ} {n : Fin k → ℕ} (u : Utility n) (q h : ℝ) :
    Fin C → (Fin C → Seq n t) → ℝ :=
  fun i y => if weights u q h (empirical y) t (y i) = 1 then 1 else 0

/-- First passing test (2.21), after the calculation of all rounds. -/
def recoveryRound {k C t : ℕ} {n : Fin k → ℕ} (u : Utility n) (β Δ : ℝ)
    (σ : Fin C → Seq n t → ℝ) : Option (Fin t) :=
  ((List.finRange t).filter fun r =>
    1 - β ≤ scoreMass u (roundLaw u (1 - β / 2) (Δ / 4) (mixture σ) r) Δ).head?

def recovery {k C t : ℕ} {n : Fin k → ℕ} (u : Utility n) (β Δ : ℝ)
    (σ : Fin C → Seq n t → ℝ) : Option (Mixed n) :=
  (recoveryRound u β Δ σ).map fun r =>
    marginal (roundLaw u (1 - β / 2) (Δ / 4) (mixture σ) r)

/-- Fixed tie-break: smallest mixed-radix rank among the score maximizers. -/
def bestTuple {k : ℕ} {n : Fin k → ℕ} (hn : ∀ r, 0 < n r)
    (u : Utility n) (Q : Tuple n → ℝ) : Tuple n :=
  if H : ∃ a : Tuple n, (∀ b, score u Q b ≤ score u Q a) ∧
      (∀ b, score u Q b = score u Q a → tupleRank a ≤ tupleRank b)
  then H.choose else fun r => ⟨0, hn r⟩

def zStar {k C t : ℕ} {n : Fin k → ℕ} (hn : ∀ r, 0 < n r)
    (u : Utility n) (β Δ : ℝ) (σ : Fin C → Seq n t → ℝ) : Seq n t :=
  fun r => bestTuple hn u (roundLaw u (1 - β / 2) (Δ / 4) (mixture σ) r)

/-- Expectation with coordinates I fixed; sums only over the remaining coordinates. -/
def fixedExpectation {C : ℕ} {Z : Type} [Fintype Z] (σ : Fin C → Z → ℝ)
    (I : Finset (Fin C)) (fixed : Fin C → Z) (f : (Fin C → Z) → ℝ) : ℝ :=
  ∑ y : ({j : Fin C // j ∉ I} → Z),
    (∏ j : {j : Fin C // j ∉ I}, σ j.val (y j)) *
      f (fun j => if hj : j ∈ I then fixed j else y ⟨j, hj⟩)

/-- (3.1): P in roundLaw is still the original mixture. -/
def deviationExpectation {k C t : ℕ} {n : Fin k → ℕ} (hn : ∀ r, 0 < n r)
    (u : Utility n) (β Δ : ℝ) (σ : Fin C → Seq n t → ℝ) (i : Fin C)
    (f : (Fin C → Seq n t) → ℝ) : ℝ :=
  fixedExpectation σ {i} (fun _ => zStar hn u β Δ σ) f
end NashAmplification.Filtering


