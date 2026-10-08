-- Prove2me | Definitions.Def_WeightedMajority_Shifting_WML
-- name    : WeightedMajority_Shifting_WML
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T14:10:14.838147+00:00
-- url     : https://prove2.me/theorems/a130b3b5-b249-4ab3-bddd-8750d1d1aa2f
-- title:
--   Runs of the modified Weighted Majority Algorithm WML, with mistake counts and the factor u (Section 3)
-- statement:
--   Fix a pool of $n$ prediction algorithms, indexed by $i = 1, \dots, n$, and a finite sequence of $T$ trials. In trial $t$ every pool member $i$ makes a binary prediction $x_i^{(t)} \in \{0,1\}$, the master algorithm makes a prediction $\lambda^{(t)} \in \{0,1\}$, and then the label $\rho^{(t)} \in \{0,1\}$ is revealed. The predictions of the pool and the labels are arbitrary (no probabilistic assumption); the bounds stated with this definition hold for every such sequence.
--
--   The master keeps a weight $w_i^{(t)}$ for each pool member, the weight at the beginning of trial $t$; $w^{(1)}$ are the initial weights and the weights after the last trial are the final weights. Write $W^{(t)} = \sum_{j} w_j^{(t)}$ for the total weight and
--   $$q_b^{(t)} = \sum_{i \,:\, x_i^{(t)} = b} w_i^{(t)}, \qquad b \in \{0,1\},$$
--   for the total weight of the members predicting $b$.
--
--   **The algorithm WML** (Littlestone and Warmuth) has two parameters $\beta$ and $\gamma$. Its run on the sequence is described by the following rules.
--
--   1. Every initial weight $w_i^{(1)}$ is positive.
--   2. The master predicts with the weighted majority: $\lambda^{(t)} = 0$ if $q_0^{(t)} > q_1^{(t)}$, $\lambda^{(t)} = 1$ if $q_1^{(t)} > q_0^{(t)}$, and either value if $q_0^{(t)} = q_1^{(t)}$.
--   3. If the master is correct ($\lambda^{(t)} = \rho^{(t)}$) no weight changes. If it errs, each member $i$ with $x_i^{(t)} \ne \rho^{(t)}$ and
--   $$w_i^{(t)} > \frac{\gamma}{n}\, W^{(t)}$$
--   has its weight multiplied by $\beta$; every other weight is unchanged. The threshold is computed from the total weight at the beginning of the trial.
--
--   For $\gamma = 0$ this is the Weighted Majority Algorithm WM. The definition also fixes the counts used in the bounds: the number of mistakes of the master, $\#\{t : \lambda^{(t)} \ne \rho^{(t)}\}$; the number of mistakes of member $i$ on the trials $t$ of a block $a \le t < b$; the minimum of the latter over the pool; and the factor
--   $$u = \frac{1+\beta}{2} + (1-\beta)\gamma .$$
--
--   These objects are what the shifting-target bounds of Section 3 (Lemma 3.1 and Theorem 3.1) are stated about.
--
--   **Formalization Note** Trials are numbered $t = 0, \dots, T-1$ (`Fin T`) and the pool is `Fin n`; the weights are a function `w : ℕ → Fin n → ℝ`, where `w t` are the weights at the beginning of trial $t$, `w 0` the initial and `w T` the final weights (values at indices beyond $T$ are unconstrained and never used). Binary values are `Bool`. Since ties may be broken either way, a run is a relation `IsWMLRun β γ x ρ w lam`, and every statement about runs holds for all tie-breaking choices. The parameter ranges $0<\beta<1$, $0\le\gamma<1/2$ are hypotheses of the theorems, not fields of the run. The minimum over the pool is an infimum in `ℕ` over `Fin n`, which is attained when $n > 0$ (the theorems assume $n > 0$).
-- source:
--   Littlestone, Warmuth, The Weighted Majority Algorithm, Inform. and Comput. 108 (1994), p. 223, Section 3 (algorithm WML); p. 215, Section 1 (algorithm WM); p. 224, Lemma 3.1 (factor u)

import Mathlib

namespace WeightedMajority.Shifting

open Finset

/-- Total weight `Σ_j w_j` of a weight vector on a pool of `n` algorithms. -/
noncomputable def totalWeight {n : ℕ} (w : Fin n → ℝ) : ℝ :=
  ∑ j, w j

/-- `voteWeight w x b` is the total weight `q_b` of the pool members whose prediction in the
current trial (`x i`) equals `b`. -/
noncomputable def voteWeight {n : ℕ} (w : Fin n → ℝ) (x : Fin n → Bool) (b : Bool) : ℝ :=
  ∑ i ∈ univ.filter (fun i => x i = b), w i

/-- The weighted-majority prediction rule (p. 215): predict according to the larger of
`q_0 = voteWeight w x false` and `q_1 = voteWeight w x true`; in case of a tie either
prediction is allowed. -/
def IsMajorityPrediction {n : ℕ} (w : Fin n → ℝ) (x : Fin n → Bool) (lam : Bool) : Prop :=
  (voteWeight w x true < voteWeight w x false → lam = false) ∧
  (voteWeight w x false < voteWeight w x true → lam = true)

/-- The WML weight update of one trial (p. 223). If the master's prediction `lam` differs from
the label `ρ`, every pool member `i` whose prediction `x i` disagrees with the label has its
weight multiplied by `β`, but only if its weight before the update is strictly larger than
`γ / n` times the total weight at the beginning of the trial. All other weights, and all weights
in a trial where the master is right, are unchanged. -/
noncomputable def wmlUpdate {n : ℕ} (β γ : ℝ) (w : Fin n → ℝ) (x : Fin n → Bool) (ρ lam : Bool) :
    Fin n → ℝ :=
  fun i => if lam ≠ ρ ∧ x i ≠ ρ ∧ (γ / (n : ℝ)) * totalWeight w < w i then β * w i else w i

/-- A run of WML (p. 223) with parameters `β, γ` on `T` trials, pool `Fin n`, pool predictions
`x t i`, labels `ρ t`, weights `w t` at the beginning of trial `t` (`w 0` the initial weights,
`w T` the final weights) and master predictions `lam t`. The initial weights are positive, each
prediction is a weighted majority vote (ties arbitrary), and the weights evolve by `wmlUpdate`. -/
structure IsWMLRun {n T : ℕ} (β γ : ℝ) (x : Fin T → Fin n → Bool) (ρ : Fin T → Bool)
    (w : ℕ → Fin n → ℝ) (lam : Fin T → Bool) : Prop where
  init_pos : ∀ i, 0 < w 0 i
  predict : ∀ t : Fin T, IsMajorityPrediction (w t) (x t) (lam t)
  update : ∀ t : Fin T, w ((t : ℕ) + 1) = wmlUpdate β γ (w t) (x t) (ρ t) (lam t)

/-- Number of mistakes of the master: trials `t` with `lam t ≠ ρ t`. -/
def masterMistakes {T : ℕ} (ρ lam : Fin T → Bool) : ℕ :=
  (univ.filter (fun t : Fin T => lam t ≠ ρ t)).card

/-- Number of mistakes of pool member `i` on the trials `t` with `a ≤ t < b`. -/
def memberMistakesOn {n T : ℕ} (x : Fin T → Fin n → Bool) (ρ : Fin T → Bool) (a b : ℕ)
    (i : Fin n) : ℕ :=
  (univ.filter (fun t : Fin T => a ≤ (t : ℕ) ∧ (t : ℕ) < b ∧ x t i ≠ ρ t)).card

/-- Minimum, over the pool, of the number of mistakes on the trials `a ≤ t < b`
(`m_0` of Lemma 3.1, `m_i` of Theorem 3.1). The infimum is over the finite set `Fin n`; it is a
minimum when `n > 0`. -/
noncomputable def bestMistakesOn {n T : ℕ} (x : Fin T → Fin n → Bool) (ρ : Fin T → Bool)
    (a b : ℕ) : ℕ :=
  ⨅ i : Fin n, memberMistakesOn x ρ a b i

/-- The contraction factor `u = (1 + β)/2 + (1 − β)γ` of Lemma 3.1. -/
noncomputable def uFactor (β γ : ℝ) : ℝ :=
  (1 + β) / 2 + (1 - β) * γ

end WeightedMajority.Shifting


