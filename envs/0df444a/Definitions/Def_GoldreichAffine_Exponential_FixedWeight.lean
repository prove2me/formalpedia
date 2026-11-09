-- Prove2me | Definitions.Def_GoldreichAffine_Exponential_FixedWeight
-- name    : GoldreichAffine_Exponential_FixedWeight
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:11:41.383566+00:00
-- url     : https://prove2.me/theorems/66477121-bf0f-435e-a0af-31348e87f6e3
-- title:
--   Fixed-weight marginal, global guesses and feasibility
-- statement:
--   Condition on an $n$-bit seed having weight $w\le n$. A global guess fixes positions $R$ to an assignment $u$. Write $n′=n-|R|$ and $w′=w-\|u\|$. The reduced parameters are feasible exactly when
--   $$0\le n′\le n,\quad 0\le w′\le n′,\quad 0\le w-w′\le n-n′.$$
--   Each such pair can be realized by a guess. Its success probability is
--   $$p_{\rm guess}=\frac{\binom{n′}{w′}}{\binom n w}.$$
--   After a correct guess, the remaining seed is uniform among words of weight $w′$. Its ordered $j$-coordinate marginal, sampled without replacement, has mass
--   $$\Pr[Z_j=z]=\frac{\binom{n′-j}{w′-\|z\|}}{\binom{n′}{w′}},\qquad j\le n′.$$
--   Binomial coefficients with a negative or too large lower index are zero. Feasibility makes both denominators positive. When $n′=w′=j=0$, the sole empty word has mass one. This exact marginal distinguishes the attack model from an independent Bernoulli approximation.
--
--   **Formalization Note** All dimensions and weights are natural numbers; explicit comparisons guard natural subtractions. The lower index $w′-\|z\|$ is computed in the integers. Guess assignments are stored on all positions with entries outside $R$ ignored.
-- source:
--   Ximing Fu, Mo Li, Shihan Lyu, STOC 2027 submission #579 (October 2026), p. 6 (PDF p. 7), §3.2, Eq. (1); fixed-weight marginal continued on p. 7 (PDF p. 8); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/579.pdf

import Definitions.Def_GoldreichAffine_Exponential_BooleanCore
open scoped BigOperators NNReal ENNReal
open MatousekLP.Codes (Word weight)
set_option autoImplicit false

namespace GoldreichAffine.Exponential

/-- Binomial coefficients are zero for negative lower indices. -/
def binomZ (n : ℕ) (k : ℤ) : ℕ := if 0 ≤ k then n.choose k.toNat else 0

/-- Exact law of the ordered j-coordinate marginal, without replacement.
    Its source domain is w' ≤ n' and j ≤ n'. -/
noncomputable def fixedWeightMass (np wp j : ℕ) (z : Word j) : ℝ≥0 :=
  (binomZ (np - j) ((wp : ℤ) - weight z) : ℝ≥0) / (np.choose wp : ℝ≥0)

noncomputable def fixedAgreement {j : ℕ} (np wp : ℕ) (Q f : Predicate j) : ℝ :=
  agreement (fixedWeightMass np wp j) Q f

/-- Each reduced pair is realized by a global guess; signed feasibility is explicit. -/
def FeasiblePair (n w np wp : ℕ) : Prop :=
  np ≤ n ∧ wp ≤ np ∧ wp ≤ w ∧ w - wp ≤ n - np

/-- A global guess fixes only R; u outside R is irrelevant. -/
structure GlobalGuess (n : ℕ) where
  positions : Finset (Fin n)
  assignment : Word n

def guessedOnes {n : ℕ} (G : GlobalGuess n) : ℕ :=
  (G.positions.filter fun i => G.assignment i = true).card

def FeasibleGuess {n : ℕ} (w : ℕ) (G : GlobalGuess n) : Prop :=
  guessedOnes G ≤ w ∧ w - guessedOnes G ≤ n - G.positions.card

noncomputable def guessingProbability (n w np wp : ℕ) : ℝ≥0∞ :=
  (np.choose wp : ℝ≥0∞) / (n.choose w : ℝ≥0∞)

end GoldreichAffine.Exponential


