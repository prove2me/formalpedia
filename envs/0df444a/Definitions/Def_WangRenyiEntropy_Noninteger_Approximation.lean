-- Prove2me | Definitions.Def_WangRenyiEntropy_Noninteger_Approximation
-- name    : WangRenyiEntropy_Noninteger_Approximation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:46:40.048728+00:00
-- url     : https://prove2.me/theorems/2230c235-cae0-4b99-894c-10f8ed392d5d
-- title:
--   Best uniform power approximation and its uniform constant
-- statement:
--   Let $\alpha>0$ and $Q$ be a real polynomial. Define its uniform error by
--   $$E_\alpha(Q)=\sup_{0\le x\le1}|Q(x)-x^\alpha|.$$
--   A best approximant at degree $k$ has degree at most $k$ and minimizes this error among all real polynomials of that degree. A uniform approximation constant $c\ge1$ means that every best approximant $Q(x)=\sum_j a_jx^j$, for every $k\ge1$, satisfies both
--   $$E_\alpha(Q)\le c k^{-2\alpha},\qquad \sum_{j=0}^k|a_j|\le c8^k.$$
--   This predicate names the single constant furnished by Lemma 2.2. Existence of best approximants and of this constant are theorem conclusions in that item, not assumptions granting success to an estimator. Compactness and continuity make the real supremum an ordinary finite uniform norm on every order used here.
-- source:
--   Qisheng Wang, STOC 2027 submission #447 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/447.pdf, printed 6 / PDF 8, §2.2, Lemma 2.2

import Mathlib

open scoped BigOperators
noncomputable section

namespace WangRenyiEntropy.Noninteger

/-- Nonempty compact interval and continuous functions when α>0, so this real
supremum is finite and is the actual uniform norm, including the zero polynomial. -/
def approximationError (α : ℝ) (Q : Polynomial ℝ) : ℝ :=
  sSup {r | ∃ x ∈ Set.Icc (0 : ℝ) 1, r = |Q.eval x - Real.rpow x α|}

/-- Degree at most k, and comparison against every polynomial of that degree. -/
def IsBestApproximation (α : ℝ) (k : ℕ) (Q : Polynomial ℝ) : Prop :=
  Q.natDegree ≤ k ∧ ∀ P : Polynomial ℝ, P.natDegree ≤ k →
    approximationError α Q ≤ approximationError α P

/-- One constant for BOTH bounds, all degrees and every best approximant.
Existence of such a constant is the content of Lemma 2.2, not an estimator axiom. -/
def ApproximationConstant (α c : ℝ) : Prop :=
  1 ≤ c ∧ ∀ k : ℕ, 1 ≤ k → ∀ Q : Polynomial ℝ,
    IsBestApproximation α k Q →
      approximationError α Q ≤ c * Real.rpow k (-2 * α) ∧
      (∑ j ∈ Finset.range (k + 1), |Q.coeff j|) ≤ c * (8 : ℝ) ^ k

end WangRenyiEntropy.Noninteger


