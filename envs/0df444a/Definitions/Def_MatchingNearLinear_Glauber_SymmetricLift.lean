-- Prove2me | Definitions.Def_MatchingNearLinear_Glauber_SymmetricLift
-- name    : MatchingNearLinear_Glauber_SymmetricLift
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T15:55:38.4566+00:00
-- url     : https://prove2.me/theorems/c42a1c08-51b4-472e-a5a7-94d4c9aa55d4
-- title:
--   Symmetric homogenization and the least covariance rate
-- statement:
--   Given a subset law $p$ on $N$ coordinates and an integer $K>N$, add $K$ disjoint auxiliary coordinates. The lifted law on subsets $U$ of the $N+K$ sites is
--
--   $$\widehat p_K(U)=\frac{p(S)}{\binom K{|S|}}\quad (|U|=K),\qquad S=U\cap[N],$$
--
--   and zero for other cardinalities. This is precisely sampling $S\sim p$ followed by a uniform auxiliary set of size $K-|S|$. The least covariance rate $C^*(t)$ is the infimum of coefficients at least one valid simultaneously after every feasible positive pin of the scalar-field law. Finite downward-closed positive supports make this set nonempty and bounded below. These objects state the uniform lift estimate without adding stability or marginal assumptions.
-- source:
--   Tianshun Miao, Yitong Yin, Sampling Matchings in Near-linear Time, STOC 2027 submission #444 (October 2026), §3.2, printed p.15 (PDF p.17), Eq. (15); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/444.pdf

import Mathlib
import Definitions.Def_MatchingNearLinear_Glauber_SubsetLaws

set_option autoImplicit false

namespace MatchingNearLinear.Glauber


open scoped BigOperators
noncomputable section
open Classical
/-- The original and auxiliary coordinates occupy disjoint intervals of Fin (N+K). -/
def originalPart {N K : ℕ} (U : Config (N+K)) : Config N :=
  Finset.univ.filter fun i => Fin.castAdd K i ∈ U

/-- Equation (15): exactly K occupied sites and K auxiliary sites. -/
def symmetricLift {N : ℕ} (p : Config N → ℝ) (K : ℕ) (U : Config (N+K)) : ℝ :=
  if U.card = K then p (originalPart U) / (Nat.choose K (originalPart U).card : ℝ) else 0

/-- Least admissible coefficient at least one, over all feasible positive pinnings. -/
def leastRate {N : ℕ} (p : Config N → ℝ) (t : ℝ) : ℝ :=
  sInf {c : ℝ | 1 ≤ c ∧ ∀ τ, 0 < pinMass (scalarTilt p t) τ →
    CovarianceBound (positivePin (scalarTilt p t) τ) c}

end
end MatchingNearLinear.Glauber


