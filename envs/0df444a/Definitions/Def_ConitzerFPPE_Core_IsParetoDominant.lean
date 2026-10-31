-- Prove2me | Definitions.Def_ConitzerFPPE_Core_IsParetoDominant
-- name    : ConitzerFPPE_Core_IsParetoDominant
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T19:01:09.956711+00:00
-- url     : https://prove2.me/theorems/dd2354dd-fef3-4500-9514-db664b8a6b1b
-- title:
--   Componentwise greatest BFPM multipliers
-- statement:
--   A pair $(\alpha,x)$ is a Pareto-dominant BFPM when it is a BFPM and, for every BFPM $(\beta,y)$ of the same finite market,
--   $$\forall i\in N,\quad\beta_i\le\alpha_i.$$
--   This means a greatest feasible multiplier vector, with its own feasible allocation witness. The comparison includes every feasible allocation. The predicate contains no equilibrium condition and makes no uniqueness claim about allocations. Empty bidder and good types are allowed.
-- source:
--   Conitzer et al., Pacing Equilibrium in First Price Auction Markets, arXiv:1811.07166v4, Lemma 1 and componentwise-order convention, p. 9; https://arxiv.org/abs/1811.07166v4

import Definitions.Def_ConitzerFPPE_Core_IsBFPM

namespace ConitzerFPPE.Core

def IsParetoDominant {N M : Type*} [Fintype N] [Fintype M] (P : MultPacing.Existence.PacingGame N M) (α : N → ℝ) (x : N → M → ℝ) : Prop :=
  IsBFPM P α x ∧ ∀ (β : N → ℝ) (y : N → M → ℝ),
    IsBFPM P β y → ∀ i, β i ≤ α i

end ConitzerFPPE.Core


