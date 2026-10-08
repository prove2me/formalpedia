-- Prove2me | Definitions.Def_MinimaxRegretRL_Bernstein_FiniteVariance
-- name    : MinimaxRegretRL_Bernstein_FiniteVariance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T15:45:10.660985+00:00
-- url     : https://prove2.me/theorems/43186830-ccf3-4511-9ef2-ede3ec3746c4
-- title:
--   Expectation and variance on a finite probability space
-- statement:
--   For a finite probability vector $p$ and a real statistic $X$, expectation is $\mathbb E_p X=\sum_zp(z)X(z)$ and variance is $\operatorname{Var}_p(X)=\mathbb E_p(X^2)-(\mathbb E_pX)^2$.
--
--   This finite-sum interface supports the general variance inequality in Lemma 2. The probability-vector conditions are imposed by the theorem using it.
-- source:
--   Azar, Osband and Munos, Minimax Regret Bounds for Reinforcement Learning, arXiv:1703.05449v2 (2017), p. 19, Lemma 2 and proof

import Mathlib

namespace MinimaxRegretRL.Bernstein

/-- Expectation of a real statistic against a finite probability vector. -/
def finiteExp {Ω : Type*} [Fintype Ω] (p : Ω → ℝ) (f : Ω → ℝ) : ℝ :=
  ∑ z : Ω, p z * f z

/-- Variance of a real statistic against a finite probability vector. -/
def finiteVar {Ω : Type*} [Fintype Ω] (p : Ω → ℝ) (f : Ω → ℝ) : ℝ :=
  finiteExp p (fun z => (f z) ^ 2) - (finiteExp p f) ^ 2

end MinimaxRegretRL.Bernstein


