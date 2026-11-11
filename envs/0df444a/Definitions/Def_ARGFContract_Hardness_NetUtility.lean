-- Prove2me | Definitions.Def_ARGFContract_Hardness_NetUtility
-- name    : ARGFContract_Hardness_NetUtility
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T20:43:24.202872+00:00
-- url     : https://prove2.me/theorems/a4d26b24-bee5-4f34-954d-23f9e9f63256
-- title:
--   Net utility and its attained optimum (2.1)–(2.2)
-- statement:
--   For exact rational gains $f$ and additive costs $c_i$, define
--
--   $$\mu(S)=f(S)-\sum_{i\in S}c_i,\qquad \operatorname{OPT}(\mu)=\max_{S\subseteq E}\mu(S).$$
--
--   The maximum is over the entire finite powerset, which always contains the empty set, including at $n=0$. It is a finite attained maximum. Rational arithmetic gives the same comparisons as the corresponding real values and supports exact machine evaluation. These definitions supply the common objective and optimum used throughout the mission.
-- source:
--   Jalal Etesami, Larkin Liu, Rilind Sahitaj, Optimal Contract Design for Rank Ordered Gain Functions with Modular Costs, STOC 2027 submission #348 (October 2026), equations (2.1)–(2.2), p. 6; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/348.pdf

import Mathlib

namespace ARGFContract.Hardness

/-- Equation (2.1), p. 6, on exact rational data. -/
def netUtility {n : ℕ} (f : Finset (Fin n) → ℚ) (c : Fin n → ℚ)
    (S : Finset (Fin n)) : ℚ := f S - ∑ i ∈ S, c i

/-- Attained maximum over the nonempty finite powerset, equations (2.2) and p. 7.
This definition has no empty-index or unbounded-index default. -/
def maxSubset {n : ℕ} (f : Finset (Fin n) → ℚ) : ℚ :=
  (Finset.univ : Finset (Finset (Fin n))).sup' Finset.univ_nonempty f

end ARGFContract.Hardness


