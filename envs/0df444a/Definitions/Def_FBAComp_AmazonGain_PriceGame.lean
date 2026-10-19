-- Prove2me | Definitions.Def_FBAComp_AmazonGain_PriceGame
-- name    : FBAComp_AmazonGain_PriceGame
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T06:51:41.516964+00:00
-- url     : https://prove2.me/theorems/0ae417ad-9fdf-465e-a8ba-af8a000a3ec3
-- title:
--   General two-seller simultaneous price game
-- statement:
--   A two-seller price game specifies real payoffs for each real price pair $(p_A,p_S)$. A pure Nash equilibrium is a pair at which neither seller gains by changing its own price alone:
--
--   $$\Pi_A(p'_A,p_S)\leq\Pi_A(p_A,p_S),\qquad \Pi_S(p_A,p'_S)\leq\Pi_S(p_A,p_S)\quad\text{for all }p'_A,p'_S\in\mathbb R.$$
--
--   This reusable definition supplies the simultaneous pricing stage of both variants of the paper's model.
-- source:
--   Lai, Liu, Xiao & Zhao, “Fulfilled by Amazon”, SSRN preprint 3270958 (PDF of 2021-10-08), pp. 11–13, timing and simultaneous Nash pricing in §3 and §4.1

import Mathlib

namespace FBAComp.AmazonGain

/-- A simultaneous two-seller price game with real prices and real payoffs. -/
structure PriceGame where
  payoffA : ℝ → ℝ → ℝ
  payoffS : ℝ → ℝ → ℝ

/-- A pure Nash equilibrium of a two-seller price game, with each player varying only its own price. -/
def PriceGame.IsNash (G : PriceGame) (pA pS : ℝ) : Prop :=
  (∀ pA', G.payoffA pA' pS ≤ G.payoffA pA pS) ∧
  (∀ pS', G.payoffS pA pS' ≤ G.payoffS pA pS)

end FBAComp.AmazonGain


