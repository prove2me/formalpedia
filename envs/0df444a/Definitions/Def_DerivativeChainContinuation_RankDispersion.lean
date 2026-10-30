-- Prove2me | Definitions.Def_DerivativeChainContinuation_RankDispersion
-- name    : DerivativeChainContinuation_RankDispersion
-- status  : Definition
-- author  : @labuka
-- created : 2026-10-26T16:40:57.762685+00:00
-- url     : https://prove2.me/theorems/cf37002a-7df5-40d2-9f1f-9686022f07b4
-- title:
--   Centered weights for a row of fixed rank
-- statement:
--   For an integer $m\ge0$ and an index $0\le i<m$, define
--
--   $$w_m(i)=2i+1-m.$$
--
--   These centered arithmetic-progression weights express ordered dispersion as a scalar product and permit exact second-moment calculations.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/RankDispersion.lean#L6-L6

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations

set_option autoImplicit false
namespace DerivativeChainContinuation
open scoped BigOperators

noncomputable def rankWeight (m : ℕ) (i : Fin m) : ℝ := 2*(i.val : ℝ)+1-m










end DerivativeChainContinuation


