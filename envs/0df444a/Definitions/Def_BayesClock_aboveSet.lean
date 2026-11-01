-- Prove2me | Definitions.Def_BayesClock_aboveSet
-- name    : BayesClock_aboveSet
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:12:22.831529+00:00
-- url     : https://prove2.me/theorems/bbea4cdf-43f4-401f-a698-22a52649cef3
-- title:
--   Bidders above a threshold, $S(t,v)$
-- statement:
--   For a set of bidders $S$, a threshold $t\ge0$ and a value vector $v$,
--
--   $$S(t,v)=\{i\in S\mid v_i>t\}.$$
--
--   The inequality is strict, unlike the acceptance event $v_i\ge p$ of an auction.
-- source:
--   Feldman, Gkatzelis, Gravin & Schoepflin, Bayesian and Randomized Clock Auctions, arXiv:2202.09291v1, §3.2, p.7

import Mathlib

open MeasureTheory
open scoped NNReal ENNReal

namespace BayesClock

/-- `S(t, v) = {i ∈ S | vi > t}`: the bidders of `S` with value strictly above `t`.
Feldman et al., arXiv:2202.09291v1, §3.2, p.7. -/
noncomputable def aboveSet {N : Type*} (S : Finset N) (t : ℝ≥0) (v : N → ℝ≥0) : Finset N :=
  S.filter (fun i => t < v i)

end BayesClock


