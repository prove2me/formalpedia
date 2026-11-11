-- Prove2me | Definitions.Def_ARGFContract_Hardness_IndependentGain
-- name    : ARGFContract_Hardness_IndependentGain
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T20:44:14.529879+00:00
-- url     : https://prove2.me/theorems/49c4dfdb-78b6-415d-98c1-f10546ae457f
-- title:
--   The normalized independent-set gain h
-- statement:
--   For a simple graph $G$ on $n$ labelled vertices, set
--
--   $$h_G(S)=\begin{cases}|S|/n&\text{if }S\text{ is independent in }G,\\0&\text{otherwise.}\end{cases}$$
--
--   The nonempty graph regime uses precisely the function in the proof of Theorem 1. At $n=0$, the only set has value zero. This definition exposes the combinatorial objective later encoded inside net utility; its range, subadditivity and attained optimum are separate theorem targets.
-- source:
--   Jalal Etesami, Larkin Liu, Rilind Sahitaj, Optimal Contract Design for Rank Ordered Gain Functions with Modular Costs, STOC 2027 submission #348 (October 2026), proof of Theorem 1, pp. 7–8, definition of h; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/348.pdf

import Definitions.Def_ARGFContract_Hardness_NetUtility
import Mathlib.Combinatorics.SimpleGraph.Clique

namespace ARGFContract.Hardness

open Classical in
/-- The function h in the proof of Theorem 1, pp. 7–8.
At n = 0 the sole subset has value 0, the total extension of the construction. -/
noncomputable def independentGain {n : ℕ} (G : SimpleGraph (Fin n))
    (S : Finset (Fin n)) : ℚ :=
  if G.IsIndepSet (S : Set (Fin n)) then (S.card : ℚ) / n else 0

end ARGFContract.Hardness


