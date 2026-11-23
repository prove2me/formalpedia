-- Prove2me | solution 1 for ApproxPolySatCH.Main.randomized_turing_in_ch
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T04:25:49.957686+00:00
-- url     : https://prove2.me/submissions/da564692-4ff4-48ce-aa77-69c563096797

import Definitions.Def_ApproxPolySatCH_Main_ResultantLanguages

set_option autoImplicit false

open ApproxPolySatCH.Main

theorem solution {A L : Language} (hA : InCH A)
    (hred : RandomizedTuringReduction L A) : InCH L := by
  rcases hA with ⟨j, hA⟩
  rcases hred with ⟨M, c, d, a, b, hclock, hcorrect⟩
  refine ⟨j + 1, A, hA, M, c, d, a, b, hclock, ?_⟩
  intro x
  have hp : 0 < 2 ^ clock a b x.length := by positivity
  constructor
  · intro hx
    have h := (hcorrect x).1 hx
    omega
  · intro hx
    by_contra hnot
    have h := (hcorrect x).2 hnot
    omega
