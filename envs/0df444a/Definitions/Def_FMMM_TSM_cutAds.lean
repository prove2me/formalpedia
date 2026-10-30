-- Prove2me | Definitions.Def_FMMM_TSM_cutAds
-- name    : FMMM_TSM_cutAds
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:20:11.481662+00:00
-- url     : https://prove2.me/theorems/af27b497-c956-4f67-9314-faab009637f2
-- title:
--   $A_S$: ads on the source side of the cut $(S, T)$
-- statement:
--   $A_S = A \cap S$ is the set of ads reachable from the source $s$ in the residual graph of the flow $F$ of $G_f$. The surgery that turns the reachability cut into the cut $(S, T)$ moves only impressions, so $A_S$ is the same before and after it. The ads on the sink side are $A_T = A \setminus A_S$.
-- source:
--   Feldman, Mehta, Mirrokni, Muthukrishnan, Online Stochastic Matching: Beating 1-1/e, arXiv:0905.4100v1, §4.2.3, p. 7 (A_S = A ∩ S, A_T)

import Mathlib
import Definitions.Def_FMMM_TSM_residReach

namespace FMMM.TSM

/-- **`A_S = A ∩ S`: the ads on the source side of the cut `(S, T)`.**
Feldman, Mehta, Mirrokni, Muthukrishnan, *Online Stochastic Matching: Beating 1-1/e*,
arXiv:0905.4100v1, §4.2.3, p. 7: "Let A_S = A ∩ S, and define A_T, I_S and I_T similarly."

`cutAds E F` is the set of ads reachable from the source in the residual graph (`residReach`).
The surgery of p. 7 moves only impressions, so `A ∩ S` is the same before and after it;
`A_T` is the complement `univ \ cutAds E F`. -/
noncomputable def cutAds {A J : Type} [Fintype A] [DecidableEq A] [DecidableEq J]
    (E F : Finset (A × J)) : Finset A := by
  classical
  exact Finset.univ.filter (fun a => residReach E F (Sum.inl a))

end FMMM.TSM


