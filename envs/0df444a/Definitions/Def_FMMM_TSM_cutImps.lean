-- Prove2me | Definitions.Def_FMMM_TSM_cutImps
-- name    : FMMM_TSM_cutImps
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:20:45.559119+00:00
-- url     : https://prove2.me/theorems/307efa31-cb60-48cd-85f9-2b1ebaeee313
-- title:
--   $I_S$: impressions on the source side of the cut after the surgery
-- statement:
--   Start from the reachability cut of the residual graph of $F$, and perform the **surgery**: every impression type on the sink side that is adjacent (in $E$) to more than one ad of $A_S$ is moved to the source side. The resulting set of impression types on the source side is
--
--   $$I_S = \{j \in J : j \text{ is reachable from } s, \text{ or } j \text{ has at least two neighbours in } A_S\},$$
--
--   and $I_T = J \setminus I_S$. The surgery does not increase the value of the cut.
-- source:
--   Feldman, Mehta, Mirrokni, Muthukrishnan, Online Stochastic Matching: Beating 1-1/e, arXiv:0905.4100v1, §4.2.3, p. 7 (surgery; I_S, I_T)

import Mathlib
import Definitions.Def_FMMM_TSM_residReach
import Definitions.Def_FMMM_TSM_cutAds

namespace FMMM.TSM

/-- **`I_S = I ∩ S`: the impressions on the source side of the cut `(S, T)` after the surgery.**
Feldman, Mehta, Mirrokni, Muthukrishnan, *Online Stochastic Matching: Beating 1-1/e*,
arXiv:0905.4100v1, §4.2.3, p. 7: "Then, we do a small bit of "surgery" to this cut: for all
i ∈ I ∩ T, if i is incident to more than one a ∈ A ∩ S, we move i over to S."

`cutImps E F` is the set of impression types `j` that are reachable from the source in the residual
graph, or are adjacent in `E` to at least two ads of `A ∩ S = cutAds E F`. `I_T` is its complement. -/
noncomputable def cutImps {A J : Type} [Fintype A] [DecidableEq A] [Fintype J] [DecidableEq J]
    (E F : Finset (A × J)) : Finset J := by
  classical
  exact Finset.univ.filter (fun j => residReach E F (Sum.inr j) ∨
    2 ≤ ((cutAds E F).filter (fun a => (a, j) ∈ E)).card)

end FMMM.TSM


