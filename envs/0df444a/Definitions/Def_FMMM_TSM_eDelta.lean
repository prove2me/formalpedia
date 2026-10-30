-- Prove2me | Definitions.Def_FMMM_TSM_eDelta
-- name    : FMMM_TSM_eDelta
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:21:24.578753+00:00
-- url     : https://prove2.me/theorems/5b7dda98-a48a-4043-9fd5-7ed5305a3f11
-- title:
--   $E_\delta$: the edges from $A_S$ to $I_T$
-- statement:
--   $E_\delta$ is the set of edges $(a, j) \in E$ that cross the cut $(S, T)$ from the ads of the source side to the impressions of the sink side:
--
--   $$E_\delta = \{(a, j) \in E : a \in A_S,\ j \in I_T\}.$$
--
--   The value of the cut is $2|A_T| + 2|I_S| + |E_\delta|$, and Lemma 1 bounds $|E_\delta|$ in terms of the ad classes.
-- source:
--   Feldman, Mehta, Mirrokni, Muthukrishnan, Online Stochastic Matching: Beating 1-1/e, arXiv:0905.4100v1, §4.2.3, p. 7 (E_δ)

import Mathlib
import Definitions.Def_FMMM_TSM_cutAds
import Definitions.Def_FMMM_TSM_cutImps

namespace FMMM.TSM

/-- **`E_δ`: the edges crossing the cut from `A_S` to `I_T`.**
Feldman, Mehta, Mirrokni, Muthukrishnan, *Online Stochastic Matching: Beating 1-1/e*,
arXiv:0905.4100v1, §4.2.3, p. 7: "Let E_δ be the set of edges (a, i) ∈ E that cross the cut (from
A_S to I_T)."

`eDelta E F` is the set of `(a, j) ∈ E` with `a ∈ A_S = cutAds E F` and `j ∈ I_T`, i.e.
`j ∉ cutImps E F`. -/
noncomputable def eDelta {A J : Type} [Fintype A] [DecidableEq A] [Fintype J] [DecidableEq J]
    (E F : Finset (A × J)) : Finset (A × J) :=
  E.filter (fun p => p.1 ∈ cutAds E F ∧ p.2 ∉ cutImps E F)

end FMMM.TSM


