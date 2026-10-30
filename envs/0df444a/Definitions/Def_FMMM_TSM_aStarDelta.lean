-- Prove2me | Definitions.Def_FMMM_TSM_aStarDelta
-- name    : FMMM_TSM_aStarDelta
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:22:29.370488+00:00
-- url     : https://prove2.me/theorems/6ef294c1-64ca-4d79-b909-9b5ae4e6b13a
-- title:
--   $A^*_\delta$: ads of $E_\delta$ adjacent to a drawn impression of $I_T$
-- statement:
--   Let $A_\delta$ be the set of ads incident to edges of $E_\delta$. For a sequence of drawn impression types $\omega_0, \dots, \omega_{n-1}$,
--
--   $$A^*_\delta(\omega) = \{a \in A_\delta : (a, \omega_t) \in E \text{ for some draw } t \text{ with } \omega_t \in I_T\},$$
--
--   the ads of $A_\delta$ that are adjacent in the realization graph to some drawn impression whose type lies on the sink side. These ads are placed on the sink side of the cut of the realization graph used to bound $\mathrm{OPT}$.
-- source:
--   Feldman, Mehta, Mirrokni, Muthukrishnan, Online Stochastic Matching: Beating 1-1/e, arXiv:0905.4100v1, §4.2.3, p. 8 (A_δ, A*_δ)

import Mathlib
import Definitions.Def_FMMM_TSM_cutImps
import Definitions.Def_FMMM_TSM_eDelta

namespace FMMM.TSM

/-- **`A*_δ`: the ads of `E_δ` adjacent to a drawn impression of `I_T`.**
Feldman, Mehta, Mirrokni, Muthukrishnan, *Online Stochastic Matching: Beating 1-1/e*,
arXiv:0905.4100v1, §4.2.3, p. 8: "Let A_δ, I_δ be the ads and impressions, respectively, that are
incident to edges in E_δ. … Let A*_δ ⊆ A_δ be the set of ads a ∈ A that are incident (in Ĝ_f) to
some i′ ∈ D(i) ⊆ Î_T."

For arrivals `ω : Fin n → J`, `aStarDelta E F ω` is the set of ads `a` incident to an edge of
`E_δ` such that some draw `t` has type `ω t ∈ I_T` (`ω t ∉ cutImps E F`) with `(a, ω t) ∈ E`. -/
noncomputable def aStarDelta {A J : Type} [Fintype A] [DecidableEq A] [Fintype J] [DecidableEq J]
    {n : ℕ} (E F : Finset (A × J)) (ω : Fin n → J) : Finset A := by
  classical
  exact ((eDelta E F).image Prod.fst).filter
    (fun a => ∃ t : Fin n, ω t ∉ cutImps E F ∧ (a, ω t) ∈ E)

end FMMM.TSM


