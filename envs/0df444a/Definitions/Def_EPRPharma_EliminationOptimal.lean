-- Prove2me | Definitions.Def_EPRPharma_EliminationOptimal
-- name    : EPRPharma_EliminationOptimal
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:21:33.444804+00:00
-- url     : https://prove2.me/theorems/8c2800f2-2b6b-48ea-97a2-5d9099dae946
-- title:
--   Eliminating over-prescription is total welfare maximizing
-- statement:
--   Under model $P$ it is total welfare maximizing to eliminate over-prescription if some equilibrium $(y,d)$ of $P$ without over-prescription has welfare at least that of every equilibrium of $P$. This is the event characterized by Proposition 3.
-- source:
--   Alev, Atasu, Toktay, Zhang, Extended Producer Responsibility for Pharmaceuticals, SSRN 2693169 (2020 posting), Proposition 3, p. 17

import Mathlib
import Definitions.Def_EPRPharma_IsEquilibrium
import Definitions.Def_EPRPharma_OverPrescribes
import Definitions.Def_EPRPharma_welfare

namespace EPRPharma

/-- **It is total welfare maximizing to eliminate over-prescription under model m.**
Alev, Atasu, Toktay, Zhang, *Extended Producer Responsibility for Pharmaceuticals*, SSRN 2693169 (2020 posting), Proposition 3, p. 17: "it is total
welfare maximizing to eliminate over-prescription". `EliminationOptimal P m` says that some
equilibrium of model m without over-prescription attains the maximal total welfare over all
equilibria of m. -/
def EliminationOptimal (P : Params) (m : Model) : Prop :=
  ∃ y d, IsEquilibrium P m y d ∧ ¬ OverPrescribes P d ∧
    ∀ y' d', IsEquilibrium P m y' d' → welfare P m y' d' ≤ welfare P m y d

end EPRPharma


