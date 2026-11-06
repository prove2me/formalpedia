-- Prove2me | Definitions.Def_GeomDRSub_Alg1Run_info
-- name    : GeomDRSub_Alg1Run_info
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:13:35.988676+00:00
-- url     : https://prove2.me/theorems/d38f9d0a-003b-462f-9da1-5e97fc61e581
-- title:
--   Information $F$ of the oracle conditions on round $t$
-- statement:
--   For a run and a round $t$, the information available when the oracle answers is the history before round $t$ together with this round's draws $(I_t,S_t,U_t)$, which determine the query point $Y_t$.
--
--   In the paper, $F$ "includes the objective sequence, the current query point, and all choices and responses preceding this answer". This $\sigma$-algebra is the smallest one with that property, so oracle conditions stated with respect to it are the strongest reading.
-- source:
--   Aggarwal–Lu, Geometry-Dependent Online and Offline Approximation for Non-Monotone DR-Submodular Maximization, arXiv:2610.00545, Section 3.2, p.9 (after (6))

import Mathlib
import Definitions.Def_GeomDRSub_Alg1Run
import Definitions.Def_GeomDRSub_Alg1Run_draws
import Definitions.Def_GeomDRSub_Alg1Run_hist

namespace GeomDRSub

/-- **The information `F` of the oracle conditions (6)–(7) on round `t`.** Aggarwal–Lu,
arXiv:2610.00545, p.9: "where the information `F` includes the objective sequence, the current query
point, and all choices and responses preceding this answer".

`R.info t` is the history `R.hist t` joined with the σ-algebra of this round's draws
`(I_t, S_t, U_t)`, which determine the query point `Y_t` given the history.

**Formalization Note.** This is the smallest σ-algebra the paper's `F` can be; a condition stated
relative to it is implied by the same condition relative to any larger `F` that contains it (tower
property), so it is the strongest reading of (6)–(7). -/
def Alg1Run.info {d : ℕ} {Ω : Type*} (R : Alg1Run d Ω) (t : ℕ) : MeasurableSpace Ω :=
  R.hist t ⊔ MeasurableSpace.comap (R.draws t) inferInstance

end GeomDRSub


