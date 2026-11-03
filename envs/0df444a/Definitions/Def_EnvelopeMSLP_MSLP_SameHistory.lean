-- Prove2me | Definitions.Def_EnvelopeMSLP_MSLP_SameHistory
-- name    : EnvelopeMSLP_MSLP_SameHistory
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:26:19.495407+00:00
-- url     : https://prove2.me/theorems/556df131-2e55-4314-9bb6-435ac9863bcb
-- title:
--   Equal history
-- statement:
--   With $\xi^t=(\xi_1,\dots,\xi_t)$, two scenarios have the same history of length $i$ when their first $i$ noises agree. Length $0$ relates all scenarios.
-- source:
--   Terça and Wozabal, Envelope Theorems for Multi-Stage Linear Stochastic Optimization, preprint (PDF of 2018-06-18), p.11

import Mathlib
import Definitions.Def_EnvelopeMSLP_MSLP

namespace EnvelopeMSLP

/-- **Equal history.** Terça and Wozabal, *Envelope Theorems for Multi-Stage Linear Stochastic Optimization*, preprint (PDF of 2018-06-18), p.11: `ξ^t = (ξ_1, …, ξ_t)`. `P.SameHistory i ω ω'` says that the first
`i` noises agree on `ω` and `ω'`, so `i = t.succ` is the history through stage `t`, and `i = 0` is the
empty history. -/
def MSLP.SameHistory {T : ℕ} {Ω : Type*} [Fintype Ω] (P : MSLP T Ω) (i : Fin (T + 1)) (ω ω' : Ω) : Prop :=
  ∀ s : Fin T, s.castSucc < i → P.ξ s ω = P.ξ s ω'

end EnvelopeMSLP


