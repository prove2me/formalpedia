-- Prove2me | Definitions.Def_EnvelopeMSLP_MSLP_IsNonanticipative
-- name    : EnvelopeMSLP_MSLP_IsNonanticipative
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:27:18.122225+00:00
-- url     : https://prove2.me/theorems/486bf4bf-7b36-49fb-bbe6-c6dc00dd5877
-- title:
--   Nonanticipative decisions
-- statement:
--   A decision process is nonanticipative when $x_t$ is a function of the history $\xi^t$: scenarios with the same $\xi^t$ get the same $x_t$.
-- source:
--   Terça and Wozabal, Envelope Theorems for Multi-Stage Linear Stochastic Optimization, preprint (PDF of 2018-06-18), display (7), p.11; display (8), p.12; §3.2, p.16

import Mathlib
import Definitions.Def_EnvelopeMSLP_MSLP_Policy
import Definitions.Def_EnvelopeMSLP_MSLP_SameHistory

namespace EnvelopeMSLP

/-- **Nonanticipative decisions:** `x_t` is a function of the history `ξ^t`. Terça and Wozabal, *Envelope Theorems for Multi-Stage Linear Stochastic Optimization*, preprint (PDF of 2018-06-18), display (7), p.11,
read through (8), p.12, and §3.2, p.16 ("the whole history of the process `ξ^t` may be required"). -/
def MSLP.IsNonanticipative {T : ℕ} {Ω : Type*} [Fintype Ω] (P : MSLP T Ω) (x : P.Policy) : Prop :=
  ∀ (t : Fin T) (ω ω' : Ω), P.SameHistory t.succ ω ω' → x t ω = x t ω'

end EnvelopeMSLP


