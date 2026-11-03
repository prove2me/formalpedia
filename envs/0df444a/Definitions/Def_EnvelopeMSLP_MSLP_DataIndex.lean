-- Prove2me | Definitions.Def_EnvelopeMSLP_MSLP_DataIndex
-- name    : EnvelopeMSLP_MSLP_DataIndex
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:26:16.236689+00:00
-- url     : https://prove2.me/theorems/9aba762a-251c-48e8-9884-828049bad7d1
-- title:
--   Index set of the joint data of (7)
-- statement:
--   One index per stage, scenario and entry of $W_t$, $T_t$, $c_t$, $h_t$. The data of all stages and scenarios together are the data of the deterministic equivalent.
-- source:
--   Terça and Wozabal, Envelope Theorems for Multi-Stage Linear Stochastic Optimization, preprint (PDF of 2018-06-18), p.11; §3.1, p.14

import Mathlib
import Definitions.Def_EnvelopeMSLP_MSLP

namespace EnvelopeMSLP

/-- **Index set of the joint data vector of (7):** one entry per stage, scenario and entry of `W_t`, `T_t`,
`c_t`, `h_t`. Terça and Wozabal, *Envelope Theorems for Multi-Stage Linear Stochastic Optimization*, preprint (PDF of 2018-06-18), p.11 ("the data of the problem in stage `t`"), stacked over all stages and
scenarios, which is the data of the deterministic equivalent of p.14. -/
abbrev MSLP.DataIndex {T : ℕ} {Ω : Type*} [Fintype Ω] (P : MSLP T Ω) : Type _ :=
  Σ t : Fin T, Ω × ((Fin (P.m t) × Fin (P.n t.succ)) ⊕ (Fin (P.m t) × Fin (P.n t.castSucc)) ⊕
    Fin (P.n t.succ) ⊕ Fin (P.m t))

end EnvelopeMSLP


