-- Prove2me | Definitions.Def_EnvelopeMSLP_MSLP_postValue
-- name    : EnvelopeMSLP_MSLP_postValue
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:28:44.798664+00:00
-- url     : https://prove2.me/theorems/fa75641a-6320-409c-8e25-6ea32107a20f
-- title:
--   Post-decision value functions
-- statement:
--   The post-decision value functions are
--   $$\bar V_{t+1}(x_t,\xi^t,\theta)=\mathbb E\big(V_{t+1}(x_t,\xi_{t+1},\theta)\mid\xi^t\big),$$
--   built by backward recursion through (8) from $V_{T+1}\equiv0$. Level $i$ takes a decision of level $i$ and the history of length $i$; level $0$ gives the expectation of the first-stage value.
--
--   **Formalization Note** Values are in `EReal`: $-\infty$ marks a decision with no feasible continuation and $+\infty$ an unbounded one.
-- source:
--   Terça and Wozabal, Envelope Theorems for Multi-Stage Linear Stochastic Optimization, preprint (PDF of 2018-06-18), p.12; display (8), p.12

import Mathlib
import Definitions.Def_EnvelopeMSLP_MSLP_condExp
import Definitions.Def_EnvelopeMSLP_MSLP_stageStep

namespace EnvelopeMSLP

/-- **Post-decision value functions.** Terça and Wozabal, *Envelope Theorems for Multi-Stage Linear Stochastic Optimization*, preprint (PDF of 2018-06-18), p.12:
`V̄_{t+1}(x_t, ξ^t, θ) = E(V_{t+1}(x_t, ξ_{t+1}, θ) | ξ^t)`, with `V_{T+1} ≡ 0`, by backward recursion
through (8). `P.postValue θ i x ω` takes the decision `x` of level `i` and the history `ξ^i` of `ω`, so
`i = 0` gives the expectation of the first-stage value at `x₀ = x`.

**Formalization Note.** Values are in `EReal`; `⊥` marks a decision with no feasible continuation
and `⊤` an unbounded one. -/
noncomputable def MSLP.postValue {T : ℕ} {Ω : Type*} [Fintype Ω] (P : MSLP T Ω) (θ : ℝ) :
    (i : Fin (T + 1)) → (Fin (P.n i) → ℝ) → Ω → EReal :=
  Fin.reverseInduction (motive := fun i => (Fin (P.n i) → ℝ) → Ω → EReal)
    (fun _ _ => 0)
    (fun t next x ω => P.condExp t.castSucc (P.stageStep θ t next x) ω)

end EnvelopeMSLP


