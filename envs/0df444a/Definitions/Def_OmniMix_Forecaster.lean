-- Prove2me | Definitions.Def_OmniMix_Forecaster
-- name    : OmniMix_Forecaster
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:39:05.55769+00:00
-- url     : https://prove2.me/theorems/0d7b5864-e916-4b3f-b299-f39648e47742
-- title:
--   Online forecaster
-- statement:
--   In each round $t=1,\dots,T$ nature reveals a context $x_t$ from a context space $X$, the learner forecasts a distribution $D_t$ over $[0,1]$ (its prediction $P_t$ is drawn from $D_t$), and nature reveals the outcome $y_t\in\{0,1\}$.
--
--   An **online forecaster** for horizon $T$ is a rule that, in round $t$, maps the history $(x_1,y_1),\dots,(x_{t-1},y_{t-1})$ and the current context $x_t$ to the forecast $D_t$.
--
--   **Formalization Note** Rounds are indexed $0,\dots,T-1$. The forecaster sees the past and the current context only, never $y_t$; past forecasts are functions of the history and are not stored. It is deterministic: the randomness of $P_t$ is averaged out in the regret.
-- source:
--   Liu–Luo–Ratliff, Omniprediction for All Mixable Proper Losses and Beyond, arXiv:2610.41023, §1, p.1

import Mathlib
import Definitions.Def_OmniMix_FinDist

namespace OmniMix

/-- **Online forecaster.** Liu–Luo–Ratliff, *Omniprediction for All Mixable Proper Losses and Beyond*, arXiv:2610.41023, §1, p.1: "for each round `t = 1, . . . , T`, the nature reveals a
context `x_t` from an arbitrary context space `X`, the learner then makes a prediction `P_t ∈ [0, 1]`,
and finally the nature reveals the true outcome `y_t ∈ {0, 1}`. Here, `P_t` … is generally random; we
let `D_t` be the distribution over `[0, 1]` from which `P_t` is drawn."

A `Forecaster X T` maps, for each round `t < T`, the history of the first `t` context–outcome pairs
and the current context `x_t` to the forecast distribution `D_t`.

**Formalization Note.** Rounds are 0-based (`Fin T`). The forecaster sees only past contexts and
outcomes and the current context, never `y_t` or later rounds; past forecasts are functions of
the history, so they are not stored. It is deterministic; the learner's randomness is the draw
`P_t ∼ D_t`, which the regret averages out. It may depend on `X`, `F` and `T`. -/
def Forecaster (X : Type*) (T : ℕ) : Type _ :=
  (t : Fin T) → (Fin t.val → X × Bool) → X → FinDist

end OmniMix


