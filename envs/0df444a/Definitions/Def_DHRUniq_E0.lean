-- Prove2me | Definitions.Def_DHRUniq_E0
-- name    : DHRUniq_E0
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:33:40.702203+00:00
-- url     : https://prove2.me/theorems/c88080da-4974-40a1-b444-bcb50f635d65
-- title:
--   Condition (E0)
-- statement:
--   If $\sigma$ is a separable state, then $E(\sigma)=0$.
--
--   This is one of the conditions on an entanglement measure $E$ in §5 of the paper.
-- source:
--   Donald, Horodecki, Rudolph, The uniqueness theorem for entanglement measures, arXiv:quant-ph/0105017v2, §5.1, (E0), p. 8

import Mathlib
import Definitions.Def_DHRUniq_BipartiteFunctional
import Definitions.Def_DHRUniq_IsSeparable

namespace DHRUniq

/-- **Condition (E0)** (Donald, Horodecki, Rudolph, *The uniqueness theorem for entanglement measures*, arXiv:quant-ph/0105017v2, §5.1, p. 8): "If `σ` is separable, then `E(σ) = 0`." -/
def E0 (E : BipartiteFunctional) : Prop :=
  ∀ ⦃a b : Type⦄ [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (σ : Matrix (a × b) (a × b) ℂ), IsSeparable σ → E σ = 0

end DHRUniq


