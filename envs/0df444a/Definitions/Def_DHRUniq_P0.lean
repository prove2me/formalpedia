-- Prove2me | Definitions.Def_DHRUniq_P0
-- name    : DHRUniq_P0
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:33:41.95799+00:00
-- url     : https://prove2.me/theorems/90d4f9b3-8785-4df4-8d94-05973c25bb61
-- title:
--   Condition (P0)
-- statement:
--   If $\sigma$ is a separable pure state of $\mathcal H^A\otimes\mathcal H^B$, then $E(\sigma)=0$.
--
--   This is one of the conditions on an entanglement measure $E$ in §5 of the paper.
-- source:
--   Donald, Horodecki, Rudolph, The uniqueness theorem for entanglement measures, arXiv:quant-ph/0105017v2, §5.2, (P0), p. 9

import Mathlib
import Definitions.Def_DHRUniq_BipartiteFunctional
import Definitions.Def_DHRUniq_IsUnitVec
import Definitions.Def_DHRUniq_IsSeparable
import Definitions.Def_ObliviousRSP_pureState

open ObliviousRSP (pureState)

namespace DHRUniq

/-- **Condition (P0)** (Donald, Horodecki, Rudolph, *The uniqueness theorem for entanglement measures*, arXiv:quant-ph/0105017v2, §5.2, p. 9): "If `σ ∈ Σ_p(H^A ⊗ H^B)` is separable, then
`E(σ) = 0`." -/
def P0 (E : BipartiteFunctional) : Prop :=
  ∀ ⦃a b : Type⦄ [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (ψ : a × b → ℂ),
    IsUnitVec ψ → IsSeparable (pureState ψ) → E (pureState ψ) = 0

end DHRUniq


