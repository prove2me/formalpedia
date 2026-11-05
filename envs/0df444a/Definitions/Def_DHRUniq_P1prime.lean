-- Prove2me | Definitions.Def_DHRUniq_P1prime
-- name    : DHRUniq_P1prime
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:33:41.741332+00:00
-- url     : https://prove2.me/theorems/a1ecc8ba-08bc-48b7-985e-a5e1a961306f
-- title:
--   Condition (P1′): $E(P_+(\mathbb C^2))=1$
-- statement:
--   The functional takes the value one on the Bell pair: $E(P_+(\mathbb C^2))=1$.
--
--   This is one of the conditions on an entanglement measure $E$ in §5 of the paper.
-- source:
--   Donald, Horodecki, Rudolph, The uniqueness theorem for entanglement measures, arXiv:quant-ph/0105017v2, §5.2, (P1′), p. 9

import Mathlib
import Definitions.Def_DHRUniq_BipartiteFunctional
import Definitions.Def_DHRUniq_psiPlus
import Definitions.Def_ObliviousRSP_pureState

open ObliviousRSP (pureState)

namespace DHRUniq

/-- **Condition (P1′) = (E1′)** (Donald, Horodecki, Rudolph, *The uniqueness theorem for entanglement measures*, arXiv:quant-ph/0105017v2, §5.2, p. 9): "`E(P_+(ℂ²)) = 1`."

**Formalization Note** `P_+(ℂ²)` is the state of `|Ψ_+(ℂ²)⟩ = (|00⟩ + |11⟩)/√2` on
`Fin 2 × Fin 2`. -/
def P1prime (E : BipartiteFunctional) : Prop :=
  E (pureState (psiPlus 2)) = 1

end DHRUniq


