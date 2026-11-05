-- Prove2me | Definitions.Def_DHRUniq_P4
-- name    : DHRUniq_P4
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:33:40.889563+00:00
-- url     : https://prove2.me/theorems/bd741026-ec8e-473b-bb70-426125436775
-- title:
--   Condition (P4): additivity on pure states
-- statement:
--   For all $n\ge1$ and every pure state $\varrho$,
--
--   $$
--   \frac{E(\varrho^{\otimes n})}{n}=E(\varrho).
--   $$
--
--   This is one of the conditions on an entanglement measure $E$ in §5 of the paper.
-- source:
--   Donald, Horodecki, Rudolph, The uniqueness theorem for entanglement measures, arXiv:quant-ph/0105017v2, §5.2, (P4), p. 10

import Mathlib
import Definitions.Def_DHRUniq_BipartiteFunctional
import Definitions.Def_DHRUniq_IsUnitVec
import Definitions.Def_WildeQIT_EntManip_tensorPowVec
import Definitions.Def_ObliviousRSP_pureState

open ObliviousRSP (pureState)
open WildeQIT.EntManip (tensorPowVec)

namespace DHRUniq

/-- **Condition (P4), additivity on pure states** (Donald, Horodecki, Rudolph, *The uniqueness theorem for entanglement measures*, arXiv:quant-ph/0105017v2, §5.2, p. 10): "For all `n ≥ 1` and all
`ϱ ∈ Σ_p(H^A ⊗ H^B)`, `E(ϱ^{⊗n}) / n = E(ϱ)`."

**Formalization Note** For `ϱ = P_ψ`, `ϱ^{⊗n} = P_{ψ^{⊗n}}` on `(H^A)^{⊗n} ⊗ (H^B)^{⊗n}`. -/
def P4 (E : BipartiteFunctional) : Prop :=
  ∀ ⦃a b : Type⦄ [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (ψ : a × b → ℂ) (n : ℕ),
    1 ≤ n → IsUnitVec ψ → E (pureState (tensorPowVec ψ n)) / n = E (pureState ψ)

end DHRUniq


