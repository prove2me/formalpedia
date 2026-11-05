-- Prove2me | Definitions.Def_DHRUniq_P5dprime
-- name    : DHRUniq_P5dprime
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:33:46.752283+00:00
-- url     : https://prove2.me/theorems/2219b92d-7887-460c-bcb4-8c2501784cf1
-- title:
--   Condition (P5′′): existence of a regularization on pure states
-- statement:
--   For every pure state $\varrho$ the limit
--
--   $$
--   E^\infty(\varrho)\equiv\lim_{n\to\infty}\frac{E(\varrho^{\otimes n})}{n}
--   $$
--
--   exists.
--
--   This is one of the conditions on an entanglement measure $E$ in §5 of the paper.
-- source:
--   Donald, Horodecki, Rudolph, The uniqueness theorem for entanglement measures, arXiv:quant-ph/0105017v2, §5.2, (P5′′), p. 10

import Mathlib
import Definitions.Def_DHRUniq_BipartiteFunctional
import Definitions.Def_DHRUniq_IsUnitVec
import Definitions.Def_WildeQIT_EntManip_tensorPowVec
import Definitions.Def_ObliviousRSP_pureState

open Filter Topology
open ObliviousRSP (pureState)
open WildeQIT.EntManip (tensorPowVec)

namespace DHRUniq

/-- **Condition (P5′′), existence of a regularization on pure states** (Donald, Horodecki, Rudolph, *The uniqueness theorem for entanglement measures*, arXiv:quant-ph/0105017v2, §5.2, p. 10): "For
all `ϱ ∈ Σ_p(H^A ⊗ H^B)`, the limit `E^∞(ϱ) ≡ lim_{n→∞} E(ϱ^{⊗n})/n` exists."

**Formalization Note** The value of the sequence at `n = 0` does not affect the limit. -/
def P5dprime (E : BipartiteFunctional) : Prop :=
  ∀ ⦃a b : Type⦄ [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (ψ : a × b → ℂ),
    IsUnitVec ψ → ∃ L : ℝ, Tendsto (fun n : ℕ => E (pureState (tensorPowVec ψ n)) / n) atTop (𝓝 L)

end DHRUniq


