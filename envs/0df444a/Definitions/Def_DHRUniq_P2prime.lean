-- Prove2me | Definitions.Def_DHRUniq_P2prime
-- name    : DHRUniq_P2prime
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:34:05.583179+00:00
-- url     : https://prove2.me/theorems/bfac80ce-e588-45f6-9e6a-b443dda618cd
-- title:
--   Condition (P2′): dependence on Schmidt coefficients only
-- statement:
--   For a pure state $\sigma$, $E(\sigma)$ depends only on the non-zero coefficients of a Schmidt decomposition of $\sigma$: two pure states, possibly on different spaces, with the same non-zero Schmidt coefficients have the same value.
--
--   This is one of the conditions on an entanglement measure $E$ in §5 of the paper.
-- source:
--   Donald, Horodecki, Rudolph, The uniqueness theorem for entanglement measures, arXiv:quant-ph/0105017v2, §5.2, (P2′), p. 9

import Mathlib
import Definitions.Def_DHRUniq_BipartiteFunctional
import Definitions.Def_DHRUniq_IsUnitVec
import Definitions.Def_DHRUniq_schmidtCoeffs
import Definitions.Def_ObliviousRSP_pureState

open ObliviousRSP (pureState)

namespace DHRUniq

/-- **Condition (P2′)** (Donald, Horodecki, Rudolph, *The uniqueness theorem for entanglement measures*, arXiv:quant-ph/0105017v2, §5.2, p. 9): "For `σ ∈ Σ_p(H^A ⊗ H^B)`, `E(σ)` depends only on the
non-zero coefficients of a Schmidt decomposition of `σ`."

**Formalization Note** The comparison is across all pairs of local spaces, as the paper uses it
("Using (P2′), we may assume that `H^A ≡ H^B ≡ H`", §8, p. 18). -/
def P2prime (E : BipartiteFunctional) : Prop :=
  ∀ ⦃a b a' b' : Type⦄ [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype a'] [DecidableEq a'] [Fintype b'] [DecidableEq b']
    (ψ : a × b → ℂ) (φ : a' × b' → ℂ),
    IsUnitVec ψ → IsUnitVec φ → schmidtCoeffs ψ = schmidtCoeffs φ →
    E (pureState ψ) = E (pureState φ)

end DHRUniq


