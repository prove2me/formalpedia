-- Prove2me | Definitions.Def_DHRUniq_E2
-- name    : DHRUniq_E2
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:34:33.394632+00:00
-- url     : https://prove2.me/theorems/840119c7-53e0-45ca-9ccd-01d43c0807ee
-- title:
--   Condition (E2): LQCC monotonicity
-- statement:
--   If $\Lambda$ is an LQCC operation, then
--
--   $$
--   E(\Lambda(\sigma))\le E(\sigma)
--   $$
--
--   for all states $\sigma$ on $\mathcal H^A\otimes\mathcal H^B$.
--
--   This is one of the conditions on an entanglement measure $E$ in §5 of the paper.
-- source:
--   Donald, Horodecki, Rudolph, The uniqueness theorem for entanglement measures, arXiv:quant-ph/0105017v2, §5.1, (E2), eq. (13), p. 8

import Mathlib
import Definitions.Def_DHRUniq_BipartiteFunctional
import Definitions.Def_DHRUniq_IsLQCC
import Definitions.Def_WildeQIT_IsDensityOperator

open WildeQIT (IsDensityOperator)

namespace DHRUniq

/-- **Condition (E2), LQCC monotonicity** (Donald, Horodecki, Rudolph, *The uniqueness theorem for entanglement measures*, arXiv:quant-ph/0105017v2, §5.1, p. 8): "If `Λ` is an LQCC operation, then
`E(Λ(σ)) ≤ E(σ)` (13) for all `σ ∈ Σ(H^A ⊗ H^B)`."

**Formalization Note** As in (P2), `Λ` ranges over LQCC operations between any two pairs of local
spaces. -/
def E2 (E : BipartiteFunctional) : Prop :=
  ∀ ⦃a b a' b' : Type⦄ [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype a'] [DecidableEq a'] [Fintype b'] [DecidableEq b']
    (Λ : Matrix (a × b) (a × b) ℂ → Matrix (a' × b') (a' × b') ℂ)
    (σ : Matrix (a × b) (a × b) ℂ), IsLQCC Λ → IsDensityOperator σ → E (Λ σ) ≤ E σ

end DHRUniq


