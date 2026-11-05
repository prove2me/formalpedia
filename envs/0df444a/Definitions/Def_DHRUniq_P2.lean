-- Prove2me | Definitions.Def_DHRUniq_P2
-- name    : DHRUniq_P2
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:34:27.00531+00:00
-- url     : https://prove2.me/theorems/afadf394-c9cf-452e-b49d-68d81072f0ec
-- title:
--   Condition (P2): LQCC monotonicity on pure states
-- statement:
--   Let $\Lambda$ be an LQCC operation between any two pairs of local spaces. If $\sigma$ is a pure state such that $\Lambda(\sigma)$ is also pure, then $E(\Lambda(\sigma))\le E(\sigma)$.
--
--   This is one of the conditions on an entanglement measure $E$ in §5 of the paper.
-- source:
--   Donald, Horodecki, Rudolph, The uniqueness theorem for entanglement measures, arXiv:quant-ph/0105017v2, §5.2, (P2), p. 9

import Mathlib
import Definitions.Def_DHRUniq_BipartiteFunctional
import Definitions.Def_DHRUniq_IsUnitVec
import Definitions.Def_DHRUniq_IsLQCC
import Definitions.Def_ObliviousRSP_pureState

open ObliviousRSP (pureState)

namespace DHRUniq

/-- **Condition (P2)** (Donald, Horodecki, Rudolph, *The uniqueness theorem for entanglement measures*, arXiv:quant-ph/0105017v2, §5.2, p. 9): "Let `Λ` be an operation which can be realized by means
of local operations and classical communications. If `σ ∈ Σ_p(H^A ⊗ H^B)` is such that `Λ(σ)` is
also pure, then `E(Λ(σ)) ≤ E(σ)`."

**Formalization Note** `Λ` is any LQCC operation (Definition 4) between any two pairs of local
spaces; a map changing the local spaces is essential (it gives the invariance under local
isomorphisms used in Lemma 11 and in the proof of Theorem 23). -/
def P2 (E : BipartiteFunctional) : Prop :=
  ∀ ⦃a b a' b' : Type⦄ [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype a'] [DecidableEq a'] [Fintype b'] [DecidableEq b']
    (Λ : Matrix (a × b) (a × b) ℂ → Matrix (a' × b') (a' × b') ℂ)
    (ψ : a × b → ℂ) (φ : a' × b' → ℂ),
    IsLQCC Λ → IsUnitVec ψ → IsUnitVec φ → Λ (pureState ψ) = pureState φ →
    E (pureState φ) ≤ E (pureState ψ)

end DHRUniq


