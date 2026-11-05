-- Prove2me | Definitions.Def_DHRUniq_E6prime
-- name    : DHRUniq_E6prime
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:33:58.97636+00:00
-- url     : https://prove2.me/theorems/9e219656-9c68-41db-a1e6-5b8bd3de2d12
-- title:
--   Condition (E6′): convexity on pure decompositions
-- statement:
--   For any state $\varrho$ and any decomposition $\varrho=\sum_ip_i|\psi_i\rangle\langle\psi_i|$ with $p_i\ge0$ and $\sum_ip_i=1$,
--
--   $$
--   E(\varrho)\le\sum_ip_iE(P_{\psi_i}).
--   $$
--
--   **Formalization Note** Decompositions are finite, the form in which the paper uses the condition (Proposition 22, p. 17).
-- source:
--   Donald, Horodecki, Rudolph, The uniqueness theorem for entanglement measures, arXiv:quant-ph/0105017v2, §5.1, (E6′), p. 9

import Mathlib
import Definitions.Def_DHRUniq_BipartiteFunctional
import Definitions.Def_DHRUniq_IsUnitVec
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_ObliviousRSP_pureState

open ObliviousRSP (pureState)
open WildeQIT (IsDensityOperator)

namespace DHRUniq

/-- **Condition (E6′), convexity on pure decompositions** (Donald, Horodecki, Rudolph, *The uniqueness theorem for entanglement measures*, arXiv:quant-ph/0105017v2, §5.1, p. 9): "For any state
`ϱ ∈ Σ(H^A ⊗ H^B)` and any decomposition `ϱ = ∑_i p_i |ψ_i⟩⟨ψ_i|` with `|ψ_i⟩ ∈ H^A ⊗ H^B`,
`p_i ≥ 0` for all `i` and `∑_i p_i = 1`, we require `E(ϱ) ≤ ∑_i p_i E(P_{ψ_i})`."

**Formalization Note** Decompositions are finite, the form in which the paper uses the condition
(Proposition 22, p. 17: "its finite decompositions into pure states"). Lemma 11 only assumes (E6′),
so requiring it for finite decompositions alone makes that lemma stronger. -/
def E6prime (E : BipartiteFunctional) : Prop :=
  ∀ ⦃a b : Type⦄ [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (ρ : Matrix (a × b) (a × b) ℂ) (ι : Type) [Fintype ι] (p : ι → ℝ) (ψ : ι → a × b → ℂ),
    IsDensityOperator ρ → (∀ i, 0 ≤ p i) → ∑ i, p i = 1 → (∀ i, IsUnitVec (ψ i)) →
    ρ = ∑ i, (p i : ℂ) • pureState (ψ i) → E ρ ≤ ∑ i, p i * E (pureState (ψ i))

end DHRUniq


