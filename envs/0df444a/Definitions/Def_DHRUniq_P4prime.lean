-- Prove2me | Definitions.Def_DHRUniq_P4prime
-- name    : DHRUniq_P4prime
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:33:40.204057+00:00
-- url     : https://prove2.me/theorems/6a451b81-1800-4560-8e2f-9eb12eba80a1
-- title:
--   Condition (P4′): asymptotic additivity on pure states
-- statement:
--   Given $\epsilon>0$ and a pure state $\varrho$, there exists an integer $N>0$ such that $n\ge N$ implies
--
--   $$
--   \frac{E(\varrho^{\otimes n})}{n}-\epsilon\le E(\varrho)\le\frac{E(\varrho^{\otimes n})}{n}+\epsilon.
--   $$
--
--   This is one of the conditions on an entanglement measure $E$ in §5 of the paper.
-- source:
--   Donald, Horodecki, Rudolph, The uniqueness theorem for entanglement measures, arXiv:quant-ph/0105017v2, §5.2, (P4′), p. 10

import Mathlib
import Definitions.Def_DHRUniq_BipartiteFunctional
import Definitions.Def_DHRUniq_IsUnitVec
import Definitions.Def_WildeQIT_EntManip_tensorPowVec
import Definitions.Def_ObliviousRSP_pureState

open ObliviousRSP (pureState)
open WildeQIT.EntManip (tensorPowVec)

namespace DHRUniq

/-- **Condition (P4′), asymptotic additivity on pure states** (Donald, Horodecki, Rudolph, *The uniqueness theorem for entanglement measures*, arXiv:quant-ph/0105017v2, §5.2, p. 10): "Given `ε > 0`
and `ϱ ∈ Σ_p(H^A ⊗ H^B)`, there exists an integer `N > 0` such that `n ≥ N` implies
`E(ϱ^{⊗n})/n − ε ≤ E(ϱ) ≤ E(ϱ^{⊗n})/n + ε`." -/
def P4prime (E : BipartiteFunctional) : Prop :=
  ∀ ⦃a b : Type⦄ [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (ψ : a × b → ℂ) (ε : ℝ),
    0 < ε → IsUnitVec ψ → ∃ N : ℕ, 0 < N ∧ ∀ n, N ≤ n →
      E (pureState (tensorPowVec ψ n)) / n - ε ≤ E (pureState ψ) ∧
        E (pureState ψ) ≤ E (pureState (tensorPowVec ψ n)) / n + ε

end DHRUniq


