-- Prove2me | Definitions.Def_DHRUniq_E4prime
-- name    : DHRUniq_E4prime
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:33:53.750435+00:00
-- url     : https://prove2.me/theorems/6c403a08-372a-477d-8c08-b850bbd7e08f
-- title:
--   Condition (E4′): asymptotic additivity
-- statement:
--   Given $\epsilon>0$ and a state $\varrho$, there exists an integer $N>0$ such that $n\ge N$ implies
--
--   $$
--   \frac{E(\varrho^{\otimes n})}{n}-\epsilon\le E(\varrho)\le\frac{E(\varrho^{\otimes n})}{n}+\epsilon.
--   $$
--
--   This is one of the conditions on an entanglement measure $E$ in §5 of the paper.
-- source:
--   Donald, Horodecki, Rudolph, The uniqueness theorem for entanglement measures, arXiv:quant-ph/0105017v2, §5.1, (E4′), p. 8

import Mathlib
import Definitions.Def_DHRUniq_BipartiteFunctional
import Definitions.Def_DHRUniq_tensorPowMat
import Definitions.Def_WildeQIT_IsDensityOperator

open WildeQIT (IsDensityOperator)

namespace DHRUniq

/-- **Condition (E4′), asymptotic additivity** (Donald, Horodecki, Rudolph, *The uniqueness theorem for entanglement measures*, arXiv:quant-ph/0105017v2, §5.1, p. 8): "Given `ε > 0` and
`ϱ ∈ Σ(H^A ⊗ H^B)`, there exists an integer `N > 0` such that `n ≥ N` implies
`E(ϱ^{⊗n})/n − ε ≤ E(ϱ) ≤ E(ϱ^{⊗n})/n + ε`." -/
def E4prime (E : BipartiteFunctional) : Prop :=
  ∀ ⦃a b : Type⦄ [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (ρ : Matrix (a × b) (a × b) ℂ) (ε : ℝ),
    0 < ε → IsDensityOperator ρ → ∃ N : ℕ, 0 < N ∧ ∀ n, N ≤ n →
      E (tensorPowMat ρ n) / n - ε ≤ E ρ ∧ E ρ ≤ E (tensorPowMat ρ n) / n + ε

end DHRUniq


