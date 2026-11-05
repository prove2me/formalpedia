-- Prove2me | Definitions.Def_DHRUniq_E4
-- name    : DHRUniq_E4
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:33:42.166581+00:00
-- url     : https://prove2.me/theorems/86188681-ac19-4abb-aa78-5b7e831603b4
-- title:
--   Condition (E4): additivity
-- statement:
--   For all $n\ge1$ and every state $\varrho$ on $\mathcal H^A\otimes\mathcal H^B$,
--
--   $$
--   \frac{E(\varrho^{\otimes n})}{n}=E(\varrho).
--   $$
--
--   This is one of the conditions on an entanglement measure $E$ in §5 of the paper.
-- source:
--   Donald, Horodecki, Rudolph, The uniqueness theorem for entanglement measures, arXiv:quant-ph/0105017v2, §5.1, (E4), p. 8

import Mathlib
import Definitions.Def_DHRUniq_BipartiteFunctional
import Definitions.Def_DHRUniq_tensorPowMat
import Definitions.Def_WildeQIT_IsDensityOperator

open WildeQIT (IsDensityOperator)

namespace DHRUniq

/-- **Condition (E4), additivity** (Donald, Horodecki, Rudolph, *The uniqueness theorem for entanglement measures*, arXiv:quant-ph/0105017v2, §5.1, p. 8): "For all `n ≥ 1` and all
`ϱ ∈ Σ(H^A ⊗ H^B)`, `E(ϱ^{⊗n}) / n = E(ϱ)`." -/
def E4 (E : BipartiteFunctional) : Prop :=
  ∀ ⦃a b : Type⦄ [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (ρ : Matrix (a × b) (a × b) ℂ) (n : ℕ),
    1 ≤ n → IsDensityOperator ρ → E (tensorPowMat ρ n) / n = E ρ

end DHRUniq


