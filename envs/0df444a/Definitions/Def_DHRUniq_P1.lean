-- Prove2me | Definitions.Def_DHRUniq_P1
-- name    : DHRUniq_P1
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:35:52.981477+00:00
-- url     : https://prove2.me/theorems/ca70891f-82ac-40ba-a79b-5b9348104c00
-- title:
--   Condition (P1): normalization on all representatives
-- statement:
--   If $P_+^d$ is any representative of $P_+(\mathbb C^d)$, for $d=1,2,\dots$, in any bipartite system, then $E(P_+^d)=\log_2 d$.
--
--   This is one of the conditions on an entanglement measure $E$ in §5 of the paper.
-- source:
--   Donald, Horodecki, Rudolph, The uniqueness theorem for entanglement measures, arXiv:quant-ph/0105017v2, §5.2, (P1), p. 9

import Mathlib
import Definitions.Def_DHRUniq_BipartiteFunctional
import Definitions.Def_DHRUniq_IsMaxEntRep
import Definitions.Def_ObliviousRSP_pureState

open ObliviousRSP (pureState)

namespace DHRUniq

/-- **Condition (P1) = (E1), normalization** (Donald, Horodecki, Rudolph, *The uniqueness theorem for entanglement measures*, arXiv:quant-ph/0105017v2, §5.2, p. 9): "If `P_+^d` is any representative
of `P_+(ℂ^d)`, then `E(P_+^d) = log_2 d` for `d = 1, 2, …`."

**Formalization Note** `IsMaxEntRep` contains `0 < d`. Every representative on every pair of local
spaces is covered, not only `|Ψ_+(ℂ^d)⟩`. -/
def P1 (E : BipartiteFunctional) : Prop :=
  ∀ ⦃a b : Type⦄ [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (d : ℕ) (ψ : a × b → ℂ),
    IsMaxEntRep d ψ → E (pureState ψ) = Real.logb 2 d

end DHRUniq


