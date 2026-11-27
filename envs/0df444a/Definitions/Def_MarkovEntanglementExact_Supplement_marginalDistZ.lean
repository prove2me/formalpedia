-- Prove2me | Definitions.Def_MarkovEntanglementExact_Supplement_marginalDistZ
-- name    : MarkovEntanglementExact_Supplement_marginalDistZ
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T00:49:06.213331+00:00
-- url     : https://prove2.me/theorems/2221c024-c1a4-4100-ba31-c2c239a48448
-- title:
--   Marginal of an occupancy on $(s_i,a_i,z)$
-- statement:
--   For a distribution $\mu$ on triples $(s,a,z)$ of a system with exogenous information, its marginal onto agent $i$'s pair and the exogenous state is
--   $$\mu_{iz}(s_i,a_i,z)=\sum_{(s',a'):\,(s',a')_i=(s_i,a_i)}\mu(s',a',z).$$
-- source:
--   Chen & Peng, Multi-agent Markov Entanglement, arXiv:2506.02385v3, Appendix J.1, p.45

import Mathlib
import Definitions.Def_markov_entanglement_multi

open scoped BigOperators
open MarkovEntanglement

namespace MarkovEntanglementExact.Supplement

/-- In a system with exogenous information `z ∈ Z`, the marginal of a distribution `μ` on
`(s, a, z)` onto agent `i`'s pair and the exogenous state:
`μ_{iz}(s_i, a_i, z) = Σ_{(s, a, z′) : (s, a)_i = (s_i, a_i), z′ = z} μ(s, a, z′)`.

Source: Chen & Peng, Multi-agent Markov Entanglement, arXiv:2506.02385v3, Appendix J.1, p.45
(the conditional `µ^π_ABz(s_B, a_B | s_A, a_A, z)` in the local transition `P_Az`). -/
def marginalDistZ {N : ℕ} {S : Fin N → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    {Z : Type*} [Fintype Z] [DecidableEq Z] (i : Fin N) (μ : JointZ S Z → ℝ) (t : S i × Z) : ℝ :=
  ∑ q : JointZ S Z, if q.1 i = t.1 ∧ q.2 = t.2 then μ q else 0

end MarkovEntanglementExact.Supplement


