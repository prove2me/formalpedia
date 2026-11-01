-- Prove2me | Definitions.Def_ShrinkingUCB_regret
-- name    : ShrinkingUCB_regret
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:19:11.161985+00:00
-- url     : https://prove2.me/theorems/59be040f-35c3-4e9b-95e9-edc4ee1ede51
-- title:
--   The regret $R(T)$ of ConsUCB
-- statement:
--   The **regret** of a run of ConsUCB against a product set $S^*$ over $T$ periods is
--
--   $$
--   R(T)=\sum_{t=1}^T\sum_{i\in S^*}\mu(i)-\sum_{t=1}^T\sum_{i\in S_t}\mu(i).
--   $$
--
--   It is a random variable through the sets $S_t$, and it uses the means $\mu$, not the realized outcomes.
-- source:
--   Jin, Simchi-Levi, Wang, Wang, Yang, Shrinking the Upper Confidence Bound: A Dynamic Product Selection Problem for Urban Warehouses, arXiv:1903.07844v2, §2, p.9

import Definitions.Def_ShrinkingUCB_ConsUCB

namespace ShrinkingUCB

/-- The regret of ConsUCB (arXiv:1903.07844v2, §2, p.9):
`R(T) = ∑_{t=1}^T ∑_{i ∈ S*} µ(i) − ∑_{t=1}^T ∑_{i ∈ S_t} µ(i)`. It depends on the table only
through the sets `S_t`, and it uses the means `µ`, not the realized outcomes. -/
noncomputable def regret {d N : ℕ} (I : LinearSemiBandit d N) (tb : TieBreak N) (α : ℝ) (K : ℕ)
    (Sstar : Finset (Fin N)) (T : ℕ) (o : OutcomeTable N) : ℝ :=
  ∑ t ∈ Finset.Icc 1 T, ∑ i ∈ Sstar, I.μ i
    - ∑ t ∈ Finset.Icc 1 T, ∑ i ∈ offered I tb α K o t, I.μ i

end ShrinkingUCB


