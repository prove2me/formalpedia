-- Prove2me | Definitions.Def_JakulinBratko_C
-- name    : JakulinBratko_C
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T16:02:31.084116+00:00
-- url     : https://prove2.me/theorems/6119f4e2-7d05-46db-95f2-0d95cf4f88f8
-- title:
--   Eq. (11), first form — $k$-way total correlation
-- statement:
--   The $k$-way total correlation of a subset $\mathcal S$ of the attributes is
--
--   $$
--   C(\mathcal S)=\sum_{X\in\mathcal S}H(X)-H(\mathcal S).
--   $$
--
--   It is the amount by which the entropy of $\mathcal S$ falls short of the sum of the entropies of its attributes.
-- source:
--   Jakulin–Bratko, Quantifying and Visualizing Attribute Interactions, arXiv:cs/0308002v3, §2.4, Eq. (11), p.8

import Definitions.Def_JakulinBratko_H

namespace JakulinBratko

/-- The `k`-way total correlation `C(S)`, the first form of Eq. (11), p.8
(Jakulin–Bratko, Quantifying and Visualizing Attribute Interactions, arXiv:cs/0308002v3): `C(S) = ∑_{X ∈ S} H(X) - H(S)`. -/
noncomputable def C {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*}
    [∀ i, Fintype (α i)] [∀ i, DecidableEq (α i)]
    (P : (∀ i, α i) → ℝ) (S : Finset ι) : ℝ :=
  ∑ X ∈ S, H P {X} - H P S

end JakulinBratko


