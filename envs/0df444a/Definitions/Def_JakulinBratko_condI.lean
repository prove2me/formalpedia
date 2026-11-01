-- Prove2me | Definitions.Def_JakulinBratko_condI
-- name    : JakulinBratko_condI
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T16:03:14.906589+00:00
-- url     : https://prove2.me/theorems/b63631fd-00aa-4eb8-84be-bfca4ddaa13c
-- title:
--   Conditional interaction information $I(\mathcal R\mid X)$, the average over the values of $X$
-- statement:
--   For an attribute $X$ and a subset $\mathcal R$ of the attributes, the conditional interaction information is the interaction information of $\mathcal R$ under the conditional law given $X=x$, averaged over $x$:
--
--   $$
--   I(\mathcal R\mid X)=\sum_{x\in\Re_X}P(x)\,I_{P(\cdot\mid x)}(\mathcal R).
--   $$
--
--   For $\mathcal R=\{A,B\}$ this is the conditional mutual information of Eq. (4), which the paper describes on p.7 as the expected interaction over the values of the conditioning attribute.
--
--   **Formalization Note** The paper writes $I(\mathcal S\setminus X\mid X)$ in Eq. (10) without defining it for general subsets. This definition is the reading stated above. It is not the entropy expression, which is a separate theorem of the mission.
-- source:
--   Jakulin–Bratko, Quantifying and Visualizing Attribute Interactions, arXiv:cs/0308002v3, §2.3.2, p.7; §2.4, Eq. (10), p.8; §3.2, p.14

import Definitions.Def_JakulinBratko_I
import Definitions.Def_JakulinBratko_condLaw

namespace JakulinBratko

/-- The conditional interaction information `I(R | X)` of Eq. (10), p.8 (Jakulin–Bratko, Quantifying and Visualizing Attribute Interactions, arXiv:cs/0308002v3): the interaction
information of `R` under the conditional law given `X = x`, averaged over the values `x` of `X`
with weights `P(x)`.

**Formalization Note.** The paper never defines `I(R | X)` for general `R`. At `|R| = 2` it is
`I(A; B | C)` of Eq. (4), which p.7 calls "the expected" interaction over the values of `C`; p.14
calls such a quantity an "average". This definition is that average. It is deliberately not the
entropy expression, which is a theorem (`condI_eq_alternating_sum`). -/
noncomputable def condI {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*}
    [∀ i, Fintype (α i)] [∀ i, DecidableEq (α i)]
    (P : (∀ i, α i) → ℝ) (X : ι) (R : Finset ι) : ℝ :=
  ∑ x : α X, attrMarg P X x * I (condLaw P X x) R

end JakulinBratko


