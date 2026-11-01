-- Prove2me | Definitions.Def_JakulinBratko_condEntSum
-- name    : JakulinBratko_condEntSum
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T16:01:28.077954+00:00
-- url     : https://prove2.me/theorems/0a8ddc59-b028-4a42-a0f8-e92ffb5e90ad
-- title:
--   Eq. (2), first form — conditional entropy as a sum
-- statement:
--   For groups $R,Y$ of attributes, with $z$ ranging over the assignments of $R\cup Y$,
--
--   $$
--   H(R\mid Y)=-\sum_{z}P(z)\log_2\frac{P(z)}{P(z|_Y)}.
--   $$
--
--   For single attributes this is the sum $-\sum_{a,b}P(a,b)\log_2P(a\mid b)$ of Eq. (2).
--
--   **Formalization Note** $P(a\mid b)$ is written as the quotient $P(a,b)/P(b)$. Groups are needed for the paper's own use of $H(A\mid B,C)$ and $H(AB\mid C)$ in Eq. (4).
-- source:
--   Jakulin–Bratko, Quantifying and Visualizing Attribute Interactions, arXiv:cs/0308002v3, §2.2, Eq. (2), p.4

import Definitions.Def_JakulinBratko_marg

namespace JakulinBratko

/-- The sum form of the conditional entropy `H(R | Y)`, the first form of Eq. (2), p.4
(Jakulin–Bratko, Quantifying and Visualizing Attribute Interactions, arXiv:cs/0308002v3): `-∑_z P(z) log₂ (P(z) / P(z|_Y))`, the sum over assignments `z` of `R ∪ Y`.

**Formalization Note.** `P(a | b)` is written as the quotient `P(a, b) / P(b)`. The paper's single
attributes `A, B` are generalized to groups `R, Y` of attributes, which Eq. (5) needs. -/
noncomputable def condEntSum {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*}
    [∀ i, Fintype (α i)] [∀ i, DecidableEq (α i)]
    (P : (∀ i, α i) → ℝ) (R Y : Finset ι) : ℝ :=
  -∑ z : (∀ i : ↥(R ∪ Y), α i),
    marg P (R ∪ Y) z *
      Real.logb 2 (marg P (R ∪ Y) z / marg P Y (Finset.restrict₂ Finset.subset_union_right z))

end JakulinBratko


