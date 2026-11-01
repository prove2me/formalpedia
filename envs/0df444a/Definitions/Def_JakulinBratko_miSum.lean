-- Prove2me | Definitions.Def_JakulinBratko_miSum
-- name    : JakulinBratko_miSum
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T16:01:47.93398+00:00
-- url     : https://prove2.me/theorems/bd6c77b3-d2e0-40b0-9bf3-5540a8505cb5
-- title:
--   Eq. (3), first form — mutual information as a sum
-- statement:
--   For groups $R,Y$ of attributes, with $z$ ranging over the assignments of $R\cup Y$,
--
--   $$
--   I(R;Y)=\sum_{z}P(z)\log_2\frac{P(z)}{P(z|_R)\,P(z|_Y)}.
--   $$
--
--   For single attributes this is the sum of Eq. (3).
--
--   **Formalization Note** Groups are needed for the paper's own use of $I(A,B;C)$ in Eq. (5).
-- source:
--   Jakulin–Bratko, Quantifying and Visualizing Attribute Interactions, arXiv:cs/0308002v3, §2.2, Eq. (3), p.4

import Definitions.Def_JakulinBratko_marg

namespace JakulinBratko

/-- The sum form of the mutual information `I(R; Y)`, the first form of Eq. (3), p.4
(Jakulin–Bratko, Quantifying and Visualizing Attribute Interactions, arXiv:cs/0308002v3): `∑_z P(z) log₂ (P(z) / (P(z|_R) P(z|_Y)))`, the sum over assignments `z` of `R ∪ Y`.

**Formalization Note.** The paper's single attributes `A, B` are generalized to groups `R, Y` of
attributes, which Eq. (5) needs (`I(A, B; C)`). -/
noncomputable def miSum {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*}
    [∀ i, Fintype (α i)] [∀ i, DecidableEq (α i)]
    (P : (∀ i, α i) → ℝ) (R Y : Finset ι) : ℝ :=
  ∑ z : (∀ i : ↥(R ∪ Y), α i),
    marg P (R ∪ Y) z *
      Real.logb 2 (marg P (R ∪ Y) z /
        (marg P R (Finset.restrict₂ Finset.subset_union_left z) *
          marg P Y (Finset.restrict₂ Finset.subset_union_right z)))

end JakulinBratko


