-- Prove2me | Definitions.Def_JakulinBratko_cmiSum
-- name    : JakulinBratko_cmiSum
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T16:01:32.936988+00:00
-- url     : https://prove2.me/theorems/e62e52fd-adb7-468c-bb4c-0186fdb1f761
-- title:
--   Eq. (4), first form — conditional mutual information as a sum
-- statement:
--   For groups $R,Y,Z$ of attributes, with $z$ ranging over the assignments of $R\cup Y\cup Z$,
--
--   $$
--   I(R;Y\mid Z)=\sum_{z}P(z)\log_2\frac{P(z)\,P(z|_Z)}{P(z|_{R\cup Z})\,P(z|_{Y\cup Z})}.
--   $$
--
--   For single attributes this is the sum of Eq. (4).
--
--   **Formalization Note** The printed quotient $P(a,b\mid c)/(P(a\mid c)P(b\mid c))$ is written with the conditional probabilities cleared. It is the same number wherever $P(a,b,c)>0$, and every other term has weight $0$.
-- source:
--   Jakulin–Bratko, Quantifying and Visualizing Attribute Interactions, arXiv:cs/0308002v3, §2.3, Eq. (4), p.4

import Definitions.Def_JakulinBratko_marg

namespace JakulinBratko

/-- The sum form of the conditional mutual information `I(R; Y | Z)`, the first form of Eq. (4), p.4
(Jakulin–Bratko, Quantifying and Visualizing Attribute Interactions, arXiv:cs/0308002v3): `∑_z P(z) log₂ (P(z) P(z|_Z) / (P(z|_(R ∪ Z)) P(z|_(Y ∪ Z))))`, the sum over assignments `z`
of `R ∪ Y ∪ Z`.

**Formalization Note.** The printed quotient `P(a, b | c) / (P(a | c) P(b | c))` is written with the
conditional probabilities cleared, which is the same number wherever `P(a, b, c) > 0`; every other
term has weight `0`. The paper's single attributes are generalized to groups. -/
noncomputable def cmiSum {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*}
    [∀ i, Fintype (α i)] [∀ i, DecidableEq (α i)]
    (P : (∀ i, α i) → ℝ) (R Y Z : Finset ι) : ℝ :=
  ∑ z : (∀ i : ↥(R ∪ Y ∪ Z), α i),
    marg P (R ∪ Y ∪ Z) z *
      Real.logb 2 (marg P (R ∪ Y ∪ Z) z *
          marg P Z (Finset.restrict₂ Finset.subset_union_right z) /
        (marg P (R ∪ Z) (Finset.restrict₂
            (Finset.union_subset_union_left Finset.subset_union_left) z) *
          marg P (Y ∪ Z) (Finset.restrict₂
            (Finset.union_subset_union_left Finset.subset_union_right) z)))

end JakulinBratko


