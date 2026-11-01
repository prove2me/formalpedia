-- Prove2me | Definitions.Def_JakulinBratko_IsLaw
-- name    : JakulinBratko_IsLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T16:00:43.073973+00:00
-- url     : https://prove2.me/theorems/a0ccbc6d-03f1-427a-a2bb-dda71c6f7ec1
-- title:
--   Joint probability distribution on a finite product of alphabets
-- statement:
--   Let $\mathcal A=\{X_1,\dots,X_n\}$ be a finite set of attributes, each with a finite alphabet $\Re_X$, and let $\Re_{\mathcal A}=\Re_{X_1}\times\dots\times\Re_{X_n}$. A joint probability distribution is a function $P:\Re_{\mathcal A}\to\mathbb R$ with
--
--   $$
--   P(\mathbf a)\ge 0\quad\text{for all }\mathbf a,\qquad \sum_{\mathbf a\in\Re_{\mathcal A}}P(\mathbf a)=1.
--   $$
--
--   Every quantity of the mission is computed from such a law.
--
--   **Formalization Note** The law is a real-valued weight function rather than a Mathlib `PMF`. Zero masses are allowed. The index type may be empty and the alphabets may differ between attributes.
-- source:
--   Jakulin–Bratko, Quantifying and Visualizing Attribute Interactions, arXiv:cs/0308002v3, §2.1, p.3; §2.4, pp.7–8

import Mathlib

namespace JakulinBratko

/-- A joint probability distribution `P(𝐚)` on the Cartesian product `ℜ_𝐀 = ℜ_{X₁} × ⋯ × ℜ_{X_n}` of
finite alphabets (§2.1, p.3; §2.4, pp.7–8, Jakulin–Bratko, Quantifying and Visualizing Attribute Interactions, arXiv:cs/0308002v3).

**Formalization Note.** The law is a real-valued weight function, nonnegative with total mass `1`.
Zero masses are allowed. The index type `ι` of the attributes may be empty, and the alphabets
may differ from attribute to attribute. -/
def IsLaw {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*} [∀ i, Fintype (α i)]
    (P : (∀ i, α i) → ℝ) : Prop :=
  (∀ a, 0 ≤ P a) ∧ ∑ a, P a = 1

end JakulinBratko


