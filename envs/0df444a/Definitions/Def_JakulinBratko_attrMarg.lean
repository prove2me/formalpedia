-- Prove2me | Definitions.Def_JakulinBratko_attrMarg
-- name    : JakulinBratko_attrMarg
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T16:00:45.917344+00:00
-- url     : https://prove2.me/theorems/92eb4797-3996-4a1d-a8c9-a5075d34ebaf
-- title:
--   Marginal distribution of a single attribute
-- statement:
--   For an attribute $X$ and a value $x\in\Re_X$,
--
--   $$
--   P(x)=\sum_{\mathbf a:\ a_X=x}P(\mathbf a).
--   $$
--
--   This is Eq. (8) for the one-attribute subset $\{X\}$.
--
--   **Formalization Note** Eq. (8) for $\{X\}$ is indexed by functions on a one-point subtype. This definition reads the same number on the alphabet of $X$ itself, which is what the product $\prod_{X\in\mathcal S}P(s_X)$ needs.
-- source:
--   Jakulin–Bratko, Quantifying and Visualizing Attribute Interactions, arXiv:cs/0308002v3, §2.1, p.3; §2.4, Eq. (8), p.8

import Mathlib

namespace JakulinBratko

/-- The marginal distribution `P(x)` of the single attribute `X`, §2.1, p.3, and Eq. (8), p.8
(Jakulin–Bratko, Quantifying and Visualizing Attribute Interactions, arXiv:cs/0308002v3): the sum of `P(𝐚)` over all full assignments with `a_X = x`.

**Formalization Note.** This is `marg P {X}` read on the alphabet `α X` itself rather than on
functions on the one-point subtype `↥{X}`. -/
def attrMarg {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*}
    [∀ i, Fintype (α i)] [∀ i, DecidableEq (α i)]
    (P : (∀ i, α i) → ℝ) (X : ι) (x : α X) : ℝ :=
  ∑ a with a X = x, P a

end JakulinBratko


