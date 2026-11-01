-- Prove2me | Definitions.Def_JakulinBratko_condLaw
-- name    : JakulinBratko_condLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T16:01:27.627224+00:00
-- url     : https://prove2.me/theorems/65031d60-ea4f-4db7-bc05-07e4421d4902
-- title:
--   Conditional distribution given the value of one attribute
-- statement:
--   For an attribute $X$ and a value $x$, the conditional distribution of the attributes given $X=x$ is
--
--   $$
--   P(\mathbf a\mid x)=\begin{cases}P(\mathbf a)/P(x)&a_X=x,\\ 0&a_X\ne x.\end{cases}
--   $$
--
--   **Formalization Note** When $P(x)=0$ Lean's division makes this the zero function. Such an $x$ has weight $0$ in the only place the object is used, the conditional interaction information.
-- source:
--   Jakulin–Bratko, Quantifying and Visualizing Attribute Interactions, arXiv:cs/0308002v3, §2.2, p.4

import Definitions.Def_JakulinBratko_attrMarg

namespace JakulinBratko

/-- The conditional distribution given `X = x` (§2.2, p.4, Jakulin–Bratko, Quantifying and Visualizing Attribute Interactions, arXiv:cs/0308002v3):
`P(𝐚 | x) = P(𝐚) / P(x)` when `a_X = x`, and `0` otherwise.

**Formalization Note.** If `P(x) = 0`, Lean's division makes this the zero function. That value
of `x` has weight `0` in `condI`, the only place this object is used. -/
noncomputable def condLaw {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*}
    [∀ i, Fintype (α i)] [∀ i, DecidableEq (α i)]
    (P : (∀ i, α i) → ℝ) (X : ι) (x : α X) (a : ∀ i, α i) : ℝ :=
  if a X = x then P a / attrMarg P X x else 0

end JakulinBratko


