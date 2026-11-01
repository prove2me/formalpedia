-- Prove2me | Definitions.Def_JakulinBratko_H
-- name    : JakulinBratko_H
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T16:01:36.530847+00:00
-- url     : https://prove2.me/theorems/40fee6fb-1e02-40ae-baa9-6b6d8642b406
-- title:
--   Eqs. (1), (9) — entropy of a subset of attributes, in bits
-- statement:
--   The entropy of a subset $\mathcal S$ of the attributes is
--
--   $$
--   H(\mathcal S)=-\sum_{\mathbf v}P(\mathbf v)\log_2 P(\mathbf v),
--   $$
--
--   the sum over the assignments $\mathbf v$ of the attributes in $\mathcal S$, with $P(\mathbf v)$ the marginal of Eq. (8) and the convention $0\log_2 0=0$. All of the mission's quantities are measured in bits.
--
--   **Formalization Note** `Real.logb 2 0 = 0` gives the convention $0\log_2 0=0$.
-- source:
--   Jakulin–Bratko, Quantifying and Visualizing Attribute Interactions, arXiv:cs/0308002v3, §2.1, Eq. (1), p.3; §2.2, p.4; §2.4, Eq. (9), p.8

import Definitions.Def_JakulinBratko_marg

namespace JakulinBratko

/-- The entropy `H(S)` of a subset of attributes, Eq. (9), p.8, in the form of Eq. (1), p.3
(Jakulin–Bratko, Quantifying and Visualizing Attribute Interactions, arXiv:cs/0308002v3), measured in bits:
`H(S) = -∑_𝐯 P(𝐯) log₂ P(𝐯)`, the sum over the assignments `𝐯` of the attributes in `S`.

**Formalization Note.** `Real.logb 2 0 = 0` gives the paper's convention `0 log₂ 0 = 0` (p.4). -/
noncomputable def H {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*}
    [∀ i, Fintype (α i)] [∀ i, DecidableEq (α i)]
    (P : (∀ i, α i) → ℝ) (S : Finset ι) : ℝ :=
  -∑ s : (∀ i : S, α i), marg P S s * Real.logb 2 (marg P S s)

end JakulinBratko


