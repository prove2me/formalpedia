-- Prove2me | Definitions.Def_JakulinBratko_I
-- name    : JakulinBratko_I
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T16:02:32.216996+00:00
-- url     : https://prove2.me/theorems/29f2f6c5-cf1b-428e-9ef4-a2724344a8af
-- title:
--   Eq. (10), first form — $k$-way interaction information
-- statement:
--   The $k$-way interaction information of a subset $\mathcal S$ of the attributes is
--
--   $$
--   I(\mathcal S)=-\sum_{\mathcal T\subseteq\mathcal S}(-1)^{|\mathcal S|-|\mathcal T|}H(\mathcal T).
--   $$
--
--   With this sign (McGill's), $I(\{A,B\})=H(A)+H(B)-H(A,B)$ is the mutual information, the exclusive or has $I=1$ bit, and a triplicated bit has $I=-1$.
--
--   **Formalization Note** The quantity is defined for every subset, including the empty set and singletons, where $I(\{X\})=-H(X)$.
-- source:
--   Jakulin–Bratko, Quantifying and Visualizing Attribute Interactions, arXiv:cs/0308002v3, §2.4, Eq. (10), p.8

import Definitions.Def_JakulinBratko_H

namespace JakulinBratko

/-- The `k`-way interaction information `I(S)`, the first form of Eq. (10), p.8
(Jakulin–Bratko, Quantifying and Visualizing Attribute Interactions, arXiv:cs/0308002v3): `I(S) = -∑_{T ⊆ S} (-1)^(|S|-|T|) H(T)`.

**Formalization Note.** This is McGill's sign convention, so that `I({A, B}) = H(A) + H(B) - H(A, B)`.
It is defined for every `S`, including `I(∅)` and singletons. The exponent is in `ℕ`, and the
subtraction `|S| - |T|` is exact because `T ⊆ S`. -/
noncomputable def I {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*}
    [∀ i, Fintype (α i)] [∀ i, DecidableEq (α i)]
    (P : (∀ i, α i) → ℝ) (S : Finset ι) : ℝ :=
  -∑ T ∈ S.powerset, (-1 : ℝ) ^ (S.card - T.card) * H P T

end JakulinBratko


