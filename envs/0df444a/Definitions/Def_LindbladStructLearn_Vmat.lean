-- Prove2me | Definitions.Def_LindbladStructLearn_Vmat
-- name    : LindbladStructLearn_Vmat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:57:03.715604+00:00
-- url     : https://prove2.me/theorems/0b93b4da-665b-416d-bacf-c0b30b8f859c
-- title:
--   The matrix $V_k$
-- statement:
--   $V_k$ is the $m\times m$ matrix acting as follows. For $P_1, P_2 \ne I$,
--
--   $$(V_k y)_{\overline P} = \sum_{\overline Q\succeq\overline P} (-1)^{s_{\overline Q}-s_{\overline P}}\, y_{\overline Q};$$
--
--   for $\overline P = (P, I)$,
--
--   $$(V_k y)_{P,I} = 2y_{P,I} + \sum_{\substack{Q:\,S_Q\subseteq S_P\\ Q\ne I,P}} \overline{c(PQ)}\, y_{Q,\mathcal P(PQ)} + \sum_{\substack{\overline Q\succeq(P,I)\\ \overline Q\ne(P,I)}} (-1)^{s_{\overline Q}-s_P} y_{\overline Q} - \sum_{\substack{\overline Q\succeq(I,P)\\ \overline Q\ne(I,P)}} (-1)^{s_{\overline Q}-s_P} y_{\overline Q}.$$
--
--   All sums run over the $k$-local pairs with $Q_1 \ne I$. Corollary 3.7 shows $V_k = A_k^{-1}$.
--
--   **Formalization Note** The conjugate $\overline{c(PQ)}$ is as printed on the rendered page (the text layer drops the bar).
-- source:
--   Lewis–Tang–Wright, Learning the structure of open quantum systems, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), Notation 3.3, Eqs. (3.16)–(3.17), p.20

import Mathlib
import Definitions.Def_LindbladStructLearn_Idx
import Definitions.Def_LindbladStructLearn_confuses
import Definitions.Def_LindbladStructLearn_pauliProd
import Definitions.Def_LindbladStructLearn_pauliPhase

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal
noncomputable section

namespace LindbladStructLearn

open LindbladTolerant.Testing

/-- The matrix `V_k` (Lewis–Tang–Wright, *Learning the structure of open quantum systems*, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), Notation 3.3, Eqs. (3.16)–(3.17), p.20). For `P₁, P₂ ≠ I`,
`(V_k y)_P̄ = Σ_(Q̄ ⪰ P̄) (−1)^(s_Q̄ − s_P̄) y_Q̄`; for `P̄ = (P, I)`,
`(V_k y)_(P,I) = 2 y_(P,I) + Σ_(Q : S_Q ⊆ S_P, Q ≠ I, P) c̄(PQ) y_(Q,𝒫(PQ))
 + Σ_(Q̄ ⪰ (P,I), Q̄ ≠ (P,I)) (−1)^(s_Q̄ − s_P) y_Q̄ − Σ_(Q̄ ⪰ (I,P), Q̄ ≠ (I,P)) (−1)^(s_Q̄ − s_P) y_Q̄`.

**Formalization Note** The conjugate `c̄(PQ)` in the second sum is as printed on the rendered page
(the text layer drops the bar); `c̄(PQ) = c(QP)`, cf. Eq. (3.10).
Every sum runs over the index set (the `k`-local pairs with `Q₁ ≠ I`). When `Q̄ ⪰ P̄` the support of
`Q̄` contains that of `P̄`, so the natural-number difference `s_Q̄ − s_P̄` is the true one;
`s_(I,P) = s_(P,I) = |supp P|`. -/
def Vmat (n k : ℕ) : Matrix (Idx n k) (Idx n k) ℂ := fun a b =>
  let P := a.1
  let Q := b.1
  let sgn : ℂ := (-1) ^ ((pairSupport Q).card - (pairSupport P).card)
  by classical exact
  if P.2 ≠ 0 then (if confuses Q P then sgn else 0)
  else
    (if Q = P then 2 else 0) +
      (if support Q.1 ⊆ support P.1 ∧ Q.1 ≠ 0 ∧ Q.1 ≠ P.1 ∧ Q.2 = pauliProd P.1 Q.1
        then star (pauliPhase P.1 Q.1) else 0) +
      (if confuses Q P ∧ Q ≠ P then sgn else 0) -
      (if confuses Q (0, P.1) ∧ Q ≠ (0, P.1) then sgn else 0)

end LindbladStructLearn


