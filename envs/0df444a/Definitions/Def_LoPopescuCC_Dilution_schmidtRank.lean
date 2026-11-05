-- Prove2me | Definitions.Def_LoPopescuCC_Dilution_schmidtRank
-- name    : LoPopescuCC_Dilution_schmidtRank
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:41:48.974878+00:00
-- url     : https://prove2.me/theorems/3b982c6f-6e38-4670-a660-399cfea8c6e3
-- title:
--   Number of terms of the Schmidt decomposition
-- statement:
--   The Schmidt rank of a bipartite vector $v$ is the number of nonzero Schmidt coefficients of $v$, that is, the rank of its coefficient matrix. It is the number of terms in the Schmidt decomposition of $v$, and it is defined for unnormalized vectors too, as needed for the residual state $\Delta$ of Eq. (9).
-- source:
--   Lo, Popescu, The classical communication cost of entanglement manipulation, arXiv:quant-ph/9902045v2, Theorem, pp. 4-5, and proof of the Lemma, p. 4

import Mathlib
import Definitions.Def_LoPopescuCC_Dilution_coeffMatrix

namespace LoPopescuCC.Dilution

/-- **Number of terms of the Schmidt decomposition** (Lo, Popescu, arXiv:quant-ph/9902045v2,
Theorem, pp. 4–5: "whose Schmidt decomposition contains 2^{O(√N)} terms"; proof of the Lemma, p. 4):
the number of nonzero Schmidt coefficients of `v`, which is the rank of its coefficient matrix.

**Formalization Note** It applies to unnormalized vectors, since the paper's `Δ` is "un-normalized". -/
noncomputable def schmidtRank {a b : Type} [Fintype b] (v : EuclideanSpace ℂ (a × b)) : ℕ :=
  (coeffMatrix v).rank

end LoPopescuCC.Dilution


