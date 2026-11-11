-- Prove2me | Definitions.Def_CatalystQLB_Query_OracleCircuit_segmentOp
-- name    : CatalystQLB_Query_OracleCircuit_segmentOp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T20:21:49.96467+00:00
-- url     : https://prove2.me/theorems/c90ab521-5ac8-4cef-90aa-b36250d9b4a3
-- title:
--   Segments $V_i$ of $U=V_qO_fV_{q-1}O_f\cdots V_2O_fV_1$
-- statement:
--   Let an oracle circuit make $q-1$ queries to $O_f$. Splitting its gate sequence at these queries writes its unitary as
--   $$U=V_q\,O_f\,V_{q-1}\,O_f\cdots V_2\,O_f\,V_1,$$
--   where each **segment** $V_i$ ($1\le i\le q$) is the product of the unitary gates and $O_g$ queries between the $(i-1)$-th and the $i$-th query to $O_f$. The segments contain no query to $f$.
--
--   **Formalization Note** 1-indexed as in the paper; an index outside $1,\dots,q$ gives the identity. `segments` splits the gate list; a segment may be empty.
-- source:
--   Arora, Chakraborty, Cojocaru, Saminathan, Singh, Computational Work Extraction: The Complexity of Catalysts, arXiv:2609.40323 (version of 2026-11-03, sha256 44854b3a…), §5.3, p.45 (PDF 48); Notation 74, p.44 (PDF 47)

import Mathlib
import Definitions.Def_CatalystQLB_Query_OracleCircuit

namespace CatalystQLB.Query

open QAlgorithms

namespace OracleCircuit

variable {n ℓ : ℕ}

/-- Split a list of steps at its `O_f` queries: `[V₁-steps, O_f, V₂-steps, …, O_f, V_q-steps]`
gives `[V₁-steps, …, V_q-steps]` (each segment in application order, possibly empty). The
result has one more segment than there are `O_f` queries. -/
def segments : List (Step n ℓ) → List (List (Step n ℓ))
  | [] => [[]]
  | s :: rest =>
    if s.isF then [] :: segments rest
    else match segments rest with
      | [] => [[s]]
      | h :: t => (s :: h) :: t

/-- The segment operator `V_i` (`1 ≤ i ≤ q`, `q − 1 = numF C`) of the factorization
`U = V_q O_f V_{q−1} O_f ⋯ V_2 O_f V_1` (Arora, Chakraborty, Cojocaru, Saminathan, Singh, *Computational Work Extraction: The Complexity of Catalysts*, arXiv:2609.40323 (version of 2026-11-03), §5.3, p.45 (PDF 48), before Eq. (43); Notation 74,
p.44 (PDF 47)): the product of the unitary steps and `O_g` queries between the `(i−1)`-th and
the `i`-th query to `O_f`.

**Formalization Note** 1-indexed as in the paper; an index `i > q` gives the identity, and `i = 0` gives `V_1` (`0 - 1 = 0` in `ℕ`); no statement uses either junk value.
`V_i` contains no `O_f` query, so it does not depend on `f` (the argument `f` is only passed
to `Step.mat`). -/
noncomputable def segmentOp (C : OracleCircuit n ℓ) (f g : Qubits n → Qubits n) (i : ℕ) :
    Matrix (Idx n ℓ) (Idx n ℓ) ℂ :=
  evalList f g ((segments C.steps).getD (i - 1) [])

end OracleCircuit

end CatalystQLB.Query


