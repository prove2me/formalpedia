-- Prove2me | Definitions.Def_CatalystQLB_Query_OracleCircuit_branchA
-- name    : CatalystQLB_Query_OracleCircuit_branchA
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T20:23:00.917592+00:00
-- url     : https://prove2.me/theorems/539268cb-c86c-4644-8273-0d76a583fc65
-- title:
--   Continuation operators $A_i$ of Notation 74
-- statement:
--   With the segments $V_i$ of a circuit making $q-1$ queries to $O_f$, define
--   $$A_{q-1}=V_q\,O_f,\qquad A_i=A_{i+1}\,V_{i+1}\,O_f\quad(1\le i<q-1),$$
--   that is $A_i=(V_qO_f)(V_{q-1}O_f)\cdots(V_{i+1}O_f)$: the rest of the circuit from its $i$-th query to $O_f$ on. Each $A_i$ is unitary.
--
--   **Formalization Note** 1-indexed, $1\le i\le q-1$; written as the ordered product over $j=q,\dots,i+1$.
-- source:
--   Arora, Chakraborty, Cojocaru, Saminathan, Singh, Computational Work Extraction: The Complexity of Catalysts, arXiv:2609.40323 (version of 2026-11-03, sha256 44854b3a…), §5.3, p.45 (PDF 48), after Eq. (43)

import Mathlib
import Definitions.Def_CatalystQLB_Query_OracleCircuit_segmentOp

namespace CatalystQLB.Query

open QAlgorithms

namespace OracleCircuit

variable {n ℓ : ℕ}

/-- The continuation operators `A_i` of Notation 74 (Arora, Chakraborty, Cojocaru, Saminathan, Singh, *Computational Work Extraction: The Complexity of Catalysts*, arXiv:2609.40323 (version of 2026-11-03), §5.3, p.45 (PDF 48), after Eq. (43):
"`A_{q−1} := V_q O_f` and `A_i := A_{i+1} V_{i+1} O_f` for `1 ≤ i < q − 1`"), i.e.
`A_i = (V_q O_f)(V_{q−1} O_f) ⋯ (V_{i+1} O_f)`, the rest of the circuit from the `i`-th query to
`O_f` on.

**Formalization Note** 1-indexed (`1 ≤ i ≤ q − 1 = numF C`), written as the ordered product over
`j = q, q − 1, …, i + 1` of `V_j O_f`. -/
noncomputable def branchA (C : OracleCircuit n ℓ) (f g : Qubits n → Qubits n) (i : ℕ) :
    Matrix (Idx n ℓ) (Idx n ℓ) ℂ :=
  ((List.range' (i + 1) (C.numF + 1 - i)).map
    (fun j => C.segmentOp f g j * Step.mat f g .queryF)).reverse.prod

end OracleCircuit

end CatalystQLB.Query


