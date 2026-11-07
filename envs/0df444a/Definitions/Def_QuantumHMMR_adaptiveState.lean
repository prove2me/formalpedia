-- Prove2me | Definitions.Def_QuantumHMMR_adaptiveState
-- name    : QuantumHMMR_adaptiveState
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:35:49.2842+00:00
-- url     : https://prove2.me/theorems/1429304a-e252-4126-837b-955aa605df5d
-- title:
--   Final state $|A^U_t\rangle$ of an adaptive algorithm, Eq. (5)
-- statement:
--   The state of a $t$-query oracle algorithm on input $|0^{n+m}\rangle$ is
--   $$
--   |A^U_t\rangle = A_t \cdot (U \otimes I_B) \cdot A_{t-1} \cdots A_1 \cdot (U \otimes I_B) \cdot A_0\, |0^{n+m}\rangle. \tag{5}
--   $$
--
--   **Formalization Note** $U \otimes I_B$ is the published `embedOp` of $U$ on the first $n$ wires; the product of the $t$ blocks $(U \otimes I_B) A_k$ is the published `orderedProd`, block $0$ acting first. For $t = 0$ the state is $A_0|0^{n+m}\rangle$.
-- source:
--   Dujmovic–Haferkamp–Poremba, On the pseudorandomness of simple quantum processes, arXiv:2610.02100 (held version sha256 9920ec45…), Section 3, Eq. (5), p.10

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P45
import Definitions.Def_QuantumHMMR_AdaptiveAlg

open QAlgorithms QAlgorithms.Papers.Independent.Extend50.P45

namespace QuantumHMMR

/-- The state of a `t`-query oracle algorithm on input `|0^{n+m}⟩`, Eq. (5) (Dujmovic–Haferkamp–Poremba, *On the pseudorandomness of simple quantum processes*, arXiv:2610.02100 (held version, sha256 9920ec45…4f20), p.10):
`|A^U_t⟩ = A_t · U · A_{t-1} ⋯ A_1 · U · A_0 |0^{n+m}⟩`, where each oracle call applies `U` to the
`n`-qubit register `A` and the identity to the ancillas `B`.

**Formalization Note** `U ⊗ I_B` is the published `embedOp U` along the first `n` wires
(`Fin.castAddEmb`). The product `(U A_{t-1}) ⋯ (U A_0)` is the published `orderedProd`, whose factor
`0` acts first; for `t = 0` the state is `A_0 |0^{n+m}⟩`. -/
noncomputable def adaptiveState {n t : ℕ} (alg : AdaptiveAlg n t) (U : QMat n) :
    EuclideanSpace ℂ (Qubits (n + alg.anc)) :=
  act ((alg.A (Fin.last t) : Matrix (Qubits (n + alg.anc)) (Qubits (n + alg.anc)) ℂ) *
      orderedProd (fun k : Fin t => embedOp U (Fin.castAddEmb alg.anc) *
        (alg.A k.castSucc : Matrix (Qubits (n + alg.anc)) (Qubits (n + alg.anc)) ℂ)))
    (zeroKet (n + alg.anc))

end QuantumHMMR


