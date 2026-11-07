-- Prove2me | Definitions.Def_PRUPermLayer_finalState
-- name    : PRUPermLayer_finalState
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:27:11.276619+00:00
-- url     : https://prove2.me/theorems/483cabed-c736-42ec-8f95-6ca079dca9f1
-- title:
--   Final state $|A^U\rangle = A_t U A_{t-1} \cdots A_1 U A_0|0\rangle$
-- statement:
--   For a $t$-query forward algorithm with unitaries $A_0, \dots, A_t$ and an oracle $U$ on the query register, the **final state** is
--   $$
--   |A^U\rangle = A_t\,(U\otimes I)\,A_{t-1} \cdots A_1\,(U \otimes I)\,A_0\,|0\rangle ,
--   $$
--   where $U \otimes I$ applies $U$ to the query register and the identity to the extra qubits, and $|0\rangle$ is the all-zeros basis state. The same $U$ answers all $t$ queries.
--
--   **Formalization Note** The query label of $|0\rangle$ is the all-zeros string $|0^n\rangle$.
-- source:
--   Shen–Zhong, Pseudorandom Unitaries from a Random Permutation and One Layer of Single-Qubit Gates, manuscript (STOC 2027 submission; held version sha256 395fcfa3…5bcb), §2.2, p.9 (PDF p.11)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_PRUPermLayer_FwdAlg

namespace PRUPermLayer

/-- The final state `|A^U⟩ = A_t (U ⊗ I) A_{t−1} ⋯ A₁ (U ⊗ I) A₀ |0⟩` of a `t`-query forward
algorithm with oracle `U` (Shen–Zhong, *Pseudorandom Unitaries from a Random Permutation and One Layer of Single-Qubit Gates*, manuscript (STOC 2027 submission; held version sha256 395fcfa3…5bcb), §2.2, p.9 (PDF p.11)). The same `U` answers all `t` queries, and it
acts on the query register only.

**Formalization Note** `|0⟩` is the basis vector of the all-zeros label: the query label
`bitsEquivFin n (fun _ => false)` (that is, `|0ⁿ⟩`) and the all-`false` workspace string. The
ordered product `QAlgorithms.orderedProd` puts its factor `0` (here `A₁ (U ⊗ I)`) first in time.
`U ⊗ I` is `Matrix.kroneckerMap (· * ·) U 1`, query register first. -/
noncomputable def finalState {n t : ℕ} (alg : FwdAlg n t) (U : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) :
    Fin (2 ^ n) × QAlgorithms.Qubits alg.m → ℂ :=
  Matrix.mulVec
    (QAlgorithms.orderedProd (fun i : Fin t =>
        (alg.A i.succ : Matrix _ _ ℂ) * Matrix.kroneckerMap (· * ·) U 1) *
      (alg.A 0 : Matrix _ _ ℂ))
    (Pi.single ((QAlgorithms.bitsEquivFin n) fun _ => false, fun _ => false) 1)

end PRUPermLayer


