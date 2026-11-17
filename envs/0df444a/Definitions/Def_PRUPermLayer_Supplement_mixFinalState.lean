-- Prove2me | Definitions.Def_PRUPermLayer_Supplement_mixFinalState
-- name    : PRUPermLayer_Supplement_mixFinalState
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T14:38:25.636825+00:00
-- url     : https://prove2.me/theorems/5a9894f6-391d-4c52-8f69-2cc096d56b24
-- title:
--   Final state $A_qO_q\cdots A_1O_1A_0|0\rangle$, $O_i\in\{U\otimes I,\,U^\dagger\otimes I\}$
-- statement:
--   For a mixed-access algorithm with directions $d_1,\dots,d_q$, unitaries $A_0,\dots,A_q$ and oracle $U$, the final state is
--   $$|A^{U,U^\dagger}\rangle=A_q\,O_q\,A_{q-1}\cdots A_1\,O_1\,A_0\,|0\rangle,\qquad O_i=\begin{cases}U\otimes I,& d_i=\text{forward},\\ U^\dagger\otimes I,& d_i=\text{inverse},\end{cases}$$
--   where $|0\rangle$ is the all-zeros basis state of the query register and the workspace.
--
--   **Formalization Note** $U^\dagger$ is the conjugate transpose, $O\otimes I$ acts on the query register (first tensor factor), and $|0\rangle$ is the label of $0^n$ together with the all-zeros workspace string, exactly as in the published forward final state.
-- source:
--   Shen–Zhong, Pseudorandom Unitaries from a Random Permutation and One Layer of Single-Qubit Gates, manuscript (STOC 2027 submission; held version sha256 395fcfa33ec861a7e9c10d88cfcefc2794b77ad1674c02661c9298c5ba565bcb), §2.2, p.9 (PDF p.11); Theorem 1.6, p.4 (PDF p.6)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_PRUPermLayer_Supplement_MixAlg

namespace PRUPermLayer.Supplement

/-- The final state `A_q O_q A_{q−1} ⋯ A₁ O₁ A₀ |0⟩` of a mixed-access algorithm with oracle `U`,
where `O_i = U ⊗ I` for a forward query and `O_i = U† ⊗ I` for an inverse query
(Shen–Zhong, *Pseudorandom Unitaries from a Random Permutation and One Layer of Single-Qubit Gates*, manuscript (STOC 2027 submission; held version sha256 395fcfa3…5bcb), §2.2, p.9 (PDF p.11) for the forward case; Theorem 1.6, p.4 (PDF p.6)).

**Formalization Note** `|0⟩` is the basis vector of the all-zeros query label
`bitsEquivFin n (fun _ => false)` and the all-`false` workspace string, as in the published
`PRUPermLayer.finalState`. `QAlgorithms.orderedProd` puts its factor `0` (here `A₁ O₁`) first in
time. `U†` is `U.conjTranspose`, and `O ⊗ I` is `Matrix.kroneckerMap (· * ·) O 1`, query register
first. -/
noncomputable def mixFinalState {n q : ℕ} (alg : MixAlg n q)
    (U : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) : Fin (2 ^ n) × QAlgorithms.Qubits alg.m → ℂ :=
  Matrix.mulVec
    (QAlgorithms.orderedProd (fun i : Fin q =>
        (alg.A i.succ : Matrix _ _ ℂ) *
          Matrix.kroneckerMap (· * ·) (if alg.d i then U else U.conjTranspose) 1) *
      (alg.A 0 : Matrix _ _ ℂ))
    (Pi.single ((QAlgorithms.bitsEquivFin n) fun _ => false, fun _ => false) 1)

end PRUPermLayer.Supplement


