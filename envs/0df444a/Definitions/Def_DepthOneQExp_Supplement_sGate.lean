-- Prove2me | Definitions.Def_DepthOneQExp_Supplement_sGate
-- name    : DepthOneQExp_Supplement_sGate
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T21:33:36.263999+00:00
-- url     : https://prove2.me/theorems/75927831-7bc7-4fbb-9385-1a783297df22
-- title:
--   The phase gate $S = \mathrm{diag}(1, i)$
-- statement:
--   The phase gate
--   $$
--   S = \begin{pmatrix} 1 & 0 \\ 0 & i\end{pmatrix},
--   $$
--   as a gate of arity 1. Its powers are $\langle S\rangle = \{I, S, Z, S^\dagger\}$ (p.15). Together with $H$ and CNOT it generates the Clifford group of Eq. (2.55).
--
--   **Formalization Note** A `MITMSynthesis.Gate` of arity 1; unitarity is proved in the module.
-- source:
--   Anshu–Balasubramanian–Haferkamp–Harrow–Tan, Depth-1 expanders on the unitary group and applications, arXiv:2609.01605 (held version, sha256 3c3f8513…aebfd87), §2.4, Eq. (2.55), p.15

import Mathlib
import Definitions.Def_MITMSynthesis_Gate

namespace DepthOneQExp.Supplement

/-- The phase gate `S = diag(1, i)` as a gate of arity 1
(Anshu–Balasubramanian–Haferkamp–Harrow–Tan, *Depth-1 expanders on the unitary group and
applications*, arXiv:2609.01605, held version sha256 3c3f8513…aebfd87, §2.4, Eq. (2.55), p.15: `S_j` is the phase gate on qubit `j`; `⟨S⟩ = {I, S, Z, S†}`, p.15).

**Formalization Note** The basis state `|0⟩` is `fun _ => 0 : Fin 1 → Fin 2`. -/
noncomputable def sGate : MITMSynthesis.Gate :=
  ⟨1, one_pos,
    ⟨Matrix.diagonal fun x : MITMSynthesis.Q 1 => if x 0 = 0 then 1 else Complex.I, by
      rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
        Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext x
      by_cases h : x 0 = 0 <;> simp [h]⟩⟩

end DepthOneQExp.Supplement


