-- Prove2me | Definitions.Def_DepthOptQC_Synth_Supplement_pauliTransfer
-- name    : DepthOptQC_Synth_Supplement_pauliTransfer
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T00:45:33.177824+00:00
-- url     : https://prove2.me/theorems/cdf2285d-0bf4-4ce8-ac0c-08594f835b5a
-- title:
--   Local Pauli labels and the Pauli-transfer operator $O_U$
-- statement:
--   For $r$ qubits, a pair of bits $(a_j,b_j)$ labels $I,Z,X,Y$ by $00,01,10,11$. The corresponding Pauli string is denoted $P(a,b)$. For an $r$-qubit unitary $U$, its **Pauli-transfer operator** is the matrix on $2r$ label qubits
--   $$
--   [O_U]_{P,Q}=2^{-r}\operatorname{Tr}(PUQU^\dagger).
--   $$
--
--   `generalizedToffoliTransfer r` specializes this operator to the $r$-qubit generalized Toffoli with $r-1$ controls; at $r=1$ the physical gate is $X$.
--
--   This is the local real encoding used by Theorems 12–14. It retains the parallel supports of the original circuit while representing conjugation by a physical gate as an operator on its Pauli labels.
--
--   **Formalization Note** The first $r$ label wires hold all $a$ bits and the next $r$ hold all $b$ bits, a fixed permutation of the paper's adjacent $(a_j,b_j)$ ordering.
-- source:
--   Vasconcelos, Depth-Optimal Quantum Compilation, arXiv:2609.34659, §8.1, pp.49–50 (PDF pp.51–52), Eqs. (233)–(239)

import Definitions.Def_DepthOptQC_Synth_Supplement_CircuitModel

set_option autoImplicit false

noncomputable section

namespace DepthOptQC.Synth.Supplement

open QAlgorithms DepthOptQC.Synth
open scoped BigOperators Matrix ComplexConjugate

/-- The Pauli operator labelled by `2r` bits, with the first `r` bits the X labels and the last
`r` bits the Z labels. Thus `00,01,10,11` label `I,Z,X,Y` on each qubit (Eq. (233), p.49). -/
def pauliLabelMatrix (r : ℕ) (p : Qubits (r + r)) : Matrix (Qubits r) (Qubits r) ℂ :=
  let a := (qubitsAppendEquiv r r p).1
  let b := (qubitsAppendEquiv r r p).2
  let overlap := (Finset.univ.filter fun i : Fin r => a i && b i).card
  Matrix.of fun y x =>
    if y = fun i => xor (x i) (a i) then
      Complex.I ^ overlap * if dotBits b x then -1 else 1
    else 0

/-- The Pauli-transfer operator `[O_U]_{P,Q}=2^{-r} Tr(P U Q U†)` of Eq. (238), acting on the
`2r` Pauli-label qubits. -/
def pauliTransfer (r : ℕ) (U : Matrix (Qubits r) (Qubits r) ℂ) :
    Matrix (Qubits (r + r)) (Qubits (r + r)) ℂ :=
  fun P Q => ((2 : ℂ) ^ r)⁻¹ * (pauliLabelMatrix r P * U * pauliLabelMatrix r Q * Uᴴ).trace

/-- The Pauli-transfer action of the `r`-qubit generalized Toffoli (with `r-1` controls); for
`r=1` this is the action of `X`, as in Theorem 13. -/
def generalizedToffoliTransfer (r : ℕ) (hr : 0 < r) :
    Matrix (Qubits (r + r)) (Qubits (r + r)) ℂ :=
  pauliTransfer r (by
    simpa [gToffoli, Nat.sub_add_cancel hr] using (gToffoli (r - 1)).mat)

end DepthOptQC.Synth.Supplement


