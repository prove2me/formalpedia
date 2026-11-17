-- Prove2me | Definitions.Def_RelDecoding_Supplement_pauliGen
-- name    : RelDecoding_Supplement_pauliGen
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T14:12:11.1142+00:00
-- url     : https://prove2.me/theorems/eebc810c-05a2-410d-946d-8305e424ca70
-- title:
--   Signed Pauli generators $a_i=\eta_iP_n(w_i)$, binary label matrix and symplectic form $J_n$
-- statement:
--   For $(x,z)\in\mathbb F_2^{n}\times\mathbb F_2^n$ let $P_n(x,z)=i^{x\cdot z}X^xZ^z=i^{x\cdot z}\bigotimes_{j=1}^n X_j^{x_j}Z_j^{z_j}$ be the **Hermitian Pauli representative**, the exponent $x\cdot z$ evaluated as an integer (eq. (77)).
--
--   1. The **signed Pauli generators** are $a_i=\eta_i P_n(w_i)$ with signs $\eta_i\in\{\pm1\}$ and labels $w_i\in\mathbb F_2^{2n}$ (eq. (76)).
--   2. The **binary label matrix** is the $2n\times s$ matrix $A=[w_1\cdots w_s]$ over $\mathbb F_2$, and $K_A=\ker A$ (eq. (81)).
--   3. The **binary symplectic form** is
--   $$J_n=\begin{pmatrix}0&I_n\\ I_n&0\end{pmatrix}$$
--   over $\mathbb F_2$ (eq. (86)), so that $(A^{\mathsf T}J_nA)_{ij}=x_i\cdot z_j+z_i\cdot x_j$ records whether $a_i$ and $a_j$ anticommute.
--
--   These are the generators of the source and target algebras of the spin-system instance of relative decoding (§4.4.1).
--
--   **Formalization Note** $P_n$ is the published `StabTestMem.weyl` on `Qubits n = Fin n → Bool` (qubit $j$ = coordinate $j$), with labels the published `CutRankSched.Pauli n`, $x$-part first. Signs are units of $\mathbb Z$.
-- source:
--   Shang, Stilck França, From Simple Sources to Quantum Advantage: Homomorphic Polynomial Transduction via Relative Decoding, arXiv:2609.35101 (held version, sha256 d2be7859…), eqs. (76)–(77), (81), p.23; eq. (86), p.24 (pdf_pages 23–24)

import Mathlib
import Definitions.Def_CutRankSched_Pauli
import Definitions.Def_StabTestMem_weyl
import Definitions.Def_RelDecoding_Supplement_labelKer

set_option autoImplicit false

namespace RelDecoding.Supplement

open QAlgorithms

/-- The **signed Pauli generators** `aᵢ = ηᵢ P_n(wᵢ)`, `ηᵢ ∈ {±1}`, `wᵢ ∈ F₂^{2n}`, where
`P_n(x, z) = i^{x·z} X^x Z^z` is the Hermitian Pauli representative with the integer exponent
`x·z`. Shang, Stilck França, *From Simple Sources to Quantum Advantage: Homomorphic Polynomial
Transduction via Relative Decoding*, arXiv:2609.35101 (held version, sha256 d2be7859…), eqs. (76)–(77),
p.23 (also p.8).

**Formalization Note.** `P_n(u)` is the published `StabTestMem.weyl u` (Hermitian convention
`i^{x·z} X^x Z^z`, integer exponent `x·z`, matrix entry `i^{x·z}(−1)^{z·y}` in row `y ⊕ x`, column
`y`), acting on `Matrix (Qubits n) (Qubits n) ℂ` with `Qubits n = Fin n → Bool`; qubit `j` is the
`j`-th coordinate of a basis string (tensor factor `j`). A label is `CutRankSched.Pauli n =
(Fin n → ZMod 2) × (Fin n → ZMod 2)`, X-part first. Signs are units of `ℤ`. -/
noncomputable def pauliGen {n s : ℕ} (η : Fin s → ℤˣ) (w : Fin s → CutRankSched.Pauli n) :
    Fin s → Matrix (Qubits n) (Qubits n) ℂ :=
  fun i => (((η i : ℤ) : ℂ)) • StabTestMem.weyl (w i)

/-- The binary **label matrix** `A = [w₁ ⋯ w_s]` (a `2n × s` matrix over `F₂`, rows `x` then `z`)
of a list of Pauli labels. Eq. (81), p.23. -/
abbrev pauliLabelMatrix {n s : ℕ} (w : Fin s → CutRankSched.Pauli n) :
    Matrix (Fin n ⊕ Fin n) (Fin s) (ZMod 2) :=
  labelMatrix fun i => pairVec (w i)

/-- The **relation code** `K_A = ker A` over `F₂` of a list of Pauli labels. Eq. (81), p.23. -/
abbrev pauliKer {n s : ℕ} (w : Fin s → CutRankSched.Pauli n) :
    Submodule (ZMod 2) (Fin s → ZMod 2) :=
  labelKer fun i => pairVec (w i)

/-- The **binary symplectic form** `J_n = [[0, I_n], [I_n, 0]]` over `F₂`, in the `(x, z)` block
order. Eq. (86), p.24. -/
def symplecticJ (n : ℕ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (ZMod 2) :=
  Matrix.fromBlocks 0 1 1 0

end RelDecoding.Supplement


