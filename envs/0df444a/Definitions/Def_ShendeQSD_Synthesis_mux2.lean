-- Prove2me | Definitions.Def_ShendeQSD_Synthesis_mux2
-- name    : ShendeQSD_Synthesis_mux2
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:17:32.567678+00:00
-- url     : https://prove2.me/theorems/50869cc8-de39-40cc-91c2-4796c452b3de
-- title:
--   Multiplexor $U_0\oplus U_1$ with one select qubit
-- statement:
--   Let $U_0,U_1$ be operators on a data register. The **multiplexor** with one (most significant) select qubit is the block-diagonal operator
--
--   $$
--   U_0\oplus U_1=\begin{pmatrix}U_0&0\\0&U_1\end{pmatrix},
--   $$
--
--   which applies $U_0$ to the data qubits when the select qubit carries $|0\rangle$ and $U_1$ when it carries $|1\rangle$. In particular $I\otimes V=V\oplus V$.
--
--   Multiplexors are the side factors of the Cosine–Sine decomposition and the object demultiplexed by Theorem 12.
--
--   **Formalization Note** The index type is `Bool × ι`, select qubit first (most significant), data register `ι` second. $I\otimes V$ is written `1 ⊗ₖ V` (Kronecker product).
-- source:
--   Shende, Bullock, Markov, Synthesis of Quantum Logic Circuits, arXiv:quant-ph/0406176v5, §3, Eq. (13), p. 8

import Mathlib

namespace ShendeQSD.Synthesis

/-- **The multiplexor `U₀ ⊕ U₁` with one select qubit.**
Shende, Bullock, Markov, *Synthesis of Quantum Logic Circuits*, arXiv:quant-ph/0406176v5,
§3, Eq. (13), p. 8: "In the event that a multiplexor has a single select bit, and the select bit is
most significant, the matrix of the quantum multiplexor is block diagonal, U = (U₀ ; U₁) … The
multiplexor will apply U₀ or U₁ to the data qubits according as the select qubit carries |0⟩ or
|1⟩ … U = U₀ ⊕ U₁".

**Formalization Note.** The index `Bool × ι` puts the select qubit first (most significant) and the
data register `ι` second. The matrix is block diagonal in the select bit: block `false` is `U₀`,
block `true` is `U₁`. `I ⊗ V` is written `1 ⊗ₖ V` (`Matrix.kronecker`), which equals `mux2 V V`. -/
def mux2 {ι : Type*} (U₀ U₁ : Matrix ι ι ℂ) : Matrix (Bool × ι) (Bool × ι) ℂ :=
  Matrix.of fun p q => if p.1 = q.1 then (if p.1 then U₁ else U₀) p.2 q.2 else 0

end ShendeQSD.Synthesis


