-- Prove2me | Definitions.Def_BaconThesis_Supercoherence_onQubit
-- name    : BaconThesis_Supercoherence_onQubit
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:16:45.129663+00:00
-- url     : https://prove2.me/theorems/51aa8550-251e-42a1-9718-0c94c977bc9f
-- title:
--   A single-qubit operator acting on qubit $i$ of an $n$-qubit register
-- statement:
--   Let $n \ge 1$ and let the $n$-qubit Hilbert space $(\mathbb C^2)^{\otimes n}$ have the computational basis $\{|x\rangle : x \in \{0,1\}^n\}$. For a qubit $i$ and a $2\times 2$ complex matrix $O$, the operator
--
--   $$O^{(i)} = I \otimes \cdots \otimes I \otimes \underbrace{O}_{i\text{th factor}} \otimes I \otimes \cdots \otimes I$$
--
--   applies $O$ to qubit $i$ and the identity to every other qubit. Its matrix entries are $\langle x|O^{(i)}|y\rangle = O_{x_i y_i}$ if $x_j = y_j$ for every $j \ne i$, and $0$ otherwise.
--
--   These are the book's single-qubit operators $\sigma_\alpha^{(i)}$ and single-subsystem operators $o^{(k)}$ of Definition 15.2.1 and (15.10).
--
--   **Formalization Note** Qubits are numbered from $0$ in Lean (the book's qubit $k$ is Lean's qubit $k-1$). On Pauli matrices, `onQubit i (pauli a)` coincides with the referenced `pauliAt a i`.
-- source:
--   Bacon, Decoherence, Control, and Symmetry in Quantum Computers, arXiv:quant-ph/0305025v1, §15.2, p.169 (PDF p.186), and Definition 15.2.1 with (15.10), pp.170–171 (PDF pp.187–188)

import Mathlib
import Definitions.Def_QMaxCutSDP_Rounding_Pauli

open QMaxCutSDP.Rounding

namespace BaconThesis.Supercoherence

/-- Bacon, *Decoherence, Control, and Symmetry in Quantum Computers*, arXiv:quant-ph/0305025v1, §15.2, p.169 (PDF p.186) and Definition 15.2.1 with (15.10), pp.170–171
(PDF pp.187–188): the single-qubit operator `O` acting on qubit `i` of an `n`-qubit register,
`I ⊗ ⋯ ⊗ O ⊗ ⋯ ⊗ I` (the book's `o^{(k)}`, `σ_α^{(i)}`).

**Formalization Note.** The register is `(Fin n → Fin 2) → ℂ` (computational basis indexed by bit
strings, `QMaxCutSDP.Rounding.Operator n`). The matrix entry at `(x, y)` is `O (x i) (y i)` when
`x` and `y` agree off qubit `i`, and `0` otherwise. Qubits are 0-based in Lean (the book's
qubit `k` is `k - 1`). For `O = pauli a` this is `pauliAt a i`. -/
def onQubit {n : ℕ} (i : Fin n) (O : Matrix (Fin 2) (Fin 2) ℂ) : Operator n :=
  fun x y => if ∀ j, j ≠ i → x j = y j then O (x i) (y i) else 0

end BaconThesis.Supercoherence


