-- Prove2me | Definitions.Def_ICSCompute_splitQ
-- name    : ICSCompute_splitQ
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:45:47.714501+00:00
-- url     : https://prove2.me/theorems/65e902c4-9840-4026-8704-d2aeb58e2f1a
-- title:
--   Splitting an $(a+b)$-qubit register into its first $a$ and last $b$ qubits
-- statement:
--   A computational-basis label of $\mathcal S(a+b)$ is a bit string $x\in\{0,1\}^{a+b}$. It corresponds to the pair formed by its first $a$ bits and its last $b$ bits, and conversely a pair of strings is joined by concatenation. This identifies $\mathcal S(a+b) = \mathcal S(a)\otimes\mathcal S(b)$ with the first $a$ qubits as the first tensor factor.
--
--   This is the single register-order convention of the mission: in a circuit description $(n, C)$ the first $n$ input and output qubits are the feedback registers, the remaining ones the external registers $P$ and $F$ (Definition 4.5).
--
--   **Formalization Note** Bits are `Bool` with `false` $=0$, an $n$-qubit basis label is `Qubits n = Fin n → Bool` (published `QAlgorithms` layer), and concatenation is `Fin.append`.
-- source:
--   Shmueli, What Can Be Computed with Indefinite Causal Structure?, arXiv:2610.40573 (version of 2026-11-03, sha256 d3e36399…b606), §3 conventions, p.14 (PDF p.16); Definition 4.5, p.19 (PDF p.21)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic

namespace ICSCompute

open QAlgorithms

/-- **Splitting an `(a + b)`-qubit register into its first `a` and last `b` qubits**
(Shmueli, *What Can Be Computed with Indefinite Causal Structure?*, arXiv:2610.40573, version of
2026-11-03, sha256 d3e36399…b606, §3 conventions p.14 (PDF p.16) and Definition 4.5, p.19
(PDF p.21): "Its first n input and output qubits form n separate single-qubit feedback pairs").

A basis label of `S(a + b)` is a bit string `x : Fin (a + b) → Bool`; it corresponds to the pair
(first `a` bits, last `b` bits), and conversely a pair is joined by `Fin.append`.

**Formalization Note** Bits are `Bool` (`false` = 0) and `QAlgorithms.Qubits n = Fin n → Bool`.
This equivalence `S(a + b) ≅ S(a) ⊗ S(b)` is the one register-order convention used in every
statement of the mission: the first `a` wires are the first tensor factor. -/
def splitQ (a b : ℕ) : Qubits (a + b) ≃ Qubits a × Qubits b where
  toFun x := (fun i => x (Fin.castAdd b i), fun j => x (Fin.natAdd a j))
  invFun y := Fin.append y.1 y.2
  left_inv x := Fin.append_castAdd_natAdd
  right_inv y := by
    rcases y with ⟨y₁, y₂⟩
    simp

end ICSCompute


