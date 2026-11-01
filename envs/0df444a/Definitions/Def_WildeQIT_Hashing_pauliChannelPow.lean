-- Prove2me | Definitions.Def_WildeQIT_Hashing_pauliChannelPow
-- name    : WildeQIT_Hashing_pauliChannelPow
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:22:19.129023+00:00
-- url     : https://prove2.me/theorems/7c8406f2-c95e-4d19-9a92-073f0e642d2a
-- title:
--   $n$ independent uses $\mathcal N_p^{\otimes n}$ of a Pauli channel
-- statement:
--   For a probability vector $p$ on $\{I,X,Y,Z\}$ and a block length $n$, $\mathcal N_p^{\otimes n}$ is the tensor product of $n$ copies of the Pauli channel $\mathcal N_p$, acting on operators on $n$ qubits. On a product input it applies $\mathcal N_p$ to each qubit; equivalently it applies the tensor-product error $E_{a^n}=E_{a_1}\otimes\cdots\otimes E_{a_n}$ with probability $\prod_ip_{a_i}$.
--
--   **Formalization Note** The tensor power is the published `QAlgorithms.piSuperop`, defined on every operator through the matrix-unit expansion, so it acts on entangled inputs (and on one share of a state entangled with a reference) as $\mathcal N_p^{\otimes n}$ does.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, §24.6.3, pp. 674–675; the n-fold channel of (24.1), p. 659

import Definitions.Def_WildeQIT_Hashing_pauliChannel

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, §24.6.3, pp. 674–675
(`n` independent uses of a Pauli channel).
-/

namespace WildeQIT.Hashing

open QAlgorithms Stabilizer

/-- **`n` independent uses of the Pauli channel**, `N_p^{⊗n}` (Wilde, *From Classical to Quantum
Shannon Theory*, arXiv:1106.1445v8, p. 675: "an i.i.d. Pauli channel issues some tensor-product
error `E_{aⁿ} ≡ E_{a₁} ⊗ ⋯ ⊗ E_{aₙ}`"; the `n`-fold channel `N^{⊗n}` of (24.1)).

**Formalization Note.** The tensor power is the published `piSuperop`, the tensor product of
`n` copies of `pauliChannel p`, defined on every operator on `n` qubits (`Qubits n`) through the
matrix-unit expansion, so it acts on entangled inputs as `N^{⊗n}` does. -/
noncomputable def pauliChannelPow (p : FinDist Pauli) (n : ℕ) : Superop (Qubits n) (Qubits n) :=
  piSuperop fun _ : Fin n => pauliChannel p

end WildeQIT.Hashing


