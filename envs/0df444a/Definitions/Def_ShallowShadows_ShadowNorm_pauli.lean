-- Prove2me | Definitions.Def_ShallowShadows_ShadowNorm_pauli
-- name    : ShallowShadows_ShadowNorm_pauli
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:31:00.267358+00:00
-- url     : https://prove2.me/theorems/2b9aae28-168d-477f-8dd8-406451f3f13d
-- title:
--   Pauli strings $P^\lambda = \bigotimes_j i^{x_jz_j}X^{x_j}Z^{z_j}$ (Eq. (1))
-- statement:
--   For $n$ qubits and a label $\lambda = (x, z) \in \{0,1\}^n \times \{0,1\}^n$, the **Pauli string** is
--
--   $$
--   P^\lambda = \bigotimes_{j\in[n]} i^{x_j z_j} X^{x_j} Z^{z_j}.
--   $$
--
--   On one qubit this gives $P^{(0,0)} = \mathbb I$, $P^{(1,0)} = X$, $P^{(0,1)} = Z$ and $P^{(1,1)} = iXZ = Y$. The $4^n$ Pauli strings are Hermitian, square to the identity, and form an orthogonal basis of the $2^n\times 2^n$ complex matrices, $\operatorname{tr}(P^\lambda P^{\lambda'}) = 2^n\delta_{\lambda\lambda'}$.
--
--   They are the basis in which the measurement channel of every depth-$d$ ensemble is diagonal.
--
--   **Formalization Note** Operators on $n$ qubits are complex matrices indexed by bit strings $\{0,1\}^n$ (`ClassicalShadow.Linear.Op n`, bit $0$ standing for $|0\rangle$). The $(a,b)$ entry is $\prod_j i^{x_jz_j}(-1)^{z_j b_j}[a_j = b_j + x_j]$. Qubits are indexed from $0$.
-- source:
--   Bertoni, Haferkamp, Hinsche, Ioannou, Eisert, Pashayan, Shallow shadows: Expectation estimation using low-depth random Clifford circuits, arXiv:2209.12924v3, §II, Eq. (1), p. 3

import Mathlib
import Definitions.Def_ClassicalShadow_Linear_Setting

open ClassicalShadow.Linear

namespace ShallowShadows.ShadowNorm

/-- Bertoni, Haferkamp, Hinsche, Ioannou, Eisert, Pashayan, *Shallow shadows: Expectation
estimation using low-depth random Clifford circuits*, arXiv:2209.12924v3, §II, Eq. (1), p. 3:
the Pauli string indexed by `λ = (x, z) ∈ {0,1}ⁿ × {0,1}ⁿ`,
`P^λ = ⊗_{j ∈ [n]} i^{x_j z_j} X^{x_j} Z^{z_j}`.

The single-qubit factor `i^{xz} X^x Z^z` has `(a, b)` entry `i^{xz} (-1)^{z b}` when `a = b + x`
(mod 2) and `0` otherwise, so `P^(0,0) = 𝕀`, `P^(1,0) = X`, `P^(0,1) = Z` and
`P^(1,1) = i X Z = Y = [[0, -i], [i, 0]]`. The entry of the tensor product is the product over the
qubits of the single-qubit entries.

**Formalization Note.** Operators on `n` qubits are `ClassicalShadow.Linear.Op n`, complex matrices
indexed by `Bits n = Fin n → Fin 2`, the bit `0` standing for `|0⟩`. The label set `{0,1}^{2n}` is
`Bits n × Bits n`, the first component `x`, the second `z`. Qubits are indexed from `0`, so the
paper's qubit `j` is index `j − 1`. The construction follows the published
`QAlgorithms.Stabilizer.PauliString`, but on `Bits n` instead of `Fin n → Bool`, so that it lives
on the carrier of the reused HKP measurement channel `ClassicalShadow.Linear.measChannel`. -/
noncomputable def pauli {n : ℕ} (lam : Bits n × Bits n) : Op n :=
  Matrix.of fun a b => ∏ j, (Complex.I ^ ((lam.1 j).val * (lam.2 j).val) *
    if a j = b j + lam.1 j then (-1 : ℂ) ^ ((lam.2 j).val * (b j).val) else 0)

end ShallowShadows.ShadowNorm


