-- Prove2me | Definitions.Def_TeleportGates_Ck_pauliFrame
-- name    : TeleportGates_Ck_pauliFrame
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T03:14:25.156043+00:00
-- url     : https://prove2.me/theorems/698edf33-dfed-4505-bf67-214cdcb9b2c4
-- title:
--   Pauli frame $R_{xz}=\bigotimes_i X^{x_i}Z^{z_i}$
-- statement:
--   For outcome strings $x,z\in\{0,1\}^n$, the Pauli frame is the $2^n\times2^n$ matrix
--
--   $$R_{xz}=\bigotimes_{i=1}^n X^{x_i}Z^{z_i},$$
--
--   where $X=\begin{pmatrix}0&1\\1&0\end{pmatrix}$, $Z=\begin{pmatrix}1&0\\0&-1\end{pmatrix}$, factor $i$ acts on qubit $i$, and on each qubit $Z^{z_i}$ is applied first. The factors are $I$, $Z$, $X$ and $XZ=-iY$. For $x=z=0$ the frame is the identity.
--
--   This is the operator $R_{xz}$ of Eq. (4): the Pauli by which the teleported state differs from the input, determined by the Bell outcomes.
--
--   **Formalization Note** The paper does not write $R_{xz}$ out; this product is what its Bell basis $|0x\rangle+(-1)^z|1\bar x\rangle$ (teleported qubit first) and the EPR pair $|00\rangle+|11\rangle$ give.
-- source:
--   Gottesman, Chuang, Quantum teleportation is a universal computational primitive, arXiv:quant-ph/9908010v1, §II, Eq. (4), p. 3 (R_xz); one-qubit case §I, p. 1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Gates

namespace TeleportGates.Ck

open QAlgorithms

/-- **The Pauli frame `R_{xz} = ⊗ᵢ X^{xᵢ} Z^{zᵢ}`.**
Gottesman, Chuang, *Quantum teleportation is a universal computational primitive*,
arXiv:quant-ph/9908010v1, §II, Eq. (4), p. 3: "|ψout⟩ = URxz|ψ⟩ = R′xzU|ψ⟩.
(4) where Rxz is an operator in C1 which depends on the (random) Bell basis measurement outcomes
xz"; for one qubit, §I, p. 1: "an additional single-qubit Pauli operation X, Y, or Z applied to it,
with the random variable xz determining which Pauli operator it is (with 00 corresponding to the
identity)".

`pauliFrame n x z` is the `2ⁿ × 2ⁿ` matrix `⊗ᵢ X^{xᵢ} Z^{zᵢ}`, with entries
`pauliFrame n x z c a = ∏ᵢ (X^{xᵢ} Z^{zᵢ}) (c i) (a i)`; factor `i` acts on qubit `i`, and on each
qubit `Z^{zᵢ}` acts first. For `xᵢ = zᵢ = 1` the factor is `XZ = −iY`.

**Formalization Note.** The paper does not write `R_{xz}` out. This explicit product is what the
Bell basis `|0x⟩ + (−1)^z|1x̄⟩` of p. 1 (teleported qubit first) and the EPR pair
`(|00⟩ + |11⟩)/√2` give: `(⟨β_{xz}| ⊗ I)(α ⊗ Ψ) = ½(α₀|x⟩ + (−1)^z α₁|x̄⟩) = ½ X^x Z^z α`. It is
defined from the outcome bits alone, not from `U`. -/
noncomputable def pauliFrame (n : ℕ) (x z : Qubits n) : Matrix (Qubits n) (Qubits n) ℂ :=
  Matrix.of fun c a =>
    ∏ i : Fin n, ((if x i then pauliX else 1) * (if z i then pauliZ else 1)) (c i) (a i)

end TeleportGates.Ck


