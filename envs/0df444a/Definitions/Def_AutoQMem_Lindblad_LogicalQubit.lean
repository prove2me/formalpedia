-- Prove2me | Definitions.Def_AutoQMem_Lindblad_LogicalQubit
-- name    : AutoQMem_Lindblad_LogicalQubit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:57:03.929234+00:00
-- url     : https://prove2.me/theorems/c83fdd7e-7063-4435-82ad-1231ed255639
-- title:
--   Designated logical qubit: encoding unitary $U$ and conjugate CSS logicals $\bar X=X^{\ell_X}$, $\bar Z=Z^{\ell_Z}$
-- statement:
--   A **designated logical qubit** of an $n$-qubit CSS code consists of
--
--   1. a unitary $U$ on $\mathcal H$ such that $U(\mathcal H_Q\otimes|0\rangle_{\mathrm{rest}})$ lies in the code space $\Pi_{\mathrm{code}}\mathcal H$;
--   2. support vectors $\ell_X,\ell_Z\in\mathbb F_2^n$ of a conjugate pair of CSS logical Pauli strings $\bar X=X^{\ell_X}\in\{I,X\}^{\otimes n}$, $\bar Z=Z^{\ell_Z}\in\{I,Z\}^{\otimes n}$: they commute with every stabilizer, $H_Z\ell_X=0$ and $H_X\ell_Z=0$, and anticommute with each other, $\ell_X\cdot\ell_Z=1$;
--   3. the representation property (14):
--   $$\bar X\,\Pi_{\mathrm{code}}=U(X_Q\otimes I_{\mathrm{rest}})U^\dagger\,\Pi_{\mathrm{code}},\qquad \bar Z\,\Pi_{\mathrm{code}}=U(Z_Q\otimes I_{\mathrm{rest}})U^\dagger\,\Pi_{\mathrm{code}} .$$
--
--   When the code encodes $k>1$ logical qubits, the others are absorbed into $\mathcal H_{\mathrm{rest}}$.
--
--   **Formalization Note** $n=n'+1\ge1$; $Q$ is qubit $0$. "A conjugate pair of CSS logical Pauli strings" is written out as the three $\mathbb F_2$ conditions the paper uses in the proof of Claim 2.11.
-- source:
--   Drechsler, Oreg, Aharonov, Autonomous Quantum Memories from Classical Stochastic Processes, arXiv:2610.05589 (PDF of 2026-11-03), Definition 2.8, eqs. (13)–(14), p. 16 (PDF p. 18); Definition 2.9, p. 16; proof of Claim 2.11, p. 17

import Mathlib
import Definitions.Def_AutoQMem_Lindblad_CSSCode_projX
import Definitions.Def_AutoQMem_Lindblad_Pauli1
import Definitions.Def_AutoQMem_Lindblad_liftQ
open Matrix

namespace AutoQMem.Lindblad

/-- **Designated logical qubit: encoding unitary and bare logical operators.** Drechsler, Oreg, Aharonov, *Autonomous Quantum Memories from Classical Stochastic Processes*,
arXiv:2610.05589 (PDF of 2026-11-03),
Definitions 2.8–2.9, p. 16 (PDF 18): "Let U be a unitary encoding operator on H such that
U(H_Q ⊗ |0⟩_rest) lies in the code space Π_code H … We choose U so that the Pauli operators of the
designated input qubit are represented on the code space by a conjugate pair of CSS logical Pauli
strings X̄ ∈ {I, X}^{⊗n} and Z̄ ∈ {I, Z}^{⊗n}: X̄ Π_code = U(X_Q ⊗ I_rest)U† Π_code,
Z̄ Π_code = U(Z_Q ⊗ I_rest)U† Π_code. (14)" and "Let ℓ_X, ℓ_Z ∈ 𝔽₂ⁿ be n-bit strings that indicate
the locations of the non-identity Pauli operators in X̄ and Z̄".

**Formalization Note.**
* `n = n' + 1 ≥ 1`; the designated qubit Q is qubit `0`, `H_rest` is qubits `1, …, n'` and
  `|0⟩_rest` is the all-zero basis vector (see `liftQ`). The other `k - 1` logical qubits live in
  `H_rest` (Definition 2.8); `k` is not a parameter.
* `X̄ = X^{ℓ_X}` and `Z̄ = Z^{ℓ_Z}` (`pauliX`, `pauliZ`, no phase).
* "a conjugate pair of CSS logical Pauli strings" is written out as the three facts the paper uses
  (proof of Claim 2.11, p. 17): `H_Z ℓ_X = 0` and `H_X ℓ_Z = 0` (each commutes with every
  stabilizer) and `ℓ_X · ℓ_Z = 1` (they anticommute).
* "U(H_Q ⊗ |0⟩_rest) lies in the code space" is `Π_code U|q,0…0⟩ = U|q,0…0⟩` for `q = 0, 1`. -/
structure LogicalQubit {n' mX mZ : ℕ} (C : CSSCode (n' + 1) mX mZ) : Type where
  /-- The encoding unitary `U`. -/
  U : Op (n' + 1)
  /-- `U` is unitary. -/
  unitary : U ∈ Matrix.unitaryGroup (Fin (n' + 1) → ZMod 2) ℂ
  /-- `ℓ_X`: the support of the bare logical `X̄`. -/
  lX : Fin (n' + 1) → ZMod 2
  /-- `ℓ_Z`: the support of the bare logical `Z̄`. -/
  lZ : Fin (n' + 1) → ZMod 2
  /-- `X̄` commutes with the Z stabilizers: `H_Z ℓ_X = 0`. -/
  commX : C.HZ *ᵥ lX = 0
  /-- `Z̄` commutes with the X stabilizers: `H_X ℓ_Z = 0`. -/
  commZ : C.HX *ᵥ lZ = 0
  /-- `X̄` and `Z̄` anticommute: `ℓ_X · ℓ_Z = 1`. -/
  anti : lX ⬝ᵥ lZ = 1
  /-- `U(H_Q ⊗ |0⟩_rest)` lies in the code space. -/
  encodes : ∀ q : ZMod 2, C.codeProj *ᵥ (U *ᵥ ket0 q) = U *ᵥ ket0 q
  /-- Eq. (14), X part: `X̄ Π_code = U (X_Q ⊗ I_rest) U† Π_code`. -/
  eq14X : pauliX lX * C.codeProj = U * liftQ (Pauli1.sigma .X) * Uᴴ * C.codeProj
  /-- Eq. (14), Z part: `Z̄ Π_code = U (Z_Q ⊗ I_rest) U† Π_code`. -/
  eq14Z : pauliZ lZ * C.codeProj = U * liftQ (Pauli1.sigma .Z) * Uᴴ * C.codeProj

end AutoQMem.Lindblad


