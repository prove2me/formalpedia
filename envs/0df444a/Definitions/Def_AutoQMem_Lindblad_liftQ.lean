-- Prove2me | Definitions.Def_AutoQMem_Lindblad_liftQ
-- name    : AutoQMem_Lindblad_liftQ
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:53:28.611718+00:00
-- url     : https://prove2.me/theorems/2cdf10d3-c2f0-40a5-a9da-6fa2df28c958
-- title:
--   Carrier-qubit embeddings $A_Q\otimes I_{\mathrm{rest}}$, $|q\rangle_Q|0\rangle_{\mathrm{rest}}$, $\rho_Q\otimes|0\rangle\langle0|_{\mathrm{rest}}$
-- statement:
--   The unencoded physical space splits as $\mathcal H=\mathcal H_Q\otimes\mathcal H_{\mathrm{rest}}$ with $\mathcal H_Q=\mathbb C^2$ the designated carrier qubit. This file fixes three embeddings:
--
--   1. $A\otimes I_{\mathrm{rest}}$ for a $2\times2$ operator $A$ on $\mathcal H_Q$;
--   2. the basis vector $|q\rangle_Q\otimes|0\rangle_{\mathrm{rest}}$, $q\in\{0,1\}$;
--   3. $\rho_Q\otimes|0\rangle\langle0|_{\mathrm{rest}}$ for a $2\times2$ matrix $\rho_Q$.
--
--   **Formalization Note** The carrier $Q$ is qubit $0$ and $\mathcal H_{\mathrm{rest}}$ consists of qubits $1,\dots,n-1$; $|0\rangle_{\mathrm{rest}}$ is the all-zero basis vector. Since the encoding unitary is arbitrary, this choice loses no generality.
-- source:
--   Drechsler, Oreg, Aharonov, Autonomous Quantum Memories from Classical Stochastic Processes, arXiv:2610.05589 (PDF of 2026-11-03), Definition 2.8, eqs. (13)–(14), p. 16 (PDF p. 18); Definition 2.18, eq. (24), p. 19

import Mathlib
import Definitions.Def_AutoQMem_Lindblad_Op
open Matrix

namespace AutoQMem.Lindblad

/-- **`A_Q ⊗ I_rest`: a carrier-qubit operator lifted to the physical space.** Drechsler, Oreg, Aharonov, *Autonomous Quantum Memories from Classical Stochastic Processes*,
arXiv:2610.05589 (PDF of 2026-11-03), Definition 2.8,
eq. (13)–(14), p. 16 (PDF 18): `H = H_Q ⊗ H_rest`, `H_Q = ℂ²`, and `X_Q ⊗ I_rest`, `Z_Q ⊗ I_rest`.

**Formalization Note.** The designated input qubit Q is qubit `0` and `H_rest` is qubits
`1, …, n'` (`Fin.tail`). Entry `(x, y)` is `A (x 0) (y 0)` if `x` and `y` agree on qubits
`1, …, n'`, and `0` otherwise. Since the encoding unitary `U` is arbitrary, naming qubit 0 as Q
loses no generality. -/
def liftQ {n' : ℕ} (A : Matrix (ZMod 2) (ZMod 2) ℂ) : Op (n' + 1) :=
  Matrix.of fun x y => A (x 0) (y 0) * if Fin.tail x = Fin.tail y then 1 else 0

/-- **The unencoded basis vector `|q⟩_Q ⊗ |0⟩_rest`** (Definition 2.8: `H_Q ⊗ |0⟩_rest`), the
computational basis vector of the bit string `(q, 0, …, 0)`. -/
def ket0 {n' : ℕ} (q : ZMod 2) : (Fin (n' + 1) → ZMod 2) → ℂ :=
  Pi.single (Fin.cons q 0 : Fin (n' + 1) → ZMod 2) 1

/-- **`ρ_Q ⊗ |0⟩⟨0|_rest`** (Definition 2.18, eq. (24), and Definition 2.17, eq. (21)): entry
`(x, y)` is `ρ_Q (x 0) (y 0)` if qubits `1, …, n'` of both `x` and `y` are `0`, and `0`
otherwise. -/
def embed0 {n' : ℕ} (ρQ : Matrix (ZMod 2) (ZMod 2) ℂ) : Op (n' + 1) :=
  Matrix.of fun x y => ρQ (x 0) (y 0) * if Fin.tail x = 0 ∧ Fin.tail y = 0 then 1 else 0

end AutoQMem.Lindblad


