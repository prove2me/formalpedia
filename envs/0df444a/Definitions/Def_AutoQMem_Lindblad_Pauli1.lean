-- Prove2me | Definitions.Def_AutoQMem_Lindblad_Pauli1
-- name    : AutoQMem_Lindblad_Pauli1
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:52:54.466608+00:00
-- url     : https://prove2.me/theorems/05faf9e0-228d-4eed-84fa-52ca3f0929d8
-- title:
--   Single-qubit Pauli labels and the carrier Paulis $I_Q,X_Q,Y_Q,Z_Q$
-- statement:
--   The four labels $P\in\{I,X,Y,Z\}$ of single-qubit Pauli operators, together with the corresponding $2\times 2$ matrices on the carrier qubit $\mathcal H_Q=\mathbb C^2$ (basis $|0\rangle,|1\rangle$):
--   $$X|q\rangle=|q\oplus1\rangle,\qquad Z|q\rangle=(-1)^q|q\rangle,\qquad Y=iXZ,\qquad I=\mathbb 1 .$$
--
--   The convention $Y=iXZ$ is the paper's ("$Y_i=iX_iZ_i$") and gives the standard Pauli $Y$. The labels index the jump operators $P_i f_{P,i,\alpha}(t)$ of a syndrome-based Lindbladian, and the matrices are the operators $X_Q,Y_Q,Z_Q$ of the effective logical channel.
-- source:
--   Drechsler, Oreg, Aharonov, Autonomous Quantum Memories from Classical Stochastic Processes, arXiv:2610.05589 (PDF of 2026-11-03), §2.2.1, p. 20 (PDF p. 22); Definition 2.8, p. 16; Appendix B (proof of Lemma 4.4), p. 65

import Mathlib
open Matrix

namespace AutoQMem.Lindblad

/-- **Single-qubit Pauli labels `P ∈ {I, X, Y, Z}`.** Drechsler, Oreg, Aharonov, *Autonomous Quantum Memories from Classical Stochastic Processes*,
arXiv:2610.05589 (PDF of 2026-11-03), §2.2.1, p. 20 (PDF 22): "We write P_i
for the single-qubit operator P ∈ {I, X, Y, Z} acting on qubit i". -/
inductive Pauli1 : Type
  | I | X | Y | Z
  deriving DecidableEq

instance : Fintype Pauli1 where
  elems := {.I, .X, .Y, .Z}
  complete := fun x => by cases x <;> decide

/-- **The single-qubit Pauli matrices `I_Q, X_Q, Y_Q, Z_Q`** on the carrier qubit Q, basis
`|0⟩, |1⟩` indexed by `ZMod 2` (Drechsler, Oreg, Aharonov, *Autonomous Quantum Memories from Classical Stochastic Processes*,
arXiv:2610.05589 (PDF of 2026-11-03), Definition 2.8, p. 16, PDF 18: "Let X_Q, Y_Q, Z_Q ∈ B(H_Q)
denote the Pauli operators acting on the designated carrier qubit Q").

**Formalization Note.** `X|q⟩ = |q + 1⟩`, `Z|q⟩ = (-1)^q |q⟩` and `Y = i X Z`, the paper's
convention "Y_i = iX_iZ_i" (Appendix B, proof of Lemma 4.4, p. 65), which is the standard Y. -/
noncomputable def Pauli1.sigma : Pauli1 → Matrix (ZMod 2) (ZMod 2) ℂ
  | .I => 1
  | .X => Matrix.of fun a b => if a = b + 1 then 1 else 0
  | .Y => Complex.I • ((Matrix.of fun a b => if a = b + 1 then 1 else 0) *
      Matrix.diagonal fun a => (-1 : ℂ) ^ a.val)
  | .Z => Matrix.diagonal fun a => (-1 : ℂ) ^ a.val

end AutoQMem.Lindblad


