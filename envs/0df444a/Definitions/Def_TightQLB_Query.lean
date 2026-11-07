-- Prove2me | Definitions.Def_TightQLB_Query
-- name    : TightQLB_Query
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T01:59:57.607794+00:00
-- url     : https://prove2.me/theorems/6ccadc87-3dbe-4961-a953-ab1497a93f8e
-- title:
--   The device register and the controlled query $O^{\mathrm c}_\omega=|0\rangle\langle0|_{\mathsf C}\otimes I+|1\rangle\langle1|_{\mathsf C}\otimes O_\omega$; the value oracle $O_f$
-- statement:
--   The device register is $A=(\mathsf C\times\mathsf Q)\times W$: a control qubit $\mathsf C$, a query register $\mathsf Q$ of the type on which the oracle acts, and a finite workspace $W$. For an oracle matrix $O_\omega$ on $\mathsf Q$ the controlled query is
--
--   $$
--   O^{\mathrm c}_\omega=|0\rangle\langle0|_{\mathsf C}\otimes I+|1\rangle\langle1|_{\mathsf C}\otimes O_\omega ,
--   $$
--
--   acting on $\mathsf C$ and $\mathsf Q$ and trivially on $W$. In the Fourier ensemble $\mathsf Q$ consists of an address register $\mathsf X$ of $n$ qubits and a target qubit $\mathsf T$, and the oracle is the value oracle
--
--   $$
--   O_f|x,b\rangle=|x,\,b\oplus(1-f(x))/2\rangle .
--   $$
--
--   Every query of a device goes through this operator, so these definitions are where the oracle enters the model.
--
--   **Formalization Note** `Q` is an arbitrary finite type and `O : Matrix Q Q ℂ`, so that Definition 3.1 and Lemma 3.2 are stated for every oracle, as in the paper (which treats two ensembles). With $f=(-1)^{\mathtt{fb}}$ we have $(1-f(x))/2=[\mathtt{fb}\,x]$, so $O_f$ is the published `QAlgorithms.xorOracle fb`.
-- source:
--   Bhateja, Esmaili, Mantri, Tight Query Lower Bounds for Quantum Sampling, with an Application to Certified Randomness, arXiv:2610.06721 (version of sha256 00a999f1…), §3.1, Eq. (8), p. 13 (PDF p. 16); §3.2, Eq. (14), p. 16 (PDF p. 19)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Query
open QAlgorithms

namespace TightQLB

/-!
# Registers, the value oracle and the controlled query

Bhateja, Esmaili, Mantri, *Tight Query Lower Bounds for Quantum Sampling, with an Application to
Certified Randomness*, arXiv:2610.06721 (version of sha256 00a999f1…), §3.1, Eq. (8), p.13
(PDF p.16); §3.2, Lemma 3.2, Eq. (14), p.16 (PDF p.19); §4, p.21 (PDF p.24).

The value oracle is `O_f|x, b⟩ = |x, b ⊕ (1 − f(x))/2⟩` on an address register `X` of `n` qubits and a
target qubit `T` (8). For an oracle unitary `O_ω` on a query register `Q`, the controlled query is
`O^c_ω = |0⟩⟨0|_C ⊗ I + |1⟩⟨1|_C ⊗ O_ω` on a control qubit `C` and `Q` (14).

**Formalization Note.**
* The query register is an arbitrary finite type `Q`, and the oracle is its matrix `O : Matrix Q Q ℂ`,
  so the experiment and its normal form are stated for every oracle, as in Definition 3.1 and
  Lemma 3.2 (which cover both of the paper's ensembles). The Fourier ensemble has `Q = X × T =
  Qubits n × Bool` and `O = valueOracle fb`.
* The device register is `Reg Q W = (C × Q) × W` with `C = Bool` and a finite workspace `W`.
* With `f(x) = (−1)^{fb x}`, `(1 − f(x))/2 = [fb x]`, so `O_f` is the published
  `QAlgorithms.xorOracle fb`, the permutation matrix of `(x, b) ↦ (x, b ⊕ fb x)`.
-/

/-- The device register: a control qubit `C`, the query register `Q`, and a finite workspace `W`. -/
abbrev Reg (Q W : Type) := (Bool × Q) × W

/-- Eq. (14), p.16 (PDF p.19): the controlled query `O^c = |0⟩⟨0|_C ⊗ I + |1⟩⟨1|_C ⊗ O` on `C × Q`. -/
def ctrl {Q : Type} [DecidableEq Q] (O : Matrix Q Q ℂ) : Matrix (Bool × Q) (Bool × Q) ℂ :=
  Matrix.of fun p p' => if p.1 = p'.1 then (if p.1 then O p.2 p'.2 else
    (if p.2 = p'.2 then 1 else 0)) else 0

/-- Lemma 3.2, p.16 (PDF p.19): the controlled query acting on `C × Q` and trivially on the
workspace `W`. -/
noncomputable def queryOn {Q : Type} [DecidableEq Q] (O : Matrix Q Q ℂ) (W : Type)
    [DecidableEq W] : Matrix (Reg Q W) (Reg Q W) ℂ :=
  Matrix.kronecker (ctrl O) (1 : Matrix W W ℂ)

/-- Eq. (8), p.13 (PDF p.16): the value oracle `O_f |x, b⟩ = |x, b ⊕ (1 − f(x))/2⟩ = |x, b ⊕ fb x⟩`
on the address register `X` and the target qubit `T`, for `f = (−1)^{fb}`. -/
def valueOracle {n : ℕ} (fb : Qubits n → Bool) : Matrix (Qubits n × Bool) (Qubits n × Bool) ℂ :=
  xorOracle fb

end TightQLB


