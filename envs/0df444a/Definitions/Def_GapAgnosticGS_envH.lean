-- Prove2me | Definitions.Def_GapAgnosticGS_envH
-- name    : GapAgnosticGS_envH
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:29:40.890107+00:00
-- url     : https://prove2.me/theorems/a5295fba-fd48-46d2-8b9b-3752630f4fd1
-- title:
--   Environment $\mathcal E_H=(\mathrm{Had}_A)(S_A)(\text{ctrl-}W)(\mathrm{Had}_A)$ of a Hamiltonian
-- statement:
--   Let $W$ be a unitary on $\mathbb C^n$ and let $A$ be one qubit. The environment unitary on $\mathbb C^n\otimes A$ is
--
--   $$\mathcal E=(I\otimes\mathrm{Had})\,(I\otimes S)\,(\text{ctrl-}W)_{AI}\,(I\otimes\mathrm{Had}),\qquad S=\mathrm{diag}(1,i),$$
--
--   where ctrl-$W$ applies $W$ to $\mathbb C^n$ when the arm qubit is $|1\rangle$. For $W=W_H$ this is the environment $\mathcal E_H$ of Lemma 3.1, whose arms are the eigenstates of $H$ and whose best arm is the ground state.
-- source:
--   Heidari–Moharrami–Tavakoli–Zhang, Gap-Agnostic Ground-State Preparation via Quantum Bandits, manuscript (STOC 2027 submission, sha256 bd767ba1…c57acc), Lemma 3.1 and its proof, p.8 (PDF p.9); §1, p.5 (PDF p.6)

import Definitions.Def_QAlgorithms_Defs_Hamiltonian
open QAlgorithms

namespace GapAgnosticGS

/-- Heidari–Moharrami–Tavakoli–Zhang, *Gap-Agnostic Ground-State Preparation via Quantum Bandits*, manuscript (STOC 2027 submission, sha256 bd767ba1…c57acc), Lemma 3.1 and its proof, p.8 (PDF p.9): "(Had_A ⊗ I_I)(S_A ⊗ I_I)(ctrl-W_H)_{AI}
(Had_A ⊗ I_I)", and §1, p.5 (PDF p.6): "apply a Hadamard gate to A, then an S gate to A and W_H
controlled by A, and finally a second Hadamard gate to A". The environment unitary `E_H` built
from a unitary `W` on `ℂⁿ` (for `W = W_H` it is the paper's `E_H`), on the register
`Fin n × Bool` (selector `I`, one-qubit arm register `A`, `false = |0⟩`).

**Formalization Note.** `Had = QAlgorithms.hadamard`, `S = QAlgorithms.phaseS = diag(1, i)`;
`ctrl-W` applies `W` to `I` when `A = |1⟩`. The arm qubit is the second tensor factor, so the
selector-first layout of `HidEnv` is kept. -/
noncomputable def envH {n : ℕ} (W : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n × Bool) (Fin n × Bool) ℂ :=
  Matrix.kronecker (1 : Matrix (Fin n) (Fin n) ℂ) hadamard *
    Matrix.kronecker (1 : Matrix (Fin n) (Fin n) ℂ) phaseS *
    Matrix.of (fun x x' : Fin n × Bool =>
      if x.2 = x'.2 then (if x.2 then W x.1 x'.1 else (1 : Matrix (Fin n) (Fin n) ℂ) x.1 x'.1)
      else 0) *
    Matrix.kronecker (1 : Matrix (Fin n) (Fin n) ℂ) hadamard

end GapAgnosticGS


