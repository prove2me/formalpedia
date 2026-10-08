-- Prove2me | Definitions.Def_QuantumWalkSearch_PhaseReflection_ReflectionCircuit
-- name    : QuantumWalkSearch_PhaseReflection_ReflectionCircuit
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T08:45:39.328947+00:00
-- url     : https://prove2.me/theorems/7e3abdaf-936f-4be4-b84d-b35a4e1c9fb1
-- title:
--   The circuit $R(P)=V^\dagger F_{\neq 0}V$: $k$ repeated phase estimations of $W(P)$ with $s=\lceil\log_2(2\pi/\Delta(P))\rceil$ (proof of Theorem 6)
-- statement:
--   Let $P$ be a Markov chain on a finite set $X$ with stationary distribution $\pi$, $W(P)$ its quantum walk on $\mathcal H=\mathbb C^{X\times X}$ and $\Delta(P)$ its phase gap. Fix an integer $k\ge 0$ and set
--   $$s=\Big\lceil\log_2\frac{2\pi}{\Delta(P)}\Big\rceil .$$
--   The circuit acts on $\mathcal H\otimes(\mathbb C^{2^s})^{\otimes k}$: one system register and $k$ ancilla registers of $s$ qubits each. Let $C_r$ be the phase-estimation circuit $C(W(P))$ applied to the system register and to ancilla register $r$, as the identity on the others, and let
--   $$V=C_{k-1}\cdots C_1C_0$$
--   (register $0$ first; $V=\mathrm{Id}$ when $k=0$). Let $F_{\neq0}$ multiply by $-1$ every computational basis state with a non-zero phase estimate in at least one of the $k$ ancilla registers, and fix the others. The circuit of the proof of Theorem 6 is
--   $$R(P)=V^\dagger\cdot F_{\neq0}\cdot V:$$
--   phase estimation repeated $k$ times, the phase flip, and the phase estimation reversed. The file also names $\Pi_0$, the orthogonal projector onto the basis states whose $k$ ancilla registers are all $0$.
--
--   $R(P)$ is the paper's approximation of the reflection $\mathrm{ref}(\pi)$ about $|\pi\rangle$; Theorem 6 bounds how far it is from that reflection on $\mathcal A+\mathcal B$.
--
--   **Formalization Note** The matrix of $W(P)$ in the basis $|x\rangle|y\rangle$ is used. The ancilla index is `Fin k → Fin (2^s)`, and the all-zeros state $|0^{ks}\rangle$ is the zero function. "Reverse the phase estimation" is the conjugate transpose $V^\dagger$, which is $V^{-1}$ because $V$ is unitary. $\lceil\cdot\rceil$ is `Nat.ceil` and $\log_2$ is `Real.logb 2`; since $0<\Delta(P)\le\pi$, $s\ge1$.
-- source:
--   Magniez, Nayak, Roland, Santha, Search via Quantum Walk, arXiv:quant-ph/0608026v4, p. 9, proof of Theorem 6 (description of the circuit R(P), s = ⌈log2(2π/∆(P))⌉)

import Mathlib
import Definitions.Def_QuantumWalkSearch_PhaseReflection_Walk
import Definitions.Def_QuantumWalkSearch_PhaseReflection_PhaseEstimation
noncomputable section

namespace QuantumWalkSearch.PhaseReflection

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The matrix of the quantum walk `W(P)` in the computational basis `|x⟩|y⟩` of `ℂ^{X×X}`. -/
def walkMatrix (P : Matrix X X ℝ) (πd : X → ℝ) : Matrix (X × X) (X × X) ℂ :=
  Matrix.toEuclideanLin.symm (walk P πd)

/-- The number of ancilla qubits per phase estimation, `s = ⌈log₂(2π/Δ)⌉` (proof of Theorem 6,
p. 9), for a phase gap `Δ`. -/
def precision (Δ : ℝ) : ℕ :=
  ⌈Real.logb 2 (2 * Real.pi / Δ)⌉₊

/-- A circuit `C` on `ℂ^ι ⊗ ℂ^{2^s}` applied to the shared system register and to ancilla
register `r` of `ℂ^ι ⊗ (ℂ^{2^s})^{⊗k}` (index `ι × (Fin k → Fin (2^s))`), acting as the identity
on the other `k − 1` ancilla registers. -/
def onRegister {ι : Type*} {s k : ℕ} (C : Matrix (ι × Fin (2 ^ s)) (ι × Fin (2 ^ s)) ℂ)
    (r : Fin k) :
    Matrix (ι × (Fin k → Fin (2 ^ s))) (ι × (Fin k → Fin (2 ^ s))) ℂ :=
  fun p q => if (∀ r' : Fin k, r' ≠ r → p.2 r' = q.2 r') then C (p.1, p.2 r) (q.1, q.2 r) else 0

/-- The `k`-fold repeated phase estimation `V = C_{k−1} ⋯ C_1 C_0`, where `C_r` is the circuit
`C(U)` applied to the system register and the `r`-th `s`-qubit ancilla register (register `0`
first). For `k = 0` it is the identity. -/
def repeatedPhaseEstimation {ι : Type*} [Fintype ι] [DecidableEq ι] (U : Matrix ι ι ℂ)
    (s k : ℕ) :
    Matrix (ι × (Fin k → Fin (2 ^ s))) (ι × (Fin k → Fin (2 ^ s))) ℂ :=
  ((List.finRange k).map fun r => onRegister (phaseEstimation U s) r).reverse.prod

/-- The phase flip of the proof of Theorem 6: multiply by `−1` every computational basis state
with a non-zero phase estimate in at least one of the `k` ancilla registers. -/
def flipNonzero {ι : Type*} [DecidableEq ι] (s k : ℕ) :
    Matrix (ι × (Fin k → Fin (2 ^ s))) (ι × (Fin k → Fin (2 ^ s))) ℂ :=
  Matrix.diagonal fun p => if p.2 = 0 then 1 else -1

/-- The orthogonal projector onto the basis states whose `k` ancilla registers are all `0`. -/
def zeroAncillaProj {ι : Type*} [DecidableEq ι] (s k : ℕ) :
    Matrix (ι × (Fin k → Fin (2 ^ s))) (ι × (Fin k → Fin (2 ^ s))) ℂ :=
  Matrix.diagonal fun p => if p.2 = 0 then 1 else 0

/-- The circuit `R(P) = V† · F_{≠0} · V` of the proof of Theorem 6 (p. 9): `V` is the phase
estimation `C(W(P))` with `s = ⌈log₂(2π/Δ(P))⌉` ancilla qubits, repeated on `k` ancilla registers;
`F_{≠0}` flips the phase of the basis states with a non-zero estimate in some register; `V†`
reverses the phase estimation. -/
def reflectionCircuit (P : Matrix X X ℝ) (πd : X → ℝ) (k : ℕ) :
    Matrix ((X × X) × (Fin k → Fin (2 ^ precision (phaseGap P πd))))
      ((X × X) × (Fin k → Fin (2 ^ precision (phaseGap P πd)))) ℂ :=
  let V := repeatedPhaseEstimation (walkMatrix P πd) (precision (phaseGap P πd)) k
  V.conjTranspose * flipNonzero (precision (phaseGap P πd)) k * V

end QuantumWalkSearch.PhaseReflection


