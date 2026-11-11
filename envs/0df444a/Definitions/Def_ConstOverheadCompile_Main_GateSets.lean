-- Prove2me | Definitions.Def_ConstOverheadCompile_Main_GateSets
-- name    : ConstOverheadCompile_Main_GateSets
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T03:58:22.365914+00:00
-- url     : https://prove2.me/theorems/a29e201f-7a2d-439a-b00b-02032773c695
-- title:
--   The rotation $R(\theta)$, the gate sets $\mathcal G=\{H,T,\mathrm{CNOT}\}$, $\mathcal S_D$, arbitrary one- and two-qubit gates, and Toffoli
-- statement:
--   For a real angle $\theta$, the single-qubit **Z-rotation** is
--   $$R(\theta)=\begin{pmatrix}1&0\\0&e^{i\theta}\end{pmatrix}.$$
--   It is not the symmetric rotation $R_z(\theta)=\mathrm{diag}(e^{-i\theta/2},e^{i\theta/2})$, which differs from it by a global phase.
--
--   The following gate sets are fixed.
--
--   1. The discrete gate set $\mathcal G=\{H,T,\mathrm{CNOT}\}$, with $H=\tfrac1{\sqrt2}\begin{pmatrix}1&1\\1&-1\end{pmatrix}$, $T=\mathrm{diag}(1,e^{i\pi/4})$, and CNOT controlled on its first qubit. A gate of a circuit may act on any ordered tuple of distinct wires, so CNOT may be applied with any control and any target. Nothing else, in particular no Pauli, $S$, $T^\dagger$ or Toffoli gate, is an elementary gate of $\mathcal G$.
--   2. The **arbitrary one- and two-qubit gates**: all unitary matrices on one qubit or on two qubits.
--   3. For a positive integer $D$, the **grid set** $\mathcal S_D=\{R(2\pi j/D):0\le j\le D-1\}$.
--   4. The set $\{H,\mathrm{CNOT}\}\cup\{R(\theta):\theta\in(0,2\pi)\}$ into which arbitrary gates are decomposed.
--   5. The Toffoli gate $|a,b,t\rangle\mapsto|a,b,t\oplus(a\wedge b)\rangle$, controls on its first two qubits.
--
--   These are the gate sets in which the paper's input circuits, intermediate circuits and output circuits are expressed.
--
--   **Formalization Note** Gates, gate applications on wires and circuits are the published `QAlgorithms` layer. Single-qubit matrices are indexed by `Bool` (`false` is $|0\rangle$). $\mathcal S_D$ is defined for every natural $D$ (it is empty for $D=0$; no statement uses that case).
-- source:
--   Chenyi Zhang, Xinyu Tan, Robin Kothari, David Gosset, Craig Gidney, Quantum circuit compilation with constant overhead, STOC 2027 submission #397 (October 2026), source.pdf SHA-256 b848604016de1821f5f693c59f328e0b2a9e535bca0b37bb664e6f40dbe3681f, p.1 Eq. (1); p.2 (definition of R(θ) before Eq. (4)); p.4 and p.10 (decomposition gate set); p.8 Eq. (18); p.6 Figure 1 (Toffoli)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Circuit

namespace ConstOverheadCompile.Main

open QAlgorithms

/-- p.2 (before Eq. (4)): the Z-rotation `R(θ) = diag(1, e^{iθ})` on one qubit, as a matrix
indexed by `Bool` (`false` = `|0⟩`). This is not `R_z(θ) = diag(e^{-iθ/2}, e^{iθ/2})` and not
`QAlgorithms.rotR`. -/
noncomputable def rot (θ : ℝ) : Matrix Bool Bool ℂ :=
  Matrix.diagonal fun a => if a then Complex.exp ((θ : ℂ) * Complex.I) else 1

/-- Eq. (1), p.1: the discrete gate set `𝒢 = {H, T, CNOT}`. CNOT has its control on gate
wire 0; a `GateApp` may place it on any ordered pair of distinct wires. Nothing else is an
elementary gate of an output circuit. -/
def CliffordT : Set Gate :=
  {Gate.ofMatrix1 hadamard, Gate.ofMatrix1 gateT, Gate.ofMatrix2 cnot}

/-- p.1, Theorem 1: the arbitrary one- and two-qubit gates, i.e. every unitary matrix on one or
on two qubits. -/
def ArbGates : Set Gate :=
  {g | (g.arity = 1 ∨ g.arity = 2) ∧ g.IsUnitary}

/-- Eq. (18), p.8: the grid set `𝒮_D = {R(2πj/D) : 0 ≤ j ≤ D − 1}` of single-qubit rotations. -/
def gridGates (D : ℕ) : Set Gate :=
  {g | ∃ j : ℕ, j < D ∧ g = Gate.ofMatrix1 (rot (2 * Real.pi * (j : ℝ) / (D : ℝ)))}

/-- p.4 and p.10: the gates CNOT, `H` and the Z-rotations `R(θ)` with `θ ∈ (0, 2π)`, into which
every one- or two-qubit gate is decomposed. -/
def HCnotRotGates : Set Gate :=
  {Gate.ofMatrix1 hadamard, Gate.ofMatrix2 cnot} ∪
    {g | ∃ θ : ℝ, θ ∈ Set.Ioo 0 (2 * Real.pi) ∧ g = Gate.ofMatrix1 (rot θ)}

/-- Figure 1 (right), p.6: the Toffoli gate on three qubits, controls on gate wires 0 and 1,
target on gate wire 2: `|a, b, t⟩ ↦ |a, b, t ⊕ (a ∧ b)⟩`. Row index = output, column = input. -/
def toffoliMat : Matrix (Qubits 3) (Qubits 3) ℂ :=
  Matrix.of fun y z => if y 0 = z 0 ∧ y 1 = z 1 ∧ y 2 = xor (z 2) (z 0 && z 1) then 1 else 0

/-- The Toffoli gate as an arity-3 gate. -/
def toffoli : Gate := ⟨3, toffoliMat⟩

end ConstOverheadCompile.Main


