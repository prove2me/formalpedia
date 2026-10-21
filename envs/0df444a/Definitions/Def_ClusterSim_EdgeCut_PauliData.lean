-- Prove2me | Definitions.Def_ClusterSim_EdgeCut_PauliData
-- name    : ClusterSim_EdgeCut_PauliData
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T05:52:27.664984+00:00
-- url     : https://prove2.me/theorems/74353880-35ca-4e2b-8386-01fef906a967
-- title:
--   The Pauli matrices and the eight measure-and-prepare triples (O_i, ρ_i, c_i) of eqs. (12)–(19), and the maps Φ_i of eq. (20) (p. 8)
-- statement:
--   The Pauli matrices are
--   $$I=\begin{pmatrix}1&0\\0&1\end{pmatrix},\quad X=\begin{pmatrix}0&1\\1&0\end{pmatrix},\quad Y=\begin{pmatrix}0&-i\\ i&0\end{pmatrix},\quad Z=\begin{pmatrix}1&0\\0&-1\end{pmatrix}.$$
--   With $|\pm\rangle=(|0\rangle\pm|1\rangle)/\sqrt2$ and $|\pm i\rangle=(|0\rangle\pm i|1\rangle)/\sqrt2$, the eight triples of eqs. (12)–(19) are
--
--   | $i$ | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 |
--   |---|---|---|---|---|---|---|---|---|
--   | $O_i$ | $I$ | $I$ | $X$ | $X$ | $Y$ | $Y$ | $Z$ | $Z$ |
--   | $\rho_i$ | $\lvert0\rangle\langle0\rvert$ | $\lvert1\rangle\langle1\rvert$ | $\lvert+\rangle\langle+\rvert$ | $\lvert-\rangle\langle-\rvert$ | $\lvert+i\rangle\langle+i\rvert$ | $\lvert-i\rangle\langle-i\rvert$ | $\lvert0\rangle\langle0\rvert$ | $\lvert1\rangle\langle1\rvert$ |
--   | $c_i$ | $+\tfrac12$ | $+\tfrac12$ | $+\tfrac12$ | $-\tfrac12$ | $+\tfrac12$ | $-\tfrac12$ | $+\tfrac12$ | $-\tfrac12$ |
--
--   Here $\rho_i$ is an eigenprojector of the Pauli observable $O_i$ with eigenvalue $2c_i$. For each $i$, the measure-and-prepare map of eq. (20) is
--   $$\Phi_i(A)=\operatorname{Tr}(AO_i)\,\rho_i\qquad(A\in\mathbb C^{2\times2}),$$
--   which measures the observable $O_i$ and prepares the state $\rho_i$.
--
--   These data are the coefficients, observables and states of Lemma 1; every cut of an edge in the mission uses them.
--
--   **Formalization Note** The eight cases are indexed by `Fin 8`; Lean's index $i$ is the paper's $i+1$. The projectors are $|\psi\rangle\langle\psi|$ = `vecMulVec ψ (star ψ)` of the explicit kets, the coefficients are real numbers.
-- source:
--   Peng, Harrow, Ozols & Wu, Simulating Large Quantum Circuits on a Small Quantum Computer, arXiv:1904.00102v2, p. 8, proof of Lemma 1, eqs. (12)–(20)

import Mathlib

namespace ClusterSim.EdgeCut

open Matrix Complex

noncomputable section

/-- The Pauli matrix `I` (p. 8). -/
def pauliI : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, 1]
/-- The Pauli matrix `X` (p. 8). -/
def pauliX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
/-- The Pauli matrix `Y` (p. 8). -/
def pauliY : Matrix (Fin 2) (Fin 2) ℂ := !![0, -I; I, 0]
/-- The Pauli matrix `Z` (p. 8). -/
def pauliZ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- `|0⟩`. -/
def ket0 : Fin 2 → ℂ := ![1, 0]
/-- `|1⟩`. -/
def ket1 : Fin 2 → ℂ := ![0, 1]
/-- `|+⟩ = (|0⟩ + |1⟩)/√2`. -/
def ketPlus : Fin 2 → ℂ := ![1 / (Real.sqrt 2 : ℂ), 1 / (Real.sqrt 2 : ℂ)]
/-- `|−⟩ = (|0⟩ − |1⟩)/√2`. -/
def ketMinus : Fin 2 → ℂ := ![1 / (Real.sqrt 2 : ℂ), -1 / (Real.sqrt 2 : ℂ)]
/-- `|+i⟩ = (|0⟩ + i|1⟩)/√2`. -/
def ketPlusI : Fin 2 → ℂ := ![1 / (Real.sqrt 2 : ℂ), I / (Real.sqrt 2 : ℂ)]
/-- `|−i⟩ = (|0⟩ − i|1⟩)/√2`. -/
def ketMinusI : Fin 2 → ℂ := ![1 / (Real.sqrt 2 : ℂ), -I / (Real.sqrt 2 : ℂ)]

/-- The projector `|ψ⟩⟨ψ|`. -/
def proj (ψ : Fin 2 → ℂ) : Matrix (Fin 2) (Fin 2) ℂ := vecMulVec ψ (star ψ)

/-- The observables `O_1, …, O_8 = I, I, X, X, Y, Y, Z, Z` of eqs. (12)–(19), p. 8.
Lean index `i : Fin 8` is the paper's `i + 1`. -/
def pauli : Fin 8 → Matrix (Fin 2) (Fin 2) ℂ :=
  ![pauliI, pauliI, pauliX, pauliX, pauliY, pauliY, pauliZ, pauliZ]

/-- The states `ρ_1, …, ρ_8 = |0⟩⟨0|, |1⟩⟨1|, |+⟩⟨+|, |−⟩⟨−|, |+i⟩⟨+i|, |−i⟩⟨−i|, |0⟩⟨0|, |1⟩⟨1|`
of eqs. (12)–(19), p. 8 (Lean index `i` is the paper's `i + 1`). -/
def eigProj : Fin 8 → Matrix (Fin 2) (Fin 2) ℂ :=
  ![proj ket0, proj ket1, proj ketPlus, proj ketMinus, proj ketPlusI, proj ketMinusI,
    proj ket0, proj ket1]

/-- The coefficients `c_1, …, c_8 = +½, +½, +½, −½, +½, −½, +½, −½` of eqs. (12)–(19), p. 8
(Lean index `i` is the paper's `i + 1`). -/
def coef : Fin 8 → ℝ := ![1 / 2, 1 / 2, 1 / 2, -1 / 2, 1 / 2, -1 / 2, 1 / 2, -1 / 2]

/-- The measure-and-prepare map of eq. (20): `Φ_i(A) = Tr(A O_i) ρ_i`. -/
def measPrep (i : Fin 8) (A : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (A * pauli i).trace • eigProj i

end

end ClusterSim.EdgeCut


