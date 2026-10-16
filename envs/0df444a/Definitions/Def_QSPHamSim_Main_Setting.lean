-- Prove2me | Definitions.Def_QSPHamSim_Main_Setting
-- name    : QSPHamSim_Main_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T21:25:33.941908+00:00
-- url     : https://prove2.me/theorems/b05f47b6-d2e9-4a9a-99cf-1fad08861c44
-- title:
--   Eqs. (1)–(6) — rotations, Fourier series, and signal operators
-- statement:
--   For a qubit, let $\sigma_x,\sigma_y,\sigma_z$ be the standard Pauli matrices and define the rotation
--   $$
--   R_\phi(\theta)=\exp\!\left[-i\frac{\theta}{2}(\sigma_x\cos\phi+\sigma_y\sin\phi)\right].
--   $$
--   For $N$ phases $\phi_1,\ldots,\phi_N$, the signal sequence is $V_\phi(\theta)=R_{\phi_N}(\theta)\cdots R_{\phi_1}(\theta)$. Four real functions $A,B,C,D$ are extracted from its matrix entries through the Pauli expansion $V_\phi=A I+iB\sigma_z+iC\sigma_x+iD\sigma_y$.
--
--   The definition also gives the normalized states $|\pm\rangle=(|0\rangle\pm|1\rangle)/\sqrt2$, cosine and sine series of degree at most $M$, and a unitary eigenbasis $|u_l\rangle$ with eigenphases $\theta_l$. It constructs $W=\sum_l e^{i\theta_l}|u_l\rangle\langle u_l|$, $U_\phi=\sum_lR_\phi(\theta_l)\otimes|u_l\rangle\langle u_l|$, their ordered product, the $|+\rangle$ block, and $V_{\mathrm{ideal}}=\sum_l e^{ih(\theta_l)}|u_l\rangle\langle u_l|$.
--
--   These objects supply one shared interpretation of the paper's single-qubit and operator formulas. The first tensor factor is the ancilla.
-- source:
--   Low, Chuang, Optimal Hamiltonian Simulation by Quantum Signal Processing, arXiv:1606.02685v2, pp. 1–3, Eqs. (1)–(6), Theorem 1

import Mathlib

set_option autoImplicit false

namespace QSPHamSim.Main
noncomputable section

abbrev QubitMatrix := Matrix (Fin 2) (Fin 2) ℂ

def sigmaX : QubitMatrix := !![0, 1; 1, 0]
def sigmaY : QubitMatrix := !![0, -Complex.I; Complex.I, 0]
def sigmaZ : QubitMatrix := !![1, 0; 0, -1]

def R (φ θ : ℝ) : QubitMatrix :=
  NormedSpace.exp (-(Complex.I * ((θ / 2 : ℝ) : ℂ)) •
    (Real.cos φ • sigmaX + Real.sin φ • sigmaY))

def qspSeq (N : ℕ) (φ : Fin N → ℝ) (θ : ℝ) : QubitMatrix :=
  (List.ofFn (fun k : Fin N => R (φ k) θ)).reverse.prod

def compA (M : QubitMatrix) : ℝ := ((M 0 0 + M 1 1) / 2).re
def compB (M : QubitMatrix) : ℝ := ((M 0 0 - M 1 1) / (2 * Complex.I)).re
def compC (M : QubitMatrix) : ℝ := ((M 0 1 + M 1 0) / (2 * Complex.I)).re
def compD (M : QubitMatrix) : ℝ := ((M 0 1 - M 1 0) / 2).re

def ketPlus : Fin 2 → ℂ := ![1 / ((Real.sqrt 2 : ℝ) : ℂ), 1 / ((Real.sqrt 2 : ℝ) : ℂ)]
def ketMinus : Fin 2 → ℂ := ![1 / ((Real.sqrt 2 : ℝ) : ℂ), -1 / ((Real.sqrt 2 : ℝ) : ℂ)]

def IsCosSeries (M : ℕ) (A : ℝ → ℝ) : Prop :=
  ∃ a : ℕ → ℝ, ∀ θ : ℝ,
    A θ = ∑ k ∈ Finset.range (M + 1), a k * Real.cos ((k : ℝ) * θ)

def IsSinSeries (M : ℕ) (C : ℝ → ℝ) : Prop :=
  ∃ c : ℕ → ℝ, ∀ θ : ℝ,
    C θ = ∑ k ∈ Finset.Icc 1 M, c k * Real.sin ((k : ℝ) * θ)

def proj (n : ℕ) (u : Matrix.unitaryGroup (Fin n) ℂ) (l : Fin n) :
    Matrix (Fin n) (Fin n) ℂ :=
  Matrix.vecMulVec (fun i => (u : Matrix (Fin n) (Fin n) ℂ) i l)
    (star (fun i => (u : Matrix (Fin n) (Fin n) ℂ) i l))

def W (n : ℕ) (u : Matrix.unitaryGroup (Fin n) ℂ) (θs : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℂ :=
  ∑ l, Complex.exp (((θs l : ℝ) : ℂ) * Complex.I) • proj n u l

def Uop (n : ℕ) (u : Matrix.unitaryGroup (Fin n) ℂ) (θs : Fin n → ℝ) (φ : ℝ) :
    Matrix (Fin 2 × Fin n) (Fin 2 × Fin n) ℂ :=
  ∑ l, Matrix.kronecker (R φ (θs l)) (proj n u l)

def Vop (n N : ℕ) (u : Matrix.unitaryGroup (Fin n) ℂ)
    (θs : Fin n → ℝ) (φ : Fin N → ℝ) :
    Matrix (Fin 2 × Fin n) (Fin 2 × Fin n) ℂ :=
  (List.ofFn (fun k : Fin N => Uop n u θs (φ k))).reverse.prod

def plusBlock (n : ℕ) (M : Matrix (Fin 2 × Fin n) (Fin 2 × Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  fun i j => ∑ a : Fin 2, ∑ b : Fin 2,
    star (ketPlus a) * M (a, i) (b, j) * ketPlus b

def Videal (n : ℕ) (u : Matrix.unitaryGroup (Fin n) ℂ)
    (θs : Fin n → ℝ) (h : ℝ → ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  ∑ l, Complex.exp (((h (θs l) : ℝ) : ℂ) * Complex.I) • proj n u l

end
end QSPHamSim.Main


