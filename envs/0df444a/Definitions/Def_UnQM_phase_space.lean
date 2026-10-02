-- Prove2me | Definitions.Def_UnQM_phase_space
-- name    : UnQM_phase_space
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-02T05:23:50.776523+00:00
-- url     : https://prove2.me/theorems/9776c2f1-1074-499b-bc38-964c925cfb7d
-- title:
--   Phase-space setting: $\gamma_0$, Hamiltonian, skew-Hamiltonian and symplectic matrices
-- statement:
--   This definition file fixes the linear-algebraic setting of Sections IV–VI of Baumgarten's paper. Throughout, $n \ge 0$ is the number of degrees of freedom and phase-space vectors are $\psi = (q_1, p_1, q_2, p_2, \dots, q_n, p_n)^T \in \mathbb R^{2n}$.
--
--   1. The $2\times 2$ symplectic unit matrix is
--   $$\eta_0 = \begin{pmatrix} 0 & 1 \\ -1 & 0 \end{pmatrix}.$$
--   2. The **symplectic unit matrix (SUM)** for $n$ degrees of freedom is the Kronecker product $\gamma_0 = \mathbf 1_n \otimes \eta_0$, a real $2n \times 2n$ matrix.
--   3. A real $2n\times 2n$ matrix $M$ is **Hamiltonian** if $M = \gamma_0 A$ for some symmetric matrix $A$.
--   4. A real $2n\times 2n$ matrix $C$ is **skew-Hamiltonian** if $C = \gamma_0 B$ for some skew-symmetric matrix $B$ ($B^T = -B$).
--   5. A real $2n\times 2n$ matrix $M$ is **symplectic** if $M\gamma_0 M^T = \gamma_0$.
--   6. For a matrix of second moments $\Sigma$, the **autocorrelation matrix** is $S = \Sigma\,\gamma_0^T$.
--
--   These notions are shared by every statement of the mission.
--
--   **Formalization Note** Indices of $2n\times 2n$ matrices are pairs $(i, b)$ with $i \in \{0,\dots,n-1\}$ and $b \in \{0, 1\}$ ($b = 0$ for $q_i$, $b=1$ for $p_i$), so $\gamma_0$ is literally the Kronecker product $\mathbf 1_n \otimes \eta_0$. For $n = 0$ all matrices are empty.
-- source:
--   C. Baumgarten, How to (Un-) Quantum Mechanics, arXiv:1810.06981v2 [physics.gen-ph] (v2 dated June 10, 2025), https://arxiv.org/abs/1810.06981, Sec. IV pp. 13–14 (Eqs. 32, 33, text before Eq. 36), Sec. V p. 15 (text before Eq. 42), Sec. VI p. 17 (Eqs. 50, 53)

import Mathlib

namespace UnQuantumMechanics

open Matrix

/-- Phase-space coordinate indices for `n` degrees of freedom: the pair `(i, 0)` is the
coordinate `qᵢ` and `(i, 1)` is the conjugate momentum `pᵢ`, so a phase-space vector is
`ψ = (q₁, p₁, q₂, p₂, …, qₙ, pₙ)ᵀ` (Baumgarten, Sec. IV, after Eq. 33). -/
abbrev PhaseIdx (n : ℕ) : Type := Fin n × Fin 2

/-- The `2 × 2` symplectic unit matrix `η₀ = [[0, 1], [-1, 0]]` (Eq. 32). -/
def eta0 : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; -1, 0]

/-- The symplectic unit matrix (SUM) `γ₀ = 1ₙ ⊗ η₀` for `n` degrees of freedom (Eq. 33),
built as a Kronecker product. -/
def gamma0 (n : ℕ) : Matrix (PhaseIdx n) (PhaseIdx n) ℝ :=
  Matrix.kroneckerMap (· * ·) (1 : Matrix (Fin n) (Fin n) ℝ) eta0

/-- A real `2n × 2n` matrix `M` is *Hamiltonian* if it can be written `M = γ₀ A` with `A`
symmetric (Sec. IV, text before Eq. 36). -/
def IsHamiltonianMatrix (n : ℕ) (M : Matrix (PhaseIdx n) (PhaseIdx n) ℝ) : Prop :=
  ∃ A : Matrix (PhaseIdx n) (PhaseIdx n) ℝ, A.IsSymm ∧ M = gamma0 n * A

/-- A real `2n × 2n` matrix `C` is *skew-Hamiltonian* if it can be written `C = γ₀ B` with
`B` skew-symmetric, `Bᵀ = -B` (Eq. 53). -/
def IsSkewHamiltonianMatrix (n : ℕ) (C : Matrix (PhaseIdx n) (PhaseIdx n) ℝ) : Prop :=
  ∃ B : Matrix (PhaseIdx n) (PhaseIdx n) ℝ, Bᵀ = -B ∧ C = gamma0 n * B

/-- A real `2n × 2n` matrix `M` is *symplectic* if `M γ₀ Mᵀ = γ₀` (Eq. 50). -/
def IsSymplecticMatrix (n : ℕ) (M : Matrix (PhaseIdx n) (PhaseIdx n) ℝ) : Prop :=
  M * gamma0 n * Mᵀ = gamma0 n

/-- The "autocorrelation matrix" `S = Σ γ₀ᵀ` attached to a matrix of second moments `Σ`
(Sec. V, text before Eq. 42). -/
def autocorr (n : ℕ) (Sig : Matrix (PhaseIdx n) (PhaseIdx n) ℝ) :
    Matrix (PhaseIdx n) (PhaseIdx n) ℝ :=
  Sig * (gamma0 n)ᵀ

end UnQuantumMechanics


