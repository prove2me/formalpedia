-- Prove2me | Definitions.Def_GapAgnosticGS_HidEnv
-- name    : GapAgnosticGS_HidEnv
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:28:46.75667+00:00
-- url     : https://prove2.me/theorems/7a345278-25ba-4846-8ae8-ddaa5ae7f25b
-- title:
--   Hidden-basis quantum bandit environment (HidQMAB, Definition 1.4)
-- statement:
--   Let $I=\mathbb C^n$ be the selector register and $A$ an arm register with a known state $|0\rangle_A$ and a known orthogonal projector $\Pi$ on $A$ (the reward-one outcome). A **hidden-basis environment** is a unitary $E$ on $I\otimes A$ together with an orthonormal basis $\{|\phi_j\rangle\}$ of $I$ and unit arm states $|\mathrm{arm}_j\rangle\in A$ such that
--
--   $$E\,|\phi_j\rangle_I|0\rangle_A=|\phi_j\rangle_I|\mathrm{arm}_j\rangle_A\qquad(j=0,\dots,n-1).$$
--
--   The basis and the arm states are unknown to the learner, who may only use $E$ and $E^\dagger$ (controlled) and the known $\Pi$. Ground-state preparation is the special case of Lemma 3.1.
--
--   **Formalization Note** $|0\rangle_A$ and $\Pi$ are parameters (known data); the structure requires $\Pi$ to be Hermitian and idempotent. Arms are indexed from $0$.
-- source:
--   Heidari–Moharrami–Tavakoli–Zhang, Gap-Agnostic Ground-State Preparation via Quantum Bandits, manuscript (STOC 2027 submission, sha256 bd767ba1…c57acc), Definition 1.4 (HidQMAB), p.4 (PDF p.5)

import Definitions.Def_QAlgorithms_Defs_Hamiltonian
open QAlgorithms

namespace GapAgnosticGS

/-- Heidari–Moharrami–Tavakoli–Zhang, *Gap-Agnostic Ground-State Preparation via Quantum Bandits*, manuscript (STOC 2027 submission, sha256 bd767ba1…c57acc), Definition 1.4 (HidQMAB), p.4 (PDF p.5): "Let I be an n-dimensional selector register
and A an arm register. A hidden-basis environment is a unitary E such that
E |ϕ_j⟩_I |0⟩_A = |ϕ_j⟩_I |arm_j⟩_A, j ∈ {1, …, n}, for an unknown orthonormal basis {|ϕ_j⟩} and
unknown normalized arm states |arm_j⟩. A known projector Π on A represents the reward-one
outcome".

A hidden-basis environment with `n` arms on the arm register `A`, with the known state
`|0⟩_A = |a₀⟩` and the known projector `Prj` (the paper's `Π`): the unitary `E` on `Fin n × A`,
the hidden orthonormal basis `φ` of `ℂⁿ` and the unit arm states `arm j`, with
`E (φ j ⊗ |a₀⟩) = φ j ⊗ arm j`.

**Formalization Note.** `a₀` and `Prj` are parameters (they are known to the learner); `proj`
requires `Prj` to be an orthogonal projector (Hermitian and idempotent), so for any other `Prj`
there is no environment. Arms are indexed `0, …, n − 1` (0-based). -/
structure HidEnv (n : ℕ) (A : Type) [Fintype A] [DecidableEq A] (a₀ : A) (Prj : Matrix A A ℂ) where
  E : Matrix (Fin n × A) (Fin n × A) ℂ
  E_unitary : E ∈ Matrix.unitaryGroup (Fin n × A) ℂ
  φ : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n))
  arm : Fin n → EuclideanSpace ℂ A
  arm_norm : ∀ j, ‖arm j‖ = 1
  proj : Prj.IsHermitian ∧ Prj * Prj = Prj
  maps : ∀ j, act E (tensorVec (φ j) (ket a₀)) = tensorVec (φ j) (arm j)

end GapAgnosticGS


