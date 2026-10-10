-- Prove2me | Definitions.Def_QCQPTightness_MultHull_Kron
-- name    : QCQPTightness_MultHull_Kron
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T18:21:57.625984+00:00
-- url     : https://prove2.me/theorems/0b05a5a2-debc-4edb-b864-8629d41f9571
-- title:
--   §3 and §6, pp. 11, 29–30 — y ⊗ z, an explicit representation A_i = I_k ⊗ 𝔸_i, 𝔸(γ), and the system (17)
-- statement:
--   Fix $N = kn$ and the block convention of Definition 3. This module introduces the objects used in §6 of the paper.
--
--   1. For $y\in\mathbb R^k$ and $z\in\mathbb R^n$, the vector $y\otimes z\in\mathbb R^N$ has $j$-th block $y_j z$.
--   2. An **explicit representation** of a QCQP consists of symmetric $\mathbb A_0,\dots,\mathbb A_m\in\mathbb S^n$ with $A_i = I_k\otimes\mathbb A_i$ for every $i\in[\![0,m]\!]$.
--   3. For $\gamma\in\mathbb R^m$, $\mathbb A(\gamma) := \mathbb A_0 + \sum_{i=1}^m\gamma_i\mathbb A_i$ (p. 11).
--   4. Given such a representation, a triple $(x, t, Z)$ with $x\in\mathbb R^N$, $t\in\mathbb R$, $Z\in\mathbb S^n$ **satisfies (17)** if
--
--   $$\begin{cases} q_0(x) + \langle\mathbb A_0, Z\rangle \le 2t\\ q_i(x) + \langle\mathbb A_i, Z\rangle\le 0, & i\in[\![m_I]\!]\\ q_i(x) + \langle\mathbb A_i, Z\rangle = 0, & i\in[\![m_I+1,m]\!]\\ Z\succeq 0,\end{cases}$$
--
--   where $\langle\mathbb A, Z\rangle = \operatorname{tr}(\mathbb A Z)$.
--
--   System (17) is the dual of $\sup_\gamma\{q(\gamma,x) : \mathbb A(\gamma)\succeq 0,\ \gamma_i\ge0\ \forall i\in[\![m_I]\!]\}$ written as a feasibility system in $(x,t,Z)$; the proof of Theorem 7 inducts on $\operatorname{rank}(Z)$ over its solutions.
--
--   **Formalization Note** Constraint indices are shifted to $\{0,\dots,m-1\}$ as in the QCQP module. $Z\succeq0$ is Mathlib's `PosSemidef`, which includes symmetry.
-- source:
--   arXiv:1911.09195v3, p. 11 (𝔸(γ)), §6, proof of Theorem 7, pp. 29–30, (17) and (18)

import Mathlib
import Definitions.Def_QCQPTightness_MultHull_QCQP
import Definitions.Def_QCQPTightness_MultHull_Mult

noncomputable section

namespace QCQPTightness.MultHull

open Matrix

/-- The Kronecker vector `y ⊗ z ∈ ℝ^N` (`N = kn`) of `y ∈ ℝ^k`, `z ∈ ℝ^n`: its `j`-th block of
`n` entries is `y_j z`, with the block identification `blockEquiv` of `Mult`. -/
def kronVec {k n N : ℕ} (h : k * n = N) (y : Fin k → ℝ) (z : Fin n → ℝ) : Fin N → ℝ :=
  fun i => y ((blockEquiv h).symm i).1 * z ((blockEquiv h).symm i).2

namespace QCQP

variable {N m : ℕ} (P : QCQP N m)

/-- An explicit representation `A_i = I_k ⊗ 𝔸_i`, `i ∈ ⟦0, m⟧`, with `𝔸_i ∈ 𝕊^n` and `N = kn`
(Definition 3, p. 11). -/
def IsKronRep {k n : ℕ} (h : k * n = N) (𝔸₀ : Matrix (Fin n) (Fin n) ℝ)
    (𝔸 : Fin m → Matrix (Fin n) (Fin n) ℝ) : Prop :=
  𝔸₀.IsSymm ∧ (∀ i, (𝔸 i).IsSymm) ∧
    P.A₀ = Matrix.reindex (blockEquiv h) (blockEquiv h) (kronId k 𝔸₀) ∧
    ∀ i, P.A i = Matrix.reindex (blockEquiv h) (blockEquiv h) (kronId k (𝔸 i))

/-- The system (17) (p. 29) in `(x, t, Z)`, `Z ∈ 𝕊^n`:
`q₀(x) + ⟨𝔸₀, Z⟩ ≤ 2t`, `q_i(x) + ⟨𝔸_i, Z⟩ ≤ 0` (inequalities), `= 0` (equalities), `Z ⪰ 0`,
with `⟨𝔸, Z⟩ = tr(𝔸Z)`. -/
def IsDualCert {n : ℕ} (𝔸₀ : Matrix (Fin n) (Fin n) ℝ) (𝔸 : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (x : Fin N → ℝ) (t : ℝ) (Z : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  Z.PosSemidef ∧ P.q₀ x + (𝔸₀ * Z).trace ≤ 2 * t ∧
    ∀ i, (P.IsIneq i → P.q i x + (𝔸 i * Z).trace ≤ 0) ∧
      (¬ P.IsIneq i → P.q i x + (𝔸 i * Z).trace = 0)

end QCQP

/-- `𝔸(γ) = 𝔸₀ + Σ γ_i 𝔸_i` (p. 11). -/
def kronAγ {m n : ℕ} (𝔸₀ : Matrix (Fin n) (Fin n) ℝ) (𝔸 : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (γ : Fin m → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  𝔸₀ + ∑ i, γ i • 𝔸 i

end QCQPTightness.MultHull


