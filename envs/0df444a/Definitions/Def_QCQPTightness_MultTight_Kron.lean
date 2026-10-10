-- Prove2me | Definitions.Def_QCQPTightness_MultTight_Kron
-- name    : QCQPTightness_MultTight_Kron
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T18:21:24.461235+00:00
-- url     : https://prove2.me/theorems/ccf53307-705c-4a4f-8eb0-3362fe009a62
-- title:
--   §6 and App. B, pp. 30, 35 — y ⊗ z, an explicit representation A_i = I_k ⊗ 𝔸_i, the hyperplane H and the system (19)
-- statement:
--   Objects used in the proof of Theorem 8 of Wang–Kılınç-Karzan.
--
--   1. For $y\in\mathbb R^k$ and $z\in\mathbb R^n$ with $N = kn$, the vector $y\otimes z\in\mathbb R^N$ has $j$-th block of $n$ entries equal to $y_j z$.
--   2. An **explicit representation** of a QCQP is a choice of symmetric $\mathbb A_0,\dots,\mathbb A_m\in\mathbb S^n$ with $A_i = I_k\otimes\mathbb A_i$ for all $i\in[\![0,m]\!]$.
--   3. The **hyperplane** of Theorem 8 is
--   $$H = \{(x,t)\in\mathbb R^{N+1} : 2t = \mathrm{Opt}_{\mathrm{SDP}}\}.$$
--   4. Given such a representation, a triple $(\hat x,\hat t, Z)$ with $Z\in\mathbb S^n$ **satisfies (19)** if
--   $$q_0(\hat x)+\langle\mathbb A_0,Z\rangle = 2\hat t,\quad q_i(\hat x)+\langle\mathbb A_i,Z\rangle\le 0\ (i\in[\![m_I]\!]),\quad q_i(\hat x)+\langle\mathbb A_i,Z\rangle = 0\ (i\in[\![m_I+1,m]\!]),\quad Z\succeq 0.$$
--
--   System (19) is the optimality system of the dual of the inner maximization $\sup_{\gamma\in\Gamma} q(\gamma,\hat x)$ written in the small matrices $\mathbb A_i$.
--
--   **Formalization Note** $y\otimes z$ uses the same block identification as the definition of multiplicity. $H$ compares $2t$ with the `EReal` value $\mathrm{Opt}_{\mathrm{SDP}}$, so $H$ is empty when $\mathrm{Opt}_{\mathrm{SDP}} = \pm\infty$. $\langle\mathbb A, Z\rangle$ is `(𝔸 * Z).trace`; $Z\succeq 0$ is `Z.PosSemidef`, which includes symmetry. The argument `h : k * n = N` of the system only fixes $k$.
-- source:
--   arXiv:1911.09195v3, §6 p. 30 (Theorem 8, H; y ⊗ z), App. B p. 35 ((19))

import Mathlib
import Definitions.Def_QCQPTightness_MultTight_QCQP
import Definitions.Def_QCQPTightness_MultTight_Mult

noncomputable section

namespace QCQPTightness.MultTight

open Matrix

/-- The vector `y ⊗ z ∈ ℝ^N` for `y ∈ ℝ^k`, `z ∈ ℝ^n`, `N = kn`: its `j`-th block of `n` entries
is `y_j z`, with the block convention of `blockEquiv` (arXiv:1911.09195v3, §6, p. 30). -/
def kronVec {k n N : ℕ} (h : k * n = N) (y : Fin k → ℝ) (z : Fin n → ℝ) : Fin N → ℝ :=
  fun i => y ((blockEquiv h).symm i).1 * z ((blockEquiv h).symm i).2

namespace QCQP

variable {N m : ℕ} (P : QCQP N m)

/-- An explicit representation `A_i = I_k ⊗ 𝔸_i` (`i ∈ ⟦0, m⟧`) with symmetric `𝔸_i ∈ 𝕊^n`,
`N = kn` (Definition 3, p. 11). -/
def IsKronRep {k n : ℕ} (h : k * n = N) (𝔸₀ : Matrix (Fin n) (Fin n) ℝ)
    (𝔸 : Fin m → Matrix (Fin n) (Fin n) ℝ) : Prop :=
  𝔸₀.IsSymm ∧ (∀ i, (𝔸 i).IsSymm) ∧
    P.A₀ = Matrix.reindex (blockEquiv h) (blockEquiv h) (kronId k 𝔸₀) ∧
    ∀ i, P.A i = Matrix.reindex (blockEquiv h) (blockEquiv h) (kronId k (𝔸 i))

/-- The hyperplane `H = {(x, t) ∈ ℝ^{N+1} : 2t = Opt_SDP}` of Theorem 8 (p. 30). -/
def hyperplaneH : Set ((Fin N → ℝ) × ℝ) := {p | ((2 * p.2 : ℝ) : EReal) = P.OptSDP}

/-- The system (19) (App. B, p. 35) in `(x̂, t̂, Z)`, `Z ∈ 𝕊^n`:
`q₀(x̂) + ⟨𝔸₀, Z⟩ = 2t̂`, `q_i(x̂) + ⟨𝔸_i, Z⟩ ≤ 0` (inequalities), `= 0` (equalities), `Z ⪰ 0`. -/
def IsDualCert19 {k n : ℕ} (_h : k * n = N) (𝔸₀ : Matrix (Fin n) (Fin n) ℝ)
    (𝔸 : Fin m → Matrix (Fin n) (Fin n) ℝ) (x : Fin N → ℝ) (t : ℝ)
    (Z : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  Z.PosSemidef ∧ P.q₀ x + (𝔸₀ * Z).trace = 2 * t ∧
    ∀ i, (P.IsIneq i → P.q i x + (𝔸 i * Z).trace ≤ 0) ∧
      (¬ P.IsIneq i → P.q i x + (𝔸 i * Z).trace = 0)

end QCQP

end QCQPTightness.MultTight


