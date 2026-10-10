-- Prove2me | Definitions.Def_QCQPTightness_Sharp_QCQP
-- name    : QCQPTightness_Sharp_QCQP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T18:19:33.748451+00:00
-- url     : https://prove2.me/theorems/0de00fee-de1f-42b9-97cd-6019b86060b4
-- title:
--   (1)–(4), §2.1, Assumption 1, pp. 1–7 — the QCQP, its epigraph 𝒟, the Shor SDP relaxation with Opt_SDP and 𝒟_SDP, the Lagrangian data and Γ
-- statement:
--   A **quadratically constrained quadratic program** (QCQP) in $N$ variables with $m$ constraints is
--   $$
--   \mathrm{Opt} := \inf_{x\in\mathbb R^N}\big\{q_0(x) : q_i(x)\le 0,\ i\in[\![m_I]\!];\ q_i(x)=0,\ i\in[\![m_I+1,m]\!]\big\},
--   $$
--   where $q_i(x)=x^\top A_ix+2b_i^\top x+c_i$ with $A_i\in\mathbb S^N$, $b_i\in\mathbb R^N$, $c_i\in\mathbb R$, and the first $m_I$ constraints are inequalities. Its **epigraph** is $\mathcal D=\{(x,t) : q_0(x)\le 2t,\ x \text{ feasible}\}$.
--
--   With $Q_i=\begin{pmatrix}c_i & b_i^\top\\ b_i & A_i\end{pmatrix}$ and $Y=\begin{pmatrix}1 & x^\top\\ x & X\end{pmatrix}$, the **SDP relaxation** is
--   $$
--   \mathrm{Opt}_{\mathrm{SDP}} := \inf_{x\in\mathbb R^N,\,X\in\mathbb S^N}\big\{\langle Q_0,Y\rangle : \langle Q_i,Y\rangle\le 0\ (i\le m_I),\ \langle Q_i,Y\rangle=0\ (i>m_I),\ Y\succeq 0\big\},
--   $$
--   and $\mathcal D_{\mathrm{SDP}}$ is the set of $(x,t)$ for which some symmetric $X$ satisfies these constraints with $\langle Q_0,Y\rangle\le 2t$.
--
--   For $\gamma\in\mathbb R^m$ put $A(\gamma)=A_0+\sum_i\gamma_iA_i$, $b(\gamma)=b_0+\sum_i\gamma_ib_i$, $c(\gamma)=c_0+\sum_i\gamma_ic_i$ and $q(\gamma,x)=q_0(x)+\sum_i\gamma_iq_i(x)$, and
--   $$
--   \Gamma=\{\gamma\in\mathbb R^m : A(\gamma)\succeq 0,\ \gamma_i\ge 0\ \forall i\in[\![m_I]\!]\}.
--   $$
--   **Assumption 1** says that the QCQP is feasible and that some $\gamma^*$ with $\gamma^*_i\ge0$ for $i\in[\![m_I]\!]$ has $A(\gamma^*)\succ 0$.
--
--   These objects are the setting of every result in the paper.
--
--   **Formalization Note** The paper's constraints $1,\dots,m$ are indexed by `Fin m` (index $i$ is the paper's $i+1$); constraint $i$ is an inequality exactly when $i < m_I$. Hence the paper's $\gamma_1$ is `γ 0`. Optimal values are infima in the extended reals `EReal`. $\langle Q,Y\rangle$ is written as the trace of $QY$; $\mathrm{Opt}=+\infty$ if the QCQP is infeasible.
-- source:
--   arXiv:1911.09195v3, (1), (2), (3), (4), §2.1 and Assumption 1, pp. 1, 4, 6–7

import Mathlib
import Definitions.Def_QCQPTightness_ConvHull_QCQP

noncomputable section

namespace QCQPTightness.Sharp

open Matrix

/-- The data of a QCQP (1) of arXiv:1911.09195v3 (§1, p. 1): the objective
`q₀(x) = xᵀA₀x + 2b₀ᵀx + c₀` and `m` constraints `q_i(x) = xᵀA_i x + 2b_iᵀx + c_i`.
Constraint `i : Fin m` is the paper's constraint `i + 1`; it is an inequality exactly when
`i + 1 ∈ ⟦m_I⟧`, i.e. `(i : ℕ) < mI`, and an equality otherwise. -/
structure QCQP (N m : ℕ) where
  A₀ : Matrix (Fin N) (Fin N) ℝ
  b₀ : Fin N → ℝ
  c₀ : ℝ
  A : Fin m → Matrix (Fin N) (Fin N) ℝ
  b : Fin m → Fin N → ℝ
  c : Fin m → ℝ
  mI : ℕ
  mI_le : mI ≤ m
  A₀_symm : A₀.IsSymm
  A_symm : ∀ i, (A i).IsSymm

namespace QCQP

variable {N m : ℕ} (P : QCQP N m)

/-- The objective `q₀`. -/
def q₀ (x : Fin N → ℝ) : ℝ := QCQPTightness.ConvHull.quad P.A₀ P.b₀ P.c₀ x

/-- The constraint function `q_i` (paper index `i + 1`). -/
def q (i : Fin m) (x : Fin N → ℝ) : ℝ := QCQPTightness.ConvHull.quad (P.A i) (P.b i) (P.c i) x

/-- Constraint `i` is an inequality constraint (paper index `i + 1 ∈ ⟦m_I⟧`). -/
def IsIneq (i : Fin m) : Prop := (i : ℕ) < P.mI

/-- The feasible region of (1). -/
def feasible : Set (Fin N → ℝ) :=
  {x | ∀ i, (P.IsIneq i → P.q i x ≤ 0) ∧ (¬ P.IsIneq i → P.q i x = 0)}

/-- `Opt`, the optimal value of (1), in `EReal` (`⊤` if infeasible, `⊥` if unbounded). -/
def Opt : EReal := ⨅ x ∈ P.feasible, ((P.q₀ x : ℝ) : EReal)

/-- The epigraph `𝒟` of (2) (p. 4). -/
def D : Set ((Fin N → ℝ) × ℝ) := {p | P.q₀ p.1 ≤ 2 * p.2 ∧ p.1 ∈ P.feasible}

/-- Feasible points `(x, X)` of the SDP relaxation (3): `X ∈ 𝕊^N`, `Y ⪰ 0`,
`⟨Q_i, Y⟩ ≤ 0` (inequalities), `⟨Q_i, Y⟩ = 0` (equalities). -/
def sdpFeasible : Set ((Fin N → ℝ) × Matrix (Fin N) (Fin N) ℝ) :=
  {p | p.2.IsSymm ∧ (QCQPTightness.ConvHull.liftY p.1 p.2).PosSemidef ∧
    ∀ i, (P.IsIneq i → (QCQPTightness.ConvHull.liftQ (P.A i) (P.b i) (P.c i) * QCQPTightness.ConvHull.liftY p.1 p.2).trace ≤ 0) ∧
      (¬ P.IsIneq i → (QCQPTightness.ConvHull.liftQ (P.A i) (P.b i) (P.c i) * QCQPTightness.ConvHull.liftY p.1 p.2).trace = 0)}

/-- `Opt_SDP` of (3), in `EReal`. -/
def OptSDP : EReal :=
  ⨅ p ∈ P.sdpFeasible, (((QCQPTightness.ConvHull.liftQ P.A₀ P.b₀ P.c₀ * QCQPTightness.ConvHull.liftY p.1 p.2).trace : ℝ) : EReal)

/-- The projected epigraph `𝒟_SDP` of (4) (p. 6). -/
def DSDP : Set ((Fin N → ℝ) × ℝ) :=
  {p | ∃ X : Matrix (Fin N) (Fin N) ℝ, (p.1, X) ∈ P.sdpFeasible ∧
    (QCQPTightness.ConvHull.liftQ P.A₀ P.b₀ P.c₀ * QCQPTightness.ConvHull.liftY p.1 X).trace ≤ 2 * p.2}

/-- `A(γ) = A₀ + Σ γ_i A_i` (§2.1, p. 6). -/
def Aγ (γ : Fin m → ℝ) : Matrix (Fin N) (Fin N) ℝ := P.A₀ + ∑ i, γ i • P.A i

/-- `b(γ) = b₀ + Σ γ_i b_i`. -/
def bγ (γ : Fin m → ℝ) : Fin N → ℝ := P.b₀ + ∑ i, γ i • P.b i

/-- `c(γ) = c₀ + Σ γ_i c_i`. -/
def cγ (γ : Fin m → ℝ) : ℝ := P.c₀ + ∑ i, γ i * P.c i

/-- The Lagrangian `q(γ, x) = q₀(x) + Σ γ_i q_i(x)`. -/
def qγ (γ : Fin m → ℝ) (x : Fin N → ℝ) : ℝ := P.q₀ x + ∑ i, γ i * P.q i x

/-- The dual object `Γ = {γ ∈ ℝ^m : A(γ) ⪰ 0, γ_i ≥ 0 ∀ i ∈ ⟦m_I⟧}` (p. 7). -/
def Gamma : Set (Fin m → ℝ) := {γ | (P.Aγ γ).PosSemidef ∧ ∀ i, P.IsIneq i → 0 ≤ γ i}

/-- Assumption 1 (p. 6): (1) is feasible and some `γ*` with `γ*_i ≥ 0` for `i ∈ ⟦m_I⟧`
has `A(γ*) ≻ 0`. -/
def Assumption1 : Prop :=
  P.feasible.Nonempty ∧ ∃ γ : Fin m → ℝ, (∀ i, P.IsIneq i → 0 ≤ γ i) ∧ (P.Aγ γ).PosDef

end QCQP

end QCQPTightness.Sharp


