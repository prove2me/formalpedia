-- Prove2me | Definitions.Def_QCQPTightness_SOCP_QCQP
-- name    : QCQPTightness_SOCP_QCQP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T18:22:08.853759+00:00
-- url     : https://prove2.me/theorems/a9bd4be8-322b-4fd6-80c0-405d81b5042e
-- title:
--   (1)–(4), Assumption 1, pp. 1–7 — the QCQP, its epigraph 𝒟, the Shor SDP relaxation with Opt_SDP and 𝒟_SDP, Γ
-- statement:
--   This module fixes the data of a **quadratically constrained quadratic program** (QCQP) and its standard semidefinite relaxation.
--
--   A QCQP in $N$ variables with $m$ constraints is given by symmetric matrices $A_0, A_1, \dots, A_m \in \mathbb{S}^N$, vectors $b_0, \dots, b_m \in \mathbb{R}^N$ and scalars $c_0, \dots, c_m \in \mathbb{R}$, together with a number $m_I \le m$ of inequality constraints. Writing $q_i(x) = x^\top A_i x + 2 b_i^\top x + c_i$, the problem (1) is
--
--   $$
--   \mathrm{Opt} = \inf_{x \in \mathbb{R}^N} \bigl\{ q_0(x) : q_i(x) \le 0 \ (i \in [\![m_I]\!]),\ q_i(x) = 0 \ (i \in [\![m_I+1, m]\!]) \bigr\}.
--   $$
--
--   Its epigraph is $\mathcal{D} = \{(x,t) : q_0(x) \le 2t,\ x \text{ feasible}\}$. With $Q_i = \begin{pmatrix} c_i & b_i^\top \\ b_i & A_i \end{pmatrix}$ and $Y = \begin{pmatrix} 1 & x^\top \\ x & X \end{pmatrix}$, the SDP relaxation (3) is
--
--   $$
--   \mathrm{Opt}_{\mathrm{SDP}} = \inf_{x \in \mathbb{R}^N,\, X \in \mathbb{S}^N} \bigl\{ \langle Q_0, Y\rangle : \langle Q_i, Y\rangle \le 0 \ (i \in [\![m_I]\!]),\ \langle Q_i, Y\rangle = 0 \ (i \in [\![m_I+1,m]\!]),\ Y \succeq 0 \bigr\},
--   $$
--
--   and $\mathcal{D}_{\mathrm{SDP}}$ (4) is the set of $(x,t)$ for which some $X \in \mathbb{S}^N$ satisfies these constraints together with $\langle Q_0, Y\rangle \le 2t$. The module also defines the aggregated data $A(\gamma) = A_0 + \sum_i \gamma_i A_i$, $b(\gamma)$, $c(\gamma)$, the Lagrangian $q(\gamma,x) = q_0(x) + \sum_i \gamma_i q_i(x)$, the dual set $\Gamma = \{\gamma \in \mathbb{R}^m : A(\gamma) \succeq 0,\ \gamma_i \ge 0 \ (i \in [\![m_I]\!])\}$, and Assumption 1 (feasibility of (1) and some $\gamma^*$ with $\gamma^*_i \ge 0$ on inequalities and $A(\gamma^*) \succ 0$).
--
--   These are the objects every statement of the paper is about.
--
--   **Formalization Note** Constraint $i : \mathrm{Fin}\ m$ is the paper's constraint $i+1$, and it is an inequality exactly when $i < m_I$. $\mathrm{Opt}$ and $\mathrm{Opt}_{\mathrm{SDP}}$ are infima in the extended reals `EReal` ($+\infty$ when infeasible, $-\infty$ when unbounded below). $\langle Q, Y\rangle$ is written $\operatorname{tr}(QY)$, and $X$ is required to be symmetric.
-- source:
--   arXiv:1911.09195v3, (1)–(4), §2.1, Assumption 1, pp. 1–7

import Mathlib
import Definitions.Def_QCQPTightness_ConvHull_QCQP

noncomputable section

namespace QCQPTightness.SOCP

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

end QCQPTightness.SOCP


