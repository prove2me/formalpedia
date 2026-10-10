-- Prove2me | Definitions.Def_QCQPTightness_ConvHull_QCQP
-- name    : QCQPTightness_ConvHull_QCQP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T17:26:03.782861+00:00
-- url     : https://prove2.me/theorems/ae20ef80-b750-4e9a-950f-b07e8c3d8123
-- title:
--   (1)–(4), §2.1, Assumption 1, pp. 1–7 — the QCQP, its epigraph 𝒟, the Shor SDP relaxation with Opt_SDP and 𝒟_SDP, the dual object Γ
-- statement:
--   This file fixes the objects of Wang and Kılınç-Karzan's analysis of the standard (Shor) semidefinite relaxation of a quadratically constrained quadratic program.
--
--   **The QCQP (1).** Fix $N\ge 0$ variables and $m$ constraints, of which the first $m_I\le m$ are inequalities and the remaining $m_E=m-m_I$ are equalities. Each function is a (possibly nonconvex) quadratic
--   $$q_i(x)=x^\top A_ix+2b_i^\top x+c_i,\qquad A_i\in\mathbb S^N,\ b_i\in\mathbb R^N,\ c_i\in\mathbb R,\qquad i=0,1,\dots,m.$$
--   The feasible region is $\{x: q_i(x)\le 0\ (i\le m_I),\ q_i(x)=0\ (i>m_I)\}$ and
--   $$\mathrm{Opt}=\inf_{x\in\mathbb R^N}\{q_0(x): x\text{ feasible}\}.$$
--
--   **The epigraph (2).** $\mathcal D=\{(x,t)\in\mathbb R^N\times\mathbb R: q_0(x)\le 2t,\ x\text{ feasible}\}$.
--
--   **The SDP relaxation (3)–(4).** With the lifted matrices $Q_i=\begin{pmatrix}c_i&b_i^\top\\ b_i&A_i\end{pmatrix}$ and $Y=\begin{pmatrix}1&x^\top\\ x&X\end{pmatrix}$, a pair $(x,X)$ with $X\in\mathbb S^N$ is SDP-feasible when $Y\succeq0$, $\langle Q_i,Y\rangle\le0$ for inequality constraints and $\langle Q_i,Y\rangle=0$ for equality constraints. Then $\mathrm{Opt}_{\mathrm{SDP}}$ is the infimum of $\langle Q_0,Y\rangle$ over SDP-feasible pairs, and the projected epigraph is
--   $$\mathcal D_{\mathrm{SDP}}=\{(x,t):\ \exists X\in\mathbb S^N,\ (x,X)\text{ SDP-feasible},\ \langle Q_0,Y\rangle\le 2t\}.$$
--
--   **The dual object (§2.1).** For $\gamma\in\mathbb R^m$ put $A(\gamma)=A_0+\sum_i\gamma_iA_i$, $b(\gamma)=b_0+\sum_i\gamma_ib_i$, $c(\gamma)=c_0+\sum_i\gamma_ic_i$ and $q(\gamma,x)=q_0(x)+\sum_i\gamma_iq_i(x)$, and
--   $$\Gamma=\{\gamma\in\mathbb R^m:\ A(\gamma)\succeq0,\ \gamma_i\ge0\ \text{for every inequality constraint } i\}.$$
--
--   **Assumption 1 (p. 6).** The feasible region of (1) is nonempty and some $\gamma^*$ with $\gamma^*_i\ge0$ on the inequality constraints has $A(\gamma^*)\succ0$.
--
--   These objects are shared by every statement of the mission: the convex hull result compares $\mathrm{conv}(\mathcal D)$ with $\mathcal D_{\mathrm{SDP}}$, and the analysis runs through $\Gamma$.
--
--   **Formalization Note.** Constraints are indexed by $i\in\{0,\dots,m-1\}$ (`Fin m`), constraint $i$ being the paper's constraint $i+1$; it is an inequality exactly when $i<m_I$. $\mathrm{Opt}$ and $\mathrm{Opt}_{\mathrm{SDP}}$ are infima in `EReal` ($+\infty$ for an empty set, $-\infty$ when unbounded below), so no junk value $0$ arises. Points of $\mathbb R^{N+1}$ are pairs `(x, t)`. $\langle Q,Y\rangle$ is written $\mathrm{tr}(QY)$, which agrees for symmetric $Q$. Symmetry of the data matrices is part of the structure.
-- source:
--   arXiv:1911.09195v3, (1) p. 1, (2) p. 4, (3)–(4) p. 6, Assumption 1 p. 6, §2.1 pp. 6–7

import Mathlib

noncomputable section

namespace QCQPTightness.ConvHull

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

/-- The quadratic function `x ↦ xᵀAx + 2bᵀx + c`. -/
def quad {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (b : Fin N → ℝ) (c : ℝ) (x : Fin N → ℝ) : ℝ :=
  x ⬝ᵥ (A *ᵥ x) + 2 * (b ⬝ᵥ x) + c

/-- The lifted matrix `Q = [[c, bᵀ], [b, A]] ∈ 𝕊^{N+1}` of (3) (p. 6). -/
def liftQ {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (b : Fin N → ℝ) (c : ℝ) :
    Matrix (Fin 1 ⊕ Fin N) (Fin 1 ⊕ Fin N) ℝ :=
  Matrix.fromBlocks (fun _ _ => c) (fun _ j => b j) (fun i _ => b i) A

/-- The lifted variable `Y = [[1, xᵀ], [x, X]]` of (3) (p. 6). -/
def liftY {N : ℕ} (x : Fin N → ℝ) (X : Matrix (Fin N) (Fin N) ℝ) :
    Matrix (Fin 1 ⊕ Fin N) (Fin 1 ⊕ Fin N) ℝ :=
  Matrix.fromBlocks (fun _ _ => 1) (fun _ j => x j) (fun i _ => x i) X

namespace QCQP

variable {N m : ℕ} (P : QCQP N m)

/-- The objective `q₀`. -/
def q₀ (x : Fin N → ℝ) : ℝ := quad P.A₀ P.b₀ P.c₀ x

/-- The constraint function `q_i` (paper index `i + 1`). -/
def q (i : Fin m) (x : Fin N → ℝ) : ℝ := quad (P.A i) (P.b i) (P.c i) x

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
  {p | p.2.IsSymm ∧ (liftY p.1 p.2).PosSemidef ∧
    ∀ i, (P.IsIneq i → (liftQ (P.A i) (P.b i) (P.c i) * liftY p.1 p.2).trace ≤ 0) ∧
      (¬ P.IsIneq i → (liftQ (P.A i) (P.b i) (P.c i) * liftY p.1 p.2).trace = 0)}

/-- `Opt_SDP` of (3), in `EReal`. -/
def OptSDP : EReal :=
  ⨅ p ∈ P.sdpFeasible, (((liftQ P.A₀ P.b₀ P.c₀ * liftY p.1 p.2).trace : ℝ) : EReal)

/-- The projected epigraph `𝒟_SDP` of (4) (p. 6). -/
def DSDP : Set ((Fin N → ℝ) × ℝ) :=
  {p | ∃ X : Matrix (Fin N) (Fin N) ℝ, (p.1, X) ∈ P.sdpFeasible ∧
    (liftQ P.A₀ P.b₀ P.c₀ * liftY p.1 X).trace ≤ 2 * p.2}

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

end QCQPTightness.ConvHull


