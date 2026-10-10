-- Prove2me | Definitions.Def_QCQPTightness_MultHull_QCQP
-- name    : QCQPTightness_MultHull_QCQP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T18:20:14.576862+00:00
-- url     : https://prove2.me/theorems/c0ea414c-304f-4028-9afe-2b0afb1b6cbf
-- title:
--   (1)–(4), Assumption 1, pp. 1–7 — the QCQP, its epigraph 𝒟, the Shor SDP relaxation with Opt_SDP and 𝒟_SDP, Γ
-- statement:
--   A **quadratically constrained quadratic program** (QCQP) in $N$ variables with $m = m_I + m_E \ge 1$ constraints is
--
--   $$\mathrm{Opt} := \inf_{x\in\mathbb R^N}\Big\{ q_0(x) : q_i(x)\le 0,\ i\in [\![m_I]\!];\ \ q_i(x) = 0,\ i \in [\![m_I+1, m]\!]\Big\},$$
--
--   where each $q_i(x) = x^\top A_i x + 2 b_i^\top x + c_i$ has $A_i\in\mathbb S^N$ (symmetric), $b_i\in\mathbb R^N$, $c_i\in\mathbb R$. The first $m_I$ constraints are inequalities, the remaining $m_E$ equalities. This module records:
--
--   1. the data $(A_i, b_i, c_i)_{i=0}^m$ and $m_I \le m$, with symmetric $A_i$;
--   2. the feasible region and $\mathrm{Opt}$ (the infimum, valued in the extended reals: $+\infty$ if infeasible, $-\infty$ if unbounded below);
--   3. the **epigraph** $\mathcal D := \{(x,t) \in \mathbb R^N\times\mathbb R : q_0(x)\le 2t,\ x \text{ feasible}\}$ of (2);
--   4. the **Shor SDP relaxation** (3): with $Q_i := \begin{pmatrix} c_i & b_i^\top\\ b_i & A_i\end{pmatrix}$ and $Y := \begin{pmatrix} 1 & x^\top\\ x & X\end{pmatrix}$, its feasible pairs $(x, X)$, $X\in\mathbb S^N$, satisfy $Y\succeq 0$, $\langle Q_i, Y\rangle \le 0$ for inequalities and $= 0$ for equalities; $\mathrm{Opt}_{\mathrm{SDP}}$ is the infimum of $\langle Q_0, Y\rangle$ over them;
--   5. the **projected epigraph** $\mathcal D_{\mathrm{SDP}}$ of (4): the pairs $(x,t)$ for which some feasible $X$ has $\langle Q_0, Y\rangle \le 2t$;
--   6. the aggregated data $A(\gamma) = A_0 + \sum_i \gamma_i A_i$, $b(\gamma)$, $c(\gamma)$, the Lagrangian $q(\gamma, x) = q_0(x) + \sum_i\gamma_i q_i(x)$, and the dual object $\Gamma := \{\gamma\in\mathbb R^m : A(\gamma)\succeq 0,\ \gamma_i\ge 0\ \forall i\in[\![m_I]\!]\}$;
--   7. **Assumption 1**: the feasible region is nonempty and some $\gamma^*$ with $\gamma^*_i \ge 0$ for $i\in[\![m_I]\!]$ has $A(\gamma^*)\succ 0$.
--
--   These are the objects every result of the paper is about: $\mathcal D \subseteq \mathcal D_{\mathrm{SDP}}$ always, and the paper studies when $\mathrm{conv}(\mathcal D) = \mathcal D_{\mathrm{SDP}}$.
--
--   **Formalization Note** Constraints are indexed by $i\in\{0,\dots,m-1\}$ (`Fin m`), the paper's constraint $i+1$; constraint $i$ is an inequality iff $i < m_I$. $\langle Q, Y\rangle$ is $\operatorname{tr}(QY)$, and $Y$ is indexed by $\{\ast\}\sqcup\{1,\dots,N\}$. $\mathrm{Opt}$ and $\mathrm{Opt}_{\mathrm{SDP}}$ are infima in `EReal`, so they are never the junk value of a real infimum. The hypothesis $m\ge 1$ is carried by the theorems, not by the structure.
-- source:
--   arXiv:1911.09195v3, (1) p. 1, (2) p. 4, (3)–(4) p. 6, §2.1 and Assumption 1, pp. 6–7

import Mathlib
import Definitions.Def_QCQPTightness_ConvHull_QCQP

noncomputable section

namespace QCQPTightness.MultHull

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

end QCQPTightness.MultHull


