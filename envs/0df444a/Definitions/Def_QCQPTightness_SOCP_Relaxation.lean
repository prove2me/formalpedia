-- Prove2me | Definitions.Def_QCQPTightness_SOCP_Relaxation
-- name    : QCQPTightness_SOCP_Relaxation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T18:22:39.115109+00:00
-- url     : https://prove2.me/theorems/cb3b0647-8888-4bcd-9375-62709fb8220e
-- title:
--   Definitions 4–5 (p. 19), (10)–(12) (pp. 20–21) — SD-QCQPs, the diagonal form, and the SOCP relaxation with Opt_SOCP and 𝒟_SOCP
-- statement:
--   A family $\{A_i\}_{i \in [\![0,m]\!]} \subseteq \mathbb{S}^N$ is **simultaneously diagonalizable** (SD) if there is an invertible $U \in \mathbb{R}^{N \times N}$ such that every $U^\top A_i U$ is diagonal (Definition 4); a QCQP (1) whose matrices $\{A_i\}_{i \in [\![0,m]\!]}$ are SD is an **SD-QCQP** (Definition 5).
--
--   After the change of variables $x \mapsto Ux$ an SD-QCQP becomes a **diagonal QCQP** (10): $A_i = \mathrm{Diag}(a_i)$ for vectors $a_0, \dots, a_m \in \mathbb{R}^N$, so that $q_i(x) = \langle a_i, x^2\rangle + 2\langle b_i, x\rangle + c_i$, where $(x^2)_j = x_j^2$.
--
--   For a diagonal QCQP the **SOCP relaxation** (11) replaces $x^2$ by a vector $y$ with $y_j \ge x_j^2$:
--
--   $$
--   \mathrm{Opt}_{\mathrm{SOCP}} = \inf_{x, y \in \mathbb{R}^N} \Bigl\{ \langle a_0, y\rangle + 2\langle b_0, x\rangle + c_0 : \begin{array}{l} \langle a_i, y\rangle + 2\langle b_i, x\rangle + c_i \le 0,\ i \in [\![m_I]\!] \\ \langle a_i, y\rangle + 2\langle b_i, x\rangle + c_i = 0,\ i \in [\![m_I+1, m]\!] \\ y_j \ge x_j^2,\ j \in [\![N]\!] \end{array} \Bigr\},
--   $$
--
--   and $\mathcal{D}_{\mathrm{SOCP}}$ (12) is the set of $(x,t) \in \mathbb{R}^{N+1}$ for which some $y \in \mathbb{R}^N$ satisfies these constraints together with $\langle a_0, y\rangle + 2\langle b_0, x\rangle + c_0 \le 2t$.
--
--   The SOCP relaxation is the lifted relaxation of Ben-Tal–den Hertog and Locatelli; it uses only $N$ additional variables and $N$ convex quadratic constraints.
--
--   **Formalization Note** The diagonal form is the predicate `IsDiagonalQCQP P a₀ a` ($A_0 = \mathrm{Diag}(a_0)$ and $A_i = \mathrm{Diag}(a_i)$ for all $i$). The SOCP objects take the vectors $a_0$, $a_i$ as arguments and use the QCQP's $b_i$, $c_i$ and $m_I$; they are meaningful for the paper only together with `IsDiagonalQCQP P a₀ a`. Constraint indices are shifted as in the QCQP module ($i : \mathrm{Fin}\ m$ is the paper's $i+1$, an inequality iff $i < m_I$). $\mathrm{Opt}_{\mathrm{SOCP}}$ is an infimum in `EReal`. Invertibility of $U$ is `IsUnit U`.
-- source:
--   arXiv:1911.09195v3, Definitions 4–5, p. 19; §4.2.1, (10), p. 20; (11)–(12), p. 21

import Mathlib
import Definitions.Def_QCQPTightness_SOCP_QCQP

noncomputable section

namespace QCQPTightness.SOCP

open Matrix

namespace QCQP

variable {N m : ℕ} (P : QCQP N m)

/-- Definition 4–5 (p. 19): the QCQP is simultaneously diagonalizable (an SD-QCQP): some
invertible `U ∈ ℝ^{N×N}` makes every `UᵀA_iU`, `i ∈ ⟦0, m⟧`, diagonal. -/
def IsSD : Prop :=
  ∃ U : Matrix (Fin N) (Fin N) ℝ, IsUnit U ∧ (Uᵀ * P.A₀ * U).IsDiag ∧
    ∀ i, (Uᵀ * P.A i * U).IsDiag

/-- The diagonal form (10) (§4.2.1, p. 20): `A₀ = Diag(a₀)` and `A_i = Diag(a_i)`, so that
`q_i(x) = ⟨a_i, x²⟩ + 2⟨b_i, x⟩ + c_i`. -/
def IsDiagonalQCQP (a₀ : Fin N → ℝ) (a : Fin m → Fin N → ℝ) : Prop :=
  P.A₀ = Matrix.diagonal a₀ ∧ ∀ i, P.A i = Matrix.diagonal (a i)

/-- Feasible points `(x, y) ∈ ℝ^N × ℝ^N` of the SOCP relaxation (11) (p. 21):
`⟨a_i, y⟩ + 2⟨b_i, x⟩ + c_i ≤ 0` (inequalities), `= 0` (equalities), and `y_j ≥ x_j²` for all `j`. -/
def socpFeasible (a : Fin m → Fin N → ℝ) :
    Set ((Fin N → ℝ) × (Fin N → ℝ)) :=
  {p | (∀ i, (P.IsIneq i → a i ⬝ᵥ p.2 + 2 * (P.b i ⬝ᵥ p.1) + P.c i ≤ 0) ∧
      (¬ P.IsIneq i → a i ⬝ᵥ p.2 + 2 * (P.b i ⬝ᵥ p.1) + P.c i = 0)) ∧
    ∀ j, p.1 j ^ 2 ≤ p.2 j}

/-- `Opt_SOCP` of (11) (p. 21), in `EReal` (`⊤` if (11) is infeasible). -/
def OptSOCP (a₀ : Fin N → ℝ) (a : Fin m → Fin N → ℝ) : EReal :=
  ⨅ p ∈ P.socpFeasible a, ((a₀ ⬝ᵥ p.2 + 2 * (P.b₀ ⬝ᵥ p.1) + P.c₀ : ℝ) : EReal)

/-- The projected epigraph `𝒟_SOCP` of (12) (p. 21). -/
def DSOCP (a₀ : Fin N → ℝ) (a : Fin m → Fin N → ℝ) : Set ((Fin N → ℝ) × ℝ) :=
  {p | ∃ y : Fin N → ℝ, (p.1, y) ∈ P.socpFeasible a ∧
    a₀ ⬝ᵥ y + 2 * (P.b₀ ⬝ᵥ p.1) + P.c₀ ≤ 2 * p.2}

end QCQP

end QCQPTightness.SOCP


