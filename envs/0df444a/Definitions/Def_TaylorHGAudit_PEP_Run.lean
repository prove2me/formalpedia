-- Prove2me | Definitions.Def_TaylorHGAudit_PEP_Run
-- name    : TaylorHGAudit_PEP_Run
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T14:47:35.483385+00:00
-- url     : https://prove2.me/theorems/aa0b2991-a94a-400f-8adb-515dd81fe7e8
-- title:
--   Actual fixed-step subgradient runs and normalized worst-case value
-- statement:
--   Fix $N\ge0$, $H\in\mathbb R^{N\times N}$, a radius $R\ge0$, $b\in\mathbb R^{N+1}$, and a symmetric matrix $C\in\mathbb R^{(N+2)\times(N+2)}$. A run on a source-class function $F$ has finite oracle values $v_i=F(x_i)$ and admissible subgradients $g_i\in\partial F(x_i)$, with
--
--   $$x_i=x_0-\sum_{k<i}h_{i,k}g_k\qquad(0\le i\le N).$$
--
--   A genuine minimizer $x_*$ has a finite value $v_*=F(x_*)$, and $\|x_0-x_*\|\le R$. With $P=[g_0\ \cdots\ g_N\ x_0-x_*]$, define
--
--   $$\mathcal P_{b,C}=\sum_{i=0}^N b_i(v_i-v_*)+\operatorname{Tr}(CP^\top P),\qquad
--   w^{(d)}_{\mu,L}=\sup_{F,x,g,v,x_*,v_*}\mathcal P_{b,C}.$$
--
--   The supremum ranges over exactly these actual functions and runs. It is independent of SDP feasibility. This is the function problem whose value Theorem 5 identifies.
--
--   **Formalization Note** The value is an `EReal` supremum of real objectives. The published coefficient mask ignores unused entries of $H$, including all coefficients at $i=0$ and $k\ge i$. The response $g_N$ remains available for the criterion. At $L=+\infty$, admissible subgradients are chosen separately for each query, even at repeated points; the chosen response at a minimizer need not be zero. The marker used in interpolation at $*$ can still have subgradient zero. Normalization uses finite differences and displacement from $x_*$, with no assumed normalization theorem.
-- source:
--   Taylor, Hendrickx & Glineur, arXiv:1502.05666v6, (PEP), p. 3 (PDF 3); §3 and (d-PEP), pp. 11–12 (PDF 11–12); Definition 4, p. 12 (PDF 12); §3.3, pp. 13–14 (PDF 13–14).

import Mathlib
import Definitions.Def_TaylorHGAudit_PEP_Class
import Definitions.Def_TaylorHG_PEP_SDP

namespace TaylorHGAudit.PEP

/-- Definition 4, p. 12, with independent admissible subgradient responses.
The published coefficient table masks every unused entry, including row zero and `g_N`. -/
def IsFixedStepRun {d N : ℕ} (H : Matrix (Fin N) (Fin N) ℝ)
    (x g : Fin (N + 1) → E d) : Prop :=
  ∀ i, x i = x 0 - ∑ k : Fin (N + 1), TaylorHG.PEP.hcoef H i k • g k

/-- The normalized criterion of §3, pp. 11–14, with finite oracle values.
The final Gram column is `x₀ - x_*`, while all `N+1` subgradient responses are retained. -/
noncomputable def criterion {d N : ℕ} (b : Fin (N + 1) → ℝ)
    (C : Matrix (Fin (N + 2)) (Fin (N + 2)) ℝ)
    (x g : Fin (N + 1) → E d) (v : Fin (N + 1) → ℝ)
    (xstar : E d) (vstar : ℝ) : ℝ :=
  b ⬝ᵥ (fun i => v i - vstar) +
    (C * TaylorHG.PEP.gramOf (Fin.snoc g (x 0 - xstar))).trace

/-- Actual function/run feasibility in (PEP), p. 3. The minimizer has a finite value.
There is no matrix feasibility, interpolation theorem, or assumed correspondence here. -/
def FunctionFeasible {d N : ℕ} (μ : NNReal) (L : ENNReal) (R : ℝ)
    (H : Matrix (Fin N) (Fin N) ℝ) (F : E d → EReal)
    (x g : Fin (N + 1) → E d) (v : Fin (N + 1) → ℝ)
    (xstar : E d) (vstar : ℝ) : Prop :=
  FClass μ L F ∧ F xstar = (vstar : EReal) ∧ (∀ y, F xstar ≤ F y) ∧
  (∀ i, HasOracle F (x i) (g i) (v i)) ∧
  IsFixedStepRun H x g ∧ ‖x 0 - xstar‖ ≤ R

/-- The function-level supremum from (PEP), normalized as in §3.
The supremum is in `EReal`: empty sets give `-∞`, unbounded objectives give `+∞`. -/
noncomputable def worstCase (d : ℕ) {N : ℕ} (μ : NNReal) (L : ENNReal) (R : ℝ)
    (H : Matrix (Fin N) (Fin N) ℝ) (b : Fin (N + 1) → ℝ)
    (C : Matrix (Fin (N + 2)) (Fin (N + 2)) ℝ) : EReal :=
  sSup {r : EReal | ∃ (F : E d → EReal) (x g : Fin (N + 1) → E d)
      (v : Fin (N + 1) → ℝ) (xstar : E d) (vstar : ℝ),
    FunctionFeasible μ L R H F x g v xstar vstar ∧
    r = (criterion b C x g v xstar vstar : EReal)}

end TaylorHGAudit.PEP


