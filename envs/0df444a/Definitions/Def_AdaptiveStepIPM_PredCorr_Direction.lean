-- Prove2me | Definitions.Def_AdaptiveStepIPM_PredCorr_Direction
-- name    : AdaptiveStepIPM_PredCorr_Direction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:18:36.126993+00:00
-- url     : https://prove2.me/theorems/3e630904-6d69-4130-a555-50faa833bba4
-- title:
--   Primal-dual search direction and scaled residuals
-- statement:
--   Let $(x,s)$ be a pair with $x,s>0$ for the standard-form data $A\in\mathbb R^{m\times n}$, write $X=\operatorname{diag}(x)$, $S=\operatorname{diag}(s)$, $\mu=x^Ts/n$, and let $\gamma$ be a parameter (the report takes $\gamma\in[0,1]$). A **search direction** $d=(d_x,d_y,d_s)$ is a solution of system (2):
--
--   $$S d_x+X d_s=\gamma\mu e-Xs,\qquad A d_x=0,\qquad A^T d_y+d_s=0.$$
--
--   The step of length $\theta$ along it is (3): $x(\theta)=x+\theta d_x$, $s(\theta)=s+\theta d_s$. The scaled vectors of (6) are
--
--   $$p=X^{-1/2}S^{1/2}d_x,\qquad q=X^{1/2}S^{-1/2}d_s,\qquad r=(XS)^{-1/2}(\gamma\mu e-Xs),$$
--
--   that is $p_j=\sqrt{s_j/x_j}\,(d_x)_j$, $q_j=\sqrt{x_j/s_j}\,(d_s)_j$, $r_j=(\gamma\mu-x_js_j)/\sqrt{x_js_j}$, and $Pq$ is the vector with coordinates $p_jq_j$, which equals the second-order term $D_xd_s$ of (8). Finally, the quantity of Lemma 4 is
--
--   $$\theta_1=\min\Bigl\{\tfrac12,\ \Bigl(\frac{\mu}{8\|Pq\|}\Bigr)^{1/2}\Bigr\},$$
--
--   with $\|\cdot\|$ the Euclidean norm.
--
--   These are the quantities bounded in Lemmas 1–5 and used to control the step lengths of every algorithm of the report.
--
--   **Formalization Note** The direction is a predicate on $(d_x,d_y,d_s)$, not a function, so no uniqueness (full row rank of $A$) is assumed. The square roots use `Real.sqrt`, which agrees with the report on $x,s>0$, the only case the report considers. When $\|Pq\|=0$ the printed formula for $\theta_1$ has $\mu/0$, read as $+\infty$, so $\theta_1=1/2$; the definition makes this case split explicit, because Lean's real division would give $\mu/0=0$ and hence $\theta_1=0$.
-- source:
--   Mizuno, Todd, Ye, On adaptive-step primal-dual interior-point algorithms for linear programming, Cornell ORIE Technical Report No. 944 (1990, rev. 1991), p. 4, equations (2), (3), (6), (8); p. 8, Lemma 4

import Mathlib
import Definitions.Def_AdaptiveStepIPM_PredCorr_Neighborhoods

open Matrix

namespace AdaptiveStepIPM.PredCorr

/-- System (2): a primal-dual search direction, including its dual multiplier. -/
def SearchDirection {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (x s : Fin n → ℝ) (γ : ℝ)
    (dx : Fin n → ℝ) (dy : Fin m → ℝ) (ds : Fin n → ℝ) : Prop :=
  (∀ j, s j * dx j + x j * ds j = γ * mu x s - x j * s j) ∧
  A *ᵥ dx = 0 ∧ Aᵀ *ᵥ dy + ds = 0

/-- The primal component of the step (3). -/
def stepX {n : ℕ} (x dx : Fin n → ℝ) (θ : ℝ) : Fin n → ℝ :=
  fun j => x j + θ * dx j

/-- The slack component of the step (3). -/
def stepS {n : ℕ} (s ds : Fin n → ℝ) (θ : ℝ) : Fin n → ℝ :=
  fun j => s j + θ * ds j

/-- The scaled primal direction p in (6). -/
noncomputable def scaledP {n : ℕ} (x s dx : Fin n → ℝ) : Fin n → ℝ :=
  fun j => Real.sqrt (s j / x j) * dx j

/-- The scaled slack direction q in (6). -/
noncomputable def scaledQ {n : ℕ} (x s ds : Fin n → ℝ) : Fin n → ℝ :=
  fun j => Real.sqrt (x j / s j) * ds j

/-- The scaled residual r in (6). -/
noncomputable def scaledR {n : ℕ} (x s : Fin n → ℝ) (γ : ℝ) : Fin n → ℝ :=
  fun j => (γ * mu x s - x j * s j) / Real.sqrt (x j * s j)

/-- The vector Pq = Dₓdₛ of (8). -/
noncomputable def Pq {n : ℕ} (x s dx ds : Fin n → ℝ) : Fin n → ℝ :=
  fun j => scaledP x s dx j * scaledQ x s ds j

/-- The repaired lower bound θ₁ of Lemma 4. At Pq = 0, the limit of the
printed expression is 1/2; real division by zero would instead yield zero. -/
noncomputable def theta1 {n : ℕ} (x s dx ds : Fin n → ℝ) : ℝ :=
  if l2Norm (Pq x s dx ds) = 0 then (1 / 2 : ℝ)
  else min (1 / 2 : ℝ) (Real.sqrt (mu x s / (8 * l2Norm (Pq x s dx ds))))

end AdaptiveStepIPM.PredCorr


