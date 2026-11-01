-- Prove2me | Definitions.Def_DoublyOptBandit_Components
-- name    : DoublyOptBandit_Components
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:26:50.745118+00:00
-- url     : https://prove2.me/theorems/91ebb025-2c4c-499f-839a-6f4b45602e4e
-- title:
--   Scaling matrix $(\nabla^2R(x)+cI)^{-1/2}$, ellipsoidal estimator, prox-mapping and barrier center ((2.2), (2.5), (3.2), (3.3))
-- statement:
--   Let $X\subseteq\mathbb R^n$ and $R$ a barrier for $X$. This module defines the building blocks of Algorithms 1 and 2.
--
--   1. The **scaling matrix** $A=(\nabla^2R(x)+c\,I_n)^{-1/2}$, the symmetric positive definite inverse square root (Algorithm 1 line 4 with $c=\eta_t\beta(t+1)$; Algorithm 2 line 5 with $c=\eta_t\beta(t+1)/\lambda_i$).
--   2. The **single-shot ellipsoidal estimator** $\hat v=n\,\hat u\,A^{-1}z$ built from an observed reward $\hat u=u(x+Az)$ and a direction $z$ ((2.2), (3.2)).
--   3. The **prox-mapping**
--   $$
--   P_R(x,\hat v,\eta)=\operatorname*{argmin}_{x'}\ \eta\langle\hat v,x-x'\rangle+\frac q2\|x-x'\|^2+D_R(x',x),
--   $$
--   with $q=\eta\beta(t+1)$ in (2.5) and $q=\eta\beta(t+1)/\lambda_i$ in (3.3), where $D_R(x',x)=R(x')-R(x)-\langle\nabla R(x),x'-x\rangle$ is the Bregman divergence (2.3).
--   4. The **center** $\bar x=\operatorname{argmin}R$ of $X$, the initialization of both algorithms.
--   5. The perturbed joint profile $\hat x=(x_j+A_jz_j)_j$.
--
--   **Formalization Note** The inverse square root is taken by the continuous functional calculus of self-adjoint matrices, so it is the symmetric positive definite root whenever $\nabla^2R(x)+cI$ is positive definite, as it is for convex $R$ and $c>0$. The minimizations run over $\operatorname{int}X$, the domain of $R$. Under the hypotheses of the theorems a unique minimizer exists, and the definitions return it; a fallback value is used only in the case those hypotheses exclude.
-- source:
--   Ba, Lin, Zhang & Zhou, Doubly Optimal No-Regret Online Learning in Strongly Monotone Games with Bandit Feedback, arXiv:2112.02856v4, (2.2), p.7; (2.3), p.7; (2.5), p.8; Algorithm 1, p.9; (3.2), (3.3), p.14; Algorithm 2, p.15; center, §2.1, p.6

import Mathlib
import Definitions.Def_BeckTeboulleMD_EMDA_bregman
import Definitions.Def_DoublyOptBandit_LocalNorm
import Definitions.Def_DoublyOptBandit_Game

open scoped InnerProductSpace

namespace DoublyOptBandit

/-- The **scaling matrix** `A = (∇²R(x) + c·Iₙ)^{−1/2}` (Ba, Lin, Zhang & Zhou,
arXiv:2112.02856v4, Algorithm 1 line 4, p.9, with `c = ηₜβ(t+1)`; Algorithm 2 line 5, p.15, with
`c = ηₜβ(t+1)/λᵢ`).

**Formalization Note** The power `−1/2` is taken by the continuous functional calculus of
self-adjoint real matrices, `cfc (r ↦ r^{−1/2})`, i.e. `U diag(μⱼ^{−1/2}) U⊤` for an orthogonal
eigendecomposition `∇²R(x) + cI = U diag(μ) U⊤`: the **symmetric positive definite** inverse square
root. For `R` convex and `C²` near `x` and `c > 0` the matrix `∇²R(x) + cI` is symmetric positive
definite, so this is the paper's matrix (`cfc` returns `0` on a non-self-adjoint argument, which
does not occur under the theorems' hypotheses). -/
noncomputable def scalingMatrix {m : ℕ} (R : EuclideanSpace ℝ (Fin m) → ℝ)
    (x : EuclideanSpace ℝ (Fin m)) (c : ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  cfc (fun r : ℝ => r ^ (-(1 / 2 : ℝ))) (hessMat R x + c • (1 : Matrix (Fin m) (Fin m) ℝ))

/-- The **single-shot ellipsoidal estimator** `v̂ = n · û · A⁻¹z` built from the observed reward
`û` and the direction `z` (arXiv:2112.02856v4, (2.2), p.7, and (3.2), p.14, with `û = u(x + Az)`;
Algorithm 1 line 8, Algorithm 2 line 11).

**Formalization Note** `n = m` is the dimension of the player's space; `A⁻¹` is the matrix
inverse and acts on `ℝᵐ` through `Matrix.toEuclideanLin`. -/
noncomputable def ellipsoidalEstimate {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) (uhat : ℝ)
    (z : EuclideanSpace ℝ (Fin m)) : EuclideanSpace ℝ (Fin m) :=
  ((m : ℝ) * uhat) • Matrix.toEuclideanLin A⁻¹ z

/-- The objective of the **prox-mapping** (2.5)/(3.3):
`x′ ↦ η⟨v̂, x − x′⟩ + (q/2)∥x − x′∥² + D_R(x′, x)` (arXiv:2112.02856v4, (2.5), p.8, where
`q = ηβ(t+1)`, and (3.3), p.14, where `q = ηβ(t+1)/λᵢ`), with the Bregman divergence (2.3), p.7,
`D_R(x′, x) = R(x′) − R(x) − ⟨∇R(x), x′ − x⟩` = `BeckTeboulleMD.EMDA.bregman R x′ x`. -/
noncomputable def proxObjective {m : ℕ} (R : EuclideanSpace ℝ (Fin m) → ℝ) (η q : ℝ)
    (vhat x x' : EuclideanSpace ℝ (Fin m)) : ℝ :=
  η * ⟪vhat, x - x'⟫_ℝ + q / 2 * ‖x - x'‖ ^ 2 + BeckTeboulleMD.EMDA.bregman R x' x

/-- The **prox-mapping** `P_R(x, v̂, η) = argmin_{x′ ∈ X} proxObjective` (arXiv:2112.02856v4,
(2.5), p.8, and (3.3), p.14).

**Formalization Note** The minimization runs over `int X`: the objective contains `R(x′)`, and the
barrier `R : int(X) → ℝ` is defined only there (Definition 2.1, p.5); a minimization over `X` with
Lean's values of the total function `R` on `∂X` could select a boundary point. For `X` compact
convex with nonempty interior, `R` a self-concordant barrier for `X` and `q ≥ 0`, the objective is
strictly convex on `int X` and tends to `+∞` at `∂X`, so the minimizer exists and is unique; the
definition returns it (via `Classical.choose`), and returns `x` in the case, excluded by those
hypotheses, that no minimizer exists. -/
noncomputable def proxPoint {m : ℕ} (X : Set (EuclideanSpace ℝ (Fin m)))
    (R : EuclideanSpace ℝ (Fin m) → ℝ) (η q : ℝ) (vhat x : EuclideanSpace ℝ (Fin m)) :
    EuclideanSpace ℝ (Fin m) :=
  open Classical in
  if h : ∃ y ∈ interior X, IsMinOn (proxObjective R η q vhat x) (interior X) y then
    Classical.choose h else x

/-- The **center** `x̄ = argmin_{x ∈ X} R(x)` of `X` with respect to the barrier `R`
(arXiv:2112.02856v4, §2.1, p.6), the initialization of Algorithm 1 (line 2, p.9) and Algorithm 2
(line 2, p.15).

**Formalization Note** As for `proxPoint`, the minimization runs over `int X`, the domain of `R`.
For `X` compact with nonempty interior and `R` a nondegenerate self-concordant barrier the
minimizer exists and is unique; the definition returns it, and `0` in the excluded case that no
minimizer exists. -/
noncomputable def barrierCenter {m : ℕ} (X : Set (EuclideanSpace ℝ (Fin m)))
    (R : EuclideanSpace ℝ (Fin m) → ℝ) : EuclideanSpace ℝ (Fin m) :=
  open Classical in
  if h : ∃ y ∈ interior X, IsMinOn R (interior X) y then Classical.choose h else 0

/-- The **perturbed joint profile** `x̂ = (x₁ + A₁z₁, …, x_N + A_N z_N)` (arXiv:2112.02856v4,
p.14, "x̂ᵢ = xᵢ + Aᵢzᵢ"; Algorithm 2 line 7, p.15). -/
noncomputable def perturb {N : ℕ} {n : Fin N → ℕ}
    (A : ∀ i, Matrix (Fin (n i)) (Fin (n i)) ℝ) (x : Joint n)
    (z : ∀ i, EuclideanSpace ℝ (Fin (n i))) : Joint n :=
  WithLp.toLp 2 (fun i => x i + Matrix.toEuclideanLin (A i) (z i))

end DoublyOptBandit


