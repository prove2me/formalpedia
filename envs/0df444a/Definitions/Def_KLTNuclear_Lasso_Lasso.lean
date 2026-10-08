-- Prove2me | Definitions.Def_KLTNuclear_Lasso_Lasso
-- name    : KLTNuclear_Lasso_Lasso
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T07:50:58.03565+00:00
-- url     : https://prove2.me/theorems/03c1d567-d41a-4eb5-92cd-95199aad175d
-- title:
--   Vector norms |z|_q, restrictions u_J, sparsity M(β) and the fixed-design Lasso estimator
-- statement:
--   Fix integers $n, p$. A **design** is a list of fixed vectors $x_1, \dots, x_n \in \mathbb R^p$, the rows of the design matrix $\mathbb X = (x_1, \dots, x_n)^\top \in \mathbb R^{n\times p}$, so that $(\mathbb X\beta)_i = x_i^\top\beta$ for $\beta \in \mathbb R^p$.
--
--   For $z \in \mathbb R^d$ the norms are
--   $$
--   |z|_1 = \sum_{j=1}^d |z(j)|, \qquad |z|_2 = \Big(\sum_{j=1}^d z(j)^2\Big)^{1/2},
--   $$
--   and for an index set $J \subseteq \{1,\dots,d\}$ the norms of the restriction $u_J$ (the vector agreeing with $u$ on $J$ and vanishing on $J^c$) are $|u_J|_1 = \sum_{j\in J}|u(j)|$ and $|u_J|_2 = (\sum_{j\in J}u(j)^2)^{1/2}$. The **support** of $\beta \in \mathbb R^p$ is $J(\beta) = \{j : \beta(j) \neq 0\}$, and the **sparsity** $M(\beta) = |J(\beta)|$ is the number of nonzero components of $\beta$.
--
--   The **prediction loss** of $\beta$ relative to $\beta^*$ is $\frac1n|\mathbb X(\beta-\beta^*)|_2^2$. Given responses $Y_1, \dots, Y_n$ and $\lambda > 0$, a **Lasso estimator** is any minimizer
--   $$
--   \hat\beta^\lambda \in \arg\min_{\beta\in\mathbb R^p}\Big\{\frac1n\sum_{i=1}^n (Y_i - x_i^\top\beta)^2 + \lambda|\beta|_1\Big\}.
--   $$
--
--   These are the objects of Section 5.4 of the paper, where the trace regression model with diagonal matrices becomes the usual linear regression model and the nuclear-norm penalized estimator becomes the Lasso.
--
--   **Formalization Note** The design is given by its rows `x i : Fin p → ℝ`. The Lasso is an argmin predicate (`IsLasso`): minimizers need not be unique, and every statement is made for every minimizer. Indices run over `Fin p`, i.e. from $0$.
-- source:
--   Koltchinskii, Lounici, Tsybakov, Nuclear-Norm Penalization and Optimal Rates for Noisy Low-Rank Matrix Completion, arXiv:1011.6256v4, pp. 24–25, §5.4 (norms |z|_q, design matrix 𝕏, Lasso estimator β̂^λ, M(β)), p. 25 (β_J)

import Mathlib

namespace KLTNuclear.Lasso

/-! Sparse linear regression vocabulary of Koltchinskii, Lounici and Tsybakov,
arXiv:1011.6256v4, §5.4, pp. 24–25: the ℓ_q norms |z|_q, the restrictions u_J, the support and
the sparsity M(β), the design map β ↦ 𝕏β and the Lasso estimator with a fixed design.
The design matrix 𝕏 = (x₁, …, xₙ)ᵀ ∈ ℝ^{n×p} is given by its rows `x i : Fin p → ℝ`. -/

/-- `|z|_1 = ∑_j |z(j)|` (p. 24). -/
noncomputable def l1Norm {d : ℕ} (z : Fin d → ℝ) : ℝ :=
  ∑ j, |z j|

/-- `|z|_2² = ∑_j z(j)²` (p. 24, the square of `|z|_2`). -/
noncomputable def l2NormSq {d : ℕ} (z : Fin d → ℝ) : ℝ :=
  ∑ j, z j ^ 2

/-- `|z|_2 = (∑_j z(j)²)^{1/2}` (p. 24). -/
noncomputable def l2Norm {d : ℕ} (z : Fin d → ℝ) : ℝ :=
  Real.sqrt (l2NormSq z)

/-- `|u_J|_1 = ∑_{j ∈ J} |u(j)|`, the ℓ₁ norm of the restriction `u_J` (p. 25–26). -/
noncomputable def l1On {d : ℕ} (u : Fin d → ℝ) (J : Finset (Fin d)) : ℝ :=
  ∑ j ∈ J, |u j|

/-- `|u_J|_2 = (∑_{j ∈ J} u(j)²)^{1/2}`, the ℓ₂ norm of the restriction `u_J` (p. 25–26). -/
noncomputable def l2On {d : ℕ} (u : Fin d → ℝ) (J : Finset (Fin d)) : ℝ :=
  Real.sqrt (∑ j ∈ J, u j ^ 2)

/-- The support `J(β) = {j : β(j) ≠ 0}`. -/
noncomputable def supp {p : ℕ} (β : Fin p → ℝ) : Finset (Fin p) :=
  Finset.univ.filter (fun j => β j ≠ 0)

/-- `M(β)`, the number of nonzero components of `β` (p. 25). -/
noncomputable def sparsity {p : ℕ} (β : Fin p → ℝ) : ℕ :=
  (supp β).card

/-- The vector `𝕏β ∈ ℝⁿ`, whose `i`-th entry is `x_iᵀβ`. -/
noncomputable def design {n p : ℕ} (x : Fin n → Fin p → ℝ) (β : Fin p → ℝ) : Fin n → ℝ :=
  fun i => ∑ j, x i j * β j

/-- The prediction loss `(1/n)|𝕏(β − β*)|_2²` (p. 25, (5.12)). -/
noncomputable def predLoss {n p : ℕ} (x : Fin n → Fin p → ℝ) (β βstar : Fin p → ℝ) : ℝ :=
  (1 / (n : ℝ)) * l2NormSq (design x (β - βstar))

/-- The Lasso criterion `(1/n) ∑_i (Y_i − x_iᵀβ)² + λ|β|_1` (p. 25). -/
noncomputable def lassoObj {n p : ℕ} (x : Fin n → Fin p → ℝ) (Y : Fin n → ℝ) (lam : ℝ)
    (β : Fin p → ℝ) : ℝ :=
  (1 / (n : ℝ)) * ∑ i, (Y i - ∑ j, x i j * β j) ^ 2 + lam * l1Norm β

/-- `β̂` is a Lasso estimator: a minimizer of the Lasso criterion over all of ℝ^p (p. 25).
Minimizers need not be unique; statements are made for every minimizer. -/
def IsLasso {n p : ℕ} (x : Fin n → Fin p → ℝ) (Y : Fin n → ℝ) (lam : ℝ)
    (βhat : Fin p → ℝ) : Prop :=
  ∀ β : Fin p → ℝ, lassoObj x Y lam βhat ≤ lassoObj x Y lam β

end KLTNuclear.Lasso


