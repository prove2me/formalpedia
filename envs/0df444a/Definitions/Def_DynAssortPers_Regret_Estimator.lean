-- Prove2me | Definitions.Def_DynAssortPers_Regret_Estimator
-- name    : DynAssortPers_Regret_Estimator
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T05:15:12.665271+00:00
-- url     : https://prove2.me/theorems/d9fca761-6bdb-4275-a06e-1ccc86471bd0
-- title:
--   Sec. 3.2 and Sec. 8, pp. 13–14, 36 — the loss (4), its gradient, the Bregman divergence $D_{\Theta^\star}$, $L_{\mathrm{quad}}$ and the estimator (5)
-- statement:
--   Fix $m$ customer types and $n$ items. An **observation** is a triple $(i,j,S)$: a type $i$, a choice $j\in\{0,1,\dots,n\}$ ($j=0$ is no purchase) and the offered set $S$. A **sample** $\mathcal O$ is a finite list of observations, repetitions allowed; write $N=|\mathcal O|$. For a matrix $\Theta\in\mathbb R^{m\times n}$, let $X_{tj}=e_{i_t}e_j^{\top}$ and $X_{t0}=0$, so that $X_{tj}\cdot\Theta=\Theta_{i_tj}$. This module defines:
--
--   1. the **negative log-likelihood** (4)
--   $$L(\Theta)=\frac1N\sum_{(i,j,S)\in\mathcal O}\log\Big(\big(1+\textstyle\sum_{j'\in S}e^{\Theta_{ij'}}\big)\big(1\text{ if }j=0,\ e^{\Theta_{ij}}\text{ otherwise}\big)^{-1}\Big)=\frac1N\sum_{t}\Big(\log\big(1+\textstyle\sum_{j\in S_t}e^{X_{tj}\cdot\Theta}\big)-X_{tj_t}\cdot\Theta\Big);$$
--   2. its **gradient**
--   $$\nabla L(\Theta)=\frac1N\sum_t\Big(\frac{\sum_{j\in S_t}e^{X_{tj}\cdot\Theta}X_{tj}}{1+\sum_{j\in S_t}e^{X_{tj}\cdot\Theta}}-X_{tj_t}\Big);$$
--   3. the **Bregman divergence** $D_{\Theta^\star}(\Delta)=L(\Theta^\star+\Delta)-L(\Theta^\star)-\nabla L(\Theta^\star)\cdot\Delta$, with $\cdot$ the Frobenius inner product;
--   4. the **quadratic function** $L_{\mathrm{quad}}(\Delta)=\frac1N\sum_t\frac1{K_t}\sum_{j\in S_t}\Delta_{i_tj}^2$, with $K_t=|S_t|$;
--   5. the **estimator** (5): $\widehat\Theta$ is a solution of
--   $$\text{minimize } L(\Theta)+\lambda\|\Theta\|_*\quad\text{subject to }\|\Theta\|_\infty\le\alpha/\sqrt{mn},$$
--   where $\|\cdot\|_*$ is the nuclear norm and $\|\Theta\|_\infty$ the largest absolute entry;
--   6. the nuclear norm of the **tail** $\bar\Theta_r=\Theta-\Theta_r$ beyond the top $r$ singular directions, $\|\bar\Theta_r\|_*=\sum_{j=r+1}^{\min(m,n)}\sigma_j(\Theta)$.
--
--   These are the objects of the static estimation problem; Algorithm 2 applies the estimator to its exploration sample.
--
--   **Formalization Note** The loss is (4) with $\log(a\cdot b^{-1})$ expanded as $\log a-\log b$, an identity. Types and items are 0-based (`Fin m`, `Fin n`), and the no-purchase choice is `none`. With an empty sample, $1/N$ is $0$ in Lean, so $L$, $\nabla L$ and $L_{\mathrm{quad}}$ vanish; the paper always has $N\ge1$. The gradient is defined by the displayed formula of p. 36 (it is the gradient of $L$; that fact is not part of the definition). The singular values are Mathlib's, indexed from $0$ in decreasing order, so $\sigma_j$ is index $j-1$; the nuclear and spectral norms, the Frobenius norm and inner product, and $\|\cdot\|_\infty$ are the published `MatrixCompletion` definitions.
-- source:
--   Kallus, Udell, Dynamic Assortment Personalization in High Dimensions, arXiv:1610.05604 (PDF sha256 2b010481…216a), Sec. 3.2.1, eq. (4), p. 13, and eq. (5), p. 14; Sec. 8, p. 36 (notation, ∇L, D_Θ⋆, Lemma 2's L_quad); eq. (2), p. 11, and p. 43 (‖Θ̄⋆_r‖_*)

import Mathlib
import Definitions.Def_matrix_completion_basic
import Definitions.Def_matrix_completion_tangent

namespace DynAssortPers.Regret

open MatrixCompletion

/-- An observation `(i, j, S)`: the customer type `i : Fin m`, the choice `j` (`none` is the
no-purchase option "item 0", `some j` an item), and the offered set `S`. A sample `𝒪` is a list of
observations (Sec. 3.2, p. 13; Algorithm 2, p. 23). -/
abbrev Obs (m n : ℕ) : Type := Fin m × Option (Fin n) × Finset (Fin n)

/-- The linear score `X_{t j_t} · Θ` of the chosen item (Sec. 8, p. 36): `Θ_{i j}` if item `j` was
chosen, and `0` for the no-purchase option (`e_0 = 0`). -/
def chosenScore {m n : ℕ} (Θ : RealMatrix m n) (o : Obs m n) : ℝ :=
  match o.2.1 with
  | none => 0
  | some j => Θ o.1 j

/-- One term of the negative log-likelihood (4):
`log((1 + ∑_{j' ∈ S} e^{Θ_{i j'}}) · (1 if j = 0, e^{Θ_{i j}} otherwise)^{-1})`,
written as `log(1 + ∑_{j' ∈ S} e^{Θ_{i j'}}) − X_{t j_t} · Θ`. -/
noncomputable def obsLoss {m n : ℕ} (Θ : RealMatrix m n) (o : Obs m n) : ℝ :=
  Real.log (1 + ∑ j ∈ o.2.2, Real.exp (Θ o.1 j)) - chosenScore Θ o

/-- The negative log-likelihood (4) of a sample `𝒪`, `L(Θ) = (1/|𝒪|) ∑_{(i,j,S) ∈ 𝒪} …`
(Sec. 3.2.1, p. 13; Algorithm 2, p. 23; Sec. 8, p. 36). -/
noncomputable def loss {m n : ℕ} (O : List (Obs m n)) (Θ : RealMatrix m n) : ℝ :=
  (1 / (O.length : ℝ)) * (O.map (obsLoss Θ)).sum

/-- The gradient of `L` displayed on p. 36:
`∇L(Θ) = (1/N) ∑_t ( ∑_{j ∈ S_t} e^{X_{tj}·Θ} X_{tj} / (1 + ∑_{j ∈ S_t} e^{X_{tj}·Θ}) − X_{t j_t} )`,
with `X_{tj} = e_{i_t} e_jᵀ` and `X_{t0} = 0`; entry `(a, b)` of the matrix. -/
noncomputable def lossGrad {m n : ℕ} (O : List (Obs m n)) (Θ : RealMatrix m n) : RealMatrix m n :=
  fun a b => (1 / (O.length : ℝ)) * (O.map (fun o =>
    (if a = o.1 ∧ b ∈ o.2.2 then
        Real.exp (Θ o.1 b) / (1 + ∑ j ∈ o.2.2, Real.exp (Θ o.1 j)) else 0) -
      (if a = o.1 ∧ o.2.1 = some b then 1 else 0))).sum

/-- The Bregman divergence `D_{Θ⋆}(Δ) = L(Θ⋆ + Δ) − L(Θ⋆) − ∇L(Θ⋆) · Δ` (p. 36), with `·` the
Frobenius inner product. -/
noncomputable def bregman {m n : ℕ} (O : List (Obs m n)) (Θs Δ : RealMatrix m n) : ℝ :=
  loss O (Θs + Δ) - loss O Θs - matrixInner (lossGrad O Θs) Δ

/-- The quadratic function of Lemma 2 (p. 36):
`L_quad(Δ) = (1/N) ∑_t Y_t(Δ)`, `Y_t(Δ) = (1/K_t) ∑_{j ∈ S_t} Δ_{i_t j}²`, `K_t = |S_t|`. -/
noncomputable def lquad {m n : ℕ} (O : List (Obs m n)) (Δ : RealMatrix m n) : ℝ :=
  (1 / (O.length : ℝ)) *
    (O.map (fun o => (1 / (o.2.2.card : ℝ)) * ∑ j ∈ o.2.2, (Δ o.1 j) ^ 2)).sum

/-- `Θ̂` is a solution of the nuclear-norm regularized maximum-likelihood problem (5), p. 14:
minimize `L(Θ) + λ‖Θ‖_*` subject to `‖Θ‖_∞ ≤ α/√(mn)`. -/
def IsEstimate {m n : ℕ} (O : List (Obs m n)) (lam α : ℝ) (Θh : RealMatrix m n) : Prop :=
  entrySupNorm Θh ≤ α / Real.sqrt ((m : ℝ) * n) ∧
    ∀ Θ : RealMatrix m n, entrySupNorm Θ ≤ α / Real.sqrt ((m : ℝ) * n) →
      loss O Θh + lam * nuclearNorm Θh ≤ loss O Θ + lam * nuclearNorm Θ

/-- The nuclear norm of the tail `Θ̄_r = Θ − Θ_r` (p. 42), which is `∑_{j=r+1}^{min(m,n)} σ_j(Θ)`
(eq. (2), p. 11; p. 43). Mathlib's singular values are indexed from `0` and sorted decreasingly, so
the paper's `σ_j` is `singularValues (j − 1)`. -/
noncomputable def tailNuclear {m n : ℕ} (Θ : RealMatrix m n) (r : ℕ) : ℝ :=
  ∑ k ∈ Finset.Ico r (min m n), (Matrix.toEuclideanLin Θ).singularValues k

end DynAssortPers.Regret


