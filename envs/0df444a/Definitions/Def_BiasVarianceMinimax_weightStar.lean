-- Prove2me | Definitions.Def_BiasVarianceMinimax_weightStar
-- name    : BiasVarianceMinimax_weightStar
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:33:07.208214+00:00
-- url     : https://prove2.me/theorems/bb7a3fd5-49f0-4f6f-abd2-df944afd459e
-- title:
--   The two-decay weights $W^*$ and problem (60)
-- statement:
--   For a scalar $a$, the two-decay vector (`twoDecay`) is
--
--   $$w_j=\frac{\lambda_1}{(j+n_0)^{(q_1+2q_2)/(2(q_1+q_2))}}+\frac{\lambda_2}{(j+n_0)^{q_2/(q_1+q_2)}},\qquad\begin{bmatrix}\lambda_1\\ \lambda_2\end{bmatrix}=\begin{bmatrix}\xi_{11}&\xi_{12}\\ \xi_{21}&\xi_{22}\end{bmatrix}\begin{bmatrix}a\\ 1\end{bmatrix}.$$
--
--   Given a scalar $a_n$ per budget, `weightStar` is the array of these vectors. The module also names the two sums $\mu'w=\sum_j w_j/(j+n_0)^{\alpha q_1}$ (`muSum`) and $\|\Sigma^{1/2}w\|^2=\sum_j(j+n_0)^{2\alpha q_2}w_j^2$ (`sigmaSum`), the scale
--
--   $$\eta^*=\Big(\frac{\sum_j (j+n_0)^{2\alpha q_2}w_j^2}{(\sum_j w_j/(j+n_0)^{\alpha q_1})^2}\Big)^{1/(2(q_1+q_2))}$$
--
--   (`etaStar`), and the feasibility of $(w,\eta,S)$ for problem (60): $\eta>0$, $S=(\eta^{q_1}\mu'w)^2=\eta^{-2q_2}\|\Sigma^{1/2}w\|^2$, $\eta\le K$, $\sum_j w_j=1$ (`Feasible60`).
--
--   **Formalization Note** The appendix sets $n_0=0$; here all sums carry $n_0$. The condition $\eta>0$ is from p.51.
-- source:
--   Lam, Zhang & Zhang, arXiv:1902.04673v1, Theorem 8, (23), p.20; (60), p.51; (66), p.52; (70), (72), p.53

import Mathlib
import Definitions.Def_BiasVarianceMinimax_riskRatio
import Definitions.Def_BiasVarianceMinimax_xi

namespace BiasVarianceMinimax

/-- The sum `μ′w = ∑ⱼ wⱼ/(j + n₀)^(α q₁)`. Lam, Zhang & Zhang, arXiv:1902.04673v1, (60) and (66),
pp.51–52, with `j` shifted by `n₀`. -/
noncomputable def muSum (q₁ q₂ : ℝ) (n₀ n : ℕ) (w : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, w i / runPoint n₀ i ^ (alpha q₁ q₂ * q₁)

/-- The sum `‖Σ^(1/2) w‖² = ∑ⱼ (j + n₀)^(2 α q₂) wⱼ²`. Lam, Zhang & Zhang, arXiv:1902.04673v1,
(60) and (66), pp.51–52, with `j` shifted by `n₀`. -/
noncomputable def sigmaSum (q₁ q₂ : ℝ) (n₀ n : ℕ) (w : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, runPoint n₀ i ^ (2 * alpha q₁ q₂ * q₂) * w i ^ 2

/-- The weights of Theorem 8 for a scalar `a`:
`wⱼ = λ₁/(j + n₀)^κ₁ + λ₂/(j + n₀)^κ₂` with `(λ₁, λ₂)ᵀ = Ξ (a, 1)ᵀ`.
Lam, Zhang & Zhang, arXiv:1902.04673v1, Theorem 8 and (23), p.20; (70) and (72), p.53. -/
noncomputable def twoDecay (q₁ q₂ : ℝ) (n₀ n : ℕ) (a : ℝ) : Fin n → ℝ := fun i =>
  (xi q₁ q₂ n₀ n).mulVec ![a, 1] 0 / runPoint n₀ i ^ kappaOne q₁ q₂
    + (xi q₁ q₂ n₀ n).mulVec ![a, 1] 1 / runPoint n₀ i ^ kappaTwo q₁ q₂

/-- The array `W∗(a)` built from a choice `a : ℕ → ℝ` of a scalar per budget.
Lam, Zhang & Zhang, arXiv:1902.04673v1, Theorem 8, p.20. -/
noncomputable def weightStar (q₁ q₂ : ℝ) (n₀ : ℕ) (a : ℕ → ℝ) : TriangularArray :=
  fun n => twoDecay q₁ q₂ n₀ n (a n)

/-- The scale `η∗ = (∑ⱼ j^(2αq₂) wⱼ∗(a)² / (∑ⱼ wⱼ∗(a)/j^(αq₁))²)^(1/(2(q₁+q₂)))`, shifted by `n₀`.
Lam, Zhang & Zhang, arXiv:1902.04673v1, p.53. -/
noncomputable def etaStar (q₁ q₂ : ℝ) (n₀ n : ℕ) (a : ℝ) : ℝ :=
  (sigmaSum q₁ q₂ n₀ n (twoDecay q₁ q₂ n₀ n a) / muSum q₁ q₂ n₀ n (twoDecay q₁ q₂ n₀ n a) ^ 2)
    ^ (1 / (2 * (q₁ + q₂)))

/-- `(w, η, S)` is feasible for problem (60): `S = (η^q₁ ∑ⱼ wⱼ/j^(αq₁))² = η^(-2q₂) ∑ⱼ j^(2αq₂) wⱼ²`,
`η ≤ K`, `∑ⱼ wⱼ = 1`, with `η > 0` from p.51 and `j` shifted by `n₀`.
Lam, Zhang & Zhang, arXiv:1902.04673v1, (60), p.51. -/
def Feasible60 (q₁ q₂ K : ℝ) (n₀ n : ℕ) (w : Fin n → ℝ) (η S : ℝ) : Prop :=
  0 < η ∧ S = (η ^ q₁ * muSum q₁ q₂ n₀ n w) ^ 2 ∧ S = 1 / η ^ (2 * q₂) * sigmaSum q₁ q₂ n₀ n w ∧
    η ≤ K ∧ ∑ i, w i = 1

end BiasVarianceMinimax


