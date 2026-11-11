-- Prove2me | Definitions.Def_SparseTensorInj_Certify_RandomModel
-- name    : SparseTensorInj_Certify_RandomModel
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T01:37:16.145292+00:00
-- url     : https://prove2.me/theorems/1aa91270-89c3-450f-916e-348201a5163c
-- title:
--   The random subgaussian tensor model of Definition 3, the $\psi_2$ bound and the utility bound of Theorem 5
-- statement:
--   Fix $n\ge k\ge2$ and parameters $\sigma,\gamma>0$. The **subgaussian norm** of a random variable is $\|X\|_{\psi_2}=\inf\{t>0:\mathbb E\exp(X^2/t^2)\le2\}$. A family $\{\chi_e\}_{e\in[n]_k}$ of random variables on a probability space is a **coefficient family of Definition 3** if the $\chi_e$ are mutually independent (not necessarily identically distributed) and
--   $$\mathbb E[\chi_e]=0,\qquad \mathbb E[\chi_e^2]\le\sigma^2,\qquad \|\chi_e\|_{\psi_2}\le\gamma .$$
--   The **random symmetric order-$k$ tensor** is
--   $$T_{i_1,\dots,i_k}=\begin{cases}\chi_{\{i_1,\dots,i_k\}}&\text{if }|\{i_1,\dots,i_k\}|=k,\\0&\text{otherwise.}\end{cases}$$
--   The variance $\sigma^2$ can be much smaller than $\gamma^2$ (sparse entries); this is what the variance-sensitive bounds exploit.
--
--   The **utility bound** of Theorem 5, without its constant $C_k$, is
--   $$b_k(n,\sigma,\gamma)=\begin{cases}\sigma n^{k/4}+\gamma\sqrt{\log(1+\gamma^2/\sigma^2)}\,\sqrt{\log n}&k\text{ even},\\ \sigma n^{k/4}+\gamma\sqrt{\log(1+\gamma^2/\sigma^2)}\,(\log n)^{k/4}&k\text{ odd},\end{cases}$$
--   with the natural logarithm.
--
--   **Formalization Note.** `Psi2Le P X γ` is: $\exp(X^2/\gamma^2)$ is integrable and $\mathbb E\exp(X^2/\gamma^2)\le2$. For $\gamma>0$ this is equivalent to $\|X\|_{\psi_2}\le\gamma$ ($t\mapsto\mathbb E\exp(X^2/t^2)$ is non-increasing and right-continuous by monotone convergence); every statement assumes $\gamma>0$, which `IsSubgaussianFamily` also records together with $\sigma>0$, measurability, `iIndepFun`, $\mathbb E\chi_e=0$ and $\mathbb E\chi_e^2\le\sigma^2$ (the integrals are of integrable functions, by the $\psi_2$ integrability). `modelTensor χ ω` is the tensor at the outcome $\omega$; `utilityBound` tests parity by `k % 2 = 0`; $n^{k/4}$ and $(\log n)^{k/4}$ are real powers.
-- source:
--   Kothari, Louis, Paul, Raghavendra, Improved Bounds for Certifying Injective Norm of Sparse Random Tensors, STOC 2027 submission (manuscript of November 3, 2026, sha256 e46cf53d…), p. 4, Definition 3 and Theorem 5

import Mathlib
import Definitions.Def_SparseTensorInj_Certify_Tensor

open MeasureTheory ProbabilityTheory

namespace SparseTensorInj.Certify

/-- The subgaussian-norm bound `‖X‖_{ψ2} ≤ γ` (Definition 3, p. 4), for `γ > 0`:
`E[exp(X^2/γ^2)] ≤ 2`, with the integrand required to be integrable. Since
`‖X‖_{ψ2} = inf {t > 0 : E[exp(X^2/t^2)] ≤ 2}` and `t ↦ E[exp(X^2/t^2)]` is non-increasing and
continuous from the right (monotone convergence), `‖X‖_{ψ2} ≤ γ` holds exactly when this does.
(Every statement using it assumes `0 < γ`.) -/
def Psi2Le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → ℝ) (γ : ℝ) : Prop :=
  Integrable (fun ω => Real.exp (X ω ^ 2 / γ ^ 2)) P ∧
    ∫ ω, Real.exp (X ω ^ 2 / γ ^ 2) ∂P ≤ 2

/-- The coefficient family of the random subgaussian tensor model (Definition 3, p. 4), with
parameters `σ, γ > 0`: random variables `χ_e` on a probability space, mutually independent (not
necessarily identically distributed), with `E[χ_e] = 0`, `E[χ_e^2] ≤ σ^2` and `‖χ_e‖_{ψ2} ≤ γ`. The
index type `ι` is `[n]_k` in the model. -/
structure IsSubgaussianFamily {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (χ : ι → Ω → ℝ) (σ γ : ℝ) : Prop where
  sigma_pos : 0 < σ
  gamma_pos : 0 < γ
  measurable : ∀ e, Measurable (χ e)
  indep : iIndepFun χ P
  mean_zero : ∀ e, ∫ ω, χ e ω ∂P = 0
  second_moment_le : ∀ e, ∫ ω, χ e ω ^ 2 ∂P ≤ σ ^ 2
  psi2_le : ∀ e, Psi2Le P (χ e) γ

/-- The random symmetric order-`k` tensor of Definition 3 (p. 4) at the outcome `ω`:
`T_{i_1, …, i_k} = χ_{{i_1, …, i_k}}` when the indices are pairwise distinct
(`|{i_1, …, i_k}| = k`), and `0` otherwise. -/
noncomputable def modelTensor {n k : ℕ} {Ω : Type*} (χ : KSubset n k → Ω → ℝ) (ω : Ω) :
    Tensor k n :=
  fun i => if h : (Finset.univ.image i).card = k then χ ⟨Finset.univ.image i, h⟩ ω else 0

/-- The utility bound of Theorem 5 (p. 4), without the constant `C_k`:
`σ n^{k/4} + γ √(log(1 + γ^2/σ^2)) · √(log n)` for even `k`, and
`σ n^{k/4} + γ √(log(1 + γ^2/σ^2)) · (log n)^{k/4}` for odd `k` (natural logarithm). -/
noncomputable def utilityBound (k n : ℕ) (σ γ : ℝ) : ℝ :=
  if k % 2 = 0 then
    σ * (n : ℝ) ^ ((k : ℝ) / 4) +
      γ * Real.sqrt (Real.log (1 + γ ^ 2 / σ ^ 2)) * Real.sqrt (Real.log n)
  else
    σ * (n : ℝ) ^ ((k : ℝ) / 4) +
      γ * Real.sqrt (Real.log (1 + γ ^ 2 / σ ^ 2)) * Real.log n ^ ((k : ℝ) / 4)

end SparseTensorInj.Certify


