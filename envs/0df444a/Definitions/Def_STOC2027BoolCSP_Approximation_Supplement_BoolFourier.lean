-- Prove2me | Definitions.Def_STOC2027BoolCSP_Approximation_Supplement_BoolFourier
-- name    : STOC2027BoolCSP_Approximation_Supplement_BoolFourier
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T18:31:55.1112+00:00
-- url     : https://prove2.me/theorems/061e5018-79df-4168-8d7d-fec616755363
-- title:
--   Walsh expansion, noise operator, influences, folding, and the Boolean and Gaussian acceptances of Lemma 13.1
-- statement:
--   For $h:\{-1,1\}^R\to\mathbb R$ and $S\subseteq[R]$ write $\chi_S(z)=\prod_{i\in S}z_i$ and $\hat h(S)=\mathbb E_z[h(z)\chi_S(z)]$ for $z$ uniform. Then
--   $$T_\theta h=\sum_S\theta^{|S|}\hat h(S)\chi_S,\qquad \mathrm{Inf}_i(h)=\sum_{S\ni i}\hat h(S)^2 .$$
--   A function $h:\{-1,1\}^R\to[0,1]$ is **folded** when $h(-z)=1-h(z)$.
--
--   Let $\mu_b$ ($b$ in a finite set) be laws on $\{-1,1\}^k$ with branch weights $p_b$, and let $\Sigma_b=\mathbb E_{\mu_b}XX^{\mathsf T}$ be the second-moment matrix of $\mu_b$. The **Gaussian acceptance** of branch $b$ for $f:\mathbb R^N\to\mathbb R$ is
--   $$2^{-k}\,\mathbb E_{\Sigma_b}\prod_{j=1}^k\big(1+f(G_j)\big),$$
--   where the $N$ columns of $(G_1,\dots,G_k)$ are independent $N(0,\Sigma_b)$ vectors. The **Boolean global-branch acceptance** of $h$ is
--   $$\sum_b p_b\,\mathbb E\prod_{j=1}^k h(X_j),$$
--   where, given $b$, the $R$ columns of the $k\times R$ matrix $X$ are independent draws from $\mu_b$ and $X_j\in\{-1,1\}^R$ is its row $j$.
--
--   These are the objects of the uniform common-function transfer, Lemma 13.1.
--
--   **Formalization Note** $\{-1,1\}$ is `Bool` (`true` is $+1$); a law on $\{-1,1\}^k$ is given by its atom masses $\mu_b(x)$. $-z$ flips every bit. Gaussian columns use `multivariateGaussian 0 Σ_b`, which is the Gaussian law for every positive semidefinite $\Sigma_b$, singular ones included.
-- source:
--   Zhijie Zheng, Yucong He, Chengzhi Xie, Approximation and Even Arity Hardness for Boolean Constraint Satisfaction, STOC 2027 submission #40 (October 2026), printed p. 28 (PDF 31), Section 13 preamble and Lemma 13.1

import Mathlib
import Definitions.Def_STOC2027BoolCSP_Approximation_Instance
import Definitions.Def_STOC2027BoolCSP_Approximation_Supplement_TwoHub

namespace STOC2027BoolCSP.Approximation.Supplement

open MeasureTheory ProbabilityTheory STOC2027BoolCSP.Approximation

/-- The Walsh character `χ_S(z) = Π_{i ∈ S} z_i` on `{-1,1}^R` (`true ↦ +1`). -/
noncomputable def chi {R : ℕ} (S : Finset (Fin R)) (z : Fin R → Bool) : ℝ :=
  ∏ i ∈ S, sgnOf (z i)

/-- The Walsh coefficient `ĥ(S) = E_z[h(z) χ_S(z)]`, `z` uniform on `{-1,1}^R`. -/
noncomputable def fourierCoeff {R : ℕ} (h : (Fin R → Bool) → ℝ) (S : Finset (Fin R)) : ℝ :=
  (∑ z, h z * chi S z) / 2 ^ R

/-- The noise operator `T_θ h = Σ_S θ^{|S|} ĥ(S) χ_S`. -/
noncomputable def noiseOp {R : ℕ} (θ : ℝ) (h : (Fin R → Bool) → ℝ) : (Fin R → Bool) → ℝ :=
  fun z => ∑ S : Finset (Fin R), θ ^ S.card * fourierCoeff h S * chi S z

/-- The influence `Inf_i(h) = Σ_{S ∋ i} ĥ(S)²`. -/
noncomputable def influence {R : ℕ} (h : (Fin R → Bool) → ℝ) (i : Fin R) : ℝ :=
  ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin R) => i ∈ S), fourierCoeff h S ^ 2

/-- `h` is folded: `h(−z) = 1 − h(z)`, where `−z` flips every bit. -/
def IsFolded {R : ℕ} (h : (Fin R → Bool) → ℝ) : Prop :=
  ∀ z, h (fun i => !z i) = 1 - h z

/-- The second-moment matrix `Σ = E_µ X Xᵀ` of a law `µ` on `{-1,1}^k` (given by its atom masses). -/
noncomputable def secondMoment {k : ℕ} (μ : (Fin k → Bool) → ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  Matrix.of fun i j => ∑ x, μ x * (sgnOf (x i) * sgnOf (x j))

/-- The Gaussian acceptance `2^{−k} E_Σ Π_{j=1}^k (1 + f(G_j))` of one branch, the `N` columns of
`(G_1, …, G_k)` being independent `N(0, Σ)` vectors. -/
noncomputable def gaussAcc {k : ℕ} (S : Matrix (Fin k) (Fin k) ℝ) {N : ℕ}
    (f : (Fin N → ℝ) → ℝ) : ℝ :=
  ∫ ω, (1 / 2 ^ k) * ∏ j, (1 + f (row ω j)) ∂colGauss k N S

/-- The Boolean global-branch acceptance `Σ_b p_b E Π_{j=1}^k h(X_j)`: branch `b` is chosen with
probability `p_b`, then the `R` columns of the `k × R` matrix `X` are drawn independently from
`µ_b`, and `X_j` is row `j`. -/
noncomputable def boolAcc {k : ℕ} {B : Type*} [Fintype B] (μ : B → (Fin k → Bool) → ℝ)
    (p : B → ℝ) {R : ℕ} (h : (Fin R → Bool) → ℝ) : ℝ :=
  ∑ b, p b * ∑ X : Fin R → Fin k → Bool,
    (∏ col, μ b (X col)) * ∏ j, h (fun col => X col j)

end STOC2027BoolCSP.Approximation.Supplement


