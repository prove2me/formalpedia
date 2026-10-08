-- Prove2me | Definitions.Def_AvgLMS_Expect_Model
-- name    : AvgLMS_Expect_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T10:41:20.688826+00:00
-- url     : https://prove2.me/theorems/65bf1553-e95c-4232-9335-1de8ec2dd7a1
-- title:
--   §2.1, p. 2 — assumptions (A1)–(A6), the least-squares objective f, the residual ξₙ, the LMS recursion (1), its average, and the processes of App. A
-- statement:
--   This file fixes the model of §2.1 of Bach and Moulines (2013) and the auxiliary processes used in Appendix A.
--
--   **Space and operators.** $\mathcal H=\mathbb R^d$ is the $d$-dimensional Euclidean space with inner product $\langle\cdot,\cdot\rangle$. For $a\in\mathcal H$, $a\otimes a$ is the rank-one operator $(a\otimes a)b=\langle a,b\rangle a$.
--
--   **Data.** On a probability space $(\Omega,\mathcal F,\mathbb P)$, the observations are pairs $(x_n,z_n)\in\mathcal H\times\mathcal H$, $n\ge1$. For $\theta^*\in\mathcal H$ the **residual** is $\xi_n=z_n-\langle\theta^*,x_n\rangle x_n$, and the **least-squares objective** is
--   $$f(\theta)=\tfrac12\,\mathbb E\big[\langle\theta,x_n\rangle^2-2\langle\theta,z_n\rangle\big],$$
--   which does not depend on $n$ because the observations are identically distributed (the file uses $n=1$).
--
--   **Assumptions (A1)–(A6).** Given an operator $H$ on $\mathcal H$, a point $\theta^*$ and reals $R,\sigma$, the predicate $\mathrm{LMSAssumptions}$ holds when:
--   1. (A1) $d\ge1$;
--   2. (A2) the $x_n,z_n$ are measurable, the pairs $(x_n,z_n)_{n\ge1}$ are mutually independent and all have the law of $(x_1,z_1)$;
--   3. (A3) $\mathbb E\|x_1\|^2<\infty$, $\mathbb E\|z_1\|^2<\infty$, $H=\mathbb E[x_1\otimes x_1]$ is the covariance operator (that is, $\langle v,Hw\rangle=\mathbb E[\langle x_1,v\rangle\langle x_1,w\rangle]$ for all $v,w$), and $H$ is invertible;
--   4. (A4) $\theta^*$ is a global minimizer of $f$;
--   5. (A6) $R>0$, $\sigma>0$, $\mathbb E[\xi_1\otimes\xi_1]\preccurlyeq\sigma^2H$ and $\mathbb E[\|x_1\|^2x_1\otimes x_1]\preccurlyeq R^2H$, where $A\preccurlyeq B$ means that $B-A$ is positive semi-definite.
--
--   **Iterates.** For a step size $\gamma$ and a starting point $\theta_0$, the **LMS recursion** (1) is
--   $$\theta_n=\theta_{n-1}-\gamma\big(\langle\theta_{n-1},x_n\rangle x_n-z_n\big),\qquad n\ge1,$$
--   and the **average** of a sequence $(p_k)$ is $\bar p_n=(n+1)^{-1}\sum_{k=0}^{n}p_k$, so that $\bar\theta_{n-1}=n^{-1}\sum_{k=0}^{n-1}\theta_k$.
--
--   **Processes of Appendix A.**
--   1. The noise-free process of A.3: $\eta_0$ given and $\eta_n=(I-\gamma x_n\otimes x_n)\eta_{n-1}$.
--   2. The processes $\eta^r_n$ of A.4 and Eq. (15), driven by a noise sequence $(\xi_n)$: $\eta^r_0=0$ for every $r$, $\eta^0_n=(I-\gamma H)\eta^0_{n-1}+\gamma\xi_n$, and for $r\ge1$, $\eta^r_n=(I-\gamma H)\eta^r_{n-1}+\gamma(H-x_n\otimes x_n)\eta^{r-1}_{n-1}$.
--   3. The ordered products of A.2: $M^j_i=(I-\gamma x_j\otimes x_j)\cdots(I-\gamma x_i\otimes x_i)$, with $M^{i-1}_i=I$.
--
--   These objects are shared by every statement of the mission: the main theorem is about $f(\bar\theta_{n-1})-f(\theta^*)$, and the lemmas of the appendix are about the auxiliary processes.
--
--   **Formalization Note.** $\mathcal H$ is `EuclideanSpace ℝ (Fin d)` (abbreviated `Hs d`). Observations are indexed from $1$; the values at index $0$ are unused. Each Loewner inequality is written as an inequality of quadratic forms ($\mathbb E\langle\xi_1,v\rangle^2\le\sigma^2\langle v,Hv\rangle$ and $\mathbb E[\|x_1\|^2\langle x_1,v\rangle^2]\le R^2\langle v,Hv\rangle$ for all $v$), which is the same order because both sides are self-adjoint. Every expectation appearing in an assumption comes with the integrability of its integrand, since Lean assigns the integral $0$ to a non-integrable function. Invertibility of $H$ is the existence of a two-sided continuous linear inverse. "$\mathbb E[\xi_n]=0$" in (A4) is a consequence of the minimality of $\theta^*$, not an assumption. The product $M^j_i$ is `Mprod γ x i (j + 1 − i)`, the product of $j+1-i$ factors starting at index $i$.
-- source:
--   Bach & Moulines, arXiv:1306.2119v1, §2.1 assumptions (A1)–(A6) and Eq. (1), p. 2; App. A.2, p. 13; App. A.3, p. 13; App. A.4 and Eq. (15), p. 14

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace RealInnerProductSpace

namespace AvgLMS.Expect

/-- The `d`-dimensional Euclidean space `ℋ = ℝ^d` of (A1). -/
abbrev Hs (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- The rank-one operator `a ⊗ a`, with the paper's convention `(a ⊗ a) b = ⟨a, b⟩ a`. -/
noncomputable def rankOne {d : ℕ} (a : Hs d) : Hs d →L[ℝ] Hs d :=
  (innerSL ℝ a).smulRight a

/-- The least-squares objective `f(θ) = (1/2) E[⟨θ, x⟩² − 2⟨θ, z⟩]` of (A4). The observations are
identically distributed, so the observation `(x 1, z 1)` stands for every `(xₙ, zₙ)`. -/
noncomputable def lsObjective {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {d : ℕ}
    (x z : ℕ → Ω → Hs d) (θ : Hs d) : ℝ :=
  (1 / 2) * ∫ ω, (⟪θ, x 1 ω⟫_ℝ ^ 2 - 2 * ⟪θ, z 1 ω⟫_ℝ) ∂μ

/-- The residual `ξₙ = zₙ − ⟨θ∗, xₙ⟩ xₙ` of (A4). -/
noncomputable def residual {Ω : Type*} {d : ℕ} (x z : ℕ → Ω → Hs d) (θstar : Hs d) (n : ℕ) (ω : Ω) : Hs d :=
  z n ω - ⟪θstar, x n ω⟫_ℝ • x n ω

/-- Assumptions (A1)–(A4) and (A6) of §2.1 (p. 2). Observations are indexed from `1`
(`x 0`, `z 0` are unused). The Loewner inequalities `E[ξ ⊗ ξ] ≼ σ²H` and `E[‖x‖² x ⊗ x] ≼ R²H` are
written as inequalities of quadratic forms, and every expectation in a hypothesis comes with the
integrability of its integrand. The covariance operator `H = E[x ⊗ x]` is given by its bilinear
form; it is assumed invertible (two-sided continuous inverse). -/
structure LMSAssumptions {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {d : ℕ}
    (x z : ℕ → Ω → Hs d) (H : Hs d →L[ℝ] Hs d) (θstar : Hs d) (R σ : ℝ) : Prop where
  /-- (A1) `d ≥ 1`. -/
  one_le_dim : 1 ≤ d
  /-- (A2) measurability of the observations. -/
  measurable_x : ∀ n, Measurable (x n)
  measurable_z : ∀ n, Measurable (z n)
  /-- (A2) the pairs `(xₙ, zₙ)`, `n ≥ 1`, are independent. -/
  indep : iIndepFun (fun n ω => (x (n + 1) ω, z (n + 1) ω)) μ
  /-- (A2) the pairs `(xₙ, zₙ)`, `n ≥ 1`, are identically distributed. -/
  identDistrib : ∀ n, IdentDistrib (fun ω => (x (n + 1) ω, z (n + 1) ω))
    (fun ω => (x 1 ω, z 1 ω)) μ μ
  /-- (A3) `E‖xₙ‖²` and `E‖zₙ‖²` are finite. -/
  memLp_x : MemLp (x 1) 2 μ
  memLp_z : MemLp (z 1) 2 μ
  /-- (A3) `H = E[xₙ ⊗ xₙ]`, through its bilinear form. -/
  integrable_cov : ∀ v w : Hs d, Integrable (fun ω => ⟪x 1 ω, v⟫_ℝ * ⟪x 1 ω, w⟫_ℝ) μ
  cov_eq : ∀ v w : Hs d, ⟪v, H w⟫_ℝ = ∫ ω, ⟪x 1 ω, v⟫_ℝ * ⟪x 1 ω, w⟫_ℝ ∂μ
  /-- (A3) `H` is invertible. -/
  H_invertible : ∃ Hinv : Hs d →L[ℝ] Hs d,
    H.comp Hinv = ContinuousLinearMap.id ℝ (Hs d) ∧ Hinv.comp H = ContinuousLinearMap.id ℝ (Hs d)
  /-- (A4) the global minimum of `f` is attained at `θ∗`. -/
  isMin : ∀ θ : Hs d, lsObjective μ x z θstar ≤ lsObjective μ x z θ
  /-- (A6) `R > 0`, `σ > 0`. -/
  R_pos : 0 < R
  σ_pos : 0 < σ
  /-- (A6) `E[ξₙ ⊗ ξₙ] ≼ σ² H`. -/
  integrable_noise : ∀ v : Hs d, Integrable (fun ω => ⟪residual x z θstar 1 ω, v⟫_ℝ ^ 2) μ
  noise_le : ∀ v : Hs d, ∫ ω, ⟪residual x z θstar 1 ω, v⟫_ℝ ^ 2 ∂μ ≤ σ ^ 2 * ⟪v, H v⟫_ℝ
  /-- (A6) `E[‖xₙ‖² xₙ ⊗ xₙ] ≼ R² H`. -/
  integrable_fourth : ∀ v : Hs d, Integrable (fun ω => ‖x 1 ω‖ ^ 2 * ⟪x 1 ω, v⟫_ℝ ^ 2) μ
  fourth_le : ∀ v : Hs d, ∫ ω, ‖x 1 ω‖ ^ 2 * ⟪x 1 ω, v⟫_ℝ ^ 2 ∂μ ≤ R ^ 2 * ⟪v, H v⟫_ℝ

/-- The LMS recursion (1): `θ₀` given and
`θₙ = θₙ₋₁ − γ(⟨θₙ₋₁, xₙ⟩ xₙ − zₙ)` for `n ≥ 1`. -/
noncomputable def lmsIter {Ω : Type*} {d : ℕ} (γ : ℝ) (θ0 : Hs d) (x z : ℕ → Ω → Hs d) :
    ℕ → Ω → Hs d
  | 0 => fun _ => θ0
  | n + 1 => fun ω =>
      lmsIter γ θ0 x z n ω - γ • (⟪lmsIter γ θ0 x z n ω, x (n + 1) ω⟫_ℝ • x (n + 1) ω - z (n + 1) ω)

/-- The average `p̄ₙ = (n + 1)⁻¹ ∑_{k=0}^{n} pₖ` of (A5); `θ̄ₙ₋₁ = avg θ (n - 1)` for `n ≥ 1`. -/
noncomputable def avg {Ω : Type*} {d : ℕ} (p : ℕ → Ω → Hs d) (n : ℕ) (ω : Ω) : Hs d :=
  ((n : ℝ) + 1)⁻¹ • ∑ k ∈ Finset.range (n + 1), p k ω

/-- The noise-free process of App. A.3 ("`ξₙ` uniformly equal to zero"):
`η₀` given and `ηₙ = (I − γ xₙ ⊗ xₙ) ηₙ₋₁`. -/
noncomputable def biasIter {Ω : Type*} {d : ℕ} (γ : ℝ) (η0 : Hs d) (x : ℕ → Ω → Hs d) :
    ℕ → Ω → Hs d
  | 0 => fun _ => η0
  | n + 1 => fun ω =>
      biasIter γ η0 x n ω - γ • (⟪x (n + 1) ω, biasIter γ η0 x n ω⟫_ℝ • x (n + 1) ω)

/-- The processes `ηʳₙ` of App. A.4 and Eq. (15): `η⁰₀ = 0`, `η⁰ₙ = (I − γH) η⁰ₙ₋₁ + γ ξₙ`, and
for `r ≥ 1`, `ηʳ₀ = 0`, `ηʳₙ = (I − γH) ηʳₙ₋₁ + γ (H − xₙ ⊗ xₙ) ηʳ⁻¹ₙ₋₁`.
`etaR γ H x ξ r n` is `ηʳₙ`. -/
noncomputable def etaR {Ω : Type*} {d : ℕ} (γ : ℝ) (H : Hs d →L[ℝ] Hs d) (x ξ : ℕ → Ω → Hs d) :
    ℕ → ℕ → Ω → Hs d
  | 0, 0 => fun _ => 0
  | 0, n + 1 => fun ω => (1 - γ • H) (etaR γ H x ξ 0 n ω) + γ • ξ (n + 1) ω
  | _ + 1, 0 => fun _ => 0
  | r + 1, n + 1 => fun ω =>
      (1 - γ • H) (etaR γ H x ξ (r + 1) n ω) +
        γ • (H (etaR γ H x ξ r n ω) - ⟪x (n + 1) ω, etaR γ H x ξ r n ω⟫_ℝ • x (n + 1) ω)

/-- The ordered products of App. A.2. `Mprod γ x i m ω` is the product of the `m` factors
`(I − γ x_{i+m−1} ⊗ x_{i+m−1}) ⋯ (I − γ xᵢ ⊗ xᵢ)` (the factor with the largest index on the
left); `m = 0` gives `I`. Hence the paper's `Mʲᵢ` is `Mprod γ x i (j + 1 − i)` for `j ≥ i − 1`,
and `Mⁱ⁻¹ᵢ = I`. -/
noncomputable def Mprod {Ω : Type*} {d : ℕ} (γ : ℝ) (x : ℕ → Ω → Hs d) (i : ℕ) :
    ℕ → Ω → (Hs d →L[ℝ] Hs d)
  | 0 => fun _ => 1
  | m + 1 => fun ω => (1 - γ • rankOne (x (i + m) ω)) * Mprod γ x i m ω

end AvgLMS.Expect


