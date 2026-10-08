-- Prove2me | Definitions.Def_NetTraffic_PoissonFBM_Setting
-- name    : NetTraffic_PoissonFBM_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T02:13:58.949207+00:00
-- url     : https://prove2.me/theorems/291f439a-f2dd-474d-ab78-e744eef7ba6a
-- title:
--   §2.2, §3.1, §4.2, §6 — the infinite source Poisson model, N, A, (2.8), b, Condition 2, R₁, A₁, P₁, j₁, σ_T²(1), σ², G_T, standard FBM, J₁ on 𝔻[0,∞)
-- statement:
--   This file fixes every object of the infinite source Poisson model under fast growth (Mikosch, Resnick, Rootzén and Stegeman 2002, §2.2, §3.1, §4.2 and §6).
--
--   1. **Heavy tails (2.8).** $F_{\mathrm{on}}$ is the law of a transmission length, a probability measure on $[0,\infty)$, with tail $\bar F_{\mathrm{on}}(x)=F_{\mathrm{on}}((x,\infty))$. Condition (2.8) asks $1<\alpha<2$ and $\bar F_{\mathrm{on}}(x)=x^{-\alpha}L(x)$ for $x>0$ with $L$ **slowly varying**: $L$ is eventually positive and $L(cx)/L(x)\to1$ as $x\to\infty$ for every $c>0$. The mean is $\mu_{\mathrm{on}}=\int x\,F_{\mathrm{on}}(dx)$.
--   2. **The quantile function (2.9).** $b(t)=(1/\bar F_{\mathrm{on}})^{\leftarrow}(t)=\inf\{x>0: 1/\bar F_{\mathrm{on}}(x)\ge t\}$.
--   3. **Fast Growth Condition 2** (§3.1): for the connection rate $\lambda=\lambda(T)$ of the $T$-th model,
--   $$\lim_{T\to\infty}\frac{b(\lambda T)}{T}=\infty .$$
--   4. **The model** (§2.2). $(\Gamma_k)_{k\in\mathbb Z}$ are the points of a rate-$\lambda$ homogeneous Poisson process on $\mathbb R$ labelled so that $\Gamma_0<0<\Gamma_1$: the spacings $-\Gamma_0,\ \Gamma_1,\ \Gamma_{k+1}-\Gamma_k\ (k\ne0)$ are iid exponential with parameter $\lambda$. The lengths $X_k$ are iid with law $F_{\mathrm{on}}$ and independent of $(\Gamma_k)$. The number of active sources and the cumulative input are
--   $$N(t)=\sum_{k=-\infty}^{\infty}\mathbf 1[\Gamma_k\le t<\Gamma_k+X_k],\qquad A(t)=\int_0^t N(s)\,ds .$$
--   5. **The region $R_1$ and its pieces** (§4.2). $R_1=\{(s,y):0<s\le T,\ y>0,\ s+y\le T\}$; $A_1=\sum_k X_k\mathbf 1[(\Gamma_k,X_k)\in R_1]$; $P_1=\#\{k:(\Gamma_k,X_k)\in R_1\}$; $m_1=(\mathbb L\times F_{\mathrm{on}})(R_1)$; $j_1$ has the law (4.4), the second marginal of $\mathbb L(ds)F_{\mathrm{on}}(dy)/m_1$ restricted to $R_1$, and $Ej_1$ is its mean. $A_1$ and $P_1$ are also used with $T$ replaced by a horizon $U$.
--   6. **Normalisation** (6.1) and §6.3. $\sigma_T^2(1)=\lambda T^3\bar F_{\mathrm{on}}(T)$, $\sigma_1^2=\alpha/((2-\alpha)(3-\alpha))$, $H=(3-\alpha)/2$,
--   $$\sigma^2=\frac{2}{(\alpha-1)(2-\alpha)(3-\alpha)},\qquad G_T(t)=\frac{A(Tt)-\lambda\mu_{\mathrm{on}}Tt}{[\lambda T^3\bar F_{\mathrm{on}}(T)\sigma^2]^{1/2}},\quad t\ge0 .$$
--   7. **Standard fractional Brownian motion** (§6, p. 55): a mean-zero Gaussian process $(B_H(t))_{t\ge0}$ with a.s. continuous paths and $\mathrm{Cov}(B_H(t),B_H(s))=\tfrac12(t^{2H}+s^{2H}-|t-s|^{2H})$.
--   8. **$J_1$ convergence in $\mathbb D[0,\infty)$.** Càdlàg paths $x_n$ converge to a càdlàg path $x$ if there are continuous, strictly increasing maps $\lambda_n$ of $[0,\infty)$ onto itself with $x_n\circ\lambda_n\to x$ and $\lambda_n\to\mathrm{id}$ uniformly on bounded intervals.
--
--   **The value of $\sigma^2$.** The paper prints (6.6), $\sigma^2=\frac1{3-\alpha}\big[\frac{\alpha}{2-\alpha}+\frac2{\mu_{\mathrm{on}}}\big]$. That value is wrong; the value above is the variance limit of $(A(T)-\lambda\mu_{\mathrm{on}}T)/\sigma_T(1)$ (see the mission description). With the printed value the limit in Theorem 3 would not be *standard* fractional Brownian motion.
--
--   **Formalization Note** Each model $T$ carries its own probability space; statements quantify over every family of models. The spacing family is indexed by $\mathbb Z$: $e_0=-\Gamma_0$, $e_1=\Gamma_1$, $e_k=\Gamma_k-\Gamma_{k-1}$ for $k\ge2$, $e_k=\Gamma_{k+1}-\Gamma_k$ for $k\le-1$. (2.8) is stated as "$x\mapsto x^\alpha\bar F_{\mathrm{on}}(x)$ is slowly varying", which is equivalent. $b(t)$ is written $\inf\{x>0: t\bar F_{\mathrm{on}}(x)\le1\}$, the same set for $t>0$ without a division by zero. $N(t)$ is the cardinality of the set of active indices and is $0$ if that set is infinite; $A_1$ is a sum of non-negative terms (`tsum`, $0$ if not summable); both junk values occur only on null events. $A$ is an interval integral. Paths are functions on $\mathbb R_{\ge0}$. The definitions duplicate those of the companion mission on the slow-growth regime, because draft items cannot import each other.
-- source:
--   Mikosch, Resnick, Rootzén and Stegeman, Is network traffic approximated by stable Lévy motion or fractional Brownian motion?, Ann. Appl. Probab. 12 (2002), pp. 28–29, §2.2 (2.8)–(2.13); p. 30, §3.1 Condition 2; pp. 33–34, §4.2 (4.1)–(4.4); pp. 55–57, §6 (6.1), definition of FBM, G_T

import Mathlib
import Definitions.Def_NetTraffic_PoissonStable_Setting

namespace NetTraffic.PoissonFBM

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

/-! ### Heavy tails, (2.8)–(2.9), and the growth condition of §3.1 -/

/-- **Fast Growth Condition 2** (§3.1, p. 30): `b(λT)/T → ∞` as `T → ∞`, where `λ = λ(T)` is the
connection rate of the `T`-th model. -/
def Condition2 (Fon : Measure ℝ) (lam : ℝ → ℝ) : Prop :=
  Tendsto (fun T => NetTraffic.PoissonStable.b Fon (lam T * T) / T) atTop atTop

/-! ### The infinite source Poisson model, §2.2 -/

/-! ### The decomposition of §4.2: region `R_1`, `A_1`, `P_1`, `m_1`, the law of `j_1` -/

/-! ### The normalisation and the limit, §6 -/

/-- (6.1): `σ_T²(1) = λ(T) T³ F̄_on(T)`. -/
noncomputable def sigmaT2 (Fon : Measure ℝ) (lam : ℝ → ℝ) (T : ℝ) : ℝ :=
  lam T * T ^ 3 * NetTraffic.PoissonStable.Fbar Fon T

/-- The limit variance of `(A(T) - λμ_on T)/σ_T(1)`: `σ² = 2/((α-1)(2-α)(3-α))`. This is the
corrected value; the paper prints (6.6) `σ² = (1/(3-α))[α/(2-α) + 2/μ_on]`. -/
noncomputable def sigma2 (α : ℝ) : ℝ :=
  2 / ((α - 1) * (2 - α) * (3 - α))

/-- `σ_1² = α/((2-α)(3-α))` of (4.9). -/
noncomputable def sigma1sq (α : ℝ) : ℝ :=
  α / ((2 - α) * (3 - α))

/-- The Hurst index of the limit, `H = (3 - α)/2`. -/
noncomputable def hurst (α : ℝ) : ℝ :=
  (3 - α) / 2

/-- §6.3, p. 57: the normalised input process of the `T`-th model,
`G_T(t) = (A(Tt) - λμ_on T t) / [λ T³ F̄_on(T) σ²]^{1/2}`, `t ≥ 0`, with the corrected `σ²`. -/
noncomputable def G {Ω : Type*} (Fon : Measure ℝ) (α : ℝ) (lam : ℝ → ℝ) (Γ X : ℤ → Ω → ℝ)
    (T : ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  (NetTraffic.PoissonStable.A Γ X (T * t) ω - lam T * NetTraffic.PoissonStable.muOn Fon * T * t) / Real.sqrt (sigmaT2 Fon lam T * sigma2 α)

/-- §6, p. 55: `B` is a **standard fractional Brownian motion** with Hurst index `H` under `P`: a
mean-zero Gaussian process on `[0, ∞)` with a.s. continuous sample paths and covariance
`Cov(B(t), B(s)) = ½(t^{2H} + s^{2H} - |t - s|^{2H})` (`σ_H = 1`). -/
def IsStdFBM {Ω : Type*} [MeasurableSpace Ω] (H : ℝ) (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) : Prop :=
  IsGaussianProcess B P ∧ (∀ t, P[B t] = 0) ∧
    (∀ s t : ℝ≥0, cov[B s, B t; P] =
      (1 / 2) * ((t : ℝ) ^ (2 * H) + (s : ℝ) ^ (2 * H) - |(t : ℝ) - s| ^ (2 * H))) ∧
    ∀ᵐ ω ∂P, Continuous (fun t => B t ω)

/-! ### The Skorokhod space `(𝔻[0, ∞), J₁)` -/

/-- A **càdlàg** path `x : [0, ∞) → ℝ`: right-continuous at every `t ≥ 0`, with a left limit at
every `t > 0`. -/
def IsCadlag (x : ℝ≥0 → ℝ) : Prop :=
  (∀ t : ℝ≥0, ContinuousWithinAt x (Set.Ici t) t) ∧
    ∀ t : ℝ≥0, 0 < t → ∃ a : ℝ, Tendsto x (𝓝[<] t) (𝓝 a)

/-- A time change: a continuous, strictly increasing map of `[0, ∞)` onto `[0, ∞)`. -/
def IsTimeChange (l : ℝ≥0 → ℝ≥0) : Prop :=
  Continuous l ∧ StrictMono l ∧ Function.Surjective l

/-- Uniform convergence on bounded intervals: uniformly on `[0, K]` for every `K`. -/
def TendstoUniformlyOnBounded {E : Type*} [MetricSpace E] (xs : ℕ → ℝ≥0 → E) (x : ℝ≥0 → E) :
    Prop :=
  ∀ K : ℝ≥0, TendstoUniformlyOn xs x atTop (Set.Icc 0 K)

/-- **`J₁` (Skorokhod) convergence** in `𝔻[0, ∞)`: the càdlàg paths `x_n` converge to the càdlàg
path `x` if there are time changes `λ_n` with `x_n ∘ λ_n → x` and `λ_n → id` uniformly on
bounded intervals. -/
def SkorohodTendsto (xs : ℕ → ℝ≥0 → ℝ) (x : ℝ≥0 → ℝ) : Prop :=
  (∀ n, IsCadlag (xs n)) ∧ IsCadlag x ∧
    ∃ l : ℕ → ℝ≥0 → ℝ≥0, (∀ n, IsTimeChange (l n)) ∧
      TendstoUniformlyOnBounded (fun n => xs n ∘ l n) x ∧ TendstoUniformlyOnBounded l id

end NetTraffic.PoissonFBM


