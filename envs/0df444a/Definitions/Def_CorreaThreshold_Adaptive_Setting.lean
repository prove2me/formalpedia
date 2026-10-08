-- Prove2me | Definitions.Def_CorreaThreshold_Adaptive_Setting
-- name    : CorreaThreshold_Adaptive_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T12:36:18.20617+00:00
-- url     : https://prove2.me/theorems/d50b4b00-bc1c-4bbc-baef-c815bc962382
-- title:
--   §4, pp. 1461–1464 — threshold rules, the quantile function F⁻¹, R(q), the quantile stopping rule, ψ, γᵢ, ρᵢ, the DP thresholds, (ODE) and the recursion (9)
-- statement:
--   Throughout, $X_1,\ldots,X_n$ are i.i.d. with common law $\mu$ on $\mathbb R$, where $\mu$ is a probability measure with $\mu((-\infty,0))=0$ (the variables are nonnegative), and $F(x)=\mu((-\infty,x])$ is their distribution function. This file fixes the objects of the adaptive threshold rule of §4.
--
--   1. **Threshold rules.** For thresholds $\tau_1,\ldots,\tau_n$, the rule stops at $t=\min\{i : X_i\ge\tau_i\}$ and receives $X_t$; when no $X_i$ reaches its threshold it receives $0$. A variant chooses at each step whether to stop when $X_i\ge\tau_i$ or when $X_i>\tau_i$.
--   2. **Quantiles.** The generalized inverse is $F^{-1}(q)=\inf\{x\ge0 : F(x)\ge q\}$, and $\tau(q)=F^{-1}(1-q)$. The quantity
--   $$R(q)=\int_0^q F^{-1}(1-\theta)\,d\theta\in[0,\infty]$$
--   is the expected reward from a variable accepted with probability $q$.
--   3. **The quantile stopping rule.** Given an acceptance probability $q$, the rule stops on a value $X$ if $X>\tau(q)$, and if $X=\tau(q)$ it stops with probability $s=[q-P(X>\tau(q))]/P(X=\tau(q))$, realised by an independent uniform coin $U$ on $[0,1]$ (stop iff $U\le s$). With acceptance probabilities $q_1,\ldots,q_n$ it scans $X_1,\ldots,X_n$ and takes the value at the first stop ($0$ if none).
--   4. **Random acceptance probabilities.** For $0=\varepsilon_0<\varepsilon_1<\cdots<\varepsilon_n=1$ and $A_i=[\varepsilon_{i-1},\varepsilon_i]$, let $\psi(q)=(n-1)(1-q)^{n-2}$, $\gamma_i=\int_{A_i}\psi(q)\,dq$, and let $q_i$ have density $f_i=\psi/\gamma_i$ on $A_i$, independently of each other, of the $X_i$ and of the coins. $E(X_r)$ is the expected reward of the quantile rule run with these $q_i$. Further $\rho_1=1/\gamma_1$ and $\rho_{i+1}=(\rho_i/\gamma_{i+1})\int_{\varepsilon_{i-1}}^{\varepsilon_i}\psi(q)(1-q)\,dq$.
--   5. **Dynamic programming.** $W_0=0$ and $W_{k+1}=E[\max(X,W_k)]$; the paper's $V_i$ is $W_{n-i+1}$, and the optimal thresholds are $\tau_n=0$, $\tau_i=V_{i+1}$.
--   6. **(ODE).** $y$ solves $y'(t)=y(t)(\ln y(t)-1)-(\beta-1)$, $y(0)=1$ on $[0,T]$ if it is continuous on $[0,T]$, has this right derivative at every $t\in[0,T)$ and takes values in $(0,1]$ there; $y(T)$ is the continuous extension.
--   7. **The recursion (9).** $w_1=x_1^{n-1}$ and $w_{i+1}=\frac{n-1}{n}\max(w_i,0)^{n/(n-1)}+x_1^{n-1}-\frac{n-1}{n}$, so that $w_i=x_i^{n-1}$ while the recursion stays nonnegative.
--
--   These are the objects in which Theorem 2 and its lemmas are stated.
--
--   **Formalization Note** Indices of the sample are 0-based in Lean: the paper's $X_i$ ($i=1,\ldots,n$) is coordinate $i-1$ of the sample. The intervals $A_i$, $\gamma_i$, $\rho_i$, $\varepsilon_i$ and the recursion keep the paper's 1-based index. Expectations of the variables are lower Lebesgue integrals in $[0,\infty]$, so an infinite mean is allowed. Lean's $\inf\emptyset=0$: $F^{-1}(1)$, i.e. $\tau(0)$, is $0$ when the support is unbounded; statements that evaluate $\tau(q)$ take $q\in(0,1]$. When $P(X=\tau(q))=0$, Lean's $s$ is $0$, so the rule differs from "stop if $X\ge\tau(q)$" only on the null event $\{X=\tau(q)\}$. The paper's recurrence for $V_i$ is printed as $V_i=E(X\mid X\ge\tau_i)$; the optimal-stopping value used here is $V_i=E[\max(X,V_{i+1})]$ (see the Theorem 2 milestones). `dpW` is a Bochner integral and is meaningful only for integrable $X$; every theorem using it assumes integrability. `rho n ε 0 = 0` and `wseq n x₁ 0 = 1` are conventions outside the paper's range.
-- source:
--   Correa, Foncea, Hoeksma, Oosterwijk, Vredeveld, Posted price mechanisms and optimal threshold strategies for random arrivals, Math. Oper. Res. 46 (2021), pp. 1461–1464, §4, Algorithm 2, Table 1, the quantile stopping rule, (ODE), (9), and the proof of Theorem 2

import Mathlib
import Definitions.Def_SamuelCahnProphet_IID_Setting

namespace CorreaThreshold.Adaptive

open MeasureTheory ProbabilityTheory

/-! ### Deterministic threshold rules (Theorem 2, p. 1464) -/

/-- The reward of the rule that stops at the first (0-based) index `i` satisfying `stop i`,
on the sample `x`: the value `x i` at that index, and `0` if no index satisfies `stop`. -/
noncomputable def firstReward {n : ℕ} (stop : Fin n → Prop) (x : Fin n → ℝ) : ℝ := by
  classical
  exact if h : (Finset.univ.filter stop).Nonempty then x ((Finset.univ.filter stop).min' h) else 0

/-- `X_t` with `t := min {i : Xᵢ ≥ τᵢ}` (Theorem 2, p. 1464), and `0` if no `Xᵢ ≥ τᵢ`. -/
noncomputable def stopReward {n : ℕ} (τ : Fin n → ℝ) (x : Fin n → ℝ) : ℝ :=
  firstReward (fun i => τ i ≤ x i) x

/-- A deterministic threshold rule that, at each index `i`, stops when `xᵢ > τᵢ` if `σ i = true`
and when `xᵢ ≥ τᵢ` if `σ i = false`; its reward, `0` if it never stops. -/
noncomputable def stopRewardMixed {n : ℕ} (τ : Fin n → ℝ) (σ : Fin n → Bool) (x : Fin n → ℝ) : ℝ :=
  firstReward (fun i => if σ i then τ i < x i else τ i ≤ x i) x

/-! ### The quantile function and `R(q)` (§4, p. 1461) -/

/-- The generalized inverse `F⁻¹(q) = inf {x ≥ 0 | F(x) ≥ q}` of the distribution function `F` of `μ`
(p. 1461). Lean's `sInf ∅ = 0`: `Finv μ 1` is `0` when the support is unbounded. -/
noncomputable def Finv (μ : Measure ℝ) (q : ℝ) : ℝ :=
  sInf {x : ℝ | 0 ≤ x ∧ q ≤ cdf μ x}

/-- `τ(q) = F⁻¹(1 − q)` (p. 1461). -/
noncomputable def tauQ (μ : Measure ℝ) (q : ℝ) : ℝ :=
  Finv μ (1 - q)

/-- `R(q) = ∫₀^q F⁻¹(1 − θ) dθ` (p. 1461, Table 1), in `[0, ∞]`. -/
noncomputable def Rq (μ : Measure ℝ) (q : ℝ) : ENNReal :=
  ∫⁻ θ in Set.Ioc 0 q, ENNReal.ofReal (Finv μ (1 - θ))

/-! ### The quantile stopping rule (p. 1462) -/

/-- The uniform law on `[0, 1]`, used for the tie-breaking coins. -/
noncomputable def unif01 : Measure ℝ :=
  volume.restrict (Set.Icc (0 : ℝ) 1)

/-- `s = [q − P(X > τ(q))] / P(X = τ(q))` (p. 1462). -/
noncomputable def sProb (μ : Measure ℝ) (q : ℝ) : ℝ :=
  (q - (μ (Set.Ioi (tauQ μ q))).toReal) / (μ {tauQ μ q}).toReal

/-- The quantile rule with acceptance probability `q` stops on the value `x` with coin `u`
(p. 1462): stop if `x > τ(q)`, and if `x = τ(q)` stop when the uniform coin `u ≤ s`
(that is, with probability `s`). -/
def stopQ (μ : Measure ℝ) (q x u : ℝ) : Prop :=
  tauQ μ q < x ∨ (x = tauQ μ q ∧ u ≤ sProb μ q)

/-- The reward of the quantile rule with acceptance probabilities `q : Fin n → ℝ` (0-based) on the
sample `x` and the coins `u`: the value at the first stop, `0` if it never stops. -/
noncomputable def ruleReward (μ : Measure ℝ) {n : ℕ} (q : Fin n → ℝ) (x u : Fin n → ℝ) : ℝ :=
  firstReward (fun i => stopQ μ (q i) (x i) (u i)) x

/-- The expected reward of the quantile rule for fixed acceptance probabilities `q`, over
`X₁, …, Xₙ` i.i.d. of law `μ` and independent uniform coins `U₁, …, Uₙ`. -/
noncomputable def ruleValue (μ : Measure ℝ) {n : ℕ} (q : Fin n → ℝ) : ENNReal :=
  ∫⁻ p, ENNReal.ofReal (ruleReward μ q p.1 p.2)
    ∂((SamuelCahnProphet.IID.iidLaw μ n).prod (Measure.pi (fun _ : Fin n => unif01)))

/-! ### The sampling of the acceptance probabilities (Table 1, p. 1461; p. 1462) -/

/-- `ψ(q) = (n − 1)(1 − q)^{n−2}` (Table 1). -/
noncomputable def psi (n : ℕ) (q : ℝ) : ℝ :=
  ((n : ℝ) - 1) * (1 - q) ^ (n - 2)

/-- `γᵢ = ∫_{Aᵢ} ψ(q) dq` with `Aᵢ = [ε_{i−1}, εᵢ]` (Table 1), with the paper's 1-based `i`. -/
noncomputable def gam (n : ℕ) (ε : ℕ → ℝ) (i : ℕ) : ℝ :=
  ∫ q in ε (i - 1)..ε i, psi n q

/-- `ρ₁ = 1/γ₁` and `ρᵢ₊₁ = (ρᵢ/γᵢ₊₁) ∫_{ε_{i−1}}^{εᵢ} ψ(q)(1 − q) dq` (Table 1, Lemma 4), 1-based;
`rho n ε 0 = 0` is not used. -/
noncomputable def rho (n : ℕ) (ε : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | 1 => 1 / gam n ε 1
  | (i + 2) => rho n ε (i + 1) / gam n ε (i + 2) * ∫ q in ε i..ε (i + 1), psi n q * (1 - q)

/-- The law of the `i`-th acceptance probability `qᵢ` (1-based): density `fᵢ = ψ/γᵢ` on
`Aᵢ = [ε_{i−1}, εᵢ]` (p. 1462). -/
noncomputable def qLaw (n : ℕ) (ε : ℕ → ℝ) (i : ℕ) : Measure ℝ :=
  (volume.restrict (Set.Icc (ε (i - 1)) (ε i))).withDensity
    (fun q => ENNReal.ofReal (psi n q / gam n ε i))

/-- `E(X_r)`, the expected reward of the quantile stopping rule (Algorithm 2, p. 1462): the
acceptance probabilities `q₁, …, qₙ` are drawn independently, `qᵢ` from `qLaw n ε i`
(0-based coordinate `j` carries the paper's `q_{j+1}`), independently of the `Xᵢ` and the coins. -/
noncomputable def quantileValue (μ : Measure ℝ) (n : ℕ) (ε : ℕ → ℝ) : ENNReal :=
  ∫⁻ q, ruleValue μ q ∂(Measure.pi (fun j : Fin n => qLaw n ε (j.val + 1)))

/-! ### The optimal (dynamic-programming) thresholds (proof of Theorem 2, p. 1464) -/

/-- The optimal value with `k` variables left: `W 0 = 0`, `W (k + 1) = E[max(X, W k)]`.
The paper's `Vᵢ` (`i = 1, …, n`) is `dpW μ (n − i + 1)`; the Bochner integral needs `X` integrable. -/
noncomputable def dpW (μ : Measure ℝ) : ℕ → ℝ
  | 0 => 0
  | (k + 1) => ∫ x, max x (dpW μ k) ∂μ

/-- The dynamic-programming thresholds `τₙ = 0`, `τᵢ = V_{i+1}`; 0-based index `j` is the paper's
`i = j + 1`, so `τ_{j+1} = dpW μ (n − (j + 1))`. -/
noncomputable def tauDP (μ : Measure ℝ) (n : ℕ) (j : Fin n) : ℝ :=
  dpW μ (n - (j.val + 1))

/-! ### The differential equation and the recursion (pp. 1463–1464) -/

/-- `y` solves (ODE) `y′ = y(ln y − 1) − (β − 1)`, `y(0) = 1`, on `[0, T]` (p. 1464): `y` is continuous
on `[0, T]`, has the right derivative given by (ODE) at every `t ∈ [0, T)`, and takes values in
`(0, 1]` there; `y(T)` is the continuous extension. -/
def IsODESol (β : ℝ) (y : ℝ → ℝ) (T : ℝ) : Prop :=
  ContinuousOn y (Set.Icc 0 T) ∧ y 0 = 1 ∧
    (∀ t ∈ Set.Ico 0 T, HasDerivWithinAt y (y t * (Real.log (y t) - 1) - (β - 1)) (Set.Ici t) t) ∧
    (∀ t ∈ Set.Ico 0 T, 0 < y t ∧ y t ≤ 1)

/-- `wᵢ = xᵢ^{n−1}` along the recursion (9) started at `x₁` (p. 1463), 1-based:
`w₁ = x₁^{n−1}` and `w_{i+1} = ((n − 1)/n) max(wᵢ, 0)^{n/(n−1)} + x₁^{n−1} − (n − 1)/n`;
`wseq n x₁ 0 = 1` is `x₀^{n−1}`. -/
noncomputable def wseq (n : ℕ) (x₁ : ℝ) : ℕ → ℝ
  | 0 => 1
  | 1 => x₁ ^ (n - 1)
  | (i + 2) => ((n : ℝ) - 1) / n * (max (wseq n x₁ (i + 1)) 0) ^ ((n : ℝ) / ((n : ℝ) - 1))
      + x₁ ^ (n - 1) - ((n : ℝ) - 1) / n

end CorreaThreshold.Adaptive


