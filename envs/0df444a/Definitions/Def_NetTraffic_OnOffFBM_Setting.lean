-- Prove2me | Definitions.Def_NetTraffic_OnOffFBM_Setting
-- name    : NetTraffic_OnOffFBM_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T00:02:54.30292+00:00
-- url     : https://prove2.me/theorems/bc24a284-e3b8-43e8-966e-d8856715ae3e
-- title:
--   §2.1, §3.2, §6, §7 — the superposed ON/OFF model, W, N, A, (2.1)–(2.2), b, Condition 2, G_T, d_T, σ₀², H, standard FBM, convergence in ℂ[0,∞)
-- statement:
--   This file fixes every object of the superposed ON/OFF model under fast growth (Mikosch, Resnick, Rootzén and Stegeman 2002, §2.1, §3.2, §6 and §7).
--
--   1. **Heavy tails (2.1)–(2.2).** $F_{\mathrm{on}}$ and $F_{\mathrm{off}}$ are the laws of the ON- and OFF-periods, probability measures on $[0,\infty)$ with tails $\bar F(x)=F((x,\infty))$ and means $\mu_{\mathrm{on}}$, $\mu_{\mathrm{off}}$; $\mu=\mu_{\mathrm{on}}+\mu_{\mathrm{off}}$. For $x>0$,
--   $$\bar F_{\mathrm{on}}(x)=x^{-\alpha}L_{\mathrm{on}}(x),\qquad \bar F_{\mathrm{off}}(x)=x^{-\alpha_{\mathrm{off}}}L_{\mathrm{off}}(x),\qquad 1<\alpha=\alpha_{\mathrm{on}}<\alpha_{\mathrm{off}}<2,$$
--   with $L_{\mathrm{on}}$, $L_{\mathrm{off}}$ **slowly varying**: eventually positive, and $L(cx)/L(x)\to1$ as $x\to\infty$ for every $c>0$.
--   2. **The quantile function (2.9)** $b(t)=(1/\bar F_{\mathrm{on}})^{\leftarrow}(t)=\inf\{x>0:1/\bar F_{\mathrm{on}}(x)\ge t\}$, and **Fast Growth Condition 2** (§3.2): the number of sources $M=M(T)$ is integer valued, non-decreasing, $M(T)\to\infty$, and
--   $$\lim_{T\to\infty}\frac{b(MT)}{T}=\infty .$$
--   3. **One source** (§2.1). $X_1,X_2,\dots$ are iid $F_{\mathrm{on}}$; $Y_{\mathrm{off}},Y_1,Y_2,\dots$ are iid $F_{\mathrm{off}}$; $B$ is Bernoulli with $P(B=1)=\mu_{\mathrm{on}}/\mu$; $X^{(0)}_{\mathrm{on}}$ and $Y^{(0)}_{\mathrm{off}}$ have the integrated-tail laws $F^{(0)}(x)=\frac1{\mu_F}\int_0^x\bar F(s)\,ds$ of $F_{\mathrm{on}}$, $F_{\mathrm{off}}$; all these variables are independent. With $Z_i=X_i+Y_i$,
--   $$T_0=B(X^{(0)}_{\mathrm{on}}+Y_{\mathrm{off}})+(1-B)Y^{(0)}_{\mathrm{off}},\qquad T_n=T_0+\sum_{i=1}^nZ_i,$$
--   $$W_t=B\,\mathbf 1_{[0,X^{(0)}_{\mathrm{on}})}(t)+\sum_{n=0}^\infty\mathbf 1_{[T_n,T_n+X_{n+1})}(t),\qquad t\ge0 .$$
--   $\gamma_W(h)=\mathrm{Cov}(W_0,W_h)$ is its covariance function, and $G_T=\int_0^T(W_u-EW_u)\,du$ its centred cumulative workload.
--   4. **The superposition** (p. 27). $M$ independent sources $W^{(1)},\dots,W^{(M)}$; $N(t)=\sum_{m=1}^MW^{(m)}_t$ and $A(t)=\int_0^tN(s)\,ds$.
--   5. **Normalisation and limit** (§7). With $L_{\mathrm{on}}(T)=T^\alpha\bar F_{\mathrm{on}}(T)$ and $M=M(T)$,
--   $$d_T=[T^{3-\alpha}L_{\mathrm{on}}(T)M]^{1/2},\qquad \sigma_0^2=\frac{2\mu_{\mathrm{off}}^2\Gamma(2-\alpha)/(\alpha-1)}{\mu^3\Gamma(4-\alpha)},\qquad H=\frac{3-\alpha}2,$$
--   and the normalised input process is $\big(A(Tt)-TM\mu^{-1}\mu_{\mathrm{on}}t\big)/d_T$, $t\ge0$.
--   6. **Standard fractional Brownian motion** (§6, p. 55): a mean-zero Gaussian process $(B_H(t))_{t\ge0}$ with a.s. continuous paths and $\mathrm{Cov}(B_H(t),B_H(s))=\tfrac12(t^{2H}+s^{2H}-|t-s|^{2H})$.
--   7. **Convergence in $\mathbb C[0,\infty)$** of paths: uniform convergence on $[0,K]$ for every $K\ge0$.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** Each model $T$ carries its own probability space. The paper's $X_{n+1}$, $Y_{n+1}$ are Lean's `X n`, `Y n` ($n\ge0$), and the paper's sources $m=1,\dots,M$ are Lean's $m=0,\dots,M-1$. Lengths are non-negative ($F((-\infty,0))=0$, implicit in "lengths"). (2.1) is stated as "$x\mapsto x^{\alpha}\bar F(x)$ is slowly varying", which is equivalent. $b(t)$ is written $\inf\{x>0:t\bar F_{\mathrm{on}}(x)\le1\}$, the same set for $t>0$ without a division by zero. The series in $W_t$ is a sum of non-negative terms (`tsum`, $0$ if not summable, which happens only on a null event). The Bernoulli law and the integrated-tail laws are written as measures on $\mathbb R$. These definitions duplicate those of the companion slow-growth ON/OFF mission, because draft items cannot import each other.
-- source:
--   Mikosch, Resnick, Rootzén and Stegeman, Is network traffic approximated by stable Lévy motion or fractional Brownian motion?, Ann. Appl. Probab. 12 (2002), pp. 25–27, §2.1 (2.1)–(2.7); p. 28, (2.9); pp. 31–32, §3.2 Condition 2; p. 55, §6 definition of FBM; pp. 61–62, §7 d_T, G_T, σ₀², (7.2)

import Mathlib

namespace NetTraffic.OnOffFBM

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

/-! ### Heavy tails (2.1)–(2.2), the quantile (2.9) and the growth conditions of §3.2 -/

/-- The right tail `F̄(x) = 1 - F(x) = F((x, ∞))` of a law `F` on `ℝ`. -/
noncomputable def Fbar (F : Measure ℝ) (x : ℝ) : ℝ :=
  F.real (Set.Ioi x)

/-- A function `L` is **slowly varying** (at infinity): eventually positive, and
`L(cx)/L(x) → 1` as `x → ∞` for every `c > 0`. -/
def IsSlowlyVarying (L : ℝ → ℝ) : Prop :=
  (∀ᶠ x in atTop, 0 < L x) ∧
    ∀ c : ℝ, 0 < c → Tendsto (fun x => L (c * x) / L x) atTop (𝓝 1)

/-- The slowly varying factor of a tail with index `a`: `L(x) = x^a F̄(x)`, so that
`F̄(x) = x^{-a} L(x)` for `x > 0`. With `a = α_on` this is `L_on` of (2.1). -/
noncomputable def Lsv (F : Measure ℝ) (a : ℝ) (x : ℝ) : ℝ :=
  x ^ a * Fbar F x

/-- The mean `∫ x F(dx)` of a law `F` on `ℝ` (`μ_on` for `F_on`, `μ_off` for `F_off`). -/
noncomputable def mean (F : Measure ℝ) : ℝ :=
  ∫ x, x ∂F

/-- `μ = E Z_1 = μ_on + μ_off`, the mean length of an ON/OFF cycle. -/
noncomputable def mu (Fon Foff : Measure ℝ) : ℝ :=
  mean Fon + mean Foff

/-- Assumptions (2.1)–(2.2) on the period laws: ON- and OFF-periods are non-negative,
`1 < α_on = α < α_off < 2`, and `F̄_on(x) = x^{-α} L_on(x)`, `F̄_off(x) = x^{-α_off} L_off(x)`
for `x > 0` with `L_on`, `L_off` slowly varying (necessarily `L_on(x) = x^α F̄_on(x)` and
`L_off(x) = x^{α_off} F̄_off(x)`). -/
structure HeavyTails (Fon Foff : Measure ℝ) (α αoff : ℝ) : Prop where
  on_nonneg : Fon (Set.Iio 0) = 0
  off_nonneg : Foff (Set.Iio 0) = 0
  one_lt : 1 < α
  lt_off : α < αoff
  off_lt_two : αoff < 2
  sv_on : IsSlowlyVarying (Lsv Fon α)
  sv_off : IsSlowlyVarying (Lsv Foff αoff)

/-- The quantile function (2.9) of `F_on`, `b(t) = (1/F̄_on)^←(t) = inf{x : 1/F̄_on(x) ≥ t}`,
written as `inf{x > 0 : t F̄_on(x) ≤ 1}` (the same set for `t > 0`, without division by zero). -/
noncomputable def b (Fon : Measure ℝ) (t : ℝ) : ℝ :=
  sInf {x : ℝ | 0 < x ∧ t * Fbar Fon x ≤ 1}

/-- §3.2: the number of sources `M = M(T)` is integer valued, non-decreasing in `T`, and
`M(T) → ∞` as `T → ∞`. -/
structure SourceCount (M : ℝ → ℕ) : Prop where
  mono : Monotone M
  tendsto : Tendsto M atTop atTop

/-- **Fast Growth Condition 2** (§3.2, p. 32): `b(MT)/T → ∞` as `T → ∞`. -/
def Condition2 (Fon : Measure ℝ) (M : ℝ → ℕ) : Prop :=
  Tendsto (fun T => b Fon ((M T : ℝ) * T) / T) atTop atTop

/-! ### One ON/OFF source, §2.1 -/

/-- The integrated-tail (equilibrium) law `F^{(0)}` of a law `F` on `[0, ∞)` with mean `m`:
`F^{(0)}(x) = (1/m) ∫_0^x F̄(s) ds`, i.e. the law with density `F̄(s)/m` on `(0, ∞)`. -/
noncomputable def eqLaw (F : Measure ℝ) : Measure ℝ :=
  (volume.restrict (Set.Ioi (0 : ℝ))).withDensity (fun s => ENNReal.ofReal (Fbar F s / mean F))

/-- The Bernoulli law with `P(B = 1) = μ_on/μ = 1 - P(B = 0)`, as a law on `ℝ`. -/
noncomputable def bernoulliLaw (Fon Foff : Measure ℝ) : Measure ℝ :=
  ENNReal.ofReal (mean Fon / mu Fon Foff) • Measure.dirac 1 +
    ENNReal.ofReal (mean Foff / mu Fon Foff) • Measure.dirac 0

/-- The random ingredients of one ON/OFF source (§2.1): the Bernoulli variable `B`, the
initial ON-period `X_on^{(0)}` (`X0`), the initial OFF-period `Y_off^{(0)}` (`Y0`), the
OFF-period `Y_off` used in the delay `T_0`, and the ON- and OFF-periods `X`, `Y`.
**Index convention:** `X n`, `Y n` (`n = 0, 1, 2, …`) are the paper's `X_{n+1}`, `Y_{n+1}`. -/
structure Source (Ω : Type*) where
  B : Ω → ℝ
  X0 : Ω → ℝ
  Y0 : Ω → ℝ
  Yoff : Ω → ℝ
  X : ℕ → Ω → ℝ
  Y : ℕ → Ω → ℝ

/-- All ingredients of a source, as one random element. -/
def Source.data {Ω : Type*} (s : Source Ω) (ω : Ω) :
    ℝ × ℝ × ℝ × ℝ × (ℕ → ℝ) × (ℕ → ℝ) :=
  (s.B ω, s.X0 ω, s.Y0 ω, s.Yoff ω, fun n => s.X n ω, fun n => s.Y n ω)

/-- The ingredients of a source indexed as one family: `0 ↦ B`, `1 ↦ X_on^{(0)}`,
`2 ↦ Y_off^{(0)}`, `3 ↦ Y_off`, `inr (inl n) ↦ X n`, `inr (inr n) ↦ Y n`. -/
def Source.family {Ω : Type*} (s : Source Ω) : Fin 4 ⊕ (ℕ ⊕ ℕ) → Ω → ℝ :=
  Sum.elim ![s.B, s.X0, s.Y0, s.Yoff] (Sum.elim s.X s.Y)

/-- §2.1: `s` is a (stationary) ON/OFF source with period laws `F_on`, `F_off` under `P`:
the ON-periods `X_1, X_2, …` are iid `F_on`, the OFF-periods `Y_off, Y_1, Y_2, …` are iid
`F_off`, `B` is Bernoulli with `P(B = 1) = μ_on/μ`, `X_on^{(0)} ∼ F_on^{(0)}`,
`Y_off^{(0)} ∼ F_off^{(0)}`, and all of these variables are mutually independent. -/
structure IsOnOffSource {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (Fon Foff : Measure ℝ)
    (s : Source Ω) : Prop where
  measurable : ∀ i, Measurable (s.family i)
  indep : iIndepFun s.family P
  law_B : P.map s.B = bernoulliLaw Fon Foff
  law_X0 : P.map s.X0 = eqLaw Fon
  law_Y0 : P.map s.Y0 = eqLaw Foff
  law_Yoff : P.map s.Yoff = Foff
  law_X : ∀ n, P.map (s.X n) = Fon
  law_Y : ∀ n, P.map (s.Y n) = Foff

/-- The delay `T_0 = B(X_on^{(0)} + Y_off) + (1 - B) Y_off^{(0)}`. -/
def Source.T0 {Ω : Type*} (s : Source Ω) (ω : Ω) : ℝ :=
  s.B ω * (s.X0 ω + s.Yoff ω) + (1 - s.B ω) * s.Y0 ω

/-- (2.3): the stationary renewal sequence `T_n = T_0 + Σ_{i=1}^n Z_i`, `Z_i = X_i + Y_i`
(in Lean indices, `T n = T_0 + Σ_{i<n} (X i + Y i)`). -/
def Source.Tn {Ω : Type*} (s : Source Ω) (n : ℕ) (ω : Ω) : ℝ :=
  s.T0 ω + ∑ i ∈ Finset.range n, (s.X i ω + s.Y i ω)

/-- (2.4): the ON/OFF process of one source,
`W_t = B 1_{[0, X_on^{(0)})}(t) + Σ_{n ≥ 0} 1_{[T_n, T_n + X_{n+1})}(t)`, `t ≥ 0`
(the ON-period starting at `T_n` is the paper's `X_{n+1}`, Lean's `X n`). The series is a
`tsum` of non-negative terms (`0` if not summable, which happens only on a null event). -/
noncomputable def Source.W {Ω : Type*} (s : Source Ω) (t : ℝ) (ω : Ω) : ℝ :=
  s.B ω * (Set.Ico 0 (s.X0 ω)).indicator (fun _ => (1 : ℝ)) t +
    ∑' n : ℕ, (Set.Ico (s.Tn n ω) (s.Tn n ω + s.X n ω)).indicator (fun _ => (1 : ℝ)) t

/-- The covariance function `γ_W(h) = Cov(W_0, W_h)` of the stationary process `W`. -/
noncomputable def gammaW {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (s : Source Ω)
    (h : ℝ) : ℝ :=
  cov[s.W 0, s.W h; P]

/-- §7, p. 61: the centred cumulative workload of one source,
`G_T = ∫_0^T (W_u - E W_u) du`. -/
noncomputable def Source.G {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (s : Source Ω)
    (T : ℝ) (ω : Ω) : ℝ :=
  ∫ u in (0 : ℝ)..T, (s.W u ω - P[s.W u])

/-! ### The superposition of `M` sources, §2.1 p. 27 -/

/-- The `T`-th model: under `P`, `src 0, …, src (M-1)` (the paper's sources `m = 1, …, M`)
are independent ON/OFF sources with period laws `F_on`, `F_off`. -/
structure IsOnOffSuperposition {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Fon Foff : Measure ℝ) (M : ℕ) (src : ℕ → Source Ω) : Prop where
  source : ∀ m, m < M → IsOnOffSource P Fon Foff (src m)
  indep : iIndepFun (fun m : Fin M => (src m).data) P

/-- The number of active sources `N(t) = Σ_{m=1}^M W_t^{(m)}`. -/
noncomputable def N {Ω : Type*} (M : ℕ) (src : ℕ → Source Ω) (t : ℝ) (ω : Ω) : ℝ :=
  ∑ m ∈ Finset.range M, (src m).W t ω

/-- (2.7): the cumulative input `A(t) = ∫_0^t N(s) ds`. -/
noncomputable def A {Ω : Type*} (M : ℕ) (src : ℕ → Source Ω) (t : ℝ) (ω : Ω) : ℝ :=
  ∫ s in (0 : ℝ)..t, N M src s ω

/-! ### The normalisation and the limit, §7 -/

/-- §7, p. 61: `d_T = [T^{3-α} L_on(T) M]^{1/2}` with `L_on(T) = T^α F̄_on(T)` and `M = M(T)`. -/
noncomputable def dT (Fon : Measure ℝ) (α : ℝ) (M : ℝ → ℕ) (T : ℝ) : ℝ :=
  Real.sqrt (T ^ (3 - α) * Lsv Fon α T * (M T : ℝ))

/-- §7, p. 61: `σ_0² = [2 μ_off² Γ(2-α)/(α-1)] / [μ³ Γ(4-α)]`. -/
noncomputable def sigma0sq (Fon Foff : Measure ℝ) (α : ℝ) : ℝ :=
  (2 * mean Foff ^ 2 * Real.Gamma (2 - α) / (α - 1)) /
    (mu Fon Foff ^ 3 * Real.Gamma (4 - α))

/-- `σ_0 = (σ_0²)^{1/2}`. -/
noncomputable def sigma0 (Fon Foff : Measure ℝ) (α : ℝ) : ℝ :=
  Real.sqrt (sigma0sq Fon Foff α)

/-- The Hurst index of the limit, `H = (3 - α)/2`. -/
noncomputable def hurst (α : ℝ) : ℝ :=
  (3 - α) / 2

/-- (7.2): the normalised cumulative input of the `T`-th model,
`(A(Tt) - T M μ^{-1} μ_on t)/d_T`, `t ≥ 0`, with `M = M(T)`. -/
noncomputable def Gnorm {Ω : Type*} (Fon Foff : Measure ℝ) (α : ℝ) (M : ℝ → ℕ)
    (src : ℕ → Source Ω) (T : ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  (A (M T) src (T * t) ω - T * (M T : ℝ) * (mu Fon Foff)⁻¹ * mean Fon * t) / dT Fon α M T

/-- §6, p. 55: `B` is a **standard fractional Brownian motion** with Hurst index `H` under `P`:
a mean-zero Gaussian process on `[0, ∞)` with a.s. continuous sample paths and covariance
`Cov(B(t), B(s)) = ½(t^{2H} + s^{2H} - |t - s|^{2H})` (`σ_H = 1`). -/
def IsStdFBM {Ω : Type*} [MeasurableSpace Ω] (H : ℝ) (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) : Prop :=
  IsGaussianProcess B P ∧ (∀ t, P[B t] = 0) ∧
    (∀ s t : ℝ≥0, cov[B s, B t; P] =
      (1 / 2) * ((t : ℝ) ^ (2 * H) + (s : ℝ) ^ (2 * H) - |(t : ℝ) - s| ^ (2 * H))) ∧
    ∀ᵐ ω ∂P, Continuous (fun t => B t ω)

/-- Convergence in `ℂ[0, ∞)`: uniform convergence on `[0, K]` for every `K ≥ 0` (locally
uniform convergence on `[0, ∞)`). -/
def UocTendsto (xs : ℕ → ℝ≥0 → ℝ) (x : ℝ≥0 → ℝ) : Prop :=
  ∀ K : ℝ≥0, TendstoUniformlyOn xs x atTop (Set.Icc 0 K)

end NetTraffic.OnOffFBM


