-- Prove2me | Definitions.Def_NetTraffic_OnOffStable_Setting
-- name    : NetTraffic_OnOffStable_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T02:14:09.071351+00:00
-- url     : https://prove2.me/theorems/f13eeae3-136a-4735-bd7c-70679c7419d4
-- title:
--   §2.1, §3.2, §4–§5 — the superposed ON/OFF model, W, N, A, (2.1)–(2.2), b, Condition 1, ξ_T, A₁, A₃, J_k, S_n, A₂₁, Θ_T, S_α(σ, β, μ), X_{α,σ,β} fidis, C_α, c, σ
-- statement:
--   This file fixes every object of the superposed ON/OFF model under slow growth (Mikosch, Resnick, Rootzén and Stegeman 2002, §2.1, §3.2, §4 and §5).
--
--   1. **Heavy tails (2.1)–(2.2).** $F_{\mathrm{on}}$ and $F_{\mathrm{off}}$ are the laws of the ON- and OFF-periods, probability measures on $[0,\infty)$ with right tails $\bar F(x)=F((x,\infty))$ and means $\mu_{\mathrm{on}}$, $\mu_{\mathrm{off}}$; $\mu=\mu_{\mathrm{on}}+\mu_{\mathrm{off}}$. For $x>0$,
--   $$\bar F_{\mathrm{on}}(x)=x^{-\alpha}L_{\mathrm{on}}(x),\qquad \bar F_{\mathrm{off}}(x)=x^{-\alpha_{\mathrm{off}}}L_{\mathrm{off}}(x),\qquad 1<\alpha=\alpha_{\mathrm{on}}<\alpha_{\mathrm{off}}<2,$$
--   with $L_{\mathrm{on}}$, $L_{\mathrm{off}}$ **slowly varying**: eventually positive, and $L(cx)/L(x)\to1$ as $x\to\infty$ for every $c>0$.
--   2. **The quantile function (2.9)** $b(t)=(1/\bar F_{\mathrm{on}})^{\leftarrow}(t)=\inf\{x>0:t\,\bar F_{\mathrm{on}}(x)\le1\}$, and **Slow Growth Condition 1** (§3.2): the number of sources $M=M(T)$ is integer valued, non-decreasing, $M(T)\to\infty$, and
--   $$\lim_{T\to\infty}\frac{b(MT)}{T}=0 .$$
--   3. **One source** (§2.1). $X_1,X_2,\dots$ are iid $F_{\mathrm{on}}$; $Y_{\mathrm{off}},Y_1,Y_2,\dots$ are iid $F_{\mathrm{off}}$; $B$ is Bernoulli with $P(B=1)=\mu_{\mathrm{on}}/\mu$; $X^{(0)}_{\mathrm{on}}$ and $Y^{(0)}_{\mathrm{off}}$ have the integrated-tail laws $F^{(0)}(x)=\frac1{\mu_F}\int_0^x\bar F(s)\,ds$ of $F_{\mathrm{on}}$, $F_{\mathrm{off}}$; all these variables are independent. With $Z_i=X_i+Y_i$,
--   $$T_0=B(X^{(0)}_{\mathrm{on}}+Y_{\mathrm{off}})+(1-B)Y^{(0)}_{\mathrm{off}},\qquad T_n=T_0+\sum_{i=1}^nZ_i,$$
--   $$W_t=B\,\mathbf 1_{[0,X^{(0)}_{\mathrm{on}})}(t)+\sum_{n=0}^\infty\mathbf 1_{[T_n,T_n+X_{n+1})}(t),\qquad t\ge0 .$$
--   4. **The superposition** (p. 27). $M$ independent such sources $W^{(1)},\dots,W^{(M)}$; $N(t)=\sum_{m=1}^MW^{(m)}_t$ and $A(t)=\int_0^tN(s)\,ds$.
--   5. **Proof objects of §5.** The renewal count $\xi_T=\sum_{n\ge0}\mathbf 1_{[0,T]}(T_n)$ with mean $\mu_T=T/\mu$; $A_1=\sum_{m}B^{(m)}\min(T,(X^{(0)}_{\mathrm{on}})^{(m)})$; $A_3=\sum_m\max(0,T^{(m)}_{\xi^{(m)}_T-1}+X^{(m)}_{\xi^{(m)}_T}-T)\mathbf 1_{[\xi^{(m)}_T\ge1]}$; $r_{\mathrm{on}}=\mu_{\mathrm{off}}/\mu$, $r_{\mathrm{off}}=\mu_{\mathrm{on}}/\mu$; $J_k=r_{\mathrm{on}}(X_k-\mu_{\mathrm{on}})-r_{\mathrm{off}}(Y_k-\mu_{\mathrm{off}})$; $S_n=\sum_{k=1}^nJ_k$, $S^{(1)}_n=r_{\mathrm{on}}\sum_{k=1}^n(X_k-\mu_{\mathrm{on}})$; $S_{T,m}=\sum_{k=1}^{\xi^{(m)}_T}J^{(m)}_k$, $A_{21}=\sum_{m=1}^MS_{T,m}$; and the event $\Theta_T=\{|\xi_T-\mu_T|\le\varepsilon_T\mu_T\}$ (5.11).
--   6. **Stable laws** (§4, p. 32). $S_\alpha(\sigma,\beta,\mu)$ is the law with characteristic function
--   $$\varphi(\theta)=\begin{cases}\exp\{-\sigma^\alpha|\theta|^\alpha(1-i\beta\,\mathrm{sign}(\theta)\tan\frac{\pi\alpha}2)+i\mu\theta\},&\alpha\ne1,\\ \exp\{-\sigma|\theta|(1+i\beta\frac2\pi\mathrm{sign}(\theta)\ln|\theta|)+i\mu\theta\},&\alpha=1.\end{cases}$$
--   The **α-stable Lévy motion** $X_{\alpha,\sigma,\beta}$ has independent stationary increments with $X(t)-X(s)\sim S_\alpha(\sigma(t-s)^{1/\alpha},\beta,0)$; for $0\le t_1\le\dots\le t_k$ the joint characteristic function of $(X(t_1),\dots,X(t_k))$ is $\prod_{j=1}^k\varphi_j(\theta_j+\dots+\theta_k)$ with $\varphi_j$ that of $S_\alpha(\sigma(t_j-t_{j-1})^{1/\alpha},\beta,0)$, $t_0=0$.
--   7. **Constants** (p. 40): $C_\alpha=\dfrac{1-\alpha}{\Gamma(2-\alpha)\cos(\pi\alpha/2)}$ (5.1), $\sigma=C_\alpha^{-1/\alpha}$, $c=\mu_{\mathrm{off}}/\mu^{1+1/\alpha}$.
--   8. **Convergence.** "$Y_T\to0$ in probability" means $P_T(|Y_T|>\eta)\to0$ for every $\eta>0$; "$Y_T\to\nu$ in distribution" means each $Y_T$ is a random element and its law converges weakly to $\nu$. The normalised input of Theorem 2 is $G_T(t)=(A(Tt)-TM\mu^{-1}\mu_{\mathrm{on}}t)/b(MT)$.
--
--   These are the objects every statement of the mission is phrased in.
--
--   **Formalization Note.** Lean's `X n`, `Y n`, `J k` ($n,k\ge0$) are the paper's $X_{n+1}$, $Y_{n+1}$, $J_{k+1}$, so the ON-period started at $T_n$ is `X n`, and the last renewal in $[0,T]$ is `Tn (ξ_T - 1)` with ON-period `X (ξ_T - 1)` (the paper's $X_{\xi_T}$). $\xi_T$ is a `Set.ncard` (junk $0$ if infinitely many renewals fall in $[0,T]$, a null event); $W$ is a `tsum` of indicators (junk $0$ if not summable, a null event); $A$ is an interval integral. $b$ is written as $\inf\{x>0: t\bar F_{\mathrm{on}}(x)\le1\}$ to avoid $1/0$ and $\inf\emptyset$; for $t>0$ this is the paper's generalized inverse. $L_{\mathrm{on}}(x)=x^\alpha\bar F_{\mathrm{on}}(x)$ is defined from the tail, which is equivalent to (2.1). Non-negativity of the period lengths is $F((-\infty,0))=0$. The integrated-tail law is given by its density $\bar F(s)/\mu_F$ on $(0,\infty)$, the same law as the page's distribution function. The fidi law of the Lévy motion is specified through its characteristic function on `EuclideanSpace ℝ (Fin k)` for sorted times. The model of each time scale $T$ lives on its own probability space $(\Omega_T,P_T)$ carrying $M(T)$ independent sources.
-- source:
--   Mikosch, Resnick, Rootzén and Stegeman, Is network traffic approximated by stable Lévy motion or fractional Brownian motion?, Ann. Appl. Probab. 12 (2002), pp. 25–27, §2.1 (2.1)–(2.4), (2.7); p. 28 (2.9); pp. 31–32, §3.2; p. 32, §4; p. 40 (5.1); pp. 41–49, §5.2–§5.4

import Mathlib
import Definitions.Def_NetTraffic_PoissonStable_Setting

namespace NetTraffic.OnOffStable

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

/-! ### Heavy tails (2.1)–(2.2), the quantile (2.9) and the growth condition of §3.2 -/

/-- The slowly varying factor of a tail with index `a`: `L(x) = x^a F̄(x)`, so that
`F̄(x) = x^{-a} L(x)` for `x > 0`. With `a = α_on` this is `L_on` of (2.1). -/
noncomputable def Lsv (F : Measure ℝ) (a : ℝ) (x : ℝ) : ℝ :=
  x ^ a * NetTraffic.PoissonStable.Fbar F x

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
  sv_on : NetTraffic.PoissonStable.IsSlowlyVarying (Lsv Fon α)
  sv_off : NetTraffic.PoissonStable.IsSlowlyVarying (Lsv Foff αoff)

/-- §3.2: the number of sources `M = M(T)` is integer valued, non-decreasing in `T`, and
`M(T) → ∞` as `T → ∞`. -/
structure SourceCount (M : ℝ → ℕ) : Prop where
  mono : Monotone M
  tendsto : Tendsto M atTop atTop

/-- **Slow Growth Condition 1** (§3.2, p. 32): `b(MT)/T → 0` as `T → ∞`, with `M = M(T)`. -/
def Condition1 (Fon : Measure ℝ) (M : ℝ → ℕ) : Prop :=
  Tendsto (fun T => NetTraffic.PoissonStable.b Fon ((M T : ℝ) * T) / T) atTop (𝓝 0)

/-! ### One ON/OFF source, §2.1 -/

/-- The integrated-tail (equilibrium) law `F^{(0)}` of a law `F` on `[0, ∞)` with mean `m`:
`F^{(0)}(x) = (1/m) ∫_0^x F̄(s) ds`, i.e. the law with density `F̄(s)/m` on `(0, ∞)`. -/
noncomputable def eqLaw (F : Measure ℝ) : Measure ℝ :=
  (volume.restrict (Set.Ioi (0 : ℝ))).withDensity (fun s => ENNReal.ofReal (NetTraffic.PoissonStable.Fbar F s / mean F))

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
(in Lean indices, `Tn n = T_0 + Σ_{i<n} (X i + Y i)`). -/
def Source.Tn {Ω : Type*} (s : Source Ω) (n : ℕ) (ω : Ω) : ℝ :=
  s.T0 ω + ∑ i ∈ Finset.range n, (s.X i ω + s.Y i ω)

/-- (2.4): the ON/OFF process of one source,
`W_t = B 1_{[0, X_on^{(0)})}(t) + Σ_{n ≥ 0} 1_{[T_n, T_n + X_{n+1})}(t)`, `t ≥ 0`
(the ON-period starting at `T_n` is the paper's `X_{n+1}`, Lean's `X n`). The series is a
`tsum` of non-negative terms (`0` if not summable, which happens only on a null event). -/
noncomputable def Source.W {Ω : Type*} (s : Source Ω) (t : ℝ) (ω : Ω) : ℝ :=
  s.B ω * (Set.Ico 0 (s.X0 ω)).indicator (fun _ => (1 : ℝ)) t +
    ∑' n : ℕ, (Set.Ico (s.Tn n ω) (s.Tn n ω + s.X n ω)).indicator (fun _ => (1 : ℝ)) t

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

/-! ### Proof objects of §5.2–§5.5 -/

/-- §5.2, p. 41: the renewal counting variable `ξ_T = Σ_{n ≥ 0} 1_{[0,T]}(T_n)`, the number of
renewal epochs `T_0, T_1, …` in `[0, T]` (`Set.ncard`: junk `0` if infinitely many, a null
event). -/
noncomputable def Source.xi {Ω : Type*} (s : Source Ω) (T : ℝ) (ω : Ω) : ℕ :=
  {n : ℕ | s.Tn n ω ∈ Set.Icc 0 T}.ncard

/-- §5.2, p. 41: `μ_T = E ξ_T = T/μ`. -/
noncomputable def muT (Fon Foff : Measure ℝ) (T : ℝ) : ℝ :=
  T / mu Fon Foff

/-- §5.2, p. 41: `A_1 = Σ_{m=1}^M B^{(m)} min(T, (X_on^{(0)})^{(m)})`. -/
noncomputable def A1 {Ω : Type*} (M : ℕ) (src : ℕ → Source Ω) (T : ℝ) (ω : Ω) : ℝ :=
  ∑ m ∈ Finset.range M, (src m).B ω * min T ((src m).X0 ω)

/-- The overshoot of the last ON-period started in `[0, T]`,
`max(0, T_{ξ_T - 1} + X_{ξ_T} - T) 1_{[ξ_T ≥ 1]}` (paper indices; in Lean indices the last
renewal is `Tn (ξ_T - 1)` and its ON-period is `X (ξ_T - 1)`). -/
noncomputable def Source.overshoot {Ω : Type*} (s : Source Ω) (T : ℝ) (ω : Ω) : ℝ :=
  if 1 ≤ s.xi T ω then
    max 0 (s.Tn (s.xi T ω - 1) ω + s.X (s.xi T ω - 1) ω - T)
  else 0

/-- §5.2, p. 41: `A_3 = Σ_{m=1}^M max(0, T^{(m)}_{ξ_T^{(m)} - 1} + X^{(m)}_{ξ_T^{(m)}} - T)
1_{[ξ_T^{(m)} ≥ 1]}` (the term subtracted in the decomposition `A(T) = A_1 + A_2 + A_3`). -/
noncomputable def A3 {Ω : Type*} (M : ℕ) (src : ℕ → Source Ω) (T : ℝ) (ω : Ω) : ℝ :=
  ∑ m ∈ Finset.range M, (src m).overshoot T ω

/-- The ON-period of the last renewal in `[0, T]` on the event `ξ_T ≥ 1`:
`X_{ξ_T} 1_{[ξ_T ≥ 1]}` (paper index; Lean's `X (ξ_T - 1)`), and `0` if `ξ_T = 0`. -/
noncomputable def Source.Xlast {Ω : Type*} (s : Source Ω) (T : ℝ) (ω : Ω) : ℝ :=
  if 1 ≤ s.xi T ω then s.X (s.xi T ω - 1) ω else 0

/-- §5.4, p. 46: `r_on = μ_off/μ`. -/
noncomputable def rOn (Fon Foff : Measure ℝ) : ℝ :=
  mean Foff / mu Fon Foff

/-- §5.4, p. 46: `r_off = μ_on/μ`. -/
noncomputable def rOff (Fon Foff : Measure ℝ) : ℝ :=
  mean Fon / mu Fon Foff

/-- §5.4, p. 46: `J_k = X_k - r_off Z_k = r_on(X_k - μ_on) - r_off(Y_k - μ_off)`
(Lean's `J k` is the paper's `J_{k+1}`). -/
noncomputable def Source.J {Ω : Type*} (Fon Foff : Measure ℝ) (s : Source Ω) (k : ℕ)
    (ω : Ω) : ℝ :=
  rOn Fon Foff * (s.X k ω - mean Fon) - rOff Fon Foff * (s.Y k ω - mean Foff)

/-- §5.4, p. 48: `S_n = Σ_{k=1}^n J_k`. -/
noncomputable def Source.S {Ω : Type*} (Fon Foff : Measure ℝ) (s : Source Ω) (n : ℕ)
    (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range n, s.J Fon Foff k ω

/-- §5.4, p. 48: `S_n^{(1)} = r_on Σ_{k=1}^n (X_k - μ_on)`. -/
noncomputable def Source.S1 {Ω : Type*} (Fon Foff : Measure ℝ) (s : Source Ω) (n : ℕ)
    (ω : Ω) : ℝ :=
  rOn Fon Foff * ∑ k ∈ Finset.range n, (s.X k ω - mean Fon)

/-- §5.4, p. 47: `S_{T,m} = Σ_{k=1}^{ξ_T^{(m)}} J_k^{(m)}` for the source `s = src m`. -/
noncomputable def Source.ST {Ω : Type*} (Fon Foff : Measure ℝ) (s : Source Ω) (T : ℝ)
    (ω : Ω) : ℝ :=
  s.S Fon Foff (s.xi T ω) ω

/-- §5.4, p. 47: `A_21 = A_21(T) = Σ_{m=1}^M S_{T,m}`. -/
noncomputable def A21 {Ω : Type*} (Fon Foff : Measure ℝ) (M : ℕ) (src : ℕ → Source Ω)
    (T : ℝ) (ω : Ω) : ℝ :=
  ∑ m ∈ Finset.range M, (src m).ST Fon Foff T ω

/-- (5.11), p. 49: the event `Θ_T = {|ξ_T - μ_T| ≤ ε_T μ_T}`. -/
def Source.Theta {Ω : Type*} (Fon Foff : Measure ℝ) (s : Source Ω) (ε : ℝ → ℝ) (T : ℝ) :
    Set Ω :=
  {ω | |(s.xi T ω : ℝ) - muT Fon Foff T| ≤ ε T * muT Fon Foff T}

/-! ### Stable laws and α-stable Lévy motion, §4 p. 32 and §5.1 p. 40 -/

/-- p. 40: `c = μ_off/μ^{1+1/α}`. -/
noncomputable def cConst (Fon Foff : Measure ℝ) (α : ℝ) : ℝ :=
  mean Foff / mu Fon Foff ^ (1 + 1 / α)

/-! ### Convergence notions -/

/-- Theorem 2, p. 40: the normalised cumulative input of the `T`-th model,
`(A(Tt) - T M μ^{-1} μ_on t)/NetTraffic.PoissonStable.b(MT)`, `t ≥ 0`, with `M = M(T)`. -/
noncomputable def Gnorm {Ω : Type*} (Fon Foff : Measure ℝ) (M : ℝ → ℕ) (src : ℕ → Source Ω)
    (T : ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  (A (M T) src (T * t) ω - T * (M T : ℝ) * (mu Fon Foff)⁻¹ * mean Fon * t) /
    NetTraffic.PoissonStable.b Fon ((M T : ℝ) * T)

end NetTraffic.OnOffStable


