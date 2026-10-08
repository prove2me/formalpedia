-- Prove2me | Definitions.Def_NetTraffic_PoissonStable_Setting
-- name    : NetTraffic_PoissonStable_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T01:09:28.503728+00:00
-- url     : https://prove2.me/theorems/a80f5138-9908-4bdf-b099-c848fe74bc22
-- title:
--   §2.2, §3.1, §4 — the infinite source Poisson model, N, A, (2.8), b, Condition 1, the regions R₁–R₄ and A₁–A₄, A₁₁–A₁₃, A₂₂, S_α(σ,β,μ) and the fidis of X_{α,σ,β}
-- statement:
--   This file fixes every object of the infinite source Poisson model under slow growth (Mikosch, Resnick, Rootzén and Stegeman 2002, §2.2, §3.1 and §4).
--
--   1. **Heavy tails (2.8).** $F_{\mathrm{on}}$ is the law of a transmission length, a probability measure on $[0,\infty)$, with tail $\bar F_{\mathrm{on}}(x)=F_{\mathrm{on}}((x,\infty))$. Condition (2.8) asks $1<\alpha<2$ and $\bar F_{\mathrm{on}}(x)=x^{-\alpha}L(x)$ for $x>0$ with $L$ **slowly varying**: $L$ is eventually positive and $L(cx)/L(x)\to1$ as $x\to\infty$ for every $c>0$. The mean is $\mu_{\mathrm{on}}=\int x\,F_{\mathrm{on}}(dx)$.
--   2. **The quantile function (2.9).** $b(t)=(1/\bar F_{\mathrm{on}})^{\leftarrow}(t)=\inf\{x>0: 1/\bar F_{\mathrm{on}}(x)\ge t\}$.
--   3. **Slow Growth Condition 1** (§3.1): for the connection rate $\lambda=\lambda(T)$ of the $T$-th model,
--   $$\lim_{T\to\infty}\frac{b(\lambda T)}{T}=0 .$$
--   4. **The model** (§2.2). $(\Gamma_k)_{k\in\mathbb Z}$ are the points of a rate-$\lambda$ homogeneous Poisson process on $\mathbb R$ labelled so that $\Gamma_0<0<\Gamma_1$: the spacings $-\Gamma_0,\ \Gamma_1,\ \Gamma_{k+1}-\Gamma_k\ (k\ne0)$ are iid exponential with parameter $\lambda$. The lengths $X_k$ are iid with law $F_{\mathrm{on}}$ and independent of $(\Gamma_k)$. The number of active sources and the cumulative input are
--   $$N(t)=\sum_{k=-\infty}^{\infty}\mathbf 1[\Gamma_k\le t<\Gamma_k+X_k],\qquad A(t)=\int_0^t N(s)\,ds .$$
--   5. **The decomposition (4.1)–(4.2).** $R_1=\{0<s\le T,\ y>0,\ s+y\le T\}$, $R_2=\{0<s\le T,\ T<s+y\}$, $R_3=\{s\le0,\ 0<s+y\le T\}$, $R_4=\{s\le0,\ T<s+y\}$, and
--   $$A_1=\sum_k X_k\mathbf 1_{R_1},\quad A_2=\sum_k (T-\Gamma_k)\mathbf 1_{R_2},\quad A_3=\sum_k (X_k+\Gamma_k)\mathbf 1_{R_3},\quad A_4=\sum_k T\,\mathbf 1_{R_4},$$
--   the indicator evaluated at $(\Gamma_k,X_k)$. $P_1=\#\{k:(\Gamma_k,X_k)\in R_1\}$, $m_1=(\mathbb L\times F_{\mathrm{on}})(R_1)$, the law (4.4) of $j_1$ is the second marginal of $\mathbb L(ds)F_{\mathrm{on}}(dy)/m_1$ restricted to $R_1$, and $Ej_1$ is its mean.
--   6. **The pieces of §4.4–4.5.** $A_{11}=\sum_{k:(\Gamma_k,X_k)\in R_1}(X_k-Ej_1)=A_1-Ej_1P_1$, $A_{12}=Ej_1(P_1-EP_1)$, $A_{13}=EA_1-\lambda\mu_{\mathrm{on}}T$, and, for $a=Tt_1<c=Tt_2$, $A_{22}=\sum_{0<\Gamma_k\le a}X_k\mathbf 1[a<\Gamma_k+X_k\le c]$.
--   7. **Stable laws** (§4, p. 32). $X\sim S_\alpha(\sigma,\beta,\mu)$ has characteristic function
--   $$Ee^{i\theta X}=\begin{cases}\exp\{-\sigma^\alpha|\theta|^\alpha(1-i\beta\,\mathrm{sign}(\theta)\tan(\pi\alpha/2))+i\mu\theta\}, & \alpha\ne1,\\ \exp\{-\sigma|\theta|(1+i\beta\tfrac2\pi\mathrm{sign}(\theta)\ln|\theta|)+i\mu\theta\}, & \alpha=1.\end{cases}$$
--   $C_\alpha=(1-\alpha)/(\Gamma(2-\alpha)\cos(\pi\alpha/2))$ (5.1) and $\sigma=C_\alpha^{-1/\alpha}$.
--   8. **α-stable Lévy motion.** $X_{\alpha,\sigma,\beta}$ has independent stationary increments with $X(t)-X(s)\sim S_\alpha(\sigma(t-s)^{1/\alpha},\beta,0)$ and $X(0)=0$. For $0\le t_1\le\dots\le t_k$ (and $t_0=0$) its finite-dimensional law has characteristic function
--   $$\theta\mapsto\prod_{j=1}^k\varphi_j(\theta_j+\dots+\theta_k),$$
--   with $\varphi_j$ the characteristic function of $S_\alpha(\sigma(t_j-t_{j-1})^{1/\alpha},\beta,0)$.
--   9. **The normalised process** of Theorem 1: $G_T(t)=(A(Tt)-T\lambda\mu_{\mathrm{on}}t)/b(\lambda T)$, $t\ge0$.
--
--   These objects are shared by the missions of this series on the infinite source Poisson model (slow and fast growth) and, for the model-free parts (the tail, $b$, slow variation, stable laws, the stable Lévy fidis and the convergence notions), by the mission on superposed ON/OFF sources under slow growth.
--
--   **Formalization Note** Each model $T$ carries its own probability space; statements quantify over every family of models. The spacing family is indexed by $\mathbb Z$: $e_0=-\Gamma_0$, $e_1=\Gamma_1$, $e_k=\Gamma_k-\Gamma_{k-1}$ for $k\ge2$, $e_k=\Gamma_{k+1}-\Gamma_k$ for $k\le-1$. (2.8) is stated as "$x\mapsto x^\alpha\bar F_{\mathrm{on}}(x)$ is slowly varying", which is equivalent. $b(t)$ is written $\inf\{x>0: t\bar F_{\mathrm{on}}(x)\le1\}$, the same set for $t>0$ without a division by zero. $N(t)$, $P_1$ and the count in $A_4$ are cardinalities (`Set.ncard`, $0$ if the set is infinite); $A_1,A_2,A_3,A_{22}$ are sums of non-negative terms (`tsum`, $0$ if not summable); both junk values occur only on null events. $A$ is an interval integral. Convergence in probability to $0$ is $P_T(|Y_T|>\eta)\to0$ for every $\eta>0$; convergence in law is weak convergence of the laws of $Y_T$, each $Y_T$ a.e. measurable. $b$ takes the infimum over $x>0$ only (the paper's $g^{\leftarrow}$ ranges over all $x$, which for $t\le1$ would include negative $x$; for large $t$, the only regime used, the two agree). `HeavyTail` records non-negativity of the lengths and the tail condition; that $F_{\mathrm{on}}$ is a probability measure is a hypothesis of every statement using it (and follows from the model when the lengths' law is $F_{\mathrm{on}}$). $R_1$ follows (4.1) literally ($y>0$); the printed (4.3) writes $m_1$ with $F_{\mathrm{on}}(T-s)$, which also counts an atom of $F_{\mathrm{on}}$ at $0$; such lengths contribute nothing to $A$.
-- source:
--   Mikosch, Resnick, Rootzén and Stegeman, Is network traffic approximated by stable Lévy motion or fractional Brownian motion?, Ann. Appl. Probab. 12 (2002), pp. 28–29, §2.2 (2.8)–(2.13); p. 30, §3.1 Condition 1; p. 32, §4 (stable laws, X_{α,σ,β}); pp. 33–34, §4.2 (4.1)–(4.4); pp. 37–39, §4.4–4.5 (A₁₁, A₁₂, A₁₃, A₂₂); p. 40 (5.1)

import Mathlib

namespace NetTraffic.PoissonStable

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

/-! ### Heavy tails, (2.8)–(2.9), and the slow growth condition of §3.1 -/

/-- The tail `F̄_on(x) = P(X_on > x) = F_on((x, ∞))` of the transmission-length law `F_on`. -/
noncomputable def Fbar (Fon : Measure ℝ) (x : ℝ) : ℝ :=
  Fon.real (Set.Ioi x)

/-- A function `L` is **slowly varying** (at infinity): eventually positive, and
`L(cx)/L(x) → 1` as `x → ∞` for every `c > 0`. -/
def IsSlowlyVarying (L : ℝ → ℝ) : Prop :=
  (∀ᶠ x in atTop, 0 < L x) ∧
    ∀ c : ℝ, 0 < c → Tendsto (fun x => L (c * x) / L x) atTop (𝓝 1)

/-- Condition (2.8) on the law `F_on` of the transmission lengths: lengths are non-negative,
`1 < α < 2`, and `F̄_on(x) = x^{-α} L(x)` for `x > 0` with `L` slowly varying. The slowly varying
function is necessarily `L(x) = x^α F̄_on(x)`, so (2.8) is stated as "this `L` is slowly varying". -/
structure HeavyTail (Fon : Measure ℝ) (α : ℝ) : Prop where
  nonneg : Fon (Set.Iio 0) = 0
  one_lt : 1 < α
  lt_two : α < 2
  slowlyVarying : IsSlowlyVarying (fun x => x ^ α * Fbar Fon x)

/-- The mean transmission length `μ_on = E X_on = ∫ x F_on(dx)`. -/
noncomputable def muOn (Fon : Measure ℝ) : ℝ :=
  ∫ x, x ∂Fon

/-- The quantile function (2.9), `b(t) = (1/F̄_on)^←(t) = inf{x > 0 : 1/F̄_on(x) ≥ t}`, written
as `inf{x > 0 : t F̄_on(x) ≤ 1}` (the same set for `t > 0`, without division by zero). -/
noncomputable def b (Fon : Measure ℝ) (t : ℝ) : ℝ :=
  sInf {x : ℝ | 0 < x ∧ t * Fbar Fon x ≤ 1}

/-- **Slow Growth Condition 1** (§3.1, p. 30): `b(λT)/T → 0` as `T → ∞`, where `λ = λ(T)` is the
connection rate of the `T`-th model (`b` is evaluated at the product `λ(T)·T`). -/
def Condition1 (Fon : Measure ℝ) (lam : ℝ → ℝ) : Prop :=
  Tendsto (fun T => b Fon (lam T * T) / T) atTop (𝓝 0)

/-! ### The infinite source Poisson model, §2.2 -/

/-- The inter-point spacings of the two-sided sequence `(Γ_k)_{k ∈ ℤ}`, indexed by `ℤ`:
`e 0 = -Γ_0`, `e 1 = Γ_1`, `e k = Γ_k - Γ_{k-1}` for `k ≥ 2` and `e k = Γ_{k+1} - Γ_k` for
`k ≤ -1`. This enumerates the family `{-Γ_0, Γ_1, (Γ_{k+1} - Γ_k, k ≠ 0)}` of §2.2 once each. -/
noncomputable def spacing {Ω : Type*} (Γ : ℤ → Ω → ℝ) (k : ℤ) (ω : Ω) : ℝ :=
  if k = 0 then -Γ 0 ω
  else if k = 1 then Γ 1 ω
  else if 2 ≤ k then Γ k ω - Γ (k - 1) ω
  else Γ (k + 1) ω - Γ k ω

/-- The infinite source Poisson model of §2.2 with connection rate `lam` and length law `Fon`, on
`(Ω, P)`: the points `Γ_k` of a rate-`lam` homogeneous Poisson process on `ℝ` labelled so that
`Γ_0 < 0 < Γ_1` (equivalently, the spacings `-Γ_0, Γ_1, Γ_{k+1} - Γ_k (k ≠ 0)` are iid
exponential with parameter `lam`), and iid marks `X_k` with law `Fon`, independent of `(Γ_k)`. -/
structure IsPoissonModel {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (lam : ℝ)
    (Fon : Measure ℝ) (Γ X : ℤ → Ω → ℝ) : Prop where
  measurable_Γ : ∀ k, Measurable (Γ k)
  measurable_X : ∀ k, Measurable (X k)
  indep_spacing : iIndepFun (spacing Γ) P
  law_spacing : ∀ k, P.map (spacing Γ k) = expMeasure lam
  indep_X : iIndepFun X P
  law_X : ∀ k, P.map (X k) = Fon
  indep_Γ_X : IndepFun (fun ω k => spacing Γ k ω) (fun ω k => X k ω) P

/-- (2.11): the number of active sources at time `t`,
`N(t) = Σ_k 1[Γ_k ≤ t < Γ_k + X_k]`. Written as the cardinality of the set of active indices
(`Set.ncard`, which is `0` if that set is infinite, a null event). -/
noncomputable def N {Ω : Type*} (Γ X : ℤ → Ω → ℝ) (t : ℝ) (ω : Ω) : ℕ :=
  Set.ncard {k : ℤ | Γ k ω ≤ t ∧ t < Γ k ω + X k ω}

/-- (2.13): the total cumulative input `A(t) = ∫_0^t N(s) ds`. -/
noncomputable def A {Ω : Type*} (Γ X : ℤ → Ω → ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  ∫ s in (0 : ℝ)..t, (N Γ X s ω : ℝ)

/-! ### The decomposition (4.1)–(4.2) of §4.2 -/

/-- (4.1): `R_1 = {(s, y) : 0 < s ≤ T, y > 0, s + y ≤ T}`. -/
def R1 (T : ℝ) : Set (ℝ × ℝ) :=
  {p | 0 < p.1 ∧ p.1 ≤ T ∧ 0 < p.2 ∧ p.1 + p.2 ≤ T}

/-- (4.1): `R_2 = {(s, y) : 0 < s ≤ T, T < s + y}`. -/
def R2 (T : ℝ) : Set (ℝ × ℝ) :=
  {p | 0 < p.1 ∧ p.1 ≤ T ∧ T < p.1 + p.2}

/-- (4.1): `R_3 = {(s, y) : s ≤ 0, 0 < s + y ≤ T}`. -/
def R3 (T : ℝ) : Set (ℝ × ℝ) :=
  {p | p.1 ≤ 0 ∧ 0 < p.1 + p.2 ∧ p.1 + p.2 ≤ T}

/-- (4.1): `R_4 = {(s, y) : s ≤ 0, T < s + y}`. -/
def R4 (T : ℝ) : Set (ℝ × ℝ) :=
  {p | p.1 ≤ 0 ∧ T < p.1 + p.2}

/-- (4.2): `A_1 = Σ_k X_k 1[(Γ_k, X_k) ∈ R_1]`, for the horizon `U` (`U = T` in (4.2),
`U = Tt` in §4.5). A sum of non-negative terms (`tsum`, `0` if not summable, a null event). -/
noncomputable def A1 {Ω : Type*} (Γ X : ℤ → Ω → ℝ) (U : ℝ) (ω : Ω) : ℝ :=
  ∑' k : ℤ, (R1 U).indicator (fun p : ℝ × ℝ => p.2) (Γ k ω, X k ω)

/-- (4.2): `A_2 = Σ_k (T - Γ_k) 1[(Γ_k, X_k) ∈ R_2]` (non-negative terms; `tsum`). -/
noncomputable def A2 {Ω : Type*} (Γ X : ℤ → Ω → ℝ) (U : ℝ) (ω : Ω) : ℝ :=
  ∑' k : ℤ, (R2 U).indicator (fun p : ℝ × ℝ => U - p.1) (Γ k ω, X k ω)

/-- (4.2): `A_3 = Σ_k (X_k + Γ_k) 1[(Γ_k, X_k) ∈ R_3]` (non-negative terms; `tsum`). -/
noncomputable def A3 {Ω : Type*} (Γ X : ℤ → Ω → ℝ) (U : ℝ) (ω : Ω) : ℝ :=
  ∑' k : ℤ, (R3 U).indicator (fun p : ℝ × ℝ => p.2 + p.1) (Γ k ω, X k ω)

/-- (4.2): `A_4 = Σ_k T 1[(Γ_k, X_k) ∈ R_4] = T · #{k : (Γ_k, X_k) ∈ R_4}` (`Set.ncard`). -/
noncomputable def A4 {Ω : Type*} (Γ X : ℤ → Ω → ℝ) (U : ℝ) (ω : Ω) : ℝ :=
  U * (Set.ncard {k : ℤ | (Γ k ω, X k ω) ∈ R4 U} : ℝ)

/-- `P_1 = #{k : (Γ_k, X_k) ∈ R_1}`, the number of points of `ν` in `R_1` (`Set.ncard`). -/
noncomputable def P1 {Ω : Type*} (Γ X : ℤ → Ω → ℝ) (U : ℝ) (ω : Ω) : ℕ :=
  Set.ncard {k : ℤ | (Γ k ω, X k ω) ∈ R1 U}

/-- (4.3): `m_1 = (𝕃 × F_on)(R_1)` (so that `λ m_1 = E ν(R_1)`), as a real number. -/
noncomputable def m1 (Fon : Measure ℝ) (T : ℝ) : ℝ :=
  ((volume : Measure ℝ).prod Fon).real (R1 T)

/-- (4.4): the law of the length `j_1` of a generic point of `ν` in `R_1`: the second marginal of
`𝕃(ds) F_on(dy) / m_1` restricted to `R_1`. -/
noncomputable def j1Law (Fon : Measure ℝ) (T : ℝ) : Measure ℝ :=
  (((volume : Measure ℝ).prod Fon) (R1 T))⁻¹ •
    (((volume : Measure ℝ).prod Fon).restrict (R1 T)).map Prod.snd

/-- `E j_1 = (1/m_1) ∬_{R_1} y ds F_on(dy)`, the mean of `j1Law`. -/
noncomputable def Ej1 (Fon : Measure ℝ) (T : ℝ) : ℝ :=
  ∫ y, y ∂(j1Law Fon T)

/-- §4.4, p. 37: `A_11 = Σ_{k : (Γ_k, X_k) ∈ R_1} (X_k - E j_1) = A_1 - E j_1 · P_1`. -/
noncomputable def A11 {Ω : Type*} (Fon : Measure ℝ) (Γ X : ℤ → Ω → ℝ) (T : ℝ) (ω : Ω) : ℝ :=
  A1 Γ X T ω - Ej1 Fon T * (P1 Γ X T ω : ℝ)

/-- §4.4, p. 37: `A_12 = E j_1 (P_1 - E P_1)`, the expectation taken under `P`. -/
noncomputable def A12 {Ω : Type*} [MeasurableSpace Ω] (Fon : Measure ℝ) (P : Measure Ω)
    (Γ X : ℤ → Ω → ℝ) (T : ℝ) (ω : Ω) : ℝ :=
  Ej1 Fon T * ((P1 Γ X T ω : ℝ) - ∫ ω', (P1 Γ X T ω' : ℝ) ∂P)

/-- §4.4, p. 37 and (4.20): the deterministic `A_13 = E A_1 - λ μ_on T`, the expectation taken
under `P` and `lam` the connection rate of the model. -/
noncomputable def A13 {Ω : Type*} [MeasurableSpace Ω] (Fon : Measure ℝ) (lam : ℝ)
    (P : Measure Ω) (Γ X : ℤ → Ω → ℝ) (T : ℝ) : ℝ :=
  (∫ ω, A1 Γ X T ω ∂P) - lam * muOn Fon * T

/-- §4.5, p. 39: the region `{(s, y) : 0 < s ≤ a, a < s + y ≤ c}` (with `a = Tt₁`, `c = Tt₂`). -/
def R22 (a c : ℝ) : Set (ℝ × ℝ) :=
  {p | 0 < p.1 ∧ p.1 ≤ a ∧ a < p.1 + p.2 ∧ p.1 + p.2 ≤ c}

/-- §4.5, p. 39: `A_22 = Σ_{0 < Γ_k ≤ a} X_k 1[a < Γ_k + X_k ≤ c]`, with `a = Tt₁`, `c = Tt₂`
(non-negative terms; `tsum`). -/
noncomputable def A22 {Ω : Type*} (Γ X : ℤ → Ω → ℝ) (a c : ℝ) (ω : Ω) : ℝ :=
  ∑' k : ℤ, (R22 a c).indicator (fun p : ℝ × ℝ => p.2) (Γ k ω, X k ω)

/-! ### Stable laws and α-stable Lévy motion, §4, p. 32 -/

/-- §4, p. 32: the characteristic function `θ ↦ E e^{iθX}` of `X ∼ S_α(σ, β, μ)`:
`exp{-σ^α|θ|^α(1 - iβ sign(θ) tan(πα/2)) + iμθ}` if `α ≠ 1`, and
`exp{-σ|θ|(1 + iβ(2/π) sign(θ) ln|θ|) + iμθ}` if `α = 1`. -/
noncomputable def stableCharFun (α σ β μ θ : ℝ) : ℂ :=
  if α ≠ 1 then
    Complex.exp (-(((σ ^ α * |θ| ^ α : ℝ) : ℂ) *
        (1 - Complex.I * ((β * Real.sign θ * Real.tan (Real.pi * α / 2) : ℝ) : ℂ))) +
      Complex.I * ((μ * θ : ℝ) : ℂ))
  else
    Complex.exp (-(((σ * |θ| : ℝ) : ℂ) *
        (1 + Complex.I * ((β * (2 / Real.pi) * Real.sign θ * Real.log |θ| : ℝ) : ℂ))) +
      Complex.I * ((μ * θ : ℝ) : ℂ))

/-- (5.1), p. 40: `C_α = (1 - α)/(Γ(2 - α) cos(πα/2))`. -/
noncomputable def Calpha (α : ℝ) : ℝ :=
  (1 - α) / (Real.Gamma (2 - α) * Real.cos (Real.pi * α / 2))

/-- The scale `σ = C_α^{-1/α}` of the (corrected) limit of Theorem 1 (the same `σ` as p. 40). -/
noncomputable def sigmaConst (α : ℝ) : ℝ :=
  Calpha α ^ (-1 / α)

/-- The time preceding `t_j` in a list of times: `t_{j-1}`, and `t_0 = 0` for the first one. -/
def prevTime {k : ℕ} (t : Fin k → ℝ) (j : Fin k) : ℝ :=
  if h : (j : ℕ) = 0 then 0 else t ⟨(j : ℕ) - 1, by omega⟩

/-- §4, p. 32: the joint characteristic function of `(X_{α,σ,β}(t_1), …, X_{α,σ,β}(t_k))` for
`0 ≤ t_1 ≤ … ≤ t_k`, the α-stable Lévy motion (independent stationary increments,
`X(t) - X(s) ∼ S_α(σ(t-s)^{1/α}, β, 0)`, `X(0) = 0`):
`θ ↦ Π_{j=1}^k φ_j(θ_j + … + θ_k)` with `φ_j` the characteristic function of
`S_α(σ(t_j - t_{j-1})^{1/α}, β, 0)` and `t_0 = 0`. -/
noncomputable def stableLevyFidiCharFun (α σ β : ℝ) {k : ℕ} (t : Fin k → ℝ)
    (θ : EuclideanSpace ℝ (Fin k)) : ℂ :=
  ∏ j : Fin k, stableCharFun α (σ * (t j - prevTime t j) ^ (1 / α)) β 0
    (∑ i ∈ Finset.univ.filter (fun i : Fin k => j ≤ i), θ i)

/-! ### Convergence notions -/

/-- `Y_T → 0` in probability as `T → ∞` (each `Y_T` on its own probability space). -/
def TendstoInProbZero {Ω : ℝ → Type*} [∀ T, MeasurableSpace (Ω T)] (P : ∀ T, Measure (Ω T))
    (Y : ∀ T, Ω T → ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → Tendsto (fun T => P T {ω | η < |Y T ω|}) atTop (𝓝 0)

/-- Convergence in distribution as `T → ∞` of the random elements `Y_T` (on the probability
space `(Ω_T, P_T)`) to the law `ν`: each `Y_T` is a random element (a.e. measurable) and the
laws of `Y_T` converge weakly to `ν`. -/
def TendstoInLaw {Ω : ℝ → Type*} [∀ T, MeasurableSpace (Ω T)] {E : Type*} [MeasurableSpace E]
    [TopologicalSpace E] [OpensMeasurableSpace E] (P : ∀ T, Measure (Ω T))
    [∀ T, IsProbabilityMeasure (P T)] (Y : ∀ T, Ω T → E) (ν : ProbabilityMeasure E) : Prop :=
  ∃ h : ∀ T, AEMeasurable (Y T) (P T),
    Tendsto (β := ProbabilityMeasure E)
      (fun T => ⟨(P T).map (Y T), Measure.isProbabilityMeasure_map (h T)⟩) atTop (𝓝 ν)

/-- Theorem 1, p. 33: the normalised cumulative input of the `T`-th model,
`(A(Tt) - Tλμ_on t)/b(λT)`, `t ≥ 0`, with `λ = λ(T)`. -/
noncomputable def Gnorm {Ω : Type*} (Fon : Measure ℝ) (lam : ℝ → ℝ) (Γ X : ℤ → Ω → ℝ)
    (T : ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  (A Γ X (T * t) ω - T * lam T * muOn Fon * t) / b Fon (lam T * T)

end NetTraffic.PoissonStable


