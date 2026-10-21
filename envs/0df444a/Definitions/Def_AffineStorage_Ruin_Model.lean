-- Prove2me | Definitions.Def_AffineStorage_Ruin_Model
-- name    : AffineStorage_Ruin_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T12:35:44.283987+00:00
-- url     : https://prove2.me/theorems/58073784-88ae-4690-aaec-3d1e2cb6835c
-- title:
--   §2.1–§2.3, pp. 1283–1287 — affine-drift risk process with two-sided jumps, ruin time, overshoot, undershoot, ϱ, φ, F, G, I_k
-- statement:
--   This file sets up the insurance risk model of Boxma and Mandjes (2021, §2) and the functions used to analyse it.
--
--   **Parameters.** A premium rate $p$, an interest rate $r$, a rate $\lambda_+$ of upward jumps ("capital injections") whose sizes are i.i.d. exponential with mean $\mu^{-1}$, a rate $\lambda_-$ of claims whose sizes are i.i.d. with density $d$ on $(0,\infty)$ and Laplace–Stieltjes transform $\delta(s)=\int_0^\infty e^{-sy}d(y)\,dy$, the rate $\nu$ of an exponential horizon $T_\nu$, and transform arguments $\alpha,\beta,\gamma\ge 0$. The standing assumptions are $p,r,\lambda_+,\lambda_-,\mu,\nu>0$, $\alpha,\beta,\gamma\ge0$, and $d$ a measurable probability density vanishing on $(-\infty,0]$. Write $\lambda=\lambda_-+\lambda_+$.
--
--   **Process.** The random primitives are the interarrival times of the two independent Poisson streams and the jump sizes, all independent. The jump epochs are $T^+_n$ (upward) and $T^-_n$ (claims). Starting from $X_0=x$, the surplus follows $dX_t=p\,dt+rX_t\,dt$ between jumps (eq. (1)). Each upward jump adds its size and each claim subtracts its size. In closed form,
--   $$X_t=xe^{rt}+\frac pr\,(e^{rt}-1)+\sum_{T^+_n\le t}e^{r(t-T^+_n)}U_n-\sum_{T^-_n\le t}e^{r(t-T^-_n)}D_n .$$
--   $X_{t-}$ is the same expression with the sums over epochs $<t$.
--
--   **Ruin quantities.** The ruin time is $\tau_x=\inf\{s>0:X_s\le0\}$, with $\tau_x=\infty$ if there is no ruin. $X_{\tau_x}$ is the overshoot and $X_{\tau_x-}$ the undershoot. With $T_\nu\sim\mathrm{Exp}(\nu)$ independent of the process,
--   $$\varrho(x)=\mathbb E\big(e^{-\alpha\tau_x+\beta X_{\tau_x}-\gamma X_{\tau_x-}}\,1_{\{\tau_x<T_\nu\}}\,\big|\,X_0=x\big),\qquad \varphi(\vartheta)=\int_0^\infty\vartheta e^{-\vartheta x}\varrho(x)\,dx .$$
--
--   **Functions of Proposition 1 and Theorem 1.** With $A=-(\alpha+\nu)/r$:
--   $$\bar F(\vartheta)=\frac pr-\frac{\lambda_-}r\frac{1-\delta(\vartheta)}\vartheta+\frac{\lambda_+}r\frac1{\mu-\vartheta},\qquad F(\vartheta)=\bar F(\vartheta)+\frac A\vartheta,$$
--   $$G_1(\vartheta)=-\frac pr,\quad G_2(\vartheta)=-\frac{\lambda_+}r\frac1{\mu-\vartheta},\quad G_3(\vartheta)=\frac{\lambda_-}r\frac{\delta(\beta)-\delta(\vartheta+\gamma)}{\vartheta+\gamma-\beta},$$
--   and $G=c_0G_1+c_\mu G_2+G_3$; the paper's $G$ is the case $c_0=\varrho(0)$, $c_\mu=\varphi(\mu)$. Further, $F_\star$ is a primitive of $F$ on $(0,\mu)\cup(\mu,\infty)$, and $I_k(\vartheta)=\int_\vartheta^\infty G_k(\eta)e^{-F_\star(\eta)}\,d\eta$.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note.** The hypotheses $r>0$ (tacit on p. 1287), $\lambda_+>0$ (with $\lambda_+=0$ the denominator of (12) vanishes), $\lambda_->0$ (needed for $\varrho(0)\in(0,1)$) and $\mu>0$ are added to the page's $p,r,\lambda_\pm\ge0$. All primitives sit in one independent family `Z : Fin 4 × ℕ → Ω → ℝ`. The jump counts are computed as least indices, which is the true count whenever the epochs increase to infinity (almost surely). $\tau_x$ takes values in $[0,\infty]$. The horizon $T_\nu$ is integrated out against its law `expMeasure ν`, which equals the expectation over an independent $T_\nu$ by Fubini. At the removable singularity $\vartheta=\beta-\gamma$, $G_3$ takes its limit value $(\lambda_-/r)\int_0^\infty ye^{-\beta y}d(y)\,dy$. Lean's $1/0=0$ makes $F$ and $G_2$ junk at $\vartheta=\mu$ and $\vartheta=0$; every statement excludes those points or integrates over them (a null set).
-- source:
--   Boxma & Mandjes, Affine storage and insurance risk models, Math. Oper. Res. 46(4) (2021), pp. 1283–1287 (PDF 4–8), §2.1–§2.3, eqs. (1)–(2), definitions of τx, ϱ, φ, F, F̄, G, G1–G3, Ik

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace AffineStorage.Ruin

/-- The parameters of the insurance risk model of Boxma–Mandjes (2021), §2.1–§2.2,
pp. 1283–1284: premium rate `p`, interest rate `r`, rate `lamPlus` (λ₊) of the upward jumps
(capital injections), rate `lamMinus` (λ₋) of the claims, rate `μ` of the exponential upward
jump sizes (mean `1/μ`), rate `ν` of the exponential horizon `T_ν` (mean `1/ν`), the transform
arguments `α, β, γ`, and the claim-size density `d`. -/
structure Params where
  p : ℝ
  r : ℝ
  lamPlus : ℝ
  lamMinus : ℝ
  μ : ℝ
  ν : ℝ
  α : ℝ
  β : ℝ
  γ : ℝ
  d : ℝ → ℝ

/-- The standing assumptions of §2.1–§2.3. `0 < p` is the hypothesis of Theorem 1; `0 < r` is
the assumption tacitly made on p. 1287 ("Here we tacitly assumed r > 0"); `0 < lamPlus`,
`0 < lamMinus` strengthen the page's `λ₊, λ₋ ⩾ 0` (with `λ₊ = 0` the denominator of (12)
vanishes, with `λ₋ = 0` ruin is impossible and `ϱ(0) ∈ (0,1)` fails); `0 < μ` and `0 < ν`
make the exponential laws proper; `α, β, γ ⩾ 0` (p. 1284); and `d` is a probability density
of a positive claim size (p. 1283: "a general nonnegative distribution … density d(·)"). -/
def Params.Standing (P : Params) : Prop :=
  0 < P.p ∧ 0 < P.r ∧ 0 < P.lamPlus ∧ 0 < P.lamMinus ∧ 0 < P.μ ∧ 0 < P.ν ∧
  0 ≤ P.α ∧ 0 ≤ P.β ∧ 0 ≤ P.γ ∧
  Measurable P.d ∧ (∀ y, 0 ≤ P.d y) ∧ (∀ y, y ≤ 0 → P.d y = 0) ∧
  ∫ y in Set.Ioi 0, P.d y = 1

/-- `λ := λ₋ + λ₊`, the total jump rate (p. 1285). -/
def Params.lam (P : Params) : ℝ := P.lamMinus + P.lamPlus

/-- The claim-size law: the measure with density `d` with respect to Lebesgue measure. -/
noncomputable def Params.claimLaw (P : Params) : Measure ℝ :=
  volume.withDensity (fun y => ENNReal.ofReal (P.d y))

/-- The Laplace–Stieltjes transform `δ(s) = ∫₀^∞ e^{-sy} d(y) dy` of the claim size. -/
noncomputable def Params.lst (P : Params) (s : ℝ) : ℝ :=
  ∫ y in Set.Ioi 0, Real.exp (-(s * y)) * P.d y

/-- The random primitives on a measurable space `Ω`: a measure `P` and one real family `Z`
indexed by `Fin 4 × ℕ`: `Z (0, n)` is the `n`-th interarrival time of the upward jumps,
`Z (1, n)` the `n`-th interarrival time of the claims, `Z (2, n)` the size of the `n`-th
upward jump and `Z (3, n)` the size of the `n`-th claim (all `0`-indexed). -/
structure Basis (Ω : Type*) [MeasurableSpace Ω] where
  P : Measure Ω
  Z : Fin 4 × ℕ → Ω → ℝ

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The probabilistic assumptions of §2.1: `P` is a probability measure; all primitives are
measurable and mutually independent; the upward jumps arrive at the epochs of a Poisson process
with rate `λ₊` (i.i.d. `Exp(λ₊)` interarrival times) and have i.i.d. `Exp(μ)` sizes; the claims
arrive at the epochs of an independent Poisson process with rate `λ₋` and have i.i.d. sizes
with density `d`. -/
def Basis.IsValid (B : Basis Ω) (P : Params) : Prop :=
  IsProbabilityMeasure B.P ∧ (∀ k, Measurable (B.Z k)) ∧ iIndepFun B.Z B.P ∧
  (∀ n, B.P.map (B.Z (0, n)) = expMeasure P.lamPlus) ∧
  (∀ n, B.P.map (B.Z (1, n)) = expMeasure P.lamMinus) ∧
  (∀ n, B.P.map (B.Z (2, n)) = expMeasure P.μ) ∧
  (∀ n, B.P.map (B.Z (3, n)) = P.claimLaw)

/-- The epoch of the `n`-th upward jump (`0`-indexed): `Z (0,0) + ⋯ + Z (0,n)`. -/
noncomputable def Basis.Tup (B : Basis Ω) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), B.Z (0, k) ω

/-- The epoch of the `n`-th claim (`0`-indexed): `Z (1,0) + ⋯ + Z (1,n)`. -/
noncomputable def Basis.Tdown (B : Basis Ω) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), B.Z (1, k) ω

/-- The number of upward jumps in `[0, t]`, computed as the least `n` with `t < Tup n`
(this is `#{n : Tup n ≤ t}` whenever the epochs increase to infinity, which holds a.s.). -/
noncomputable def Basis.Nup (B : Basis Ω) (t : ℝ) (ω : Ω) : ℕ :=
  sInf {n : ℕ | t < B.Tup n ω}

/-- The number of claims in `[0, t]`, computed as the least `n` with `t < Tdown n`. -/
noncomputable def Basis.Ndown (B : Basis Ω) (t : ℝ) (ω : Ω) : ℕ :=
  sInf {n : ℕ | t < B.Tdown n ω}

/-- The number of upward jumps in `[0, t)`, computed as the least `n` with `t ≤ Tup n`. -/
noncomputable def Basis.NupBefore (B : Basis Ω) (t : ℝ) (ω : Ω) : ℕ :=
  sInf {n : ℕ | t ≤ B.Tup n ω}

/-- The number of claims in `[0, t)`, computed as the least `n` with `t ≤ Tdown n`. -/
noncomputable def Basis.NdownBefore (B : Basis Ω) (t : ℝ) (ω : Ω) : ℕ :=
  sInf {n : ℕ | t ≤ B.Tdown n ω}

/-- The surplus process `X_t` started from `X_0 = x`, written in closed form by variation of
constants: between jumps it follows `dX_t = p dt + r X_t dt` (eq. (1)), each upward jump adds
its size and each claim subtracts its size, and every amount grows at rate `r` afterwards:
`X_t = x e^{rt} + (p/r)(e^{rt} - 1) + Σ_{jumps ≤ t} e^{r(t - T⁺_n)} Z(2,n)
  - Σ_{claims ≤ t} e^{r(t - T⁻_n)} Z(3,n)`. Right-continuous: jumps at time `t` are included. -/
noncomputable def Basis.X (B : Basis Ω) (P : Params) (x t : ℝ) (ω : Ω) : ℝ :=
  x * Real.exp (P.r * t) + P.p / P.r * (Real.exp (P.r * t) - 1)
    + ∑ n ∈ Finset.range (B.Nup t ω), Real.exp (P.r * (t - B.Tup n ω)) * B.Z (2, n) ω
    - ∑ n ∈ Finset.range (B.Ndown t ω), Real.exp (P.r * (t - B.Tdown n ω)) * B.Z (3, n) ω

/-- The left limit `X_{t-}`: the same closed form with only the jumps strictly before `t`. -/
noncomputable def Basis.Xminus (B : Basis Ω) (P : Params) (x t : ℝ) (ω : Ω) : ℝ :=
  x * Real.exp (P.r * t) + P.p / P.r * (Real.exp (P.r * t) - 1)
    + ∑ n ∈ Finset.range (B.NupBefore t ω), Real.exp (P.r * (t - B.Tup n ω)) * B.Z (2, n) ω
    - ∑ n ∈ Finset.range (B.NdownBefore t ω), Real.exp (P.r * (t - B.Tdown n ω)) * B.Z (3, n) ω

/-- The ruin time (end of the residual busy period), p. 1284:
`τ_x = inf{s > 0 : X_s ⩽ 0 | X_0 = x}`, with `τ_x = ∞` (here `⊤`) if there is no ruin. -/
noncomputable def Basis.tau (B : Basis Ω) (P : Params) (x : ℝ) (ω : Ω) : ℝ≥0∞ :=
  ⨅ (s : ℝ) (_ : 0 < s ∧ B.X P x s ω ≤ 0), ENNReal.ofReal s

/-- The penalty `e^{-α τ_x + β X_{τ_x} - γ X_{τ_x-}}` (read only on `{τ_x < ∞}`). -/
noncomputable def Basis.payoff (B : Basis Ω) (P : Params) (x : ℝ) (ω : Ω) : ℝ :=
  Real.exp (-(P.α * (B.tau P x ω).toReal) + P.β * B.X P x (B.tau P x ω).toReal ω
    - P.γ * B.Xminus P x (B.tau P x ω).toReal ω)

/-- `ϱ(x) = 𝔼(e^{-α τ_x + β X_{τ_x} - γ X_{τ_x-}} 1{τ_x < T_ν} | X_0 = x)` (p. 1285). The
horizon `T_ν ∼ Exp(ν)` is independent of the process, so it is integrated out against its law
`expMeasure ν`: `ϱ(x) = ∫ 𝔼(penalty · 1{τ_x < s}) Exp(ν)(ds)`. -/
noncomputable def rho (B : Basis Ω) (P : Params) (x : ℝ) : ℝ :=
  ∫ s, (∫ ω, Set.indicator {ω | B.tau P x ω < ENNReal.ofReal s} (B.payoff P x) ω ∂B.P)
    ∂(expMeasure P.ν)

/-- The transform `φ(ϑ) = ∫₀^∞ ϑ e^{-ϑx} ϱ(x) dx` (p. 1284): `ϱ` at an `Exp(ϑ)` initial level. -/
noncomputable def phi (B : Basis Ω) (P : Params) (ϑ : ℝ) : ℝ :=
  ∫ x in Set.Ioi 0, ϑ * Real.exp (-(ϑ * x)) * rho B P x

/-- `F̄(ϑ) = p/r - (λ₋/r)(1 - δ(ϑ))/ϑ + (λ₊/r) · 1/(μ - ϑ)` (p. 1286). -/
noncomputable def Fbar (P : Params) (ϑ : ℝ) : ℝ :=
  P.p / P.r - P.lamMinus / P.r * ((1 - P.lst ϑ) / ϑ) + P.lamPlus / P.r * (1 / (P.μ - ϑ))

/-- `F(ϑ) = F̄(ϑ) + A/ϑ` with `A = -(α + ν)/r` (p. 1286). -/
noncomputable def F (P : Params) (ϑ : ℝ) : ℝ :=
  Fbar P ϑ + (-(P.α + P.ν) / P.r) / ϑ

/-- `G₁(ϑ) = -p/r` (p. 1287). -/
noncomputable def G1 (P : Params) (_ϑ : ℝ) : ℝ := -(P.p / P.r)

/-- `G₂(ϑ) = -(λ₊/r) · 1/(μ - ϑ)` (p. 1287). -/
noncomputable def G2 (P : Params) (ϑ : ℝ) : ℝ := -(P.lamPlus / P.r) * (1 / (P.μ - ϑ))

/-- `G₃(ϑ) = (λ₋/r)(δ(β) - δ(ϑ + γ))/(ϑ + γ - β)` (p. 1287); at the removable singularity
`ϑ = β - γ` (p. 1286) it takes the limit value `(λ₋/r) ∫₀^∞ y e^{-βy} d(y) dy = -(λ₋/r) δ'(β)`. -/
noncomputable def G3 (P : Params) (ϑ : ℝ) : ℝ :=
  if ϑ + P.γ = P.β then
    P.lamMinus / P.r * ∫ y in Set.Ioi 0, y * Real.exp (-(P.β * y)) * P.d y
  else
    P.lamMinus / P.r * ((P.lst P.β - P.lst (ϑ + P.γ)) / (ϑ + P.γ - P.β))

/-- `G(ϑ) = c₀ G₁(ϑ) + c_μ G₂(ϑ) + G₃(ϑ)`; with `c₀ = ϱ(0)` and `c_μ = φ(μ)` this is the
function `G` of p. 1286 (decomposition on p. 1287). -/
noncomputable def G (P : Params) (c0 cμ ϑ : ℝ) : ℝ :=
  c0 * G1 P ϑ + cμ * G2 P ϑ + G3 P ϑ

/-- `F⋆` is a primitive of `F` on `(0, μ) ∪ (μ, ∞)` (p. 1287: "F⋆(·) the primitive of F(·)").
This fixes `F⋆` up to one additive constant on `(0, μ)` and another on `(μ, ∞)`. -/
def IsPrimitiveF (P : Params) (Fs : ℝ → ℝ) : Prop :=
  ∀ η, 0 < η → η ≠ P.μ → HasDerivAt Fs (F P η) η

/-- `I_k(ϑ) = ∫_ϑ^∞ G_k(η) exp(-F⋆(η)) dη` (p. 1287), for a function `Gk` and a primitive `Fs`. -/
noncomputable def I (Gk : ℝ → ℝ) (Fs : ℝ → ℝ) (ϑ : ℝ) : ℝ :=
  ∫ η in Set.Ioi ϑ, Gk η * Real.exp (-(Fs η))

end AffineStorage.Ruin


