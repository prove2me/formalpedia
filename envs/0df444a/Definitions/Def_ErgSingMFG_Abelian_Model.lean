-- Prove2me | Definitions.Def_ErgSingMFG_Abelian_Model
-- name    : ErgSingMFG_Abelian_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-23T03:55:12.507422+00:00
-- url     : https://prove2.me/theorems/8c68376b-0cfd-49b3-8eb0-c082e95fd602
-- title:
--   §2–§3, pp. 4–7 — filtered space, controls 𝒜, SDE (2.1), reflection, 𝒜_d, 𝒜_e, J (3.1), G (3.2), V (9.1), λ⋆ (4.2), limit law, θ(μ), Definitions 3.1–3.2
-- statement:
--   The probabilistic layer. A **setting** is a probability space $(\Omega,\mathcal F,P)$ with a filtration $\mathbb F=(\mathcal F_t)_{t\ge0}$ satisfying the usual conditions and an $\mathbb F$-Brownian motion $B$ (continuous paths, adapted, increments independent of the past).
--
--   1. A **control** $\nu\in\mathcal A$ (2.2) is an adapted, nonnegative process with nondecreasing right-continuous paths and $\nu_{0-}=0$; $d\nu$ is its Lebesgue–Stieltjes measure on $[0,\infty)$, including the initial jump $\nu_0$.
--   2. $X$ **solves (2.1)** from $x$ under $\nu$ if it is adapted, $\mathbb R_+$-valued and right-continuous, and a.s. $X_t=x+\int_0^tb(X_s)ds+\int_0^t\sigma(X_s)dB_s+\nu_t$ for all $t$ (the stochastic integral is the platform relation `HasBrownianItoIntegral`).
--   3. $\nu$ **reflects** $X$ upward at $a$ if a.s. $X_t\ge a$ for all $t$ and $d\nu$ charges only $\{t:X_t=a\}$ (9.11).
--   4. $\mathcal A_d=\{\nu\in\mathcal A:E[\int_0^\infty e^{-rs}d\nu_s]<\infty\}$ and $\mathcal A_e=\{\nu\in\mathcal A:E[\nu_T]<\infty\ \forall T>0\}$ (3.3).
--   5. The payoffs are
--   $$J(x,\nu,\theta;r)=E\Big[\int_0^\infty e^{-rs}\pi(X_s,\theta)ds-\int_0^\infty e^{-rs}d\nu_s\Big],\qquad G(x,\nu,\theta)=\limsup_{T\uparrow\infty}\frac1TE\Big[\int_0^T\pi(X_s,\theta)ds-\nu_T\Big],$$
--   and the values are $V(x,\theta;r)=\sup_{\nu\in\mathcal A_d}J(x,\nu,\theta;r)$ (9.1) and $\lambda^\star(\theta)=\sup_{\nu\in\mathcal A_e}G(x,\nu,\theta)$ (4.2).
--   6. $X$ has **limiting distribution** $\mu$ if the laws of $X_t$ converge weakly to the probability measure $\mu$; $\theta=\theta(\mu)$ means $\mu$ is carried by $\mathbb R_+$, $\int f\,d\mu<\infty$ and $\theta=F(\int f\,d\mu)$ (3.4).
--   7. **Definition 3.1.** $(\nu,\theta)\in\mathcal A_d\times\mathbb R_+$ is an equilibrium of the discounted MFG for $x$ if $J(x,\nu,\theta;r)\ge J(x,\nu',\theta;r)$ for all $\nu'\in\mathcal A_d$ and the optimally controlled process has a limiting distribution $\mu$ with $\theta=\theta(\mu)$. **Definition 3.2** is the same with $\mathcal A_e$ and $G$.
--
--   The file also defines the hitting time $\tau_y=\inf\{t\ge0:X_t=y\}\in[0,\infty]$, and the expected discounted profit of the uncontrolled process, $\bar v(x,\theta)=E_x[\int_0^\infty e^{-rs}\pi(X_s,\theta)ds]$ along a solution of (2.1) from $x$ with $\nu\equiv0$ (p. 18, the function $\bar v$ in the candidate value (9.2)).
--
--   **Formalization Note.** $J$, $G$, $V$, $\lambda^\star$ take values in $[-\infty,+\infty]$: the expectations of the nonnegative profit and cost are lower Lebesgue integrals in $[0,\infty]$ and are subtracted in `EReal`; suprema are `EReal` suprema over admissible controls together with their solutions of (2.1). The optimally controlled process is carried as an explicit solution $X$; optimality compares with every admissible $\nu'$ and every solution $X'$ of (2.1) under it. The reflection conditions hold almost surely. Controls are required to have nonnegative, nondecreasing, right-continuous paths for every $\omega$ (the paper: almost surely), and solutions of (2.1) to be $\mathbb R_+$-valued and right-continuous for every $\omega$; under the usual conditions every process with these properties almost surely has an indistinguishable modification with them surely, and payoffs, laws and the reflection conditions do not see the modification. $\bar v$ is the `EReal` supremum of the zero-control payoff over the solutions of (2.1) from $x$ with $\nu\equiv0$, which is $-\infty$ if there is none and otherwise the common value of all of them (strong uniqueness).
-- source:
--   Cao, Dianetti, Ferrari, Stationary Discounted and Ergodic Mean Field Games with Singular Controls, arXiv:2105.07213v1, pp. 4–7 and 18, (2.1)–(2.2), (3.1)–(3.4), Definitions 3.1, 3.2, (4.2), (9.1), (9.11)

import Mathlib
import Definitions.Def_EthierKurtz_HasBrownianItoIntegral
import Definitions.Def_ErgSingMFG_Abelian_Analytic

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ErgSingMFG.Abelian

/-- The probabilistic data of §2 (p. 4) on a measurable space `Ω`: the measure `P`, the
filtration `𝔽 = (ℱ_t)_{t ≥ 0}` and the Brownian motion `B`. -/
structure Setting (Ω : Type) [mΩ : MeasurableSpace Ω] where
  /-- the probability measure `P` -/
  P : Measure Ω
  /-- the filtration `𝔽 = (ℱ_t)_{t ≥ 0}` -/
  ℱ : Filtration ℝ≥0 mΩ
  /-- the `𝔽`-Brownian motion `B` -/
  B : ℝ≥0 → Ω → ℝ

variable {Ω : Type} [MeasurableSpace Ω]

/-- The standing probabilistic setting of p. 4: `P` is a probability measure; the filtration
satisfies the usual conditions (right-continuous, `ℱ₀` contains every `P`-null set); `B` is an
`𝔽`-Brownian motion (a real Brownian motion with continuous paths, adapted, whose increments
`B_{s+t} − B_s` are independent of `ℱ_s`). -/
def IsSetting (S : Setting Ω) : Prop :=
  IsProbabilityMeasure S.P ∧
  (∀ t, S.ℱ t = ⨅ s, ⨅ (_ : t < s), S.ℱ s) ∧
  (∀ s : Set Ω, S.P s = 0 → MeasurableSet[S.ℱ 0] s) ∧
  IsBrownianReal S.B S.P ∧
  (∀ ω, Continuous (S.B · ω)) ∧
  (∀ t, Measurable[S.ℱ t] (S.B t)) ∧
  ∀ s t : ℝ≥0, Indep (S.ℱ s)
    (MeasurableSpace.comap (fun ω => S.B (s + t) ω - S.B s ω) inferInstance) S.P

/-- `ν ∈ 𝒜` (2.2): `ν` is `𝔽`-adapted, nonnegative, with nondecreasing right-continuous paths;
the convention `ν_{0−} = 0` makes `ν₀ > 0` an initial jump (see `ext`, `stMeas`). -/
def IsControl (S : Setting Ω) (ν : ℝ≥0 → Ω → ℝ) : Prop :=
  (∀ t, Measurable[S.ℱ t] (ν t)) ∧ (∀ t ω, 0 ≤ ν t ω) ∧ (∀ ω, Monotone fun t => ν t ω) ∧
  (∀ ω t, ContinuousWithinAt (fun s => ν s ω) (Ici t) t)

/-- The path of `ν` extended to `ℝ` by `ν_{0−} = 0` (value `0` at negative times). -/
noncomputable def ext (ν : ℝ≥0 → Ω → ℝ) (ω : Ω) : ℝ → ℝ :=
  fun t => if t < 0 then 0 else ν t.toNNReal ω

open Classical in
/-- The Lebesgue–Stieltjes measure `dν_t(ω)` of the extended path, carrying the mass `ν₀(ω)` at
`t = 0` (the initial jump, p. 7). The zero measure if the path is not monotone (never the case for
a control). -/
noncomputable def stMeas (ν : ℝ≥0 → Ω → ℝ) (ω : Ω) : Measure ℝ :=
  if h : Monotone (ext ν ω) then h.stieltjesFunction.measure else 0

/-- `X` solves the controlled state equation (2.1) `dX_t = b(X_t)dt + σ(X_t)dB_t + dν_t`,
`X_{0−} = x`:
1. `X` is `𝔽`-adapted with values in `ℝ₊ = (0, ∞)`, and has right-continuous paths;
2. `s ↦ b(X_s)` is integrable on every `[0, t]`;
3. there is a process `M`, the Itô integral `∫₀^· σ(X_s) dB_s` (platform relation
   `EthierKurtz.HasBrownianItoIntegral`), such that almost surely, for all `t ≥ 0`,
   `X_t = x + ∫₀ᵗ b(X_s) ds + M_t + ν_t`. -/
def IsStateSol (m : Model) (S : Setting Ω) (x : ℝ) (ν X : ℝ≥0 → Ω → ℝ) : Prop :=
  (∀ t, Measurable[S.ℱ t] (X t)) ∧ (∀ t ω, 0 < X t ω) ∧
  (∀ ω t, ContinuousWithinAt (fun s => X s ω) (Ici t) t) ∧
  (∀ ω (t : ℝ≥0), IntervalIntegrable (fun s : ℝ => m.b (X s.toNNReal ω)) volume 0 (t : ℝ)) ∧
  ∃ M : ℝ≥0 → Ω → ℝ,
    EthierKurtz.HasBrownianItoIntegral S.P (fun t => S.ℱ t) S.B (fun t ω => m.σ (X t ω)) M ∧
    ∀ᵐ ω ∂S.P, ∀ t : ℝ≥0,
      X t ω = x + (∫ s in (0 : ℝ)..(t : ℝ), m.b (X s.toNNReal ω)) + M t ω + ν t ω

/-- `ν` reflects `X` upward at the barrier `a` (Skorokhod conditions, (9.11)): almost surely,
`X_t ≥ a` for all `t ≥ 0` and `dν` charges only times `t ≥ 0` at which `X_t = a`. -/
def ReflAt (S : Setting Ω) (a : ℝ) (ν X : ℝ≥0 → Ω → ℝ) : Prop :=
  ∀ᵐ ω ∂S.P, (∀ t, a ≤ X t ω) ∧ stMeas ν ω {t | 0 ≤ t ∧ a < X t.toNNReal ω} = 0

/-- The discounted cost `∫_{[0,∞)} e^{−rt} dν_t(ω) ∈ [0, ∞]`, including the initial jump. -/
noncomputable def costD (r : ℝ) (ν : ℝ≥0 → Ω → ℝ) (ω : Ω) : ℝ≥0∞ :=
  ∫⁻ t in Ici (0 : ℝ), ENNReal.ofReal (Real.exp (-(r * t))) ∂(stMeas ν ω)

/-- `ν ∈ 𝒜_d` (3.3) at the rate `r`: `ν ∈ 𝒜` and `E[∫₀^∞ e^{−rs} dν_s] < ∞`. -/
def Ad (S : Setting Ω) (r : ℝ) (ν : ℝ≥0 → Ω → ℝ) : Prop :=
  IsControl S ν ∧ ∫⁻ ω, costD r ν ω ∂S.P < ⊤

/-- `ν ∈ 𝒜_e` (3.3): `ν ∈ 𝒜` and `E[ν_T] < ∞` for every `T > 0`. -/
def Ae (S : Setting Ω) (ν : ℝ≥0 → Ω → ℝ) : Prop :=
  IsControl S ν ∧ ∀ T : ℝ≥0, 0 < T → ∫⁻ ω, ENNReal.ofReal (ν T ω) ∂S.P < ⊤

/-- The discounted payoff (3.1) along the state `X` of the control `ν`:
`J = E[∫₀^∞ e^{−rs} π(X_s, θ) ds] − E[∫₀^∞ e^{−rs} dν_s]`, in `[−∞, +∞]`. Both expectations are of
nonnegative quantities (`π ≥ 0`), taken in `[0, ∞]` and subtracted in `EReal`; on `𝒜_d` the cost
is finite, so the difference is the paper's. -/
noncomputable def J (m : Model) (S : Setting Ω) (r θ : ℝ) (ν X : ℝ≥0 → Ω → ℝ) : EReal :=
  ((∫⁻ ω, (∫⁻ s in Ioi (0 : ℝ),
      ENNReal.ofReal (Real.exp (-(r * s)) * m.π (X s.toNNReal ω) θ)) ∂S.P : ℝ≥0∞) : EReal)
    - ((∫⁻ ω, costD r ν ω ∂S.P : ℝ≥0∞) : EReal)

/-- The ergodic payoff (3.2) along the state `X` of the control `ν`:
`G = limsup_{T↑∞} (1/T) E[∫₀ᵀ π(X_s, θ) ds − ν_T]`, in `[−∞, +∞]`, with the two expectations of
nonnegative quantities taken in `[0, ∞]` and subtracted in `EReal` (on `𝒜_e`, `E[ν_T] < ∞`). -/
noncomputable def G (m : Model) (S : Setting Ω) (θ : ℝ) (ν X : ℝ≥0 → Ω → ℝ) : EReal :=
  limsup (fun T : ℝ≥0 => (((1 / (T : ℝ)) : ℝ) : EReal) *
    (((∫⁻ ω, (∫⁻ s in Ioc (0 : ℝ) (T : ℝ),
        ENNReal.ofReal (m.π (X s.toNNReal ω) θ)) ∂S.P : ℝ≥0∞) : EReal)
      - ((∫⁻ ω, ENNReal.ofReal (ν T ω) ∂S.P : ℝ≥0∞) : EReal))) atTop

/-- The discounted value (9.1): `V(x, θ; r) = sup_{ν ∈ 𝒜_d} J(x, ν, θ; r)`, the supremum in `EReal`
over admissible controls together with their solutions of (2.1) from `x`. -/
noncomputable def V (m : Model) (S : Setting Ω) (x θ r : ℝ) : EReal :=
  ⨆ p : {p : (ℝ≥0 → Ω → ℝ) × (ℝ≥0 → Ω → ℝ) // Ad S r p.1 ∧ IsStateSol m S x p.1 p.2},
    J m S r θ p.1.1 p.1.2

/-- The expected discounted profit of the uncontrolled process from `x` (p. 18, below (9.2)):
`v̄(x, θ) = E_x[∫₀^∞ e^{−rs} π(X_s, θ) ds]`, the payoff `J` of the zero control along a solution of
(2.1) from `x` with `ν ≡ 0`, taken as the `EReal` supremum over such solutions (`⊥` if there is
none; by strong uniqueness every solution gives the same value). -/
noncomputable def vbar (m : Model) (S : Setting Ω) (x θ r : ℝ) : EReal :=
  ⨆ X : {X : ℝ≥0 → Ω → ℝ // IsStateSol m S x (fun _ _ => 0) X},
    J m S r θ (fun _ _ => 0) X.1

/-- The ergodic value (4.2): `λ⋆(θ) = sup_{ν ∈ 𝒜_e} G(x, ν, θ)`, the supremum in `EReal` over
admissible controls together with their solutions of (2.1) from `x`. -/
noncomputable def lamStar (m : Model) (S : Setting Ω) (x θ : ℝ) : EReal :=
  ⨆ p : {p : (ℝ≥0 → Ω → ℝ) × (ℝ≥0 → Ω → ℝ) // Ae S p.1 ∧ IsStateSol m S x p.1 p.2},
    G m S θ p.1.1 p.1.2

/-- `X` admits the limiting distribution `μ`: `μ` is a probability measure and the laws of `X_t`
converge weakly to `μ` as `t → ∞` (tested against bounded continuous functions). -/
def HasLimitLaw (S : Setting Ω) (X : ℝ≥0 → Ω → ℝ) (μ : Measure ℝ) : Prop :=
  IsProbabilityMeasure μ ∧ ∀ g : BoundedContinuousFunction ℝ ℝ,
    Tendsto (fun t : ℝ≥0 => ∫ ω, g (X t ω) ∂S.P) atTop (𝓝 (∫ y, g y ∂μ))

/-- `θ = θ(μ)` (3.4) with `θ` finite: `μ` is carried by `ℝ₊`, `∫_{ℝ₊} f dμ < ∞`, and
`θ = F(∫_{ℝ₊} f dμ)`. -/
def ThetaEq (m : Model) (μ : Measure ℝ) (θ : ℝ) : Prop :=
  μ (Iic 0) = 0 ∧ ∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal (m.f y) ∂μ < ⊤ ∧
    θ = m.F (∫ y in Ioi (0 : ℝ), m.f y ∂μ)

/-- Definition 3.1 (p. 7): `(ν, θ) ∈ 𝒜_d × ℝ₊` is an equilibrium of the discounted MFG at the rate
`r` for the initial condition `x`, with `X` the optimally controlled process (a solution of (2.1)
under `ν` from `x`):
1. `J(x, ν, θ; r) ≥ J(x, ν′, θ; r)` for every `ν′ ∈ 𝒜_d` and every solution `X′` of (2.1) under
   `ν′` from `x`;
2. `X` admits a limiting distribution `μ` with `θ = θ(μ)`. -/
def IsDiscEq (m : Model) (S : Setting Ω) (r x : ℝ) (ν X : ℝ≥0 → Ω → ℝ) (θ : ℝ) : Prop :=
  0 < θ ∧ Ad S r ν ∧ IsStateSol m S x ν X ∧
  (∀ ν' X' : ℝ≥0 → Ω → ℝ, Ad S r ν' → IsStateSol m S x ν' X' →
    J m S r θ ν' X' ≤ J m S r θ ν X) ∧
  ∃ μ : Measure ℝ, HasLimitLaw S X μ ∧ ThetaEq m μ θ

/-- Definition 3.2 (p. 7): `(ν, θ) ∈ 𝒜_e × ℝ₊` is an equilibrium of the ergodic MFG for the
initial condition `x`, with `X` the optimally controlled process (a solution of (2.1) under `ν`
from `x`):
1. `G(x, ν, θ) ≥ G(x, ν′, θ)` for every `ν′ ∈ 𝒜_e` and every solution `X′` of (2.1) under `ν′`
   from `x`;
2. `X` admits a limiting distribution `μ` with `θ = θ(μ)`. -/
def IsErgEq (m : Model) (S : Setting Ω) (x : ℝ) (ν X : ℝ≥0 → Ω → ℝ) (θ : ℝ) : Prop :=
  0 < θ ∧ Ae S ν ∧ IsStateSol m S x ν X ∧
  (∀ ν' X' : ℝ≥0 → Ω → ℝ, Ae S ν' → IsStateSol m S x ν' X' →
    G m S θ ν' X' ≤ G m S θ ν X) ∧
  ∃ μ : Measure ℝ, HasLimitLaw S X μ ∧ ThetaEq m μ θ

/-- The hitting time `τ_y = inf{t ≥ 0 : X_t = y} ∈ [0, ∞]` of the level `y` by `X` (`∞` if never
hit). -/
noncomputable def hitTime (X : ℝ≥0 → Ω → ℝ) (y : ℝ) (ω : Ω) : ℝ≥0∞ :=
  ⨅ t ∈ {t : ℝ≥0 | X t ω = y}, ((t : ℝ≥0) : ℝ≥0∞)

end ErgSingMFG.Abelian


