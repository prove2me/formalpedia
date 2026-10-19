-- Prove2me | Definitions.Def_VarContrib_RegularMPE_Setting
-- name    : VarContrib_RegularMPE_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-18T20:12:09.680878+00:00
-- url     : https://prove2.me/theorems/abd178fd-ae83-45f9-911c-0f5c9b8aa103
-- title:
--   §2.1, pp. 6–9 — filtered space, Wiener process, uncontrolled family, state equation, controls Ξ, payoffs, Σ, reflection, Assumptions 1–3
-- statement:
--   The probabilistic layer of the model. A **setting** consists of a probability measure $P$ on $\Omega$, a filtration $(\mathcal F_t)_{t\ge0}$, a Wiener process $W$, a family of uncontrolled processes $X^x$ indexed by the initial value $x$, and two functions $\psi,\varphi$ (the increasing and decreasing fundamental solutions).
--
--   The objects built on it:
--
--   1. **Resolvent** (1), (3): $(Rg)(x)=\mathbb E\big[\int_0^\infty e^{-rt}g(X^x_t)\,dt\big]$.
--   2. **Controls $\Xi$**: adapted, nonnegative processes $\zeta$ with nondecreasing right-continuous paths, with $\zeta_{0-}=0$, so that $\zeta_0>0$ is a jump at time $0$.
--   3. **Discounted contribution** $\int_{[0,\infty)}e^{-rt}\,d\zeta_t$, the Lebesgue–Stieltjes integral of the path, which counts the time-$0$ jump.
--   4. **State solution**: $Z$ solves $dZ_t=b(Z_t)\,dt+\sigma(Z_t)\,dW_t+d\zeta_t$, $Z_{0-}=x$, if $Z$ is adapted, takes values in $I$, has right-continuous paths, and almost surely for all $t\ge0$
--   $$Z_t=x+\int_0^t b(Z_s)\,ds+\int_0^t\sigma(Z_s)\,dW_s+\zeta_t ,$$
--   with the Itô integral in the sense of the platform relation `EthierKurtz.HasBrownianItoIntegral`.
--   5. **Admissibility** of $\zeta$ along $Z$: $\zeta\in\Xi$, $e^{-rt}\pi(Z_t)$ is $P\otimes dt$-integrable, and $\mathbb E\int_{[0,\infty)}e^{-rt}d\zeta_t<\infty$.
--   6. **Payoffs**: for a control $\zeta$, $\mathbb E\big[\int_0^\infty e^{-rt}\pi(Z_t)dt-\int_{[0,\infty)}e^{-rt}k\,d\zeta_t\big]$; for a regular rate $d\xi_t=v(Z_t)dt$, $\mathbb E\int_0^\infty e^{-rt}(\pi(Z_t)-k\,v(Z_t))\,dt$.
--   7. **The class $\Sigma$** (p. 13): $d\zeta_t=v(t,Z_t)dt+d\zeta^s_t$ with $v\ge0$ Lipschitz in $x$ on $I$ and of linear growth (constants uniform in $t$), and $\zeta^s$ a control whose Stieltjes measure is singular with respect to Lebesgue measure (local-time part plus jumps).
--   8. **Reflection at $\theta$**: $Z_t\ge\theta$ for all $t$, and $d\zeta$ charges only the times at which $Z_t=\theta$.
--
--   The **standing assumptions** (one predicate) are: $P$ is a probability measure and $(\mathcal F_t)$ satisfies the usual conditions; $W$ is an $(\mathcal F_t)$-Brownian motion with continuous paths; $I$ is a nonempty open interval containing $x_0$; $\mu<0$, $\sigma>0$ on $I$, $k>0$, $r>0$; for every $x\in I$, $X^x$ solves $dX=\mu(X)dt+\sigma(X)dW$, $X_0=x$, with continuous paths; and
--
--   1. Assumption 1: (i) $\mu$, $\sigma$ are Lipschitz on $I$ with $|\mu(x)|+|\sigma(x)|\le\delta(1+|x|)$, $\delta>0$; (ii) for $x\in I$, $\{e^{-r\tau}(X^x_\tau)^-:\tau\text{ a finite stopping time}\}$ is uniformly integrable and $\lim_{t\to\infty}\mathbb E[e^{-rt}(X^x_t)^-]=0$;
--   2. Assumption 2: $\pi$ is continuous and strictly increasing on $I$, $\pi<\pi_M$ on $I$ for some $\pi_M>0$, and $e^{-rt}\pi(X^x_t)$ is $P\otimes dt$-integrable;
--   3. $\psi,\varphi$ are positive, $C^2$ on $I$, $\mathcal A\psi=\mathcal A\varphi=0$ on $I$, $\psi$ strictly increasing, $\varphi$ strictly decreasing, and $\mathbb E[e^{-r\tau_y}]=\psi(x)/\psi(y)$ for $x\le y$ and $=\varphi(x)/\varphi(y)$ for $y\le x$, where $\tau_y$ is the hitting time of $y$ by $X^x$;
--   4. Assumption 3: (i) $\lim_{x\to a}(R\pi)(x)<0$ (the limit exists in $[-\infty,\infty]$) and $\lim_{x\to a}(R\pi)(x)/\varphi(x)=0$; (ii) $q$ is strictly increasing below some $x^*\in I$ and strictly decreasing above it; (iii) with $S'(x)=\exp(\int_{x_0}^x 2\mu(y)/\sigma^2(y)\,dy)$,
--   $$\lim_{x\to a}q(x)=-\infty,\quad \lim_{x\to a}q(x)\psi'(x)S'(x)=0,\quad \lim_{x\to b}q(x)\varphi'(x)S'(x)=0,\quad \lim_{x\to b}\frac{(Rq)'(x)}{\varphi'(x)}>0 ;$$
--   5. $e^{-rt}q(X^x_t)$ is $P\otimes dt$-integrable for $x\in I$, so that $(Rq)$ is defined.
--
--   These are the objects in which the single decision maker problem (Lemma 1), the best-response verification (Theorem 1) and the equilibrium (Theorem 2) are stated.
--
--   **Formalization Note.** Time is $[0,\infty)$ as `ℝ≥0`. The initial value $x$ is the pre-jump value $Z_{0-}$ (the paper conditions on "$Z_0=x$" but lets the control jump at time $0$). Payoffs are compared only for admissible controls; a control with infinite expected cost, or whose discounted running profit is not integrable, has payoff $-\infty$ since $\pi$ is bounded above, so this loses no deviation. The fundamental solutions are pinned by the Laplace transforms of hitting times (Borodin–Salminen), as the paper's citation does. The base point $x_0\in I$ of the scale density replaces the printed $0$, which need not lie in $I$; changing it multiplies the expressions of Assumption 3(iii) by a positive constant. The printed bound $\lim_{x\to b}\pi(x)<\pi_M$ is stated as $\pi<\pi_M$ on $I$, which is equivalent for an increasing $\pi$ up to the choice of $\pi_M$. The integrability of $e^{-rt}q(X^x_t)$ is not printed; the paper presupposes it when it writes $(Rq)$ and $(Rq)'$. The usual conditions are right-continuity and $\mathcal F_0$ containing all $P$-null sets.
-- source:
--   Kwon, Game of Variable Contributions to the Common Good under Uncertainty, arXiv:1904.00500v1, pp. 6–9 and 11–13, §2.1, Assumptions 1–3, (1), (3), class Σ_i

import Mathlib
import Definitions.Def_EthierKurtz_HasBrownianItoIntegral
import Definitions.Def_VarContrib_RegularMPE_Model

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace VarContrib.RegularMPE

/-- The probabilistic data of §2.1 on a measurable space `Ω`: the measure `P`, the filtration
`(ℱ_t)`, the Wiener process `W`, the uncontrolled family `X^x` (`X x t ω` is `X^x_t(ω)`), and
the increasing and decreasing fundamental solutions `ψ`, `φ` of `𝒜ψ = 𝒜φ = 0` (p. 9). -/
structure Setting (Ω : Type*) [mΩ : MeasurableSpace Ω] where
  /-- the probability measure `P` -/
  P : Measure Ω
  /-- the filtration `(ℱ_t)_{t ≥ 0}` -/
  ℱ : Filtration ℝ≥0 mΩ
  /-- the Wiener process `W` -/
  W : ℝ≥0 → Ω → ℝ
  /-- the uncontrolled process `X^x` started at `x` -/
  X : ℝ → ℝ≥0 → Ω → ℝ
  /-- the increasing fundamental solution `ψ` -/
  ψ : ℝ → ℝ
  /-- the decreasing fundamental solution `φ` -/
  φ : ℝ → ℝ

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The resolvent `(Rg)(x) = E^x[∫₀^∞ e^{−rt} g(X^x_t) dt]` of (1) and (3), along the
uncontrolled process. -/
noncomputable def R (m : Model) (S : Setting Ω) (g : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ ω, (∫ t in Ioi (0 : ℝ), Real.exp (-(m.r * t)) * g (S.X x t.toNNReal ω)) ∂S.P

/-- The class `Ξ` of controls (p. 7): `ζ` is `(ℱ_t)`-adapted, nonnegative, with nondecreasing
right-continuous (hence càdlàg) paths. The convention `ζ_{0−} = 0` makes `ζ₀ > 0` a jump at
time `0`. -/
def IsControl (S : Setting Ω) (ζ : ℝ≥0 → Ω → ℝ) : Prop :=
  (∀ t, Measurable[S.ℱ t] (ζ t)) ∧ (∀ t ω, 0 ≤ ζ t ω) ∧ (∀ ω, Monotone fun t => ζ t ω) ∧
  (∀ ω t, ContinuousWithinAt (fun s => ζ s ω) (Ici t) t)

/-- The path of `ζ` extended to `ℝ` by `ζ_{0−} = 0` (value `0` at negative times). -/
noncomputable def ext (ζ : ℝ≥0 → Ω → ℝ) (ω : Ω) : ℝ → ℝ :=
  fun t => if t < 0 then 0 else ζ t.toNNReal ω

open Classical in
/-- The Stieltjes measure `dζ_t(ω)` of the extended path; it carries the mass `ζ₀(ω)` at `0`
(the initial jump). The zero measure if the path is not monotone (never the case for a
control). -/
noncomputable def stMeas (ζ : ℝ≥0 → Ω → ℝ) (ω : Ω) : Measure ℝ :=
  if h : Monotone (ext ζ ω) then h.stieltjesFunction.measure else 0

/-- The discounted contribution `∫_{[0,∞)} e^{−rt} dζ_t(ω)`, including the jump at time `0`,
with values in `[0, ∞]`. -/
noncomputable def cost (m : Model) (ζ : ℝ≥0 → Ω → ℝ) (ω : Ω) : ℝ≥0∞ :=
  ∫⁻ t in Ici (0 : ℝ), ENNReal.ofReal (Real.exp (-(m.r * t))) ∂(stMeas ζ ω)

/-- `Z` is a solution of the controlled state equation
`dZ_t = b(Z_t) dt + σ(Z_t) dW_t + dζ_t`, `Z_{0−} = x` (p. 7):
1. `Z` is `(ℱ_t)`-adapted and takes its values in `I`;
2. its paths are right-continuous;
3. `s ↦ b(Z_s)` is integrable on every `[0, t]`;
4. there is a process `M` that is the Itô integral `∫₀^· σ(Z_s) dW_s` (platform relation
   `HasBrownianItoIntegral`) such that, almost surely, for all `t ≥ 0`,
   `Z_t = x + ∫₀ᵗ b(Z_s) ds + M_t + ζ_t`. -/
def IsStateSol (m : Model) (S : Setting Ω) (b : ℝ → ℝ) (x : ℝ) (ζ Z : ℝ≥0 → Ω → ℝ) : Prop :=
  (∀ t, Measurable[S.ℱ t] (Z t)) ∧ (∀ t ω, Z t ω ∈ m.I) ∧
  (∀ ω t, ContinuousWithinAt (fun s => Z s ω) (Ici t) t) ∧
  (∀ ω (t : ℝ≥0), IntervalIntegrable (fun s : ℝ => b (Z s.toNNReal ω)) volume 0 (t : ℝ)) ∧
  ∃ M : ℝ≥0 → Ω → ℝ,
    EthierKurtz.HasBrownianItoIntegral S.P (fun t => S.ℱ t) S.W (fun t ω => m.σ (Z t ω)) M ∧
    ∀ᵐ ω ∂S.P, ∀ t : ℝ≥0,
      Z t ω = x + (∫ s in (0 : ℝ)..(t : ℝ), b (Z s.toNNReal ω)) + M t ω + ζ t ω

/-- An admissible control for the state `Z`: `ζ ∈ Ξ`, the discounted running profit
`e^{−rt} π(Z_t)` is integrable for `P ⊗ dt` on `Ω × (0, ∞)`, and the expected discounted
contribution `E[∫_{[0,∞)} e^{−rt} dζ_t]` is finite. -/
def Adm (m : Model) (S : Setting Ω) (ζ Z : ℝ≥0 → Ω → ℝ) : Prop :=
  IsControl S ζ ∧
  Integrable (fun p : Ω × ℝ => Real.exp (-(m.r * p.2)) * m.π (Z p.2.toNNReal p.1))
    (S.P.prod (volume.restrict (Ioi (0 : ℝ)))) ∧
  ∫⁻ ω, cost m ζ ω ∂S.P < ⊤

/-- The payoff `E[∫₀^∞ e^{−rt} π(Z_t) dt − ∫_{[0,∞)} e^{−rt} k dζ_t]` (p. 7) of a player who
contributes `ζ`, along the state `Z` (used only for admissible `ζ`). -/
noncomputable def devPay (m : Model) (S : Setting Ω) (ζ Z : ℝ≥0 → Ω → ℝ) : ℝ :=
  ∫ ω, ((∫ t in Ioi (0 : ℝ), Real.exp (-(m.r * t)) * m.π (Z t.toNNReal ω))
    - m.k * (cost m ζ ω).toReal) ∂S.P

/-- The payoff `E[∫₀^∞ e^{−rt} (π(Z_t) − k v(Z_t)) dt]` of a player who contributes at the
regular rate `dξ_t = v(Z_t) dt`, along the state `Z`. -/
noncomputable def regPay (m : Model) (S : Setting Ω) (v : ℝ → ℝ) (Z : ℝ≥0 → Ω → ℝ) : ℝ :=
  ∫ ω, (∫ t in Ioi (0 : ℝ), Real.exp (-(m.r * t)) *
    (m.π (Z t.toNNReal ω) - m.k * v (Z t.toNNReal ω))) ∂S.P

/-- `ζ ∈ Σ` along the state `Z` (p. 13): `dζ_t = v(t, Z_t) dt + dζˢ_t`, where the rate `v ≥ 0`
is Lipschitz in `x` on `I` (one constant for all `t`) with linear growth (one `δ` for all `t`),
and `ζˢ` is a control whose Stieltjes measure is singular with respect to Lebesgue measure (the
local-time part `ξˡ` plus the jumps `Δξ`). -/
def InSigma (m : Model) (S : Setting Ω) (ζ Z : ℝ≥0 → Ω → ℝ) : Prop :=
  ∃ v : ℝ≥0 → ℝ → ℝ, ∃ ζs : ℝ≥0 → Ω → ℝ,
    (∀ t, ∀ x ∈ m.I, 0 ≤ v t x) ∧
    (∃ L : ℝ≥0, ∀ t, LipschitzOnWith L (v t) m.I) ∧
    (∃ δ : ℝ, ∀ t, ∀ x ∈ m.I, |v t x| ≤ δ * (1 + |x|)) ∧
    IsControl S ζs ∧ (∀ ω, stMeas ζs ω ⟂ₘ volume) ∧
    ∀ ω (t : ℝ≥0), ζ t ω = (∫ s in (0 : ℝ)..(t : ℝ), v s.toNNReal (Z s.toNNReal ω)) + ζs t ω

/-- `ζ` reflects `Z` upward at `θ` (Skorokhod conditions): `Z_t ≥ θ` for all `t ≥ 0`, and
`dζ` charges only times at which `Z_t = θ` (so a jump at time `0` from `x < θ` lands at `θ`). -/
def ReflAt (θ : ℝ) (ζ Z : ℝ≥0 → Ω → ℝ) : Prop :=
  (∀ t ω, θ ≤ Z t ω) ∧ ∀ ω, stMeas ζ ω {t | 0 ≤ t ∧ θ < Z t.toNNReal ω} = 0

/-- The hitting time `τ_y = inf{t ≥ 0 : X^x_t = y}` of `y` by the uncontrolled process
(`⊤` if `y` is never hit). -/
noncomputable def hitTime (S : Setting Ω) (x y : ℝ) (ω : Ω) : WithTop ℝ≥0 :=
  ⨅ t ∈ {t : ℝ≥0 | S.X x t ω = y}, (t : WithTop ℝ≥0)

/-- The discount factor `e^{−rτ}` of a time `τ ∈ [0, ∞]`, with `e^{−r·∞} = 0`. -/
noncomputable def discAt (r : ℝ) : WithTop ℝ≥0 → ℝ
  | ⊤ => 0
  | (t : ℝ≥0) => Real.exp (-(r * t))

/-- The standing assumptions of §2.1 and Assumptions 1–3 (pp. 6–9), for the symmetric game:
1. `P` is a probability measure, and `(ℱ_t)` satisfies the usual conditions (right-continuous,
   `ℱ₀` contains every `P`-null set);
2. `W` is an `(ℱ_t)`-Brownian motion: a real Brownian motion with continuous paths, adapted,
   with `W_{s+t} − W_s` independent of `ℱ_s`;
3. `I` is a nonempty open interval containing `x₀`;
4. `μ < 0` and `σ > 0` on `I`, `k > 0`, `r > 0` (p. 7);
5. Assumption 1(i): `μ`, `σ` Lipschitz on `I` with `|μ(x)| + |σ(x)| ≤ δ(1 + |x|)`, `δ > 0`;
6. for every `x ∈ I`, `X^x` solves `dX = μ(X) dt + σ(X) dW`, `X_0 = x`, with continuous paths;
7. Assumption 1(ii): for `x ∈ I`, `{e^{−rτ}(X^x_τ)⁻ : τ a finite stopping time}` is uniformly
   integrable and `E[e^{−rt}(X^x_t)⁻] → 0` as `t → ∞`;
8. Assumption 2: `π` is continuous and strictly increasing on `I`, bounded above by some
   `π_M > 0`, and `e^{−rt}π(X^x_t)` is `P ⊗ dt`-integrable for `x ∈ I`;
9. `ψ`, `φ` are positive, `C²` on `I`, solve `𝒜ψ = 𝒜φ = 0` on `I`, `ψ` is strictly increasing,
   `φ` strictly decreasing, and `E[e^{−rτ_y}] = ψ(x)/ψ(y)` for `x ≤ y`, `= φ(x)/φ(y)` for
   `y ≤ x`, where `τ_y` is the hitting time of `y` by `X^x` (Borodin–Salminen);
10. Assumption 3(i): `lim_{x→a} (Rπ)(x)` exists in `[−∞, ∞]` and is `< 0`, and
    `lim_{x→a} (Rπ)(x)/φ(x) = 0`;
11. Assumption 3(ii): `q` is strictly increasing below some `x* ∈ I` and strictly decreasing
    above it;
12. Assumption 3(iii): `lim_{x→a} q(x) = −∞`, `lim_{x→a} q(x)ψ′(x)exp(∫_{x₀}^x 2μ/σ²) = 0`,
    `lim_{x→b} q(x)φ′(x)exp(∫_{x₀}^x 2μ/σ²) = 0`, and `lim_{x→b} (Rq)′(x)/φ′(x)` exists in
    `[−∞, ∞]` and is `> 0`;
13. `(Rq)` is defined: `e^{−rt}q(X^x_t)` is `P ⊗ dt`-integrable for `x ∈ I`. -/
structure Standing (m : Model) (S : Setting Ω) : Prop where
  prob : IsProbabilityMeasure S.P
  filt_rightCont : ∀ t, S.ℱ t = ⨅ s, ⨅ (_ : t < s), S.ℱ s
  filt_complete : ∀ s : Set Ω, S.P s = 0 → MeasurableSet[S.ℱ 0] s
  bm : IsBrownianReal S.W S.P
  bm_cont : ∀ ω, Continuous (S.W · ω)
  bm_adapted : ∀ t, Measurable[S.ℱ t] (S.W t)
  bm_indep : ∀ s t : ℝ≥0, Indep (S.ℱ s)
    (MeasurableSpace.comap (fun ω => S.W (s + t) ω - S.W s ω) inferInstance) S.P
  I_open : IsOpen m.I
  I_ordConnected : m.I.OrdConnected
  I_nonempty : m.I.Nonempty
  x₀_mem : m.x₀ ∈ m.I
  μ_neg : ∀ x ∈ m.I, m.μ x < 0
  σ_pos : ∀ x ∈ m.I, 0 < m.σ x
  k_pos : 0 < m.k
  r_pos : 0 < m.r
  lipschitz : ∃ L : ℝ≥0, LipschitzOnWith L m.μ m.I ∧ LipschitzOnWith L m.σ m.I
  growth : ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ m.I, |m.μ x| + |m.σ x| ≤ δ * (1 + |x|)
  uncontrolled : ∀ x ∈ m.I, IsStateSol m S m.μ x (fun _ _ => 0) (S.X x) ∧
    ∀ ω, Continuous (S.X x · ω)
  ui_neg : ∀ x ∈ m.I, UniformIntegrable
    (fun τ : {τ : Ω → ℝ≥0 // IsStoppingTime S.ℱ (fun ω => ((τ ω : ℝ≥0) : WithTop ℝ≥0))} =>
      fun ω => Real.exp (-(m.r * (τ.1 ω : ℝ))) * max (-(S.X x (τ.1 ω) ω)) 0) 1 S.P
  tail_neg : ∀ x ∈ m.I, Tendsto
    (fun t : ℝ≥0 => ∫ ω, Real.exp (-(m.r * (t : ℝ))) * max (-(S.X x t ω)) 0 ∂S.P) atTop (𝓝 0)
  π_cont : ContinuousOn m.π m.I
  π_strictMono : StrictMonoOn m.π m.I
  π_bdd : ∃ πM : ℝ, 0 < πM ∧ ∀ x ∈ m.I, m.π x < πM
  π_integrable : ∀ x ∈ m.I,
    Integrable (fun p : Ω × ℝ => Real.exp (-(m.r * p.2)) * m.π (S.X x p.2.toNNReal p.1))
      (S.P.prod (volume.restrict (Ioi (0 : ℝ))))
  ψ_pos : ∀ x ∈ m.I, 0 < S.ψ x
  φ_pos : ∀ x ∈ m.I, 0 < S.φ x
  ψ_C2 : ContDiffOn ℝ 2 S.ψ m.I
  φ_C2 : ContDiffOn ℝ 2 S.φ m.I
  ψ_ode : ∀ x ∈ m.I, gen m S.ψ x = 0
  φ_ode : ∀ x ∈ m.I, gen m S.φ x = 0
  ψ_strictMono : StrictMonoOn S.ψ m.I
  φ_strictAnti : StrictAntiOn S.φ m.I
  hit_up : ∀ x ∈ m.I, ∀ y ∈ m.I, x ≤ y →
    ∫ ω, discAt m.r (hitTime S x y ω) ∂S.P = S.ψ x / S.ψ y
  hit_down : ∀ x ∈ m.I, ∀ y ∈ m.I, y ≤ x →
    ∫ ω, discAt m.r (hitTime S x y ω) ∂S.P = S.φ x / S.φ y
  A3i_lim : ∃ L : EReal, L < 0 ∧
    Tendsto (fun x => ((R m S m.π x : ℝ) : EReal)) (lowerEnd m.I) (𝓝 L)
  A3i_ratio : Tendsto (fun x => R m S m.π x / S.φ x) (lowerEnd m.I) (𝓝 0)
  A3ii : ∃ xs ∈ m.I, StrictMonoOn (q m) {x | x ∈ m.I ∧ x < xs} ∧
    StrictAntiOn (q m) {x | x ∈ m.I ∧ xs < x}
  A3iii_q : Tendsto (q m) (lowerEnd m.I) atBot
  A3iii_ψ : Tendsto (fun x => q m x * deriv S.ψ x *
      Real.exp (∫ y in m.x₀..x, 2 * m.μ y / m.σ y ^ 2)) (lowerEnd m.I) (𝓝 0)
  A3iii_φ : Tendsto (fun x => q m x * deriv S.φ x *
      Real.exp (∫ y in m.x₀..x, 2 * m.μ y / m.σ y ^ 2)) (upperEnd m.I) (𝓝 0)
  A3iii_Rq : ∃ L : EReal, 0 < L ∧
    Tendsto (fun x => ((deriv (R m S (q m)) x / deriv S.φ x : ℝ) : EReal)) (upperEnd m.I) (𝓝 L)
  q_integrable : ∀ x ∈ m.I,
    Integrable (fun p : Ω × ℝ => Real.exp (-(m.r * p.2)) * q m (S.X x p.2.toNNReal p.1))
      (S.P.prod (volume.restrict (Ioi (0 : ℝ))))

end VarContrib.RegularMPE


