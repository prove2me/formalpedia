-- Prove2me | Definitions.Def_PropagatorLimit_Scaling_Setting
-- name    : PropagatorLimit_Scaling_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T12:47:45.484324+00:00
-- url     : https://prove2.me/theorems/7a5559ef-6a0a-4806-beac-3e18808d9517
-- title:
--   Notation p. 3, p. 5, Assumptions A.1–A.2 pp. 24–25, Theorem A.3 p. 25 — filtered Brownian motions, Itô processes with Itô volatility, the time grid, very good extensions, stable convergence in law
-- statement:
--   This file fixes the probabilistic setting shared by every statement of the mission. Throughout, $(\Omega,\mathcal F,(\mathcal F_t)_{t\ge0},P)$ is a filtered probability space and time runs over $[0,\infty)$; statements only read times in $[0,T]$.
--
--   1. **Brownian motions.** A process $W$ is an $(\mathcal F_t)$-Brownian motion if it has the finite-dimensional laws of a standard Brownian motion, continuous paths, is adapted, and its increments $(W_{s+u}-W_s)_{u\ge0}$ are independent of $\mathcal F_s$ for every $s$. A **Brownian pair** $(W,W^\perp)$ consists of two such Brownian motions that are independent of each other and whose joint increments after $s$ are independent of $\mathcal F_s$.
--   2. **Local boundedness.** A process is locally bounded if, along a localizing sequence of stopping times, every stopped process is uniformly bounded.
--   3. **Assumption A.1** (p. 24). A real state process $X$ with Itô dynamics
--   $$dX_t=b_t\,dt+\sigma_t\,dW_t,\qquad d\sigma_t=\tilde b_t\,dt+\tilde\sigma_t\,dW_t+a_t\,dW^\perp_t,$$
--   where $b,\tilde b,\tilde\sigma,a$ are locally bounded. The equations hold almost surely for all $t$, the stochastic integrals being continuous Itô integrals.
--   4. **The order flow** (p. 5). An Itô process $F\in\mathcal L^2$ (that is, adapted with $E[\int_0^T|F_t|^2dt]<\infty$, p. 3) with $dF_t=\mu_t\,dt+v_t\,dW_t$ and $dv_t=a_t\,dt+\eta_t\,dW_t+b_t\,dW^\perp_t$, where $\mu,a,\eta,b$ are locally bounded and càdlàg and the volatility $v$ is positive. These are the dynamics of Assumption A.1 under the renaming $(F,\mu,v,a,\eta,b)\mapsto(X,b,\sigma,\tilde b,\tilde\sigma,a)$.
--   5. **The time grid** (p. 3). $\Delta t^N=T/N$, $t^N_n=n\Delta t^N$, and $\Delta X^N_n=X_{t^N_n}-X_{t^N_{n-1}}$ for $n\ge1$. The number of grid steps up to time $t$ is $\lceil t/\Delta t^N\rceil\wedge N$.
--   6. **Assumption A.2** (p. 25). $F:[0,T]\times\mathbb R\to\mathbb R$ satisfies, for a function $G$ of at most linear growth and a constant $\gamma>1/2$: $F(t,x)=-F(t,-x)$; $x\mapsto F(t,x)$ is $C^1$; $|F(t,x)|+|\partial_xF(t,x)|\le G(x)$; $|F(t,x)-F(s,x)|\le G(x)|t-s|^\gamma$, for all $t,s\in[0,T]$ and $x\in\mathbb R$.
--   7. **The ingredients of Theorem A.3.** With $\tilde E[f(Z)]$ the expectation of $f(Z)$ for a standard normal $Z$: the normalized sum $\sqrt{\Delta t^N}\sum_{n=1}^{\lceil t/\Delta t^N\rceil\wedge N}F\big(t^N_{n-1},\Delta X^N_n/\sqrt{\Delta t^N}\big)$, the drift density $b_s\tilde E[\partial_xF(s,\sigma_sZ)]+\frac{\tilde\sigma_s}{2}\tilde E[(Z^2-1)\partial_xF(s,\sigma_sZ)]$, the diffusion coefficient $\sqrt{\tilde E[F^2(s,\sigma_sZ)]}$ and the covariation density $\tilde E[ZF(s,\sigma_sZ)]/\sqrt{\tilde E[F^2(s,\sigma_sZ)]}$.
--   8. **Very good extensions.** An extension is a filtered probability space $(\Omega',\mathcal F',(\mathcal G_t),P')$ with a measurable map $\pi:\Omega'\to\Omega$ such that $P'\circ\pi^{-1}=P$ and $\pi^{-1}(\mathcal F_t)\subseteq\mathcal G_t$. It is **very good** if $E'[Y\circ\pi\mid\mathcal G_t]=E[Y\mid\mathcal F_t]\circ\pi$ almost surely for every bounded $\mathcal F$-measurable $Y$ and every $t$, so that every $(\mathcal F_t)$-martingale remains a $(\mathcal G_t)$-martingale.
--   9. **Stable convergence in law on $[0,T]$.** Processes $X^N$ on $\Omega$ converge stably in law to a process $X$ on an extension if
--   $$E\big[Y\,f(X^N)\big]\longrightarrow E'\big[(Y\circ\pi)\,f(X)\big]$$
--   for every bounded measurable $Y$ on $\Omega$ and every bounded path functional $f$ that is Lipschitz for the uniform distance $\sup_{t\in[0,T]}|x_t-y_t|$.
--
--   These are the objects of Theorem 3.3 and of the appendix argument (Theorem A.3) that proves it.
--
--   **Formalization Note** Time is $\mathbb R_{\ge0}$. Brownian paths are continuous for every $\omega$ (a version choice). Itô integrals are the published `EthierKurtz.HasBrownianItoIntegral` relation (step approximations converging in probability), required to have continuous paths, and the cross variation is the published `EthierKurtz.HasCrossVariation`. "Itô process" is read with its usual conventions: the coefficients are progressively measurable and almost every drift path is locally integrable, so no Lebesgue integral in an equation takes a default value off a null set. The pathwise square-integrability of the Itô integrands is required for every $\omega$, as the published Itô-integral relation does. The uniform distance is $[0,\infty]$-valued, so unbounded paths are at infinite distance rather than at the default value $0$. The sums use `Finset.Icc 1 n`, the paper's $\sum_{m=1}^n$. The diffusion and covariation coefficients of Theorem A.3 are set to $0$ after the horizon $T$, where $F$ is not constrained; no statement reads them there. On a time where $\sigma_s=0$, the covariation density is $0/0$, which Lean evaluates to $0$.
-- source:
--   Muhle-Karbe, Wang & Webster, Stochastic liquidity as a proxy for nonlinear price impact, SSRN 4286108 (version of November 2, 2023), p. 3 (Notation), p. 5 (order flow), p. 24 (Assumption A.1), p. 25 (Assumption A.2, Theorem A.3)

import Mathlib
import Definitions.Def_EthierKurtz_HasBrownianItoIntegral
import Definitions.Def_EthierKurtz_HasCadlagPaths
import Definitions.Def_EthierKurtz_HasCrossVariation

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace PropagatorLimit.Scaling

/-! ### Brownian motions with respect to a filtration -/

/-- `W` is a Brownian motion with respect to the filtration `𝓕` (p. 5, p. 24): its laws are
those of a standard Brownian motion, every path is continuous (a version choice), it is
`𝓕`-adapted, and its increments after `s` are independent of `𝓕 s`. -/
def IsFBrownian {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) : Prop :=
  IsBrownianReal W P ∧ (∀ ω, Continuous (W · ω)) ∧ Adapted 𝓕 W ∧
  ∀ s : ℝ≥0, Indep
    (⨆ u : ℝ≥0, MeasurableSpace.comap (fun ω => W (s + u) ω - W s ω) inferInstance)
    (𝓕 s) P

/-- The pair `(W, W^⊥)` of p. 5 and Assumption A.1, p. 24: two `𝓕`-Brownian motions that are
independent of each other, whose joint increments after `s` are independent of `𝓕 s`. -/
def IsBrownianPair {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (𝓕 : Filtration ℝ≥0 mΩ) (W Wperp : ℝ≥0 → Ω → ℝ) : Prop :=
  IsFBrownian P 𝓕 W ∧ IsFBrownian P 𝓕 Wperp ∧
  Indep (⨆ t : ℝ≥0, MeasurableSpace.comap (W t) inferInstance)
    (⨆ t : ℝ≥0, MeasurableSpace.comap (Wperp t) inferInstance) P ∧
  ∀ s : ℝ≥0, Indep
    ((⨆ u : ℝ≥0, MeasurableSpace.comap (fun ω => W (s + u) ω - W s ω) inferInstance) ⊔
      ⨆ u : ℝ≥0, MeasurableSpace.comap (fun ω => Wperp (s + u) ω - Wperp s ω) inferInstance)
    (𝓕 s) P

/-- A process is locally bounded: along a localizing sequence of `𝓕`-stopping times, every
stopped process is uniformly bounded. -/
def IsLocBdd {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (𝓕 : Filtration ℝ≥0 mΩ) (X : ℝ≥0 → Ω → ℝ) : Prop :=
  Locally (fun Y : ℝ≥0 → Ω → ℝ => ∃ C : ℝ, ∀ t ω, |Y t ω| ≤ C) 𝓕 X P

/-! ### Assumption A.1: an Itô process with Itô volatility -/

/-- The data of Assumption A.1, p. 24: `dX = b dt + σ dW`,
`dσ = b̃ dt + σ̃ dW + a dW^⊥`. Field `bt` is `b̃` and field `σt` is `σ̃`. -/
structure ItoSV (Ω : Type) where
  X : ℝ≥0 → Ω → ℝ
  b : ℝ≥0 → Ω → ℝ
  σ : ℝ≥0 → Ω → ℝ
  bt : ℝ≥0 → Ω → ℝ
  σt : ℝ≥0 → Ω → ℝ
  a : ℝ≥0 → Ω → ℝ

/-- Assumption A.1, p. 24. All processes are adapted, the coefficients are progressively
measurable, `b, b̃, σ̃, a` are locally bounded, almost every drift path is locally integrable, and
there are continuous Itô integrals `J_X = ∫ σ dW`, `J_σ = ∫ σ̃ dW`, `J_a = ∫ a dW^⊥` such that
almost surely, for all `t`,
`X_t = X_0 + ∫₀ᵗ b + J_X(t)` and `σ_t = σ_0 + ∫₀ᵗ b̃ + J_σ(t) + J_a(t)`. -/
def IsItoSV {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (𝓕 : Filtration ℝ≥0 mΩ) (W Wperp : ℝ≥0 → Ω → ℝ) (S : ItoSV Ω) : Prop :=
  Adapted 𝓕 S.X ∧ Adapted 𝓕 S.σ ∧
  IsProgressive 𝓕 S.b ∧ IsProgressive 𝓕 S.σ ∧ IsProgressive 𝓕 S.bt ∧
  IsProgressive 𝓕 S.σt ∧ IsProgressive 𝓕 S.a ∧
  IsLocBdd P 𝓕 S.b ∧ IsLocBdd P 𝓕 S.bt ∧ IsLocBdd P 𝓕 S.σt ∧ IsLocBdd P 𝓕 S.a ∧
  (∀ᵐ ω ∂P, ∀ t : ℝ≥0, IntervalIntegrable (fun u : ℝ => S.b u.toNNReal ω) volume 0 t.val ∧
    IntervalIntegrable (fun u : ℝ => S.bt u.toNNReal ω) volume 0 t.val) ∧
  ∃ JX Jσ Ja : ℝ≥0 → Ω → ℝ,
    (∀ ω, Continuous (JX · ω)) ∧ (∀ ω, Continuous (Jσ · ω)) ∧ (∀ ω, Continuous (Ja · ω)) ∧
    EthierKurtz.HasBrownianItoIntegral P (fun t => 𝓕 t) W S.σ JX ∧
    EthierKurtz.HasBrownianItoIntegral P (fun t => 𝓕 t) W S.σt Jσ ∧
    EthierKurtz.HasBrownianItoIntegral P (fun t => 𝓕 t) Wperp S.a Ja ∧
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      S.X t ω = S.X 0 ω + (∫ u in (0 : ℝ)..t.val, S.b u.toNNReal ω) + JX t ω ∧
      S.σ t ω = S.σ 0 ω + (∫ u in (0 : ℝ)..t.val, S.bt u.toNNReal ω) + Jσ t ω + Ja t ω

/-! ### The order flow of p. 5 -/

/-- The order flow of p. 5: `dF = µ dt + v dW`, `dv = a dt + η dW + b dW^⊥`.
These letters are p. 5's, not Assumption A.1's (see `Flow.toItoSV`). -/
structure Flow (Ω : Type) where
  F : ℝ≥0 → Ω → ℝ
  mu : ℝ≥0 → Ω → ℝ
  v : ℝ≥0 → Ω → ℝ
  a : ℝ≥0 → Ω → ℝ
  eta : ℝ≥0 → Ω → ℝ
  b : ℝ≥0 → Ω → ℝ

/-- The name map from p. 5 to Assumption A.1: `(F, µ, v, a, η, b) ↦ (X, b, σ, b̃, σ̃, a)`. -/
def Flow.toItoSV {Ω : Type} (fl : Flow Ω) : ItoSV Ω where
  X := fl.F
  b := fl.mu
  σ := fl.v
  bt := fl.a
  σt := fl.eta
  a := fl.b

/-- The standing assumptions of p. 5 on the order flow on `[0, T]`: the Itô dynamics of
Assumption A.1 under the name map, `µ, a, η, b` càdlàg, the volatility `v` positive, and
`F ∈ L²`, i.e. `E[∫₀ᵀ |F_t|² dt] < ∞` (p. 3). -/
def IsFlow {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (𝓕 : Filtration ℝ≥0 mΩ) (W Wperp : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (fl : Flow Ω) : Prop :=
  IsItoSV P 𝓕 W Wperp fl.toItoSV ∧
  EthierKurtz.HasCadlagPaths fl.mu ∧ EthierKurtz.HasCadlagPaths fl.a ∧
  EthierKurtz.HasCadlagPaths fl.eta ∧ EthierKurtz.HasCadlagPaths fl.b ∧
  (∀ t ω, 0 < fl.v t ω) ∧
  (∫⁻ ω, ∫⁻ u in Set.Icc (0 : ℝ) T, ENNReal.ofReal (fl.F u.toNNReal ω ^ 2) ∂volume ∂P) < ⊤

/-! ### The time grid -/

/-- The mesh width `Δt^N = T / N` (p. 3). -/
noncomputable def dt (T : ℝ≥0) (N : ℕ) : ℝ := (T : ℝ) / N

/-- The grid point `t^N_n = n Δt^N` (p. 3). -/
noncomputable def grid (T : ℝ≥0) (N n : ℕ) : ℝ≥0 := (n : ℝ≥0) * T / N

/-- The increment `ΔX^N_n = X_{t^N_n} − X_{t^N_{n−1}}` (p. 3), used for `n ≥ 1`
(at `n = 0` the natural-number subtraction gives `0`, a value no statement reads). -/
noncomputable def incr {Ω : Type} (T : ℝ≥0) (N : ℕ) (X : ℝ≥0 → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  X (grid T N n) ω - X (grid T N (n - 1)) ω

/-- The number of grid steps up to time `t`: `⌈t / Δt^N⌉`, capped at `N`
(Theorem A.3's `⌈Nt⌉`, read for a horizon `T`). -/
noncomputable def nsteps (T : ℝ≥0) (N : ℕ) (t : ℝ≥0) : ℕ :=
  min N ⌈(t : ℝ) / dt T N⌉₊

/-! ### Gaussian expectation -/

/-- `Ẽ[f(Z)]` for a standard normal `Z`. -/
noncomputable def gaussExp (f : ℝ → ℝ) : ℝ := ∫ z, f z ∂(gaussianReal 0 1)

/-! ### Assumption A.2 -/

/-- Assumption A.2, p. 25, for `F : [0, T] × ℝ → ℝ`, a bounding function `G` (the page's `g`)
of at most linear growth and a constant `γ > 1/2`. Only `t ∈ [0, T]` is constrained. -/
def IsA2 (T : ℝ≥0) (F : ℝ≥0 → ℝ → ℝ) (G : ℝ → ℝ) (γ : ℝ) : Prop :=
  (∃ C : ℝ, ∀ x, |G x| ≤ C * (1 + |x|)) ∧ 1 / 2 < γ ∧
  (∀ t ≤ T, ∀ x, F t x = -F t (-x)) ∧
  (∀ t ≤ T, ContDiff ℝ 1 (F t)) ∧
  (∀ t ≤ T, ∀ x, |F t x| + |deriv (F t) x| ≤ G x) ∧
  (∀ t ≤ T, ∀ s ≤ T, ∀ x, |F t x - F s x| ≤ G x * |(t : ℝ) - s| ^ γ)

/-! ### The ingredients of Theorem A.3 -/

/-- The normalized sum of Theorem A.3, p. 25, at time `t`:
`√Δt^N Σ_{n=1}^{⌈t/Δt^N⌉ ∧ N} F(t^N_{n−1}, ΔX^N_n / √Δt^N)`. -/
noncomputable def stepSum {Ω : Type} (T : ℝ≥0) (N : ℕ) (F : ℝ≥0 → ℝ → ℝ)
    (X : ℝ≥0 → Ω → ℝ) (ω : Ω) (t : ℝ≥0) : ℝ :=
  Real.sqrt (dt T N) * ∑ n ∈ Finset.Icc 1 (nsteps T N t),
    F (grid T N (n - 1)) (incr T N X n ω / Real.sqrt (dt T N))

/-- The drift density of the limit in Theorem A.3 at time `s`, for drift `b_s`, volatility
`σ_s` and vol-of-vol `σ̃_s`: `b_s Ẽ[∂ₓF(s, σ_s Z)] + (σ̃_s/2) Ẽ[(Z² − 1) ∂ₓF(s, σ_s Z)]`. -/
noncomputable def driftA3 (F : ℝ≥0 → ℝ → ℝ) (s : ℝ≥0) (b σ σt : ℝ) : ℝ :=
  b * gaussExp (fun z => deriv (F s) (σ * z)) +
    σt / 2 * gaussExp (fun z => (z ^ 2 - 1) * deriv (F s) (σ * z))

/-- The diffusion coefficient `√(Ẽ[F²(s, σ_s Z)])` of Theorem A.3 for `s ≤ T`, and `0` after
the horizon `T` (where `F` is not constrained). -/
noncomputable def volA3 (T : ℝ≥0) (F : ℝ≥0 → ℝ → ℝ) (s : ℝ≥0) (σ : ℝ) : ℝ :=
  if s ≤ T then Real.sqrt (gaussExp (fun z => F s (σ * z) ^ 2)) else 0

/-- The covariation density `Ẽ[Z F(s, σ_s Z)] / √(Ẽ[F²(s, σ_s Z)])` of `[W, W′]` in
Theorem A.3 for `s ≤ T`, and `0` after the horizon `T`. -/
noncomputable def corrA3 (T : ℝ≥0) (F : ℝ≥0 → ℝ → ℝ) (s : ℝ≥0) (σ : ℝ) : ℝ :=
  if s ≤ T then gaussExp (fun z => z * F s (σ * z)) /
    Real.sqrt (gaussExp (fun z => F s (σ * z) ^ 2)) else 0

/-! ### Very good extensions and stable convergence in law -/

/-- An extension of the filtered probability space `(Ω, 𝓕, P)`: a filtered space
`(Ω', 𝓖, P')` with a projection `π : Ω' → Ω`. -/
structure Extension (Ω : Type) [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (𝓕 : Filtration ℝ≥0 mΩ) where
  Ω' : Type
  m' : MeasurableSpace Ω'
  P' : Measure Ω'
  π : Ω' → Ω
  𝓖 : Filtration ℝ≥0 m'

instance {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 ‹_›}
    (E : Extension Ω P 𝓕) : MeasurableSpace E.Ω' := E.m'

/-- A very good extension (Jacod–Protter): `P'` is a probability measure whose image under
`π` is `P`, `𝓖_t` contains `π⁻¹(𝓕_t)`, and for every bounded `𝓕`-measurable `Y`,
`E'[Y ∘ π | 𝓖_t] = E[Y | 𝓕_t] ∘ π` almost surely (so every `𝓕`-martingale stays a
`𝓖`-martingale). -/
def Extension.IsVeryGood {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (E : Extension Ω P 𝓕) : Prop :=
  IsProbabilityMeasure E.P' ∧ Measurable E.π ∧ E.P'.map E.π = P ∧
  (∀ t, MeasurableSpace.comap E.π (𝓕 t) ≤ E.𝓖 t) ∧
  ∀ Y : Ω → ℝ, Measurable Y → (∃ C : ℝ, ∀ ω, |Y ω| ≤ C) → ∀ t : ℝ≥0,
    E.P'[Y ∘ E.π | E.𝓖 t] =ᵐ[E.P'] (P[Y | 𝓕 t]) ∘ E.π

/-- The uniform distance on `[0, T]`, valued in `[0, ∞]`. -/
noncomputable def supEDist (T : ℝ≥0) (x y : ℝ≥0 → ℝ) : ℝ≥0∞ :=
  ⨆ t ∈ Set.Icc 0 T, edist (x t) (y t)

/-- Test functionals on paths: bounded, and Lipschitz for the uniform distance on `[0, T]`. -/
def IsTestFunctional (T : ℝ≥0) (f : (ℝ≥0 → ℝ) → ℝ) : Prop :=
  (∃ C : ℝ, ∀ x, |f x| ≤ C) ∧ ∃ L : ℝ≥0, ∀ x y, edist (f x) (f y) ≤ L * supEDist T x y

/-- Stable convergence in law on `[0, T]` of processes `X^N` on `Ω` to a continuous-path
process `X` on an extension `E`: for every bounded measurable `Y` on `Ω` and every test
functional `f`, both expectations are of integrable variables and
`E[Y f(X^N)] → E'[(Y ∘ π) f(X)]`. -/
def StablyConverges {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    {𝓕 : Filtration ℝ≥0 mΩ} (T : ℝ≥0) (XN : ℕ → Ω → ℝ≥0 → ℝ) (E : Extension Ω P 𝓕)
    (X : E.Ω' → ℝ≥0 → ℝ) : Prop :=
  ∀ Y : Ω → ℝ, Measurable Y → (∃ C : ℝ, ∀ ω, |Y ω| ≤ C) →
    ∀ f : (ℝ≥0 → ℝ) → ℝ, IsTestFunctional T f →
      (∀ N, Integrable (fun ω => Y ω * f (XN N ω)) P) ∧
      Integrable (fun ω' => Y (E.π ω') * f (X ω')) E.P' ∧
      Tendsto (fun N => ∫ ω, Y ω * f (XN N ω) ∂P) atTop
        (𝓝 (∫ ω', Y (E.π ω') * f (X ω') ∂E.P'))

end PropagatorLimit.Scaling


