-- Prove2me | Definitions.Def_HedgePSNV_Supplement_GenModel
-- name    : HedgePSNV_Supplement_GenModel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T03:52:47.050796+00:00
-- url     : https://prove2.me/theorems/58ff5aab-0639-420e-b19b-8d6693e89145
-- title:
--   The general operational model of §EC.5: $J$ factors $A_T=C_T+\tilde\Sigma\tilde B_T$, $K$-dimensional noise, payoff $H_T(q,a)$
-- statement:
--   **Data.** A horizon $T>0$, an initial asset price $x_0>0$, a $J\times K$ matrix $\tilde\Sigma$, and a payoff $H_T(q,a)$ Borel in $a$; a probability space $(\Omega,\mathbb P)$ with a Brownian motion $B$, a $K$-dimensional Brownian motion $\tilde B$, filtrations $\mathcal F,\mathcal G$, the asset price $X$ with drift $\mu$ and volatility $\sigma$ (8), and the $J$-dimensional asset-driven component $C$.
--
--   **Derived objects.** The operational factors
--   $$
--   A_T=C_T+\tilde\Sigma\tilde B_T\qquad(\text{EC.5.1}),
--   $$
--   the market price of risk $\eta=\mu/\sigma$, the density $Z_t=\exp(-\int_0^t\eta\,dB-\tfrac12\int_0^t\eta^2ds)$ and $d\mathbb P^M/d\mathbb P=Z_T$ (12), $V_t(q)=\mathbb E^M[H_T(q,A_T)\mid\mathcal F_t]$ (EC.10.1), $V_0(q)=\mathbb E^M[H_T(q,A_T)]$, $Z^M_t=\mathbb E^M(Z_T\mid\mathcal F_t)$, gains processes $\int\theta\,dX$ and $d\tilde B$-integrals $\int\delta\cdot d\tilde B=\sum_k\int\delta_k\,d\tilde B_k$.
--
--   **Standing model.** $\mathbb P$ is a probability measure; $B$ and the $K$ coordinates of $\tilde B$ are independent standard Brownian motions; $\mathcal F,\mathcal G$ are the augmented natural filtrations of $(B,\tilde B)$ and $B$; $\mu,\sigma$ continuous and $\mathcal G$-adapted, $\sigma>0$; $X$ continuous, $\mathcal G$-adapted, $X_0=x_0$, solving (8); $(X,\mu,\sigma)$ Markovian under $\mathbb P$ and $(X,\sigma)$ under $\mathbb P^M$; $C$ is $\mathcal G$-adapted with $C_v-C_u$ measurable with respect to $\sigma\{X_t:u\le t\le v\}$. Also: $H_T(q,A_T)\in L^2(\mathbb P)$ for every $q\ge0$, Assumption 4 ($\int_0^T\mathbb E[(X_t\sigma_t)^2]dt<\infty$) and Assumption 5 ($Z$ a square-integrable $\mathbb P$-martingale on $[0,T]$).
--
--   This is the setting of Theorems EC.1–EC.2 and Lemma EC.13.
--
--   **Formalization Note** The asset part mirrors the published `HedgePSNV.Model` field by field (“the asset price model is the same”, p.ec61). §EC.5 states no continuity and no $C_0=0$ for $C$, so none is imposed. The printed “$C_t$ … is a $K$-dimensional stochastic process” is read as $J$-dimensional, as $A_T\in\mathbb R^J$ requires.
-- source:
--   Wang–Yao–Zhang, How Does Risk Hedging Impact Operations? Insights from a Price-Setting Newsvendor Model, arXiv:2201.01026v4, (EC.5.1)–(EC.5.2), pp.ec14–ec15; (EC.10.1), p.ec59; §3.1 (8), (11), (12), pp.11–12

import Mathlib
import Definitions.Def_EthierKurtz_HasBrownianItoIntegral
import Definitions.Def_HedgePSNV_IsMartingaleOn
import Definitions.Def_HedgePSNV_IsMarkovWrt
import Definitions.Def_HedgePSNV_IsAugmentedNaturalFiltration

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace HedgePSNV.Supplement

open HedgePSNV

/-- The primitive data of the general operational model of §EC.5, arXiv:2201.01026v4,
pp.ec14–ec15: the horizon `T > 0`, the initial asset price `x₀ > 0`, the `J × K` noise loading
matrix `Σ̃ = [σ̃ⱼₖ]` (`Sig`) of (EC.5.1), and the operational payoff `H_T(q, a)` of a decision
`q ∈ ℝⁿ` (`q ≥ 0`) at the level `a ∈ ℝᴶ` of the stochastic operational factors.

**Formalization Note** `H` is Borel measurable in `a` for each `q`, so that `H_T(q, A_T)` is a
random variable (the paper takes its expectation and variance). `x₀ > 0` is the positivity of
an asset price, as in the published `HedgePSNV.Params`. -/
structure GenParams (n J K : ℕ) where
  T : ℝ≥0
  x₀ : ℝ
  Sig : Matrix (Fin J) (Fin K) ℝ
  H : (Fin n → ℝ) → (Fin J → ℝ) → ℝ
  hT : 0 < T
  hx₀ : 0 < x₀
  hH : ∀ q : Fin n → ℝ, Measurable (H q)

/-- The data of the general model of §EC.5, arXiv:2201.01026v4, pp.ec14–ec15: the asset model
of §3.1 (a probability space `(Ω, P)`, the Brownian motion `B` driving the asset price `X` with
drift `µ` and volatility `σ` in (8), the filtrations `F` and `G`, the Itô integral `Jx` of
`X_uσ_u dB_u` in (8) and the Itô integral `I` of `η dB` in (12)), a `K`-dimensional Brownian
motion `B̃` (`Bt`), and the `J`-dimensional asset-driven component `C` of the operational
factors `A_T = C_T + Σ̃B̃_T` (EC.5.1). The hypotheses are `GenModel.Standing`.

**Formalization Note** Processes are indexed by `ℝ≥0` and only `t ∈ [0, T]` matters, as in the
published `HedgePSNV.Model`, whose fields this structure mirrors with `B̃` and `C` vector
valued. -/
structure GenModel {n J K : ℕ} (g : GenParams n J K) (Ω : Type*) [m : MeasurableSpace Ω] where
  P : Measure Ω
  B : ℝ≥0 → Ω → ℝ
  Bt : ℝ≥0 → Ω → (Fin K → ℝ)
  F : Filtration ℝ≥0 m
  G : Filtration ℝ≥0 m
  X : ℝ≥0 → Ω → ℝ
  μ : ℝ≥0 → Ω → ℝ
  σ : ℝ≥0 → Ω → ℝ
  C : ℝ≥0 → Ω → (Fin J → ℝ)
  Jx : ℝ≥0 → Ω → ℝ
  I : ℝ≥0 → Ω → ℝ

namespace GenModel

variable {n J K : ℕ} {g : GenParams n J K} {Ω : Type*} [m : MeasurableSpace Ω]

/-- The stochastic operational factors `A_T = C_T + Σ̃B̃_T`, arXiv:2201.01026v4, (EC.5.1),
p.ec14. -/
def AT (M : GenModel g Ω) (ω : Ω) : Fin J → ℝ := M.C g.T ω + g.Sig.mulVec (M.Bt g.T ω)

/-- The market price of risk `η_t = µ_t/σ_t`, arXiv:2201.01026v4, (11), p.12. -/
noncomputable def η (M : GenModel g Ω) (t : ℝ≥0) (ω : Ω) : ℝ := M.μ t ω / M.σ t ω

/-- `Z_t = exp(−∫_0^t η_s dB_s − ½∫_0^t η_s² ds)`, arXiv:2201.01026v4, (12), p.12, with the
Itô integral `∫_0^t η dB = I_t`. -/
noncomputable def Z (M : GenModel g Ω) (t : ℝ≥0) (ω : Ω) : ℝ :=
  Real.exp (-(M.I t ω) - (1 / 2) * ∫ u in (0 : ℝ)..(t : ℝ), M.η u.toNNReal ω ^ 2)

/-- The risk-neutral measure `P^M`, `dP^M/dP := Z_T`, arXiv:2201.01026v4, (12), p.12. -/
noncomputable def PM (M : GenModel g Ω) : Measure Ω :=
  M.P.withDensity (fun ω => ENNReal.ofReal (M.Z g.T ω))

/-- The operational payoff `H_T(q, A_T)` of the decision `q` as a random variable,
arXiv:2201.01026v4, p.ec14. -/
def Hq (M : GenModel g Ω) (q : Fin n → ℝ) (ω : Ω) : ℝ := g.H q (M.AT ω)

/-- `V_0(q) = E^M[H_T(q, A_T)]`, arXiv:2201.01026v4, (EC.10.2) and (EC.10.9), pp.ec59, ec63. -/
noncomputable def V0 (M : GenModel g Ω) (q : Fin n → ℝ) : ℝ := ∫ ω, M.Hq q ω ∂M.PM

/-- The projected operational payoff `V_t(q) := E^M[H_T(q, A_T) | F_t]`, arXiv:2201.01026v4,
(EC.10.1), p.ec59. -/
noncomputable def V (M : GenModel g Ω) (q : Fin n → ℝ) (t : ℝ≥0) : Ω → ℝ :=
  condExp (M.F t) M.PM (M.Hq q)

/-- `Z^M_t := E^M(Z_T | F_t)`, arXiv:2201.01026v4, (16), p.15. -/
noncomputable def ZM (M : GenModel g Ω) (t : ℝ≥0) : Ω → ℝ :=
  condExp (M.F t) M.PM (M.Z g.T)

/-- The constant `Z^M_0 = E^M(Z_T)`, arXiv:2201.01026v4, (16) p.15 and (EC.10.5) p.ec59. -/
noncomputable def ZM0 (M : GenModel g Ω) : ℝ := ∫ ω, M.Z g.T ω ∂M.PM

/-- `χ` is the gains process `χ_t = ∫_0^t θ_s dX_s` on `[0, T]`, arXiv:2201.01026v4, (EC.5.3)
p.ec15 and (EC.7.15) p.ec29: almost surely for every `t ≤ T`,
`χ_t = ∫_0^t θ_uX_uµ_u du + K_t`, where `K` is the Itô integral `∫_0^· θ_uX_uσ_u dB_u`.

**Formalization Note** Identical to the published `HedgePSNV.Model.IsXGains` (the asset model
is the same): the Itô integral is `EthierKurtz.HasBrownianItoIntegral` with the integrand cut
off after `T`, and the drift integral is a pathwise interval integral. -/
def IsXGains (M : GenModel g Ω) (θ χ : ℝ≥0 → Ω → ℝ) : Prop :=
  (∀ ω, ∀ t : ℝ≥0, t ≤ g.T → IntervalIntegrable
      (fun u : ℝ => θ u.toNNReal ω * M.X u.toNNReal ω * M.μ u.toNNReal ω) volume 0 (t : ℝ)) ∧
  ∃ Kp : ℝ≥0 → Ω → ℝ,
    EthierKurtz.HasBrownianItoIntegral M.P (fun t => M.F t) M.B
      (fun t ω => if t ≤ g.T then θ t ω * M.X t ω * M.σ t ω else 0) Kp ∧
    ∀ᵐ ω ∂M.P, ∀ t : ℝ≥0, t ≤ g.T →
      χ t ω = (∫ u in (0 : ℝ)..(t : ℝ),
        θ u.toNNReal ω * M.X u.toNNReal ω * M.μ u.toNNReal ω) + Kp t ω

/-- `L` is the Itô integral `∫_0^· δ_s · dB̃_s = Σ_k ∫_0^· δ_{s,k} dB̃_{s,k}` on `[0, T]` of a
`K`-vector integrand `δ` against the `K`-dimensional Brownian motion `B̃` (the `dB̃` term of
(EC.10.2), arXiv:2201.01026v4, p.ec59): `L` is the sum of `K` scalar Itô integrals, each given
by `EthierKurtz.HasBrownianItoIntegral` with the integrand cut off after `T`. -/
def IsBtIntegral (M : GenModel g Ω) (δ : ℝ≥0 → Ω → (Fin K → ℝ)) (L : ℝ≥0 → Ω → ℝ) : Prop :=
  ∃ Lk : Fin K → ℝ≥0 → Ω → ℝ,
    (∀ k : Fin K, EthierKurtz.HasBrownianItoIntegral M.P (fun t => M.F t)
      (fun t ω => M.Bt t ω k) (fun t ω => if t ≤ g.T then δ t ω k else 0) (Lk k)) ∧
    ∀ t ω, L t ω = ∑ k : Fin K, Lk k t ω

/-- The standing model of §EC.5, arXiv:2201.01026v4, pp.ec14–ec15, which keeps the asset model
of §3.1 (pp.11–12, with footnote 4):
1. `P` is a probability measure; `B` is a standard Brownian motion; `B̃ = (B̃_1, …, B̃_K)` is a
   `K`-dimensional standard Brownian motion (independent standard Brownian coordinates),
   independent of `B` (as path-valued random variables);
2. `F` and `G` are the `P`-augmented natural filtrations of `(B, B̃)` and of `B`;
3. `µ`, `σ` are continuous `G`-adapted processes with `σ > 0`;
4. `X` is a continuous `G`-adapted process with `X_0 = x₀` solving (8);
5. `(X, µ, σ)` is Markovian under `P` (with respect to `F`);
6. `C` is `G`-adapted (each component `C_j` is adapted to the filtration generated by `B`) and,
   for `u ≤ v ≤ T`, `C_v − C_u` is measurable with respect to `σ{X_t : u ≤ t ≤ v}`;
7. `I` is the Itô integral `∫_0^· η dB` entering `Z` in (12), in a `G`-adapted version;
8. `(X, σ)` is Markovian under `P^M` (with respect to `F`).

**Formalization Note** Items 1–5, 7, 8 are the published `HedgePSNV.Model.Standing` verbatim
(the paper: "the asset price model is the same", p.ec61); item 6 is the §EC.5 hypothesis on
`C` (p.ec14), which states no continuity and no `C_0 = 0`, so none is imposed. -/
structure Standing (M : GenModel g Ω) : Prop where
  prob : IsProbabilityMeasure M.P
  brownB : IsBrownianReal M.B M.P
  brownBt : ∀ k : Fin K, IsBrownianReal (fun t ω => M.Bt t ω k) M.P
  indepBt : iIndepFun (fun (k : Fin K) ω (t : ℝ≥0) => M.Bt t ω k) M.P
  indep : IndepFun (fun ω t => M.B t ω) (fun ω t => M.Bt t ω) M.P
  filtF : IsAugmentedNaturalFiltration M.P (fun t ω => (M.B t ω, M.Bt t ω)) M.F
  filtG : IsAugmentedNaturalFiltration M.P M.B M.G
  μ_cont : ∀ ω, Continuous (fun t => M.μ t ω)
  σ_cont : ∀ ω, Continuous (fun t => M.σ t ω)
  μ_adapted : StronglyAdapted M.G M.μ
  σ_adapted : StronglyAdapted M.G M.σ
  σ_pos : ∀ t ω, 0 < M.σ t ω
  X_cont : ∀ ω, Continuous (fun t => M.X t ω)
  X_adapted : StronglyAdapted M.G M.X
  X_zero : ∀ ω, M.X 0 ω = g.x₀
  X_ito : EthierKurtz.HasBrownianItoIntegral M.P (fun t => M.F t) M.B
    (fun t ω => M.X t ω * M.σ t ω) M.Jx
  X_sde : ∀ᵐ ω ∂M.P, ∀ t : ℝ≥0, t ≤ g.T →
    M.X t ω = g.x₀ + (∫ u in (0 : ℝ)..(t : ℝ), M.X u.toNNReal ω * M.μ u.toNNReal ω) + M.Jx t ω
  markovP : IsMarkovWrt M.P M.F g.T (fun t ω => (M.X t ω, M.μ t ω, M.σ t ω))
  C_adapted : StronglyAdapted M.G M.C
  C_incr : ∀ u v : ℝ≥0, u ≤ v → v ≤ g.T →
    Measurable[⨆ t : ℝ≥0, ⨆ (_ : t ∈ Set.Icc u v), MeasurableSpace.comap (M.X t) inferInstance]
      (fun ω => M.C v ω - M.C u ω)
  I_ito : EthierKurtz.HasBrownianItoIntegral M.P (fun t => M.F t) M.B M.η M.I
  I_adapted : StronglyAdapted M.G M.I
  markovPM : IsMarkovWrt M.PM M.F g.T (fun t ω => (M.X t ω, M.σ t ω))

/-- Square integrability of the operational payoff under `P`: `H_T(q, A_T) ∈ L²(P)` for every
decision `q ≥ 0`.

**Formalization Note** Not printed: the mean–variance problems (EC.5.3)–(EC.5.4) presuppose
`Var[H_T(q, A_T)] < ∞`; this is the general-payoff analogue of the published
`HedgePSNV.Model.NegPartL2`. -/
def PayoffL2 (M : GenModel g Ω) : Prop :=
  ∀ q : Fin n → ℝ, 0 ≤ q → MemLp (M.Hq q) 2 M.P

/-- Assumption 4, arXiv:2201.01026v4, p.11: `∫_0^T E[(X_tσ_t)²] dt < ∞`. -/
def Assumption4 (M : GenModel g Ω) : Prop :=
  ∫⁻ u in Set.Icc (0 : ℝ) (g.T : ℝ),
      ∫⁻ ω, ENNReal.ofReal ((M.X u.toNNReal ω * M.σ u.toNNReal ω) ^ 2) ∂M.P < ⊤

/-- Assumption 5, arXiv:2201.01026v4, p.12: `Z_t` is a square-integrable martingale over
`[0, T]` under `P` (with respect to `F`). -/
def Assumption5 (M : GenModel g Ω) : Prop :=
  IsMartingaleOn g.T M.F M.P M.Z ∧ ∀ t : ℝ≥0, t ≤ g.T → MemLp (M.Z t) 2 M.P

end GenModel

end HedgePSNV.Supplement


