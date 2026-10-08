-- Prove2me | Definitions.Def_JacodTodorov10_LLN_Model
-- name    : JacodTodorov10_LLN_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T01:17:46.653198+00:00
-- url     : https://prove2.me/theorems/565affd9-dc20-4a74-bd29-804e3276e373
-- title:
--   §2, §8.1 — the Itô semimartingale model (2.1)/(8.1), local boundedness, Assumptions (H-r) and (K-v)
-- statement:
--   This file fixes the model of Jacod and Todorov. The data are the observed process $X$ with drift $b$, volatility coefficient $\sigma$ and jump field $\delta(\omega,t,z)$; two Brownian motions $W,W'$; a Poisson random measure $\mu$ on $\mathbb R_+\times E$ with compensator $ds\otimes\lambda(dz)$; processes $Z,\overline Z$ and a function $\Sigma:\mathbb R^2\to\mathbb R$; and the coefficients $\widehat b,\widehat\sigma,\widehat\sigma',\widehat\delta$ of $Z$.
--
--   1. **Itô semimartingale representation.** $Y$ has the representation (2.1)/(8.1) with drift $\beta$, Brownian coefficients $s,s'$ and jump field $H$ if $Y$ is adapted with a.s. càdlàg paths, $\beta,s,s'$ are progressively measurable, $H$ is predictable, and for every $t$, almost surely,
--   $$Y_t = Y_0+\int_0^t\beta_u\,du+\int_0^t s_u\,dW_u+\int_0^t s'_u\,dW'_u+\int_0^t\!\!\int_E H(u,z)1_{\{|H(u,z)|\le1\}}(\mu-\nu)(du,dz)+\int_0^t\!\!\int_E H(u,z)1_{\{|H(u,z)|>1\}}\mu(du,dz).$$
--   2. **The model.** $(W,W')$ is a pair of independent $(\mathcal F_t)$-Brownian motions, $\mu$ is an $(\mathcal F_t)$-Poisson random measure, and $X$ has the representation (2.1), i.e. the above with $\beta=b$, $s=\sigma$, $s'=0$, $H=\delta$. The volatility is $c_t=\sigma_t^2$, with left limit $c_{t-}=(\sigma_{t-})^2$.
--   3. **Local boundedness.** $\Gamma$ is locally bounded if there are stopping times $\tau_k\uparrow\infty$ a.s. and constants $C_k$ with $|\Gamma_t|\le C_k$ for $t\le\tau_k$ on $\{\tau_k>0\}$.
--   4. **Assumption (H-$r$)**, $r\in[0,2]$: (a) $b$ is locally bounded; (b) $\sigma$ is càdlàg and neither $\sigma_t$ nor $\sigma_{t-}$ vanishes; (c) $|\delta(\omega,t,z)|\le\Gamma_t(\omega)\gamma(z)$ for a locally bounded $\Gamma$ and a measurable $\gamma\ge0$ with $\int_E(\gamma(z)^r\wedge1)\,\lambda(dz)<\infty$.
--   5. **Assumption (K-$v$)**, $v\in(0,1]$: $\sigma_t=\Sigma(Z_t,\overline Z_t)$ with $\Sigma$ of class $C^1$ and $Z,\overline Z$ adapted, where (a) $Z$ has the representation (8.1) with coefficients $\widehat b,\widehat\sigma,\widehat\sigma',\widehat\delta$ driven by the same $W,W',\mu$; $\widehat b,\widehat\sigma,\widehat\sigma'$ are locally bounded; $\widehat\delta$ satisfies (H-2)(c) if $v\le1/2$ and (H-$1/v$)(c) if $v>1/2$; and if $v>1/2$ the continuous martingale part of $Z$ vanishes, $\widehat\sigma=\widehat\sigma'=0$; (b) for a locally bounded $\Gamma'$,
--   $$0<s\le1\ \Longrightarrow\ |\overline Z_{t+s}-\overline Z_t|\le\Gamma'_{t+s}\,s^v.\qquad(2.2)$$
--
--   These are the standing hypotheses of every result of the mission.
--
--   **Formalization Note** The Brownian integrals are the published `EthierKurtz.HasBrownianItoIntegral` (dyadic predictable step approximation, pathwise square-integrable integrand); the jump integrals are those of `JacodTodorov10.LLN.Noise`. The identity (2.1) holds a.s. for each $t$. The indicators in (2.1) are printed $1_{\{|\delta(t,z)|\le1\}}$ inside $\int_0^t\ldots(ds,dz)$; they are read as $\delta(s,z)$. The power $\gamma^r$ uses $0^r=0$ for all $r$, so $\gamma^0=1_{\{\gamma>0\}}$: (H-0) means finite jump activity. (H-$r$) is defined for $r\in[0,2]$ because (K-$v$) uses (H-2); the theorems add $r<2$. Path conditions, $\sigma=\Sigma(Z,\overline Z)$ and (2.2) hold almost surely. Following §8.1, $Z$ uses the same Poisson measure as $X$ and a second Brownian motion $W'$ independent of $W$ (the paper: "it is no restriction"); clause (b) of (H-·) is not imposed on $Z$, since for $v>1/2$ it contradicts $\widehat\sigma=\widehat\sigma'=0$, and only bounds on $\widehat\sigma,\widehat\sigma'$ are used.
-- source:
--   Jacod, Todorov, Do price and volatility jump together?, arXiv:1010.4990v1 (Ann. Appl. Probab. 20 (2010)), §2, pp. 3–4 ((2.1), Assumption (H-r), Assumption (K-v), (2.2)); §8.1, p. 24 ((8.1), (8.2))

import Mathlib
import Definitions.Def_EthierKurtz_HasBrownianItoIntegral
import Definitions.Def_JacodTodorov10_LLN_Noise

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace JacodTodorov10.LLN

/-- The data of the model of Jacod–Todorov, *Do price and volatility jump together?*,
arXiv:1010.4990v1, §2, pp. 3–4 and §8.1, p. 24, on a probability space `Ω` with auxiliary space `E`:
* the observed process `X`, its drift `b`, its volatility coefficient `σ` and its jump field
  `δ(ω, t, z)` of (2.1);
* the two Brownian motions `W`, `W'` and the atoms `N(ω) ⊆ ℝ₊ × E` of the Poisson random measure `μ`;
* the processes `Z`, `Z̄` and the `C¹` function `Σ` of Assumption (K-v), with `σ_t = Σ(Z_t, Z̄_t)`;
* the coefficients `b̂`, `σ̂`, `σ̂'`, `δ̂` of the representation (8.1) of `Z`. -/
structure Data (Ω E : Type*) where
  /-- the observed process `X` -/
  X : ℝ≥0 → Ω → ℝ
  /-- the drift `b` of `X` -/
  b : ℝ≥0 → Ω → ℝ
  /-- the volatility coefficient `σ` of `X` -/
  σ : ℝ≥0 → Ω → ℝ
  /-- the jump field `δ(ω, t, z)` of `X` -/
  δ : Ω → ℝ≥0 → E → ℝ
  /-- the Brownian motion `W` -/
  W : ℝ≥0 → Ω → ℝ
  /-- the second Brownian motion `W'` of (8.1) -/
  W' : ℝ≥0 → Ω → ℝ
  /-- the atoms of the Poisson random measure `μ` -/
  N : Ω → Set (ℝ≥0 × E)
  /-- the process `Z` of (K-v) -/
  Z : ℝ≥0 → Ω → ℝ
  /-- the process `Z̄` of (K-v) -/
  Zbar : ℝ≥0 → Ω → ℝ
  /-- the drift `b̂` of `Z` in (8.1) -/
  bhat : ℝ≥0 → Ω → ℝ
  /-- the coefficient `σ̂` of `dW` in (8.1) -/
  σhat : ℝ≥0 → Ω → ℝ
  /-- the coefficient `σ̂'` of `dW'` in (8.1) -/
  σhat' : ℝ≥0 → Ω → ℝ
  /-- the jump field `δ̂` of `Z` in (8.1) -/
  δhat : Ω → ℝ≥0 → E → ℝ
  /-- the `C¹` function `Σ` of (K-v) -/
  Sig : ℝ × ℝ → ℝ

/-- `Y` is an **Itô semimartingale with the representation (2.1)/(8.1)** (arXiv:1010.4990v1, §2,
p. 3 and §8.1, p. 24) driven by the Brownian motions `W`, `W'` and the Poisson random measure with
atoms `N`, with drift `β`, Brownian coefficients `s`, `s'` and jump field `H`:
`Y` has a.s. càdlàg paths and is adapted, `β`, `s`, `s'` are progressively measurable, `H` is
predictable, the big jumps (`|H| > 1`) up to time `t` are a.s. finitely many, and for every `t`, a.s.,
`Y_t = Y_0 + ∫_0^t β_u du + ∫_0^t s_u dW_u + ∫_0^t s'_u dW'_u
  + ∫_0^t ∫_E H 1_{|H| ≤ 1} (μ − ν)(du, dz) + ∫_0^t ∫_E H 1_{|H| > 1} μ(du, dz)`.

Formalization Note: the Brownian integrals are the published `EthierKurtz.HasBrownianItoIntegral`,
the compensated integral is `HasCompInt` and the big-jump integral is `bigSum`; the identity holds
a.s. for each fixed `t`, since the stochastic integrals are only defined up to null sets. The
indicators are written `1_{|H(s,z)| ≤ 1}`, reading the printed `δ(t, z)` inside `∫_0^t … (ds, dz)`
as `δ(s, z)`. For `X` itself (2.1) has no `dW'` term: it is this predicate with `s' = 0`. -/
def IsItoRep {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (P : Measure Ω) (lam : Measure E)
    (N : Ω → Set (ℝ≥0 × E)) (W W' : ℝ≥0 → Ω → ℝ) (Y β s s' : ℝ≥0 → Ω → ℝ)
    (H : Ω → ℝ≥0 → E → ℝ) : Prop :=
  (∀ᵐ ω ∂P, KurtzProtter91.Integrals.IsCadlag (fun t => Y t ω)) ∧ Adapted 𝓕 Y ∧
    IsStronglyProgressive 𝓕 β ∧ IsStronglyProgressive 𝓕 s ∧ IsStronglyProgressive 𝓕 s' ∧
    Measurable[(𝓕.predictable).prod ‹MeasurableSpace E›]
      (fun q : (ℝ≥0 × Ω) × E => H q.1.2 q.1.1 q.2) ∧
    (∀ t : ℝ≥0, ∀ᵐ ω ∂P, {p : ℝ≥0 × E | p ∈ N ω ∧ p.1 ≤ t ∧ 1 < |H ω p.1 p.2|}.Finite) ∧
    ∃ JW JW' Jμ : ℝ≥0 → Ω → ℝ,
      EthierKurtz.HasBrownianItoIntegral P (fun t => 𝓕 t) W s JW ∧
      EthierKurtz.HasBrownianItoIntegral P (fun t => 𝓕 t) W' s' JW' ∧
      HasCompInt P lam N (fun ω t z => if |H ω t z| ≤ 1 then H ω t z else 0) Jμ ∧
      ∀ t : ℝ≥0, ∀ᵐ ω ∂P,
        Y t ω = Y 0 ω + (∫ u in (0 : ℝ)..(t : ℝ), β u.toNNReal ω) + JW t ω + JW' t ω + Jμ t ω +
          bigSum N H t ω

/-- The standing model of arXiv:1010.4990v1, §2, p. 3 and §8.1, p. 24: `(W, W')` is a pair of
independent `(𝓕_t)`-Brownian motions, `μ` (atoms `N`) is an `(𝓕_t)`-Poisson random measure with
compensator `ds ⊗ λ(dz)`, and `X` has the representation (2.1) driven by `W` and `μ`. The
representation (8.1) of `Z` is part of Assumption (K-v), see `KAssume`. -/
def IsModel {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (P : Measure Ω) (lam : Measure E)
    (M : Data Ω E) : Prop :=
  IsFBrownianPair 𝓕 P M.W M.W' ∧ IsFPoisson 𝓕 P lam M.N ∧
    IsItoRep 𝓕 P lam M.N M.W M.W' M.X M.b M.σ (fun _ _ => 0) M.δ

/-- A process `Γ` is **locally bounded**: there are `(𝓕_t)`-stopping times `τ_k`, nondecreasing in
`k`, with `τ_k → ∞` a.s., and constants `C_k` such that `|Γ_t| ≤ C_k` whenever `0 < τ_k` and
`t ≤ τ_k` (used in (H-r)(a), (c) and (K-v)(b), arXiv:1010.4990v1, pp. 3–4). -/
def LocBdd {Ω : Type*} [MeasurableSpace Ω] (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (P : Measure Ω) (Γ : ℝ≥0 → Ω → ℝ) : Prop :=
  ∃ (τ : ℕ → Ω → WithTop ℝ≥0) (C : ℕ → ℝ),
    (∀ k, IsStoppingTime 𝓕 (τ k)) ∧ (∀ ω, Monotone (fun k => τ k ω)) ∧
    (∀ᵐ ω ∂P, ∀ T : ℝ≥0, ∃ k, (T : WithTop ℝ≥0) < τ k ω) ∧
    ∀ k ω (t : ℝ≥0), 0 < τ k ω → (t : WithTop ℝ≥0) ≤ τ k ω → |Γ t ω| ≤ C k

/-- The power `x^r` with the convention `0^r = 0` for every `r`, so that `γ(z)^0 = 1_{γ(z) > 0}`
(arXiv:1010.4990v1, p. 3: "When (H-0) holds, then the jumps of X have finite activity"). For
`x > 0` it is the real power `x ^ r`. -/
noncomputable def pow0 (x r : ℝ) : ℝ :=
  if x = 0 then 0 else x ^ r

/-- Clause (c) of Assumption (H-q) for a jump field `H` (arXiv:1010.4990v1, p. 3):
`|H(ω, t, z)| ≤ Γ_t(ω) γ(z)` for a locally bounded process `Γ` and a nonrandom measurable
`γ ≥ 0` with `∫_E (γ(z)^q ∧ 1) λ(dz) < ∞` (with `γ^0 = 1_{γ > 0}`, see `pow0`). -/
def JumpDom {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (P : Measure Ω) (lam : Measure E) (q : ℝ)
    (H : Ω → ℝ≥0 → E → ℝ) : Prop :=
  ∃ (Γ : ℝ≥0 → Ω → ℝ) (γ : E → ℝ), LocBdd 𝓕 P Γ ∧ Measurable γ ∧ (∀ z, 0 ≤ γ z) ∧
    (∀ ω t z, |H ω t z| ≤ Γ t ω * γ z) ∧
    ∫⁻ z, ENNReal.ofReal (min (pow0 (γ z) q) 1) ∂lam < ⊤

/-- **Assumption (H-r)** (arXiv:1010.4990v1, §2, p. 3), for `r ∈ [0, 2]`:
(a) `b` is locally bounded; (b) `σ` is càdlàg and neither `σ_t` nor `σ_{t−}` vanishes;
(c) `|δ(ω, t, z)| ≤ Γ_t(ω) γ(z)` with `Γ` locally bounded and `∫_E (γ^r ∧ 1) dλ < ∞`.

Formalization Note: the page introduces (H-r) "below r ∈ [0, 2)", but Assumption (K-v) applies
(H-2) to `Z`, so the range `[0, 2]` is allowed here and the theorems add `r < 2`. The path
conditions of (b) hold almost surely. At `t = 0`, `σ_{0−} = σ_0`. -/
def HAssume {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (P : Measure Ω) (lam : Measure E) (r : ℝ)
    (M : Data Ω E) : Prop :=
  0 ≤ r ∧ r ≤ 2 ∧ LocBdd 𝓕 P M.b ∧
    (∀ᵐ ω ∂P, KurtzProtter91.Integrals.IsCadlag (fun t => M.σ t ω) ∧
      ∀ t : ℝ≥0, M.σ t ω ≠ 0 ∧ Function.leftLim (fun s => M.σ s ω) t ≠ 0) ∧
    JumpDom 𝓕 P lam r M.δ

/-- **Assumption (K-v)** (arXiv:1010.4990v1, §2, p. 4), for `v ∈ (0, 1]`: `σ_t = Σ(Z_t, Z̄_t)` with
`Σ` a `C¹` function on `ℝ²` and `Z`, `Z̄` adapted, where
(a) `Z` is an Itô semimartingale with the representation (8.1) (same `W`, `W'`, `μ` as in §8.1,
p. 24) whose drift `b̂` is locally bounded and whose jump field satisfies (H-2)(c) when `v ≤ 1/2`
and (H-1/v)(c) when `v > 1/2`, the coefficients `σ̂`, `σ̂'` are locally bounded, and when `v > 1/2`
the continuous martingale part vanishes, `σ̂ = σ̂' = 0`;
(b) `|Z̄_{t+s} − Z̄_t| ≤ Γ'_{t+s} s^v` for `0 < s ≤ 1`, with `Γ'` locally bounded (2.2).

Formalization Note: (8.1) writes `Z` with the same Poisson measure as `X` and a second Brownian
motion `W'` independent of `W`; the page says this is no restriction "up to augmenting" `μ`. Clause
(b) of (H-·) (σ̂ càdlàg and nonvanishing) is not imposed on `Z`: for `v > 1/2` it contradicts the
vanishing of the continuous martingale part, and §8 uses only bounds on `σ̂`, `σ̂'`. The identity
`σ = Σ(Z, Z̄)` and (2.2) hold almost surely. -/
def KAssume {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (P : Measure Ω) (lam : Measure E) (v : ℝ)
    (M : Data Ω E) : Prop :=
  0 < v ∧ v ≤ 1 ∧ ContDiff ℝ 1 M.Sig ∧ Adapted 𝓕 M.Z ∧ Adapted 𝓕 M.Zbar ∧
    (∀ᵐ ω ∂P, ∀ t : ℝ≥0, M.σ t ω = M.Sig (M.Z t ω, M.Zbar t ω)) ∧
    IsItoRep 𝓕 P lam M.N M.W M.W' M.Z M.bhat M.σhat M.σhat' M.δhat ∧
    LocBdd 𝓕 P M.bhat ∧ LocBdd 𝓕 P M.σhat ∧ LocBdd 𝓕 P M.σhat' ∧
    JumpDom 𝓕 P lam (if v ≤ 1 / 2 then 2 else 1 / v) M.δhat ∧
    (1 / 2 < v → ∀ t ω, M.σhat t ω = 0 ∧ M.σhat' t ω = 0) ∧
    ∃ Γ' : ℝ≥0 → Ω → ℝ, LocBdd 𝓕 P Γ' ∧
      ∀ᵐ ω ∂P, ∀ (t s : ℝ≥0), 0 < s → s ≤ 1 →
        |M.Zbar (t + s) ω - M.Zbar t ω| ≤ Γ' (t + s) ω * (s : ℝ) ^ v

/-- The volatility `c_t = σ_t²` (arXiv:1010.4990v1, §2, p. 3). -/
noncomputable def c {Ω : Type*} (σ : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  σ t ω ^ 2

/-- The left limit `c_{t−} = (σ_{t−})²` of the volatility (with `c_{0−} = c_0`). -/
noncomputable def cLeft {Ω : Type*} (σ : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  Function.leftLim (fun s => σ s ω) t ^ 2

end JacodTodorov10.LLN


