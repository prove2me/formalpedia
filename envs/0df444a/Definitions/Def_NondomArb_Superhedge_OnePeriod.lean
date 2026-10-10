-- Prove2me | Definitions.Def_NondomArb_Superhedge_OnePeriod
-- name    : NondomArb_Superhedge_OnePeriod
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T14:22:52.658746+00:00
-- url     : https://prove2.me/theorems/144787f6-f714-4280-ad59-160f5da3f2ee
-- title:
--   §3: the one-period market — convex 𝒫, NA(𝒫), 𝒬 = {Q ⋘ 𝒫 : E_Q[ΔS] = 0}, π(f) and the set Θ
-- statement:
--   This is the one-period market of §3 of Bouchard–Nutz.
--
--   Let $(\Omega,\mathcal F)$ be a measurable space, $\mathcal F_0=\{\emptyset,\Omega\}$, $\mathcal F_1=\mathcal F$, and let $\mathcal P$ be a nonempty convex set of probability measures on $\mathcal F$. The stock has a deterministic price $S_0\in\mathbb R^d$ and an $\mathcal F$-measurable price $S_1$; write $\Delta S=S_1-S_0$. Trading strategies are vectors $H\in\mathbb R^d$.
--
--   1. **NA($\mathcal P$)**: for $H\in\mathbb R^d$, $H\Delta S\ge0$ $\mathcal P$-q.s. implies $H\Delta S=0$ $\mathcal P$-q.s.
--   2. **Martingale measures**:
--   $$\mathcal Q=\{Q\in\mathfrak P(\Omega):\ Q\lll\mathcal P,\ E_Q[\Delta S]=0\}.$$
--   3. **Superhedging price** (3.2) of a random variable $f$:
--   $$\pi(f)=\inf\{x\in\mathbb R:\ \exists H\in\mathbb R^d,\ x+H\Delta S\ge f\ \ \mathcal P\text{-q.s.}\}\in[-\infty,\infty].$$
--   4. **The set** $\Theta=\{R\in\mathfrak P(\Omega):\ R\lll\mathcal P,\ E_R[|\Delta S|+|f|]<\infty\}$ of Lemmas 3.3–3.6.
--
--   These objects are the one-step building blocks of the multi-period theory: the multi-period market of §4 is a concatenation of such one-period markets.
--
--   **Formalization Note** Under convention (1.1), $E_Q[\Delta S^i]=0$ forces $\Delta S^i\in L^1(Q)$ (a component with $E^+=E^-=\infty$ would have expectation $-\infty$), so $\mathcal Q$ is encoded with `Integrable` and a zero Bochner integral. Convexity is stated for the measures: $aP+(1-a)P'\in\mathcal P$ for $a\in[0,1]$. $|\Delta S|$ is the sup norm on $\mathbb R^d$, which gives the same finiteness condition as the Euclidean norm. The price is an infimum in `EReal` with $\inf\emptyset=+\infty$.
-- source:
--   Bouchard, Nutz, Arbitrage and duality in nondominated discrete-time models, arXiv:1305.6008v3, pp. 12–13, §3 (setting); p. 13, Lemma 3.3 (Θ); p. 15, (3.2)

import Mathlib
import Definitions.Def_NondomArb_Superhedge_Basic

namespace NondomArb.Superhedge.OnePeriod

open MeasureTheory

/-! §3 (pp. 12–13): the one-period market on a measurable space `(Ω, F)` with `F_0 = {∅, Ω}`, a
nonempty convex set `𝒫` of probability measures, a deterministic `S_0 ∈ ℝ^d` and an
`F`-measurable `S_1`; only the increment `ΔS = S_1 − S_0 : Ω → ℝ^d` enters. Strategies are
vectors `H ∈ ℝ^d`; no options. -/

/-- The standing assumptions on `𝒫` in §3: a nonempty, convex set of probability measures. -/
def IsConvexModelSet {Ω : Type*} [MeasurableSpace Ω] (Pset : Set (Measure Ω)) : Prop :=
  Pset.Nonempty ∧ (∀ P ∈ Pset, IsProbabilityMeasure P) ∧
    ∀ P ∈ Pset, ∀ P' ∈ Pset, ∀ a : NNReal, a ≤ 1 → a • P + (1 - a) • P' ∈ Pset

/-- **NA(𝒫)** in the one-period market: for `H ∈ ℝ^d`, `HΔS ≥ 0` `𝒫`-q.s. implies `HΔS = 0`
`𝒫`-q.s. -/
def NA {Ω : Type*} [MeasurableSpace Ω] (Pset : Set (Measure Ω)) {d : ℕ} (ΔS : Ω → (Fin d → ℝ)) :
    Prop :=
  ∀ H : Fin d → ℝ, QS Pset (fun ω => 0 ≤ H ⬝ᵥ ΔS ω) → QS Pset (fun ω => H ⬝ᵥ ΔS ω = 0)

/-- `𝒬 = {Q ∈ 𝔓(Ω) : Q ⋘ 𝒫, E_Q[ΔS] = 0}` (p. 13). Under convention (1.1), `E_Q[ΔS^i] = 0`
forces `ΔS^i ∈ L¹(Q)`, so the condition is `ΔS` `Q`-integrable with zero mean. -/
def MartMeasures {Ω : Type*} [MeasurableSpace Ω] (Pset : Set (Measure Ω)) {d : ℕ}
    (ΔS : Ω → (Fin d → ℝ)) : Set (Measure Ω) :=
  {Q | IsProbabilityMeasure Q ∧ AbsContSet Q Pset ∧ Integrable ΔS Q ∧ ∫ ω, ΔS ω ∂Q = 0}

/-- The one-period superhedging price (3.2):
`π(f) = inf{x ∈ ℝ : ∃ H ∈ ℝ^d, x + HΔS ≥ f 𝒫-q.s.}` in `[−∞, ∞]`, `inf ∅ = +∞`. -/
noncomputable def price {Ω : Type*} [MeasurableSpace Ω] (Pset : Set (Measure Ω)) {d : ℕ}
    (ΔS : Ω → (Fin d → ℝ)) (f : Ω → ℝ) : EReal :=
  sInf {x : EReal | ∃ x' : ℝ, x = (x' : EReal) ∧ ∃ H : Fin d → ℝ,
    QS Pset (fun ω => f ω ≤ x' + H ⬝ᵥ ΔS ω)}

/-- The set `Θ` of Lemma 3.3 and Lemma 3.6: probability measures `R ⋘ 𝒫` with
`E_R[|ΔS| + |f|] < ∞`. -/
def Theta {Ω : Type*} [MeasurableSpace Ω] (Pset : Set (Measure Ω)) {d : ℕ}
    (ΔS : Ω → (Fin d → ℝ)) (f : Ω → ℝ) : Set (Measure Ω) :=
  {R | IsProbabilityMeasure R ∧ AbsContSet R Pset ∧
    (∫⁻ ω, ENNReal.ofReal (‖ΔS ω‖ + |f ω|) ∂ R) < ⊤}

end NondomArb.Superhedge.OnePeriod


