-- Prove2me | Definitions.Def_EliasGlobalClock_LowerBound_Supplement_analysis
-- name    : EliasGlobalClock_LowerBound_Supplement_analysis
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T07:34:46.473849+00:00
-- url     : https://prove2.me/theorems/7c7d2277-582d-439c-840b-42513e2c1d48
-- title:
--   Window progress, deviation, efficiency dichotomy and delivery properties of Algorithm 2
-- statement:
--   Along each realization $\omega$ of an adversary model for Algorithm 2 write $Q(t)$, $N_j$, $A(t)$, $D(t)$ for the counts and $H_j=B\lceil16\,\mathrm{prd}(k_j)/\delta\rceil$ for the window length at block boundary $t_j$. For an integer threshold $R$ this definition names the following properties, each quantified over every adversary model and every initial population $q_0$.
--
--   1. **Window progress** (the conclusion of Lemma 5.2): for every block $j\ge1$, conditionally on $\mathcal F_{t_j}$ on the event $\{N_j\ge R\}$,
--   $$\mathbb E\big[D(t_j+H_j)-D(t_j)+\delta\,(A(t_j+H_j)-A(t_j))\,\big|\,\mathcal F_{t_j}\big]\ge cH_j.$$
--   2. **Capped window progress** (Corollary 5.3): the same with the progress replaced by $Y=\min\{D_i+\delta A_i,H_j\}$.
--   3. **Deviation bound** with $\eta$ and $a$ (Lemma C.4): for every block boundary $s$ and every $q_0$ there is $T_0$ such that for every adversary and every integer $T\ge T_0$
--   $$\Pr\big(Q(t_j)\ge R\ \text{for all }t_j\in[s,T],\ D(T)+\delta A(T)\le(c-\eta)T\big)\le\exp\!\Big(-\frac{aT}{\log_2^4(T+Q(0)+2)}\Big).$$
--   4. **Efficiency dichotomy** (Theorem 5.4): almost surely either (i) $N_j<R$ for infinitely many $j$, every player eventually succeeds, and $D(t_j)\ge A(t_j)-R$, $A(t_j)\le t_j+R$ whenever $N_j<R$; or (ii) $N_j\ge R$ for all large $j$ and $\liminf_{T\to\infty}(D(T)+\delta A(T))/T\ge c$.
--   5. **Delivery for rate $\lambda$** (Theorem 5.5): if almost surely $A(t)<\lambda t$ for infinitely many integers $t$, then almost surely $Q(t_j)<R$ for infinitely many $j$ and every player eventually succeeds.
--
--   Naming these properties lets one threshold $R$ be shared between Lemma 5.2, Corollary 5.3, Lemma C.4 and Theorems 5.4–5.5, as in the paper.
--
--   **Formalization Note** A conditional expectation bound $\mathbb E[X\mid\mathcal F]\ge Y$ on an $\mathcal F$-measurable event $G$, for $X\ge0$, is written as $\int_S Y\,dP\le\int_S X\,dP$ for every $\mathcal F$-measurable $S\subseteq G$ (lower Lebesgue integrals in $[0,\infty]$; no integrability is assumed). The liminf is written as: for every $c'<c$, eventually $c'T\le D(T)+\delta A(T)$, which is the liminf in the extended reals.
-- source:
--   Kuowen Chen, Shengquan Du, Tsvi Kopelowitz, Seth Pettie, Ben Plosk, STOC 2027 submission #1311 (October 2026), The Necessity of Elias Codes in the Global Clock Model, printed pp.14–19, 33–36 / PDF pp.15–20, 34–37: §5.2 (windows, Lemma 5.2, Corollary 5.3), §5.3 (Theorems 5.4, 5.5, λ-adversary), Appendix C.3 (Lemma C.4); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1311.pdf

import Definitions.Def_EliasGlobalClock_LowerBound_Supplement_algorithmTwo

open MeasureTheory ProbabilityTheory Filter

namespace EliasGlobalClock.LowerBound.Supplement

/-! Path-wise counts of Algorithm 2 and the window, deviation, dichotomy and delivery
properties of §5.2–5.3 and Appendix C.3 (printed pp.14–19, 33–36 / PDF pp.15–20, 34–37),
stated for every adversary model so that one threshold `R` can be shared between results. -/

section Path

variable {Ω : Type*}

/-- The arrival batches along the realization `ω`. -/
def pathArrivals (a : ℕ → Ω → ℕ) (ω : Ω) : ℕ → ℕ := fun t => a t ω

/-- The fresh uniforms along the realization `ω`. -/
def pathCoins (U : Player → ℕ → Ω → ℝ) (ω : Ω) : Player → ℕ → ℝ := fun v t => U v t ω

/-- `Q(t)` along `ω`. -/
noncomputable def popAt (ε : ℝ) (q₀ : ℕ) (a : ℕ → Ω → ℕ) (U : Player → ℕ → Ω → ℝ)
    (t : ℕ) (ω : Ω) : ℕ :=
  population ε q₀ (pathArrivals a ω) (pathCoins U ω) t

/-- `N_j = Q(t_j)` along `ω`. -/
noncomputable def blockPop (ε : ℝ) (q₀ : ℕ) (a : ℕ → Ω → ℕ) (U : Player → ℕ → Ω → ℝ)
    (j : ℕ) (ω : Ω) : ℕ :=
  popAt ε q₀ a U (blockStart ε j) ω

/-- `D(t)` along `ω`. -/
noncomputable def depAt (ε : ℝ) (q₀ : ℕ) (a : ℕ → Ω → ℕ) (U : Player → ℕ → Ω → ℝ)
    (t : ℕ) (ω : Ω) : ℕ :=
  departures ε q₀ (pathArrivals a ω) (pathCoins U ω) t

/-- `A(t)` along `ω`. -/
def arrAt (a : ℕ → Ω → ℕ) (t : ℕ) (ω : Ω) : ℕ := arrivals (pathArrivals a ω) t

/-- Credited progress `D_i + δ A_i` of the window that starts at block boundary `t_j` with
length `H = B⌈16 prd(k_j)/δ⌉`, `k_j = ⌈log_{1+δ} N_j⌉`. -/
noncomputable def blockWindowProgress (ε : ℝ) (q₀ : ℕ) (a : ℕ → Ω → ℕ)
    (U : Player → ℕ → Ω → ℝ) (j : ℕ) (ω : Ω) : ℝ :=
  windowProgress ε q₀ (pathArrivals a ω) (pathCoins U ω) (blockStart ε j)
    (windowLength ε (blockPop ε q₀ a U j ω))

/-- Every possible player that exists along `ω` eventually succeeds. -/
def AllEventuallySucceed (ε : ℝ) (q₀ : ℕ) (a : ℕ → Ω → ℕ) (U : Player → ℕ → Ω → ℝ)
    (ω : Ω) : Prop :=
  ∀ v, PlayerExists q₀ (pathArrivals a ω) v →
    ∃ t, SucceedsAt ε q₀ (pathArrivals a ω) (pathCoins U ω) v t

end Path

/-- The conclusion of Lemma 5.2 for the threshold `R`: for every adversary model and every
block boundary `t_j`, conditionally on `ℱ_{t_j}` and on the event `N_j ≥ R`, the expected
credited progress of the window starting at `t_j` is at least `c H`. The generalized
(`[0,∞]`-valued) conditional expectation is expressed by integrating over every
`ℱ_{t_j}`-measurable `S ⊆ {N_j ≥ R}`. -/
def WindowProgress.{v} (ε : ℝ) (R : ℕ) : Prop :=
  ∀ (Ω : Type v) [mΩ : MeasurableSpace Ω] (P : Measure Ω) (ℱ : Filtration ℕ mΩ)
    (U : Player → ℕ → Ω → ℝ) (a : ℕ → Ω → ℕ) (q₀ : ℕ), IsAdversaryModel P ℱ U a →
    ∀ j, 1 ≤ j → ∀ S : Set Ω, MeasurableSet[ℱ (blockStart ε j)] S →
      S ⊆ {ω | R ≤ blockPop ε q₀ a U j ω} →
      ∫⁻ ω in S, ENNReal.ofReal (rateC ε * windowLength ε (blockPop ε q₀ a U j ω)) ∂P ≤
        ∫⁻ ω in S, ENNReal.ofReal (blockWindowProgress ε q₀ a U j ω) ∂P

/-- The conclusion of Corollary 5.3 for the threshold `R`: the same bound for the capped
progress `Y_i = min{D_i + δA_i, H_i}`. -/
def CappedWindowProgress.{v} (ε : ℝ) (R : ℕ) : Prop :=
  ∀ (Ω : Type v) [mΩ : MeasurableSpace Ω] (P : Measure Ω) (ℱ : Filtration ℕ mΩ)
    (U : Player → ℕ → Ω → ℝ) (a : ℕ → Ω → ℕ) (q₀ : ℕ), IsAdversaryModel P ℱ U a →
    ∀ j, 1 ≤ j → ∀ S : Set Ω, MeasurableSet[ℱ (blockStart ε j)] S →
      S ⊆ {ω | R ≤ blockPop ε q₀ a U j ω} →
      ∫⁻ ω in S, ENNReal.ofReal (rateC ε * windowLength ε (blockPop ε q₀ a U j ω)) ∂P ≤
        ∫⁻ ω in S, ENNReal.ofReal (min (blockWindowProgress ε q₀ a U j ω)
          (windowLength ε (blockPop ε q₀ a U j ω))) ∂P

/-- The conclusion of Lemma C.4 for threshold `R`, slack `η` and constant `a_{ε,η}`: for every
deterministic block boundary `s = t_{j₀}` and initial population `q₀` there is a cutoff `T₀`
such that, for every adversary and every integer `T ≥ T₀`,
`Pr(Q(t_j) ≥ R at every block boundary t_j ∈ [s, T], D(T) + δA(T) ≤ (c − η)T)
  ≤ exp(−a T / log₂⁴(T + Q(0) + 2))`. -/
def DeviationBound.{v} (ε : ℝ) (R : ℕ) (η aε : ℝ) : Prop :=
  ∀ j₀, 1 ≤ j₀ → ∀ q₀ : ℕ, ∃ T₀ : ℕ,
    ∀ (Ω : Type v) [mΩ : MeasurableSpace Ω] (P : Measure Ω) (ℱ : Filtration ℕ mΩ)
      (U : Player → ℕ → Ω → ℝ) (a : ℕ → Ω → ℕ), IsAdversaryModel P ℱ U a →
      ∀ T : ℕ, T₀ ≤ T →
        P {ω | (∀ j, 1 ≤ j → blockStart ε j₀ ≤ blockStart ε j → blockStart ε j ≤ T →
                  R ≤ blockPop ε q₀ a U j ω) ∧
               (depAt ε q₀ a U T ω : ℝ) + delta ε * arrAt a T ω ≤ (rateC ε - η) * T} ≤
          ENNReal.ofReal (Real.exp (-(aε * T / Real.logb 2 (T + q₀ + 2) ^ 4)))

/-- The conclusion of Theorem 5.4 for threshold `R`: against every adversary, almost surely
(i) `N_j < R` for infinitely many blocks, every player eventually succeeds, and at each block
boundary with `N_j < R`, `D(t_j) ≥ A(t_j) − R` and `A(t_j) ≤ t_j + R`; or (ii) `N_j ≥ R` for
all sufficiently late blocks and `liminf_{T→∞} (D(T) + δA(T))/T ≥ c`, written as: for every
`c' < c`, eventually `c' T ≤ D(T) + δA(T)`. -/
def EfficiencyDichotomy.{v} (ε : ℝ) (R : ℕ) : Prop :=
  ∀ (Ω : Type v) [mΩ : MeasurableSpace Ω] (P : Measure Ω) (ℱ : Filtration ℕ mΩ)
    (U : Player → ℕ → Ω → ℝ) (a : ℕ → Ω → ℕ) (q₀ : ℕ), IsAdversaryModel P ℱ U a →
    ∀ᵐ ω ∂P,
      ((∃ᶠ j in atTop, blockPop ε q₀ a U j ω < R) ∧
        AllEventuallySucceed ε q₀ a U ω ∧
        ∀ j, 1 ≤ j → blockPop ε q₀ a U j ω < R →
          (arrAt a (blockStart ε j) ω : ℤ) - R ≤ depAt ε q₀ a U (blockStart ε j) ω ∧
          arrAt a (blockStart ε j) ω ≤ blockStart ε j + R) ∨
      ((∀ᶠ j in atTop, R ≤ blockPop ε q₀ a U j ω) ∧
        ∀ c' < rateC ε, ∀ᶠ T in atTop,
          c' * T ≤ (depAt ε q₀ a U T ω : ℝ) + delta ε * arrAt a T ω)

/-- The conclusion of Theorem 5.5 for threshold `R` and rate `λ`: against every λ-adversary
(almost surely `A(t) < λt` for infinitely many integers `t`), almost surely `Q(t_j) < R` at
infinitely many block boundaries and every player eventually succeeds. -/
def LambdaDelivery.{v} (ε : ℝ) (R : ℕ) (lam : ℝ) : Prop :=
  ∀ (Ω : Type v) [mΩ : MeasurableSpace Ω] (P : Measure Ω) (ℱ : Filtration ℕ mΩ)
    (U : Player → ℕ → Ω → ℝ) (a : ℕ → Ω → ℕ) (q₀ : ℕ), IsAdversaryModel P ℱ U a →
    (∀ᵐ ω ∂P, ∃ᶠ t in atTop, (arrAt a t ω : ℝ) < lam * t) →
    ∀ᵐ ω ∂P, (∃ᶠ j in atTop, blockPop ε q₀ a U j ω < R) ∧ AllEventuallySucceed ε q₀ a U ω

end EliasGlobalClock.LowerBound.Supplement


