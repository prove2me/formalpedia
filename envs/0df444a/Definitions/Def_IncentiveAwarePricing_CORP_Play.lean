-- Prove2me | Definitions.Def_IncentiveAwarePricing_CORP_Play
-- name    : IncentiveAwarePricing_CORP_Play
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-18T17:28:27.001045+00:00
-- url     : https://prove2.me/theorems/7039deab-f98c-454f-9e61-38261a4360b5
-- title:
--   §3–§4, pp. 13–22 — the CORP policy (Table 1, (8)–(10)), buyers' strategies, the play, discounted utilities, rationality, revenue (3), benchmark (5), regret (7), lies (27)
-- statement:
--   This file defines the repeated game of Golrezaei, Javanmard and Mirrokni: the CORP policy (Table 1, p. 22), the buyers' strategies, the resulting random play, and the seller's regret. Periods are $t=1,2,\dots$; episodes are $k=1,2,\dots$ with $\ell_k=2^{k-1}$ and $E_k=\{\ell_k,\dots,\ell_{k+1}-1\}$.
--
--   1. **Data and likelihood** (8)–(9), p. 20. In period $t$ buyer $i$ faces the threshold $\tau_{it}=\max\{b^+_{-it},r_{it}\}$, with $b^+_{-it}=\max_{j\ne i}b_{jt}$, and the outcome $q_{it}\in\{0,1\}$. The negative log-likelihood of episode $k-1$ is
--   $$\mathcal L_{ik}(\beta)=-\sum_{t\in E_{k-1}}\Big\{q_{it}\log\big(1-F(\tau_{it}-\langle x_t,\beta\rangle)\big)+(1-q_{it})\log F(\tau_{it}-\langle x_t,\beta\rangle)\Big\},$$
--   valued in $[0,+\infty]$ with $\log 0=-\infty$ and $0\times(-\infty)=0$ (footnote 12). An **estimator** is a selection $\hat\beta_{ik}$, for every episode $k\ge2$, buyer $i$ and data set, of a minimizer of $\mathcal L_{ik}$ over the ball $\|\beta\|\le B_p$ (8); $\hat\beta_{i1}=0$.
--   2. **CORP** (Table 1). In each period $t\in E_k$, with probability $1/\ell_k$ (exploration) one buyer $i^\circ$ is chosen uniformly at random and offered the item at a price $r\sim\mathrm{Uniform}[0,B]$, $B=B_p+B_n$; he gets it iff $b_{i^\circ t}\ge r$ and then pays $r$; the other buyers' reserves are $+\infty$ and their likelihood terms vanish. With probability $1-1/\ell_k$ (exploitation) the seller runs the lazy second-price auction with reserves $r_{it}=\mathrm{res}(\langle x_t,\hat\beta_{ik}\rangle)$ (10).
--   3. **Buyers** (pp. 17–18). A strategy profile gives buyer $i$'s bid in period $t$ as a function of his own history $H_{it}$ of valuations, bids, allocations and payments, the feature vector $x_t$, his valuation $v_{it}$ and a private uniform seed. The **deviation** $\sigma^{i,k}$ lets buyer $i$ follow $\sigma_i$ before period $\ell_{k-1}$ and bid truthfully from $\ell_{k-1}$ on, other buyers unchanged.
--   4. **Randomness.** Each period draws, independently, $x_t\sim\mathcal D$, $z_t\sim F^{\otimes N}$, the exploration coin $u_t\sim U[0,1]$, $i^\circ\sim U(\{1,\dots,N\})$, $r\sim U[0,B]$ and seeds $s_t\sim U[0,1]^{N}$; the path law is the infinite product over periods, and the play is defined recursively.
--   5. **Utility** (p. 18): $u_{it}=\gamma^t(v_{it}q_{it}-p_{it})$ and $U_i=\sum_{t\ge1}\mathbb E[u_{it}]$. **Utility-maximizing** buyers (pinned as the inequality used on p. 77): for every buyer $i$ and every episode $k\ge2$, if the deviation $\sigma^{i,k}$'s discounted utility sums to $U'$, then $\sigma$'s sums to some $U\ge U'$.
--   6. **Bids** are at most $M$ almost surely (p. 14) and pairwise distinct almost surely (p. 20).
--   7. **Revenue and regret** (3), (5), (7): $\mathrm{rev}_t=\mathbb E[\sum_ip_{it}q_{it}]$; the benchmark $\mathrm{rev}^\star=\mathbb E[\max\{v^-,r^{\star+}\}\,\mathbb I(v^+\ge r^{\star+})]$ is the expected revenue of the lazy second-price auction with truthful bids and reserves $r^\star_i(x)=\mathrm{res}(\langle x,\beta_i\rangle)$ (4); the regret is
--   $$\mathrm{Regret}(T)=\sum_{t=1}^T(\mathrm{rev}^\star-\mathrm{rev}_t).$$
--   8. **Lies** (27), p. 51: $|L_{ik}|$ counts the periods $t\in E_{k-1}$ in which buyer $i$ faces a finite threshold and $\mathbb I(v_{it}>\tau_{it})\neq\mathbb I(b_{it}>\tau_{it})$. Shading is $s_{it}=(v_{it}-b_{it})^+$ and overbidding $o_{it}=(b_{it}-v_{it})^+$.
--
--   These are the objects of Theorem 4.1 and Proposition 9.2.
--
--   **Formalization Note** Periods and episodes are indexed from $0$ internally: Lean's period $n$ is the paper's $t=n+1$ and Lean's episode $e$ is the paper's $k=e+1$, so $\ell_k=2^e$ and exploration happens iff $u_t<1/2^e$. Period $1$ is therefore always an exploration period, and the initial reserve $r_{i1}=0$ of Table 1 never acts. The factor $1/\ell_{k-1}$ of (9) is dropped (it does not change the minimizers). The estimator and the reserve rule are arbitrary selections, carried as parameters of the market instance and constrained only by their defining optimality. Exploration is a posted price to the chosen buyer, as Table 1 and (100) describe; in the likelihood the chosen buyer's threshold is $\max\{b^+_{-it},r_t\}$ as (9) prints. The rationality notion is the weakest one the proof uses; every best-response profile satisfies it and the all-truthful profile satisfies it with equality. The discounted-utility sequences are bounded by a multiple of $\gamma^t$ whenever valuations and payments are bounded, so the summability in the rationality hypothesis is not a restriction.
-- source:
--   Golrezaei, Javanmard, Mirrokni, Dynamic Incentive-Aware Learning: Robust Pricing in Contextual Auctions, arXiv:2002.11137v1, pp. 13–22: (3) p. 15, (5) p. 16, (7) and buyers' utility pp. 17–18, (8)–(9) p. 20, (10) p. 21, Table 1 p. 22; (27) p. 51; p. 77 (rationality)

import Mathlib
import Definitions.Def_LogConcaveOn
import Definitions.Def_IncentiveAwarePricing_CORP_Model

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace ENNReal

namespace IncentiveAwarePricing.CORP

/-! ### Data the firm keeps, and the negative log-likelihood (9)

Periods are indexed internally by `n : ℕ`, the paper's period `t = n + 1`. Episodes are indexed
internally by `e : ℕ`, the paper's episode `k = e + 1`, so `ℓ_k = 2^(k-1) = 2^e` and
`E_k = {2^e, …, 2^(e+1) - 1}` (paper periods). -/

/-- One observation of the censored likelihood (9) for one buyer in one period:
`(x_t, τ_it, won, active)`, where `τ_it = max{b⁺_{-it}, r_it}` is the threshold, `won` records
`q_it = 1`, and `active = false` marks a buyer whose reserve was `+∞` in an exploration period,
whose term in (9) is `log F(+∞) = log 1 = 0`. -/
abbrev Obs (d : ℕ) := Ctx d × ℝ × Bool × Bool

/-- The term of `-(9)` contributed by one observation at the candidate vector `β`:
`-log(1 - F(τ - ⟨x, β⟫))` if the buyer won and `-log F(τ - ⟨x, β⟫)` if he lost, `0` if inactive.
The term is chosen by `q_it` (convention `0 × (-∞) = 0`, footnote 12). -/
noncomputable def obsNLL (f : ℝ → ℝ) {d : ℕ} (β : Ctx d) (o : Obs d) : ℝ≥0∞ :=
  if o.2.2.2 then
    (if o.2.2.1 then nll (1 - noiseCDF f (o.2.1 - ⟪o.1, β⟫))
      else nll (noiseCDF f (o.2.1 - ⟪o.1, β⟫)))
  else 0

/-- The negative log-likelihood (9) of one episode's data of one buyer, without the positive
factor `1/ℓ_{k-1}` (which does not move the argmin). Values in `[0, ∞]`. -/
noncomputable def negLogLik (f : ℝ → ℝ) {d m : ℕ} (data : Fin m → Obs d) (β : Ctx d) : ℝ≥0∞ :=
  ∑ j, obsNLL f β (data j)

/-- An estimator: `est e i data` is buyer `i`'s estimate at the start of paper-episode
`k = e + 2`, computed from the `2^e = ℓ_{k-1}` observations of paper-episode `k - 1 = e + 1`. -/
abbrev Estimator (N d : ℕ) := (e : ℕ) → Fin N → (Fin (2 ^ e) → Obs d) → Ctx d

/-- `est` is a selection of the argmin (8): its value lies in the ball `‖β‖ ≤ Bp` and minimizes
the negative log-likelihood (9) over that ball, for every episode, buyer and data set. -/
def IsCORPEstimator (f : ℝ → ℝ) (Bp : ℝ) {N d : ℕ} (est : Estimator N d) : Prop :=
  ∀ e i data, est e i data ∈ Metric.closedBall (0 : Ctx d) Bp ∧
    ∀ β ∈ Metric.closedBall (0 : Ctx d) Bp, negLogLik f data (est e i data) ≤ negLogLik f data β

/-- Each estimator map is measurable in the data. -/
def EstimatorMeasurable {N d : ℕ} (est : Estimator N d) : Prop :=
  ∀ e i, Measurable (est e i)

/-! ### Buyers' strategies (pp. 17–19) -/

/-- A (randomized) bidding strategy profile: `σ i n h x v s` is buyer `i`'s bid in paper period
`t = n + 1`, given his own history `h` of `(v, b, q, p)` records of periods `1, …, t - 1`, the
feature vector `x_t`, his valuation `v_it` and a private uniform seed `s ∈ [0, 1]`. -/
abbrev Strategy (N d : ℕ) :=
  Fin N → (n : ℕ) → (Fin n → ℝ × ℝ × ℝ × ℝ) → Ctx d → ℝ → ℝ → ℝ

/-- Every buyer's bid map is jointly measurable in (history, context, value, seed). -/
def StrategyMeasurable {N d : ℕ} (σ : Strategy N d) : Prop :=
  ∀ i n, Measurable
    (fun p : (Fin n → ℝ × ℝ × ℝ × ℝ) × Ctx d × ℝ × ℝ => σ i n p.1 p.2.1 p.2.2.1 p.2.2.2)

/-- The truthful profile: every buyer bids his valuation. -/
def truthful (N d : ℕ) : Strategy N d := fun _ _ _ _ v _ => v

/-- `deviate σ i e`: buyer `i` follows `σ i` before paper period `2^e` and bids truthfully from
period `2^e` on (`2^e = ℓ_{k-1}` for paper-episode `k = e + 2`); every other buyer keeps his
strategy. -/
def deviate {N d : ℕ} (σ : Strategy N d) (i : Fin N) (e : ℕ) : Strategy N d :=
  Function.update σ i (fun n h x v s => if 2 ^ e ≤ n + 1 then v else σ i n h x v s)

/-! ### The market instance and the CORP policy (Table 1) -/

/-- A market instance together with CORP's two selections: noise bound `Bn` and density `f`,
preference bound `Bp`, feature law `D`, preference vectors `β`, the MLE selection `est` (8) and
the reserve selection `res` (10). -/
structure Market (N d : ℕ) where
  Bp : ℝ
  Bn : ℝ
  f : ℝ → ℝ
  D : Measure (Ctx d)
  β : Fin N → Ctx d
  est : Estimator N d
  res : ℝ → ℝ

/-- `B = Bp + Bn`, the upper end of the exploration price range (p. 12). -/
def Market.B {N d : ℕ} (E : Market N d) : ℝ := E.Bp + E.Bn

/-- What happens in one period. -/
structure Record (N d : ℕ) where
  x : Ctx d
  explore : Bool
  value : Fin N → ℝ
  bid : Fin N → ℝ
  won : Fin N → Bool
  pay : Fin N → ℝ
  thresh : Fin N → ℝ
  active : Fin N → Bool

/-- A placeholder record (never read: the play only reads strictly earlier periods). -/
def Record.zero (N d : ℕ) : Record N d :=
  ⟨0, false, 0, 0, fun _ => false, 0, 0, fun _ => false⟩

/-- `q_it ∈ {0, 1}`. -/
def Record.alloc {N d : ℕ} (R : Record N d) (i : Fin N) : ℝ := if R.won i then 1 else 0

/-- Buyer `i`'s observation for the likelihood (9). -/
def Record.obs {N d : ℕ} (R : Record N d) (i : Fin N) : Obs d :=
  (R.x, R.thresh i, R.won i, R.active i)

/-- The per-period randomness `(x_t, z_t, u_t, i°_t, r_t, s_t)`: feature vector, noise vector,
the uniform `u_t` deciding exploration, the buyer chosen in exploration, the exploration price
and the buyers' private seeds. -/
abbrev Draw (N d : ℕ) := Ctx d × (Fin N → ℝ) × ℝ × Fin N × ℝ × (Fin N → ℝ)

/-- The 0-based episode index `e` of 0-based period `n`: paper period `t = n + 1` lies in paper
episode `k = e + 1` iff `2^e ≤ t < 2^(e+1)`. -/
def episodeOf (n : ℕ) : ℕ := Nat.log 2 (n + 1)

/-- The 0-based periods `n` of 0-based episode `e` (paper periods `2^e, …, 2^(e+1) - 1`). Both
subtractions are exact since `2^e ≥ 1`. -/
def episodePeriods (e : ℕ) : Finset ℕ := Finset.Ico (2 ^ e - 1) (2 ^ (e + 1) - 1)

/-- CORP's estimate `β̂_ik` for paper-episode `k = e + 1`, from the history `H`:
`β̂_i1 = 0`; for `k ≥ 2` the selection `est` applied to buyer `i`'s observations in episode
`k - 1`, i.e. 0-based periods `2^e' - 1 + j`, `j < 2^e'`, where `e = e' + 1`. -/
noncomputable def estimateAt {N d : ℕ} (E : Market N d) (H : ℕ → Record N d) :
    ℕ → Fin N → Ctx d
  | 0, _ => 0
  | e' + 1, i => E.est e' i (fun j => (H (2 ^ e' - 1 + j)).obs i)

/-- One period of play under CORP (Table 1) at 0-based period `n`, given the history `H` of
earlier periods and this period's draw `w`.

* Exploration (with probability `1/ℓ_k = 1/2^e`, i.e. `u_t < 1/2^e`): the chosen buyer `i°` is
  offered the item at the price `r ∼ U[0, B]`; he gets it iff `b ≥ r` and then pays `r`; every
  other buyer has reserve `+∞`.
* Exploitation: lazy second-price auction with reserves `r_it = res ⟨x_t, β̂_ik⟩`. -/
noncomputable def step {N d : ℕ} (E : Market N d) (σ : Strategy N d) (n : ℕ)
    (H : ℕ → Record N d) (w : Draw N d) : Record N d := by
  classical
  exact
    let x := w.1
    let z := w.2.1
    let u := w.2.2.1
    let i0 := w.2.2.2.1
    let r := w.2.2.2.2.1
    let s := w.2.2.2.2.2
    let e := episodeOf n
    let v := values x E.β z
    let b : Fin N → ℝ := fun i =>
      σ i n (fun m => ((H m).value i, (H m).bid i, (H m).alloc i, (H m).pay i)) x (v i) (s i)
    if u < 1 / (2 : ℝ) ^ e then
      { x := x, explore := true, value := v, bid := b,
        won := fun i => decide (i = i0 ∧ r ≤ b i),
        pay := fun i => if i = i0 ∧ r ≤ b i then r else 0,
        thresh := fun i => thresh b (fun _ => r) i,
        active := fun i => decide (i = i0) }
    else
      let rr : Fin N → ℝ := fun i => E.res ⟪x, estimateAt E H e i⟫
      { x := x, explore := false, value := v, bid := b,
        won := fun i => decide (LazyWins b rr i),
        pay := lazyPay b rr,
        thresh := thresh b rr,
        active := fun _ => true }

/-- The history after `n` periods: entries `m < n` are the records of periods `m`, later entries
are placeholders. -/
noncomputable def hist {N d : ℕ} (E : Market N d) (σ : Strategy N d) (ω : ℕ → Draw N d) :
    ℕ → ℕ → Record N d
  | 0 => fun _ => Record.zero N d
  | n + 1 => Function.update (hist E σ ω n) n (step E σ n (hist E σ ω n) (ω n))

/-- The record of 0-based period `n` along the sample path `ω`. -/
noncomputable def record {N d : ℕ} (E : Market N d) (σ : Strategy N d) (ω : ℕ → Draw N d)
    (n : ℕ) : Record N d :=
  hist E σ ω (n + 1) n

/-! ### The probability space -/

/-- The uniform law on `[a, b]`. -/
noncomputable def unif (a b : ℝ) : Measure ℝ := ProbabilityTheory.cond volume (Set.Icc a b)

/-- The law of one period's draw: `x ∼ D`, `z ∼ F^{⊗N}`, `u ∼ U[0,1]`, `i° ∼ U([N])`,
`r ∼ U[0, B]`, `s ∼ U[0,1]^{⊗N}`, all independent. -/
noncomputable def drawLaw {N d : ℕ} (E : Market N d) : Measure (Draw N d) :=
  E.D.prod ((Measure.pi fun _ : Fin N => noiseLaw E.f).prod ((unif 0 1).prod
    ((uniformOn (Set.univ : Set (Fin N))).prod ((unif 0 E.B).prod
      (Measure.pi fun _ : Fin N => unif 0 1)))))

/-- The law of the whole sample path: i.i.d. draws across periods (the product `⊗_{n ∈ ℕ}` of
`drawLaw`). It is the zero measure only if `drawLaw` is not a probability measure, which never
happens under the standing assumptions (`N ≥ 1`, `B > 0`, `f` a density, `D` a probability). -/
noncomputable def pathLaw {N d : ℕ} (E : Market N d) : Measure (ℕ → Draw N d) := by
  classical
  exact if h : IsProbabilityMeasure (drawLaw E) then
    haveI := h
    Measure.infinitePi (fun _ : ℕ => drawLaw E)
  else 0

/-! ### Buyers' utilities and the rationality hypothesis -/

/-- Buyer `i`'s undiscounted utility in 0-based period `n`: `v_it q_it - p_it`. -/
noncomputable def periodUtility {N d : ℕ} (E : Market N d) (σ : Strategy N d) (i : Fin N)
    (n : ℕ) (ω : ℕ → Draw N d) : ℝ :=
  (record E σ ω n).value i * (record E σ ω n).alloc i - (record E σ ω n).pay i

/-- The sequence `E[u_it] = γ^t E[v_it q_it - p_it]`, `t = n + 1`, whose sum is `U_i1` (p. 18). -/
noncomputable def discountedUtilitySeq {N d : ℕ} (E : Market N d) (γ : ℝ) (σ : Strategy N d)
    (i : Fin N) (n : ℕ) : ℝ :=
  γ ^ (n + 1) * ∫ ω, periodUtility E σ i n ω ∂(pathLaw E)

/-- Utility-maximizing buyers (p. 18), in the form used by the proof (p. 77): no buyer `i` gains
by switching to truthful bidding from the start `ℓ_{k-1} = 2^e` of any episode `k - 1 ≥ 1`
onwards, i.e. if the deviation's discounted utility sums to `U'`, then `σ`'s sums to some
`U ≥ U'`. -/
def UtilityMaximizing {N d : ℕ} (E : Market N d) (γ : ℝ) (σ : Strategy N d) : Prop :=
  ∀ (i : Fin N) (e : ℕ) (U' : ℝ), HasSum (discountedUtilitySeq E γ (deviate σ i e) i) U' →
    ∃ U, HasSum (discountedUtilitySeq E γ σ i) U ∧ U' ≤ U

/-- Bids are bounded by `M` (p. 14). -/
def BidsBounded {N d : ℕ} (E : Market N d) (M : ℝ) (σ : Strategy N d) : Prop :=
  ∀ n (i : Fin N), ∀ᵐ ω ∂(pathLaw E), (record E σ ω n).bid i ≤ M

/-- Submitted bids are distinct (p. 20), almost surely. -/
def BidsDistinct {N d : ℕ} (E : Market N d) (σ : Strategy N d) : Prop :=
  ∀ n (i j : Fin N), i ≠ j → pathLaw E {ω | (record E σ ω n).bid i = (record E σ ω n).bid j} = 0

/-! ### Revenue (3), benchmark (5), regret (7) -/

/-- Expected revenue `rev_t = E[∑_i p_it q_it]` (3) in 0-based period `n`. -/
noncomputable def revenue {N d : ℕ} (E : Market N d) (σ : Strategy N d) (n : ℕ) : ℝ :=
  ∫ ω, ∑ i, (record E σ ω n).pay i ∂(pathLaw E)

/-- The benchmark revenue (5): truthful buyers in a lazy second-price auction with the reserves
`r⋆_i(x) = res ⟨x, β_i⟩` of (4), in expectation over `x ∼ D` and `z ∼ F^{⊗N}`. -/
noncomputable def benchmarkRevenue {N d : ℕ} (E : Market N d) : ℝ :=
  ∫ xz, lazyRevenue (values xz.1 E.β xz.2) (fun i => E.res ⟪xz.1, E.β i⟫)
    ∂(E.D.prod (Measure.pi fun _ : Fin N => noiseLaw E.f))

/-- The `T`-period regret `∑_{t=1}^T (rev⋆_t - rev_t)` of CORP for the instance `E` against the
strategy profile `σ`. -/
noncomputable def regret {N d : ℕ} (E : Market N d) (σ : Strategy N d) (T : ℕ) : ℝ :=
  ∑ n ∈ Finset.range T, (benchmarkRevenue E - revenue E σ n)

/-! ### Lies, shading and overbidding (27), Proposition 9.2 -/

/-- `|L_ik|` of (27) for paper-episode `k = e + 2`: the number of periods `t ∈ E_{k-1}` (0-based
episode `e`) in which buyer `i` faces a finite threshold `τ_it = max{b⁺_{-it}, r_it}` and
`I(v_it > τ_it) ≠ I(b_it > τ_it)`. A buyer whose reserve is `+∞` (not chosen in an exploration
period) never lies. -/
noncomputable def lieCount {N d : ℕ} (E : Market N d) (σ : Strategy N d) (i : Fin N) (e : ℕ)
    (ω : ℕ → Draw N d) : ℕ := by
  classical
  exact ((episodePeriods e).filter fun n =>
    (record E σ ω n).active i = true ∧
      ¬ (((record E σ ω n).thresh i < (record E σ ω n).value i) ↔
        ((record E σ ω n).thresh i < (record E σ ω n).bid i))).card

/-- Shading `s_it = (v_it - b_it)⁺`. -/
def Record.shading {N d : ℕ} (R : Record N d) (i : Fin N) : ℝ := max (R.value i - R.bid i) 0

/-- Overbidding `o_it = (b_it - v_it)⁺`. -/
def Record.overbidding {N d : ℕ} (R : Record N d) (i : Fin N) : ℝ := max (R.bid i - R.value i) 0

end IncentiveAwarePricing.CORP


