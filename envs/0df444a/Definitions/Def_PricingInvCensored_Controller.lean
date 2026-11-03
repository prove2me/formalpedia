-- Prove2me | Definitions.Def_PricingInvCensored_Controller
-- name    : PricingInvCensored_Controller
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:50:11.632555+00:00
-- url     : https://prove2.me/theorems/55d4f458-10d3-4b77-9e02-71e2f073f8eb
-- title:
--   Algorithms 1–3 as an observation-driven controller: bisection for the order-up-to level, the difference estimator $\widehat\Delta_G$, trisection on prices
-- statement:
--   **The learning algorithm** (Algorithms 1–3, pp. 13, 16, 18). The firm knows only $\underline p,\overline p,b,h,\bar y$ and the parameters $C_1,C_2$. The module writes the paper's three procedures as one deterministic controller whose input at each period is the starting stock $x_t$, and whose update after the period receives the realized stock level $y_t$ and the sales $o_t=\min\{D_t,y_t\}$.
--
--   1. **Trisection** (Algorithm 3). Epoch $\zeta$ has an active interval $[L_\zeta,U_\zeta]$, starting from $[\underline p,\overline p]$, the points $\alpha_\zeta=\tfrac23L_\zeta+\tfrac13U_\zeta$, $\beta_\zeta=\tfrac13L_\zeta+\tfrac23U_\zeta$ and the budget
--   $$N_\zeta=\Big\lceil g\big(C_2/(\beta_\zeta-\alpha_\zeta)^4\big)\Big\rceil,\qquad g(x)=\big(x+\lceil\log_2(x\bar y)\rceil\big)\big\lceil\log_2\big(x+\lceil\log_2(x\bar y)\rceil\big)\big\rceil.$$
--   It calls SearchOrderUpTo at $\alpha_\zeta$ and at $\beta_\zeta$, then EstimateGDifference, and moves to $[\alpha_\zeta,U_\zeta]$ if $\widehat\Delta_G>0$ and to $[L_\zeta,\beta_\zeta]$ otherwise.
--   2. **SearchOrderUpTo$(p,n,C_1)$** (Algorithm 1). A bisection on $[0,\bar y]$ starting at $m_0=\bar y/2$. Each budget period posts $(p,m_\tau)$, adds $b+p$ to $g_\tau$ if no stock is left and subtracts $h$ otherwise, and forms $\hat g_\tau\pm C_1/\sqrt{n_\tau}$ with $\hat g_\tau=g_\tau/n_\tau$; while $\tau<\lceil\log_2(n\bar y)\rceil$ a confidence interval above $0$ moves the bracket up and one below $0$ moves it down. Before the first stage and after every move the firm posts $\underline p$ and orders nothing until the stock falls below the new midpoint; these drain periods do not count toward the budget $n$. After $n$ budget periods it returns the midpoint visited most often.
--   3. **EstimateGDifference$(p,\hat y,p',\hat y',n)$** (Algorithm 2). It posts $(p,\hat y)$ for $n$ periods and $(p',\hat y')$ for $n$ more, records sales $o_t$ and leftovers $\delta_t$, sets
--   $$\hat u=\sup\Big\{u: F_{\hat\nu'}(u)\le\tfrac{h}{b+p+h}\Big\}$$
--   for the empirical CDF $F_{\hat\nu'}$ of the second half's leftovers, and returns
--   $$\widehat\Delta_G(p,p')=\Big[\tfrac1n\sum_{t\in\mathcal T_2}p'o'_t-h\delta'_t\Big]-\Big[\tfrac1n\sum_{t\in\mathcal T_1}po_t-h\delta_t\Big]+b\Big[\hat u\,\tfrac{h}{b+p+h}-\tfrac1n\sum_{t\in\mathcal T_2}\delta'_t\mathbf 1\{0<\delta'_t\le\hat u\}\Big].$$
--
--   The controller is the policy whose regret Theorem 1 bounds; `trisect` is also used by Eq. (EC.16).
--
--   **Formalization Note** The controller never sees $\lambda$, $\mu$, $f_\mu$, the noise or $(p^*,y^*)$. "No inventories are left" is $o_t=y_t$. $g_\tau$ is reset with $n_\tau$ when the bracket moves. Line 14 breaks ties toward the latest stage. Leftovers use the realized level, $\delta_t=y_t-o_t$. Instantaneous transitions (a call returning, an epoch ending) happen within a period, bounded by a fuel of 8; with positive budgets at most two occur per period.
-- source:
--   Chen, Wang & Zhou, Optimal Policies for Dynamic Pricing and Inventory Control with Nonparametric Censored Demands, SSRN 3750413 (2022-10-19), Algorithm 1 p.13, Algorithm 2 p.16, Algorithm 3 and footnote ** p.18

import Mathlib

namespace PricingInvCensored

/-- **The firm's known parameters** for Algorithms 1–3 of Chen, Wang & Zhou, SSRN 3750413
(2022-10-19), pp.13, 16, 18: the price range `[p̲, p̄] = [low, high]`, the costs `b`, `h`, the known
upper bound `ȳ = ybar` (Assumption 1(2), p.9), and the algorithm parameters `C₁ = C1`, `C₂ = C2`
(Algorithm 3, line 1, p.18).

**Formalization Note.** These are the only numbers the controller below may use. It never sees the
demand curve `λ`, the noise law `µ`, its density, the noise realizations, or the clairvoyant
solution. -/
structure Params where
  low : ℝ
  high : ℝ
  b : ℝ
  h : ℝ
  ybar : ℝ
  C1 : ℝ
  C2 : ℝ

/-- The function `g(x) := (x + ⌈log₂(xȳ)⌉)⌈log₂(x + ⌈log₂(xȳ)⌉)⌉` of Algorithm 3, footnote **,
p.18 (Chen, Wang & Zhou, SSRN 3750413). -/
noncomputable def gfun (ybar x : ℝ) : ℝ :=
  (x + ⌈Real.logb 2 (x * ybar)⌉) * ⌈Real.logb 2 (x + ⌈Real.logb 2 (x * ybar)⌉)⌉

/-- The epoch budget `N_ζ = ⌈g(C₂/(β_ζ − α_ζ)⁴)⌉` of Algorithm 3, line 4, p.18, as a function of the
width `w = β_ζ − α_ζ`. -/
noncomputable def budget (P : Params) (w : ℝ) : ℤ := ⌈gfun P.ybar (P.C2 / w ^ 4)⌉

/-- The left trisection point `α = (2/3)L + (1/3)U` (Algorithm 3, line 4, p.18). -/
noncomputable def trisectAlpha (L U : ℝ) : ℝ := 2 / 3 * L + 1 / 3 * U

/-- The right trisection point `β = (1/3)L + (2/3)U` (Algorithm 3, line 4, p.18). -/
noncomputable def trisectBeta (L U : ℝ) : ℝ := 1 / 3 * L + 2 / 3 * U

/-- **The trisection update**, Algorithm 3, lines 7–10, p.18 (Chen, Wang & Zhou, SSRN 3750413):
given the active interval `[L, U]` and the estimate `D = Δ̂_G(α, β)`, the next interval is
`[α, U]` if `D > 0` and `[L, β]` otherwise. -/
noncomputable def trisect (L U D : ℝ) : ℝ × ℝ :=
  if 0 < D then (trisectAlpha L U, U) else (L, trisectBeta L U)

/-- The empirical CDF `F_ν̂(u) = #{i : x_i ≤ u} / n` of a finite sample (Algorithm 2, line 4,
p.16). -/
noncomputable def empCDF (xs : List ℝ) (u : ℝ) : ℝ :=
  (xs.countP (fun x => decide (x ≤ u)) : ℝ) / xs.length

/-- `û := sup{u : F_ν̂′(u) ≤ θ}` (Algorithm 2, line 4, p.16, with `θ = h/(b+p+h)`). -/
noncomputable def uHat (θ : ℝ) (xs : List ℝ) : ℝ := sSup {u : ℝ | empCDF xs u ≤ θ}

/-- **The difference estimator** `Δ̂_G(p, p′)` of Algorithm 2, line 5, p.16 (Chen, Wang & Zhou,
SSRN 3750413):
`Δ̂_G = [(1/n)Σ_{T₂}(p′o′_t − hδ′_t)] − [(1/n)Σ_{T₁}(p o_t − hδ_t)]
  + b[û·h/(b+p+h) − (1/n)Σ_{T₂} δ′_t 1{0 < δ′_t ≤ û}]`, where `obs1`, `obs2` list the pairs
`(o_t, δ_t)` of the two halves and `û = uHat (h/(b+p+h)) (δ′_t)`.

**Formalization Note.** The threshold `h/(b+p+h)` uses the lower price `p`, as printed in line 4. -/
noncomputable def deltaHat (P : Params) (p p' : ℝ) (n : ℕ) (obs1 obs2 : List (ℝ × ℝ)) : ℝ :=
  let θ := P.h / (P.b + p + P.h)
  let d2 := obs2.map Prod.snd
  let u := uHat θ d2
  (obs2.map (fun od => p' * od.1 - P.h * od.2)).sum / n
    - (obs1.map (fun od => p * od.1 - P.h * od.2)).sum / n
    + P.b * (u * θ - (d2.map (fun d => if 0 < d ∧ d ≤ u then d else 0)).sum / n)

/-- **State of one call `SearchOrderUpTo(p, n, C₁)`**, Algorithm 1, p.13 (Chen, Wang & Zhou,
SSRN 3750413): the price `p`, the budget `n`, the budget periods used so far, the stage `τ`, the
bracket `L_τ`, `U_τ`, the midpoint `m_τ`, the stage counters `n_τ` and `g_τ`, the best earlier
stage `(n_τ', m_τ')` for line 14, and whether a drain (lines 3, 10, 13) is in progress. -/
structure SearchState where
  price : ℝ
  n : ℕ
  used : ℕ
  stage : ℕ
  lo : ℝ
  hi : ℝ
  mid : ℝ
  visits : ℕ
  score : ℝ
  best : ℕ × ℝ
  draining : Bool

/-- Line 2 of Algorithm 1: `L₀ = 0`, `U₀ = ȳ`, `m₀ = ȳ/2`, `n₀ = 0`, `τ = 0`, `g₀ = 0`; then the
drain of line 3. -/
noncomputable def searchInit (P : Params) (p : ℝ) (n : ℕ) : SearchState :=
  ⟨p, n, 0, 0, 0, P.ybar, P.ybar / 2, 0, 0, (0, P.ybar / 2), true⟩

/-- Line 14 of Algorithm 1: return the midpoint explored most often; ties go to the latest stage. -/
def searchResult (s : SearchState) : ℝ := if s.best.1 ≤ s.visits then s.mid else s.best.2

/-- The action of a `SearchOrderUpTo` call at a period with starting stock `x`: during a drain with
`x ≥ m_τ`, post `p̲` and order nothing; otherwise, while budget remains, post `(p, m_τ)`
(line 5); `none` once the budget is spent (the call returns). -/
noncomputable def searchAction (P : Params) (s : SearchState) (x : ℝ) : Option (ℝ × ℝ) :=
  if s.draining = true ∧ s.mid ≤ x then some (P.low, x)
  else if s.used < s.n then some (s.price, s.mid) else none

/-- Lines 6–13 of Algorithm 1 after a period with starting stock `x`, stock level `level` and sales
`o`. A drain period changes nothing. A budget period updates `n_τ ← n_τ + 1` and
`g_τ ← g_τ + (b+p)` if no inventory is left (`o = level`), `g_τ ← g_τ − h` otherwise, forms
`ĝ_τ ± C₁/√n_τ`, and moves the bracket (lines 8–13), resetting `n_τ` and `g_τ` and starting a
drain. -/
noncomputable def searchUpdate (P : Params) (s : SearchState) (x level o : ℝ) : SearchState :=
  if s.draining = true ∧ s.mid ≤ x then s
  else
    let v := s.visits + 1
    let g := if o = level then s.score + (P.b + s.price) else s.score - P.h
    let ghat := g / (v : ℝ)
    let rad := P.C1 / Real.sqrt (v : ℝ)
    let best' := if s.best.1 ≤ v then (v, s.mid) else s.best
    if (s.stage : ℤ) < ⌈Real.logb 2 ((s.n : ℝ) * P.ybar)⌉ ∧ 0 < ghat - rad then
      ⟨s.price, s.n, s.used + 1, s.stage + 1, s.mid, s.hi, (s.mid + s.hi) / 2, 0, 0, best', true⟩
    else if (s.stage : ℤ) < ⌈Real.logb 2 ((s.n : ℝ) * P.ybar)⌉ ∧ ghat + rad < 0 then
      ⟨s.price, s.n, s.used + 1, s.stage + 1, s.lo, s.mid, (s.lo + s.mid) / 2, 0, 0, best', true⟩
    else
      ⟨s.price, s.n, s.used + 1, s.stage, s.lo, s.hi, s.mid, v, g, s.best, false⟩

/-- The four sub-routine calls of one epoch of Algorithm 3 (lines 5–6, p.18):
`SearchOrderUpTo(α, N, C₁)`, `SearchOrderUpTo(β, N, C₁)` (with `ŷ` stored), and the two halves of
`EstimateGDifference(α, ŷ, β, ŷ′, N)` with the collected pairs `(o_t, δ_t)`. -/
inductive Phase where
  | search1 (s : SearchState)
  | search2 (yhat : ℝ) (s : SearchState)
  | est1 (yhat yhat' : ℝ) (obs1 : List (ℝ × ℝ))
  | est2 (yhat yhat' : ℝ) (obs1 obs2 : List (ℝ × ℝ))

/-- **Controller state** of Algorithm 3 (Chen, Wang & Zhou, SSRN 3750413, p.18): the active
interval `[L_ζ, U_ζ]` and the current sub-routine call. -/
structure State where
  lo : ℝ
  hi : ℝ
  phase : Phase

/-- The epoch budget `N_ζ` as a natural number, from the active interval. -/
noncomputable def epochBudget (P : Params) (L U : ℝ) : ℕ :=
  (budget P (trisectBeta L U - trisectAlpha L U)).toNat

/-- Line 2 of Algorithm 3: `ζ = 0`, `L₀ = p̲`, `U₀ = p̄`, and the first call
`SearchOrderUpTo(α₀, N₀, C₁)`. -/
noncomputable def initState (P : Params) : State :=
  ⟨P.low, P.high,
    .search1 (searchInit P (trisectAlpha P.low P.high) (epochBudget P P.low P.high))⟩

/-- The decision at a period with starting stock `x`: the pair `(price, order-up-to target)` and the
controller state after the instantaneous transitions (a call returning, an epoch ending with the
trisection update of lines 7–10). `fuel` bounds the number of instantaneous transitions; with
positive epoch budgets at most two occur per period. -/
noncomputable def act : ℕ → Params → State → ℝ → (ℝ × ℝ) × State
  | 0, P, st, x => ((P.low, x), st)
  | fuel + 1, P, st, x =>
    let a := trisectAlpha st.lo st.hi
    let bb := trisectBeta st.lo st.hi
    let n := epochBudget P st.lo st.hi
    match st.phase with
    | .search1 s =>
      match searchAction P s x with
      | some d => (d, st)
      | none => act fuel P ⟨st.lo, st.hi, .search2 (searchResult s) (searchInit P bb n)⟩ x
    | .search2 yh s =>
      match searchAction P s x with
      | some d => (d, st)
      | none => act fuel P ⟨st.lo, st.hi, .est1 yh (searchResult s) []⟩ x
    | .est1 yh yh' obs1 =>
      if obs1.length < n then ((a, yh), st)
      else act fuel P ⟨st.lo, st.hi, .est2 yh yh' obs1 []⟩ x
    | .est2 _yh yh' obs1 obs2 =>
      if obs2.length < n then ((bb, yh'), st)
      else
        let LU := trisect st.lo st.hi (deltaHat P a bb n obs1 obs2)
        act fuel P ⟨LU.1, LU.2, .search1 (searchInit P (trisectAlpha LU.1 LU.2)
          (epochBudget P LU.1 LU.2))⟩ x

/-- The fuel for instantaneous transitions per period. -/
def transitionFuel : ℕ := 8

/-- **One decision of the controller** of Algorithms 1–3 (Chen, Wang & Zhou, SSRN 3750413,
pp.13, 16, 18) at a period with starting stock `x`: the posted price, the order-up-to target, and
the state to be updated with the period's observation.

**Formalization Note.** The controller is a deterministic function of the parameters and the
observation history (starting stocks, its own decisions, sales). Drain steps post `p̲` with target
`x` (order nothing); they do not count toward a call's budget (footnote * of Algorithm 1). -/
noncomputable def step (P : Params) (st : State) (x : ℝ) : (ℝ × ℝ) × State :=
  act transitionFuel P st x

/-- **The controller's update** with the observation of a period: starting stock `x`, realized
stock level `level` and sales `o = min{D_t, level}`. In `EstimateGDifference` the pair
`(o_t, δ_t)` with leftover `δ_t = level − o_t` is recorded. -/
noncomputable def update (P : Params) (st : State) (x level o : ℝ) : State :=
  match st.phase with
  | .search1 s => ⟨st.lo, st.hi, .search1 (searchUpdate P s x level o)⟩
  | .search2 yh s => ⟨st.lo, st.hi, .search2 yh (searchUpdate P s x level o)⟩
  | .est1 yh yh' obs1 => ⟨st.lo, st.hi, .est1 yh yh' (obs1 ++ [(o, level - o)])⟩
  | .est2 yh yh' obs1 obs2 => ⟨st.lo, st.hi, .est2 yh yh' obs1 (obs2 ++ [(o, level - o)])⟩

end PricingInvCensored


