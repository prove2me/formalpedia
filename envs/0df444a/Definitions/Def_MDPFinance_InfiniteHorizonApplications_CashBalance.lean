-- Prove2me | Definitions.Def_MDPFinance_InfiniteHorizonApplications_CashBalance
-- name    : MDPFinance_InfiniteHorizonApplications_CashBalance
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:59:22.569336+00:00
-- url     : https://prove2.me/theorems/330fdd56-bd60-4032-b103-3952cc578757
-- title:
--   The infinite-horizon cash balance model
-- statement:
--   An inventory/cash-balance model: from level $x$, order up to $a \ge x$ at linear two-sided cost
--   $c(a-x)$ ($c_u$ per unit ordered, $c_d$ per unit disposed), incur a holding/shortage cost $L(a)$
--   on the post-order level, then a random demand $Z$ arrives, moving the state to $a - Z$. Rendered
--   via bespoke real-valued operators rather than the generic `Kernel`-based model, since the
--   transition is the explicit shift $a - Z$. This is the infinite-horizon extension (§7.6.2) of the
--   finite-horizon cash balance problem of chunk `02d` (§2.6.2).
--
--   **Moderation note.** Rewritten as a cost model with the model's own value functions. The draft's market lacked the book's assumptions on $L$ (convex, $L(0)=0$, $L(x)/|x|\to\infty$) and on $Z$ (finite expectation), had $c_u,c_d\ge 0$ instead of $>0$, and its value functionals were real Bochner recursions of *negative* costs with a `limsup`, while Theorem 7.6.1's formula is the book's cost formula. Now: policies $\pi\in F^\infty$ (`IsCBPolicy`), costs $V_n^\pi$, $J_n=\inf_\pi V_n^\pi$, $J_\infty^\pi=\sup_n V_n^\pi$, $J_\infty=\inf_\pi J_\infty^\pi$ and $J=\lim_n J_n$ in $[0,\infty]$ (Lebesgue integrals), and the $(S^-,S^+)$-rule `cbRule`.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 225, §7.6.2 model data (restated from §2.6.2)

import Mathlib

open MeasureTheory ProbabilityTheory

namespace MDPFinance.InfiniteHorizonApplications

open scoped ENNReal

/-- The infinite-horizon cash balance model (Bäuerle–Rieder, §2.6.2, p. 46-47, PDF 61-62,
restated for the infinite-horizon extension of §7.6.2, p. 225, PDF 236): state `x ∈ ℝ` (cash
level), new cash level `a ∈ ℝ` chosen at linear transfer cost `c(a-x)` (`c(z) := c_u z^+ + c_d
z^-`, `c_u, c_d > 0`), holding cost `L(a)` (`L ≥ 0`, `L(0) = 0`, convex, `L(x)/|x| → ∞`), then an
i.i.d. cash change `Z` with finite expectation (law `μ_Z`) moves the state to `a - Z`; discount
`β ∈ (0,1)`. Treated, as in the book, as a cost-minimization problem with costs in `[0,∞]`. -/
structure CashBalanceMarket where
  cu : ℝ
  cd : ℝ
  hcu : 0 < cu
  hcd : 0 < cd
  L : ℝ → ℝ
  hL_nonneg : ∀ x, 0 ≤ L x
  hL0 : L 0 = 0
  hL_convex : ConvexOn ℝ Set.univ L
  hL_coercive : Filter.Tendsto (fun x => L x / |x|) Filter.atTop Filter.atTop ∧
    Filter.Tendsto (fun x => L x / |x|) Filter.atBot Filter.atTop
  hL_meas : Measurable L
  μZ : Measure ℝ
  isProbμZ : IsProbabilityMeasure μZ
  hZ_int : Integrable id μZ
  β : ℝ
  hβ0 : 0 < β
  hβ1 : β < 1

/-- `c(z) := c_u z^+ + c_d z^-`. -/
noncomputable def CashBalanceMarket.c (Mk : CashBalanceMarket) (z : ℝ) : ℝ :=
  Mk.cu * max z 0 + Mk.cd * max (-z) 0

/-- A policy `π = (f_0, f_1, …) ∈ F^∞`: measurable decision rules `f_k : ℝ → ℝ` giving the new
cash level (`D(x) := A = ℝ`, all actions admissible). -/
def IsCBPolicy (π : ℕ → ℝ → ℝ) : Prop := ∀ k, Measurable (π k)

/-- The `n`-stage expected discounted cost `V_n^π(x) := 𝔼^π_x[Σ_{k<n} β^k (c(A_k - X_k) +
L(A_k))] ∈ [0,∞]` of a policy `π`, by the reward iteration (peeling `f_0` off). -/
noncomputable def CashBalanceMarket.Vpi (Mk : CashBalanceMarket) (π : ℕ → ℝ → ℝ) :
    ℕ → ℝ → ℝ≥0∞
  | 0, _ => 0
  | (n + 1), x =>
      ENNReal.ofReal (Mk.c (π 0 x - x) + Mk.L (π 0 x)) + ENNReal.ofReal Mk.β *
        ∫⁻ z, Vpi Mk (fun k => π (k + 1)) n (π 0 x - z) ∂Mk.μZ

/-- `J_n(x) := inf_{π ∈ F^∞} V_n^π(x)`, the `n`-stage minimal cost. -/
noncomputable def CashBalanceMarket.Jn (Mk : CashBalanceMarket) (n : ℕ) (x : ℝ) : ℝ≥0∞ :=
  ⨅ π ∈ {π : ℕ → ℝ → ℝ | IsCBPolicy π}, Mk.Vpi π n x

/-- `J_∞^π(x) := lim_n V_n^π(x) = sup_n V_n^π(x)` (costs are nonnegative, so the sequence is
increasing), the infinite-horizon expected discounted cost of `π`. -/
noncomputable def CashBalanceMarket.Jinfpi (Mk : CashBalanceMarket) (π : ℕ → ℝ → ℝ) (x : ℝ) :
    ℝ≥0∞ :=
  ⨆ n, Mk.Vpi π n x

/-- `J_∞(x) := inf_{π ∈ F^∞} J_∞^π(x)`, the minimal infinite-horizon cost (Eq. (7.1) as a
cost). -/
noncomputable def CashBalanceMarket.Jinf (Mk : CashBalanceMarket) (x : ℝ) : ℝ≥0∞ :=
  ⨅ π ∈ {π : ℕ → ℝ → ℝ | IsCBPolicy π}, Mk.Jinfpi π x

/-- `J(x) := lim_n J_n(x) = sup_n J_n(x)`, the limit value function (`J_n` is increasing in
`n`). -/
noncomputable def CashBalanceMarket.Jlim (Mk : CashBalanceMarket) (x : ℝ) : ℝ≥0∞ :=
  ⨆ n, Mk.Jn n x

/-- The `(S^-,S^+)` decision rule (7.4): transfer up to `S^-` below `S^-`, do nothing between,
transfer down to `S^+` above `S^+`. -/
noncomputable def cbRule (Sm Sp : ℝ) (x : ℝ) : ℝ :=
  if x < Sm then Sm else if x ≤ Sp then x else Sp

end MDPFinance.InfiniteHorizonApplications


