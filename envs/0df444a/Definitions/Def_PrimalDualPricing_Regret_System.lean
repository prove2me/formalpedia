-- Prove2me | Definitions.Def_PrimalDualPricing_Regret_System
-- name    : PrimalDualPricing_Regret_System
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T03:23:11.894419+00:00
-- url     : https://prove2.me/theorems/54f98bb8-869a-4fc2-970a-67f791ecf20d
-- title:
--   §2.2 and §4, pp. 7, 13–14 — Poisson arrivals, sales, stock-out, revenue $J^\pi_n$, regret $R^\pi_n$ and the events $A_k,B_k,C_k$
-- statement:
--   This file defines the stochastic system in which Algorithm 1 is evaluated, its revenue and regret, and the events used in the analysis.
--
--   **Arrivals.** On a probability space $(\Omega,\mathbb P)$, the processes $N_1,\dots,N_M$ are independent unit-rate Poisson processes with right-continuous paths, jointly measurable in time and outcome. In the $n$-th system, type-$m$ consumers arrive at rate $n\,d_m(P_m(t))$ when charged $P_m(t)$. The uncapped cumulative sales of type $m$ are
--   $$S_m(t)=N_m\Big(n\int_0^t d_m(P_m(s))\,ds\Big),\qquad S(t)=\sum_{m=1}^M S_m(t),$$
--   where $P$ is the price path of Algorithm 1. These are the sales of the modified system of §4, in which the policy runs until $T$.
--
--   **Revenue and regret.** The inventory is $\lfloor nc\rfloor$ units. The stock-out time is $\sigma=\inf\{t\in[0,T]:S(t)\ge\lfloor nc\rfloor\}$, with $\sigma=T$ if the inventory is not depleted. After $\sigma$ the choke price applies and nothing is sold. The revenue is
--   $$\sum_{m=1}^M\int_{(0,\sigma]}P_m(t)\,dS_m(t),$$
--   $J^\pi_n(T,c)$ is its expectation, and the regret (6) is
--   $$R^\pi_n(T,c)=1-\frac{J^\pi_n(T,c)}{J^D_n(T,c)}.$$
--
--   **Events** (p. 14). With the interval estimators of phase $k$:
--   - $A_k=\bigcap_m\{p^*_m\in[\underline p^{(k)}_m,\overline p^{(k)}_m]\}$;
--   - $B_k=\{z^*\in[\underline z^{(k)},\overline z^{(k)}]\}$;
--   - $C_k=\bigcap_m\{\mathcal P_m(z)\in[\underline p^{(k)}_m,\overline p^{(k)}_m]\ \forall z\in[\underline z^{(k)},\overline z^{(k)}]\}$.
--
--   The file also defines the pathwise integral $\int_0^t\sum_m d_m(P_m(s))\,ds$ used in Lemmas 6 and 8.
--
--   **Formalization Note** Each $N_m$ is a unit-rate Poisson process in the sense of the published `IsPoissonProcess`. Independence, right-continuity and joint measurability are added here. They make sales and revenue, which evaluate $N_m$ at random times, random variables. The real system holds $\lfloor nc\rfloor$ units because sales are integers; this equals $nc$ when $nc$ is an integer. Integrals along the price path are finite sums over its segments.
-- source:
--   Chen, Gallego, A Primal-dual Learning Algorithm for Personalized Dynamic Pricing with an Inventory Constraint, arXiv:1812.09234v3, p. 4 (Poisson arrivals), p. 5 (choke price after depletion), p. 7, §2.2, Eq. (6); pp. 13–14, §4 (modified system, events A_k, B_k, C_k)

import Mathlib
import Definitions.Def_ProcessingNetworks_Stability_BaselineAssumptions
import Definitions.Def_PrimalDualPricing_Regret_Model
import Definitions.Def_PrimalDualPricing_Regret_FluidValue
import Definitions.Def_PrimalDualPricing_Regret_Params
import Definitions.Def_PrimalDualPricing_Regret_Algorithm

namespace PrimalDualPricing.Regret

open MeasureTheory ProbabilityTheory Set

/-- `M` independent unit-rate Poisson processes on the probability space `(Ω, ℙ)` (§2, p. 4: the
type-`m` arrivals are independent Poisson processes; by the time change, type `m`'s arrivals under the
intensity `n d_m(P_m(t))` are `N m (n ∫_0^t d_m(P_m(s)) ds)`).

* `poisson`: each `N m` is a unit-rate Poisson process (`IsPoissonProcess`, published definition).
* `indep`: the `M` path-valued random variables are independent.
* `rightCont`, `jointMeas`: every path is right-continuous on `[0, ∞)` and `(t, ω) ↦ N m t ω` is jointly
  measurable. These regularity conditions are standard for a Poisson process; they are imposed so that
  quantities evaluating `N` at random times (sales, revenue) are random variables. -/
structure IndepPoissonPaths {Ω : Type*} [MeasureSpace Ω] {M : ℕ} (N : Fin M → ℝ → Ω → ℕ) : Prop where
  poisson : ∀ m, ProcessingNetworks.Stability.IsPoissonProcess (N m) 1
  indep : iIndep (fun m : Fin M => MeasurableSpace.comap (fun ω => fun t => N m t ω) inferInstance) ℙ
  rightCont : ∀ m ω, ∀ t, 0 ≤ t → ContinuousWithinAt (fun s => N m s ω) (Ici t) t
  jointMeas : ∀ m, Measurable (fun z : ℝ × Ω => N m z.1 z.2)

namespace Setting

variable {M : ℕ} (S : Setting M)

/-- The data the firm knows (p. 8): `T`, `c`, `p̲`, `p̄`, `z̄`. -/
def known : Known := ⟨S.T, S.c, S.pLow, S.pHigh, S.zHigh⟩

/-- The price path of Algorithm 1 with parameter `ε` in the `n`-th system on the outcome `ω`. -/
noncomputable def path {Ω : Type*} (eps : ℝ) (n : ℕ) (N : Fin M → ℝ → Ω → ℕ) (ω : Ω) :
    List (Segment M) :=
  schedule S.known S.d eps n (fun m t => N m t ω)

/-- The algorithm's state (interval estimators) at the beginning of phase `k` on the outcome `ω`. -/
noncomputable def stateOf {Ω : Type*} (eps : ℝ) (n : ℕ) (N : Fin M → ℝ → Ω → ℕ) (k : ℕ) (ω : Ω) :
    AlgState M :=
  stateAt S.known S.d eps n (fun m t => N m t ω) k

/-- Uncapped cumulative sales of type `m` up to time `t`, `S_m(t) = N_m(n ∫_0^t d_m(P_m(s)) ds)`: the
sales process of the modified system of §4 (pp. 13–14), in which the policy runs to `T` regardless
of the inventory. -/
noncomputable def salesM {Ω : Type*} (eps : ℝ) (n : ℕ) (N : Fin M → ℝ → Ω → ℕ) (m : Fin M) (t : ℝ)
    (ω : Ω) : ℕ :=
  salesOf S.d n (fun m t => N m t ω) (S.path eps n N ω) m t

/-- Uncapped aggregate sales `S(t) = ∑_m S_m(t)`. -/
noncomputable def totalSales {Ω : Type*} (eps : ℝ) (n : ℕ) (N : Fin M → ℝ → Ω → ℕ) (t : ℝ)
    (ω : Ω) : ℕ :=
  ∑ m, S.salesM eps n N m t ω

/-- The pathwise integral `∫_0^t ∑_m d_m(P_m(s)) ds` of the demand rates along the algorithm's price
path (a finite sum over its segments). -/
noncomputable def demandIntegral {Ω : Type*} (eps : ℝ) (n : ℕ) (N : Fin M → ℝ → Ω → ℕ) (t : ℝ)
    (ω : Ω) : ℝ :=
  ((S.path eps n N ω).map fun s => ∑ m, S.d m (s.price m) * s.overlap t).sum

/-- The inventory of the `n`-th system in units, `⌊n c⌋` (sales are integers; it is `n c` when `n c` is
an integer). -/
noncomputable def capacity (n : ℕ) : ℕ := ⌊(n : ℝ) * S.c⌋₊

/-- The stock-out time `σ = inf{t ∈ [0, T] : S(t) ≥ ⌊n c⌋}`, and `σ = T` if the inventory is not
depleted by `T`. -/
noncomputable def stockout {Ω : Type*} (eps : ℝ) (n : ℕ) (N : Fin M → ℝ → Ω → ℕ) (ω : Ω) : ℝ :=
  open Classical in
  if ∃ t ∈ Icc 0 S.T, S.capacity n ≤ S.totalSales eps n N t ω then
    sInf {t | t ∈ Icc 0 S.T ∧ S.capacity n ≤ S.totalSales eps n N t ω}
  else S.T

/-- The revenue of Algorithm 1 in the (real) `n`-th system on the outcome `ω`: every sale of type `m`
made at time `t ∈ (0, min(T, σ)]` earns the price `P_m(t)` then charged; after the stock-out time `σ`
the price is the choke price `p_∞` and nothing is sold. On each segment `(a, b]` with price vector `p`
this is `∑_m p_m (S_m(b ∧ σ) − S_m(a ∧ σ))`. -/
noncomputable def revenue {Ω : Type*} (eps : ℝ) (n : ℕ) (N : Fin M → ℝ → Ω → ℕ) (ω : Ω) : ℝ :=
  let σ := S.stockout eps n N ω
  ((S.path eps n N ω).map fun s => ∑ m, s.price m *
      ((S.salesM eps n N m (max 0 (min s.stop σ)) ω : ℝ)
        - (S.salesM eps n N m (max 0 (min s.start σ)) ω : ℝ))).sum

/-- The expected revenue `J^π_n(T, c)` of Algorithm 1 in the `n`-th system (p. 7). -/
noncomputable def expRevenue {Ω : Type*} [MeasureSpace Ω] (eps : ℝ) (n : ℕ)
    (N : Fin M → ℝ → Ω → ℕ) : ℝ :=
  ∫ ω, S.revenue eps n N ω

/-- The regret (6) (p. 7): `R^π_n(T, c) = 1 − J^π_n(T, c) / J^D_n(T, c)`, with `J^D_n` the fluid value of
the `n`-th system (demand `n d_m`, inventory `n c`). -/
noncomputable def regret {Ω : Type*} [MeasureSpace Ω] (eps : ℝ) (n : ℕ)
    (N : Fin M → ℝ → Ω → ℕ) : ℝ :=
  1 - S.expRevenue eps n N / fluidValueN S.d S.pinf S.c S.T n

/-- The event `A_k = ∩_m {p*_m ∈ [p̲_m^{(k)}, p̄_m^{(k)}]}` (p. 14). -/
def eventA {Ω : Type*} (eps : ℝ) (n : ℕ) (N : Fin M → ℝ → Ω → ℕ) (k : ℕ) : Set Ω :=
  {ω | ∀ m, S.pstar m ∈ Icc ((S.stateOf eps n N k ω).I.pLo m) ((S.stateOf eps n N k ω).I.pHi m)}

/-- The event `B_k = {z* ∈ [z̲^{(k)}, z̄^{(k)}]}` (p. 14). -/
def eventB {Ω : Type*} (eps : ℝ) (n : ℕ) (N : Fin M → ℝ → Ω → ℕ) (k : ℕ) : Set Ω :=
  {ω | S.zstar ∈ Icc (S.stateOf eps n N k ω).I.zLo (S.stateOf eps n N k ω).I.zHi}

/-- The event `C_k = ∩_m {𝒫_m(z) ∈ [p̲_m^{(k)}, p̄_m^{(k)}] ∀ z ∈ [z̲^{(k)}, z̄^{(k)}]}` (p. 14). -/
def eventC {Ω : Type*} (eps : ℝ) (n : ℕ) (N : Fin M → ℝ → Ω → ℕ) (k : ℕ) : Set Ω :=
  {ω | ∀ m, ∀ z ∈ Icc (S.stateOf eps n N k ω).I.zLo (S.stateOf eps n N k ω).I.zHi,
    S.P m z ∈ Icc ((S.stateOf eps n N k ω).I.pLo m) ((S.stateOf eps n N k ω).I.pHi m)}

end Setting

end PrimalDualPricing.Regret


