-- Prove2me | Definitions.Def_owmr_network_model
-- name    : owmr_network_model
-- status  : Definition
-- author  : @Ming Hu
-- created : 2026-11-16T00:53:13.27799+00:00
-- url     : https://prove2.me/theorems/7fda75b6-2ab5-49e2-bbe1-1133a41d0022
-- title:
--   OWMR model: dynamics, period cost, $C(\pi)$, and $\mathrm{OPT}$
-- statement:
--   An **OWMR network** with $n$ retailers consists of a supplier lead time $L_0\in\mathbb N$, retailer lead times $L_i\in\mathbb N$, a probability measure $\mu$ on $[0,\infty)^n$ (the common law of the demand vectors $D_t=(D_{1,t},\dots,D_{n,t})$, which are i.i.d. over periods $t=0,1,2,\dots$, with possibly dependent components), setup costs $K_0$ (supplier) and $K_i$ (retailers), holding rates $h$ (warehouse) and $H_i$ (retailers), and a common backlog penalty $p$. The **standing assumptions** are $0<\mathbb E D_{i,t}<\infty$ for every $i$, $K_0,K_i\ge0$, and $h,H_i,p>0$. Write $K_{\max}=\max_iK_i$.
--
--   In period $t$, scheduled shipments arrive; the warehouse places a supplier order $q_{0,t}$, which arrives in period $t+L_0$; it dispatches $q_{i,t}$ to retailer $i$, which arrives in period $t+L_i$; then demand occurs. A **valid initial state** prescribes warehouse stock $W_{-1}\ge0$, retailer net inventories $I_{i,-1}$, and nonnegative pipeline quantities arriving at the warehouse in periods $t<L_0$ and at retailer $i$ in periods $t<L_i$. Inventories evolve by
--
--   $$W_t=W_{t-1}+q_{0,t-L_0}-\sum_iq_{i,t},\qquad I_{i,t}=I_{i,t-1}+q_{i,t-L_i}-D_{i,t},$$
--
--   and the period cost (1) is
--
--   $$c_t=K_0\mathbf 1_{\{q_{0,t}>0\}}+\sum_iK_i\mathbf 1_{\{q_{i,t}>0\}}+hW_t+\sum_i\big(H_iI_{i,t}^++pI_{i,t}^-\big).$$
--
--   A **policy** chooses $q_{0,t}$ and $q_{i,t}$ from the demand history and auxiliary randomness $u$, drawn from a probability law $\nu$ independent of all demands. It is **nonanticipative** if the decisions of period $t$ depend on demands only through $D_0,\dots,D_{t-1}$, and **feasible** if orders and dispatches are nonnegative and $\sum_iq_{i,t}\le W_{t-1}+q_{0,t-L_0}$. The long-run average cost and the optimal cost (2) are
--
--   $$C(\pi)=\limsup_{T\to\infty}\frac1T\,\mathbb E_\pi\sum_{t=0}^{T-1}c_t,\qquad\mathrm{OPT}=\inf_{\pi\ \text{nonanticipative and feasible}}C(\pi).$$
--
--   Every guarantee of the mission compares the cost of a constructed policy with $\mathrm{OPT}$.
--
--   **Formalization Note** Demand vectors have type `Fin n → ℝ≥0`. The expected cost of periods $0,\dots,T-1$ is the lower Lebesgue integral of $\sum_{t<T}\max(c_t,0)$, as an extended nonnegative real, under $\nu\otimes\mu^{\otimes T}$, with the history $D_0,\dots,D_{T-1}$ extended by zero vectors (the costs of these periods involve no later demand); for feasible policies $c_t\ge0$. Hence $C(\pi),\mathrm{OPT}\in[0,\infty]$. In $\mathrm{OPT}$ the infimum ranges over every auxiliary probability space $(U,\nu)$ with `U : Type` and every measurable, nonanticipative policy that is feasible for every $u$ and every demand sequence. A deterministic policy is a policy on the one-point space.
-- source:
--   M. Hu, "A 5/2 Guarantee for Echelon Stock (s,S) Policies in One-Warehouse Multi-Retailer Systems", working paper (manuscript of November 2026), Section 3 (Model and Main Results), pp. 6-7, equations (1) and (2).

import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.LiminfLimsup

/-!
# The one-warehouse multi-retailer (OWMR) model

Source: M. Hu, "A 5/2 Guarantee for Echelon Stock (s,S) Policies in One-Warehouse
Multi-Retailer Systems", Section 3 (Model and Main Results), equations (1) and (2).

A warehouse replenishes retailers `i : Fin n` from an outside supplier in discrete periods
`t = 0, 1, 2, …`. In each period: (1) shipments sent earlier arrive as scheduled; (2) the warehouse
may place a supplier order `q₀,t`; (3) it may dispatch `q_{i,t}` to each retailer from the stock
available in that period; (4) demand `D_{i,t}` occurs and is met from retailer stock or backlogged;
holding and backlog costs are charged on the resulting inventories. A supplier order placed in
period `t` arrives in period `t + L₀` (in time for that period's dispatches) and a dispatch to
retailer `i` in period `t` arrives in period `t + L_i` (in time for that period's demand).

The demand vectors `D_t = (D_{1,t}, …, D_{n,t})` are i.i.d. over periods with law `μ`; the
components of one vector may be dependent.
-/

open MeasureTheory
open scoped ENNReal NNReal

noncomputable section

namespace OWMR

/-- A demand vector: one nonnegative demand per retailer. -/
abbrev DemandVec (n : ℕ) := Fin n → ℝ≥0

/-- Primitive data of an OWMR network with `n` retailers. -/
structure Network (n : ℕ) where
  /-- supplier lead time `L₀` -/
  L0 : ℕ
  /-- retailer lead times `L_i` -/
  L : Fin n → ℕ
  /-- common law of the i.i.d. per-period demand vectors `D_t` -/
  μ : Measure (DemandVec n)
  /-- `μ` is a probability measure -/
  isProb : IsProbabilityMeasure μ
  /-- supplier setup cost `K₀` (per positive supplier order) -/
  K0 : ℝ
  /-- retailer setup costs `K_i` (per positive dispatch to retailer `i`) -/
  K : Fin n → ℝ
  /-- warehouse holding cost rate `h` -/
  h : ℝ
  /-- retailer holding cost rates `H_i` -/
  H : Fin n → ℝ
  /-- common backlog penalty rate `p` -/
  p : ℝ

attribute [instance] Network.isProb

variable {n : ℕ}

/-- The standing assumptions of Section 3: `0 < 𝔼 D_{i,t} < ∞` for every retailer,
`K₀, K_i ≥ 0`, `h > 0`, `H_i > 0`, `p > 0`. (Nonnegativity of demand is built into
`DemandVec`; finiteness of the lead times is built into `ℕ`.) -/
structure Network.Standing (N : Network n) : Prop where
  mean_pos : ∀ i, 0 < ∫⁻ x, (x i : ℝ≥0∞) ∂N.μ
  mean_lt_top : ∀ i, ∫⁻ x, (x i : ℝ≥0∞) ∂N.μ < ∞
  K0_nonneg : 0 ≤ N.K0
  K_nonneg : ∀ i, 0 ≤ N.K i
  h_pos : 0 < N.h
  H_pos : ∀ i, 0 < N.H i
  p_pos : 0 < N.p

/-- `K_max = max_i K_i`. -/
def Network.Kmax (N : Network n) : ℝ := ⨆ i, N.K i

/-- A prescribed initial state: warehouse stock `W`, retailer net inventories `I_i`, and the
pipelines, indexed by arrival period: `supPipe t` arrives at the warehouse in period `t`
(only `t < L₀` is used) and `retPipe i t` arrives at retailer `i` in period `t` (only `t < L_i`
is used). -/
structure InitState (n : ℕ) where
  W : ℝ
  I : Fin n → ℝ
  supPipe : ℕ → ℝ
  retPipe : Fin n → ℕ → ℝ

/-- A valid initial state has nonnegative warehouse stock and nonnegative pipeline quantities. -/
def InitState.Valid (x : InitState n) : Prop :=
  0 ≤ x.W ∧ (∀ t, 0 ≤ x.supPipe t) ∧ ∀ i t, 0 ≤ x.retPipe i t

/-- A policy with auxiliary randomness `u : U`: the supplier order `q₀,t = order t u D` and the
dispatches `q_{i,t} = dispatch t u D i` in period `t`, as functions of `u` and of the whole demand
sequence `D = (D_s)_{s ∈ ℕ}`. Nonanticipativity is the separate predicate
`Policy.Nonanticipative`. -/
structure Policy (n : ℕ) (U : Type) where
  order : ℕ → U → (ℕ → DemandVec n) → ℝ
  dispatch : ℕ → U → (ℕ → DemandVec n) → Fin n → ℝ

namespace Policy

variable {U : Type}

/-- Period-`t` decisions depend on the demand sequence only through `D_0, …, D_{t-1}`. -/
def Nonanticipative (π : Policy n U) : Prop :=
  ∀ (t : ℕ) (u : U) (d d' : ℕ → DemandVec n), (∀ s < t, d s = d' s) →
    π.order t u d = π.order t u d' ∧ π.dispatch t u d = π.dispatch t u d'

/-- Measurability of every decision in `(u, D)`. -/
def IsMeasurable [MeasurableSpace U] (π : Policy n U) : Prop :=
  ∀ t : ℕ, Measurable (fun ω : U × (ℕ → DemandVec n) => π.order t ω.1 ω.2) ∧
    ∀ i, Measurable (fun ω : U × (ℕ → DemandVec n) => π.dispatch t ω.1 ω.2 i)

/-- Quantity arriving at the warehouse in period `t`. -/
def supArrival (N : Network n) (x : InitState n) (π : Policy n U) (u : U)
    (d : ℕ → DemandVec n) (t : ℕ) : ℝ :=
  if t < N.L0 then x.supPipe t else π.order (t - N.L0) u d

/-- Quantity arriving at retailer `i` in period `t`. -/
def retArrival (N : Network n) (x : InitState n) (π : Policy n U) (u : U)
    (d : ℕ → DemandVec n) (i : Fin n) (t : ℕ) : ℝ :=
  if t < N.L i then x.retPipe i t else π.dispatch (t - N.L i) u d i

/-- Warehouse stock `W_t` after the dispatches of period `t`:
`W_t = W_{t-1} + q_{0,t-L₀} - ∑_i q_{i,t}`. -/
def whStock (N : Network n) (x : InitState n) (π : Policy n U) (u : U)
    (d : ℕ → DemandVec n) (t : ℕ) : ℝ :=
  x.W + ∑ s ∈ Finset.range (t + 1), (supArrival N x π u d s - ∑ i, π.dispatch s u d i)

/-- Stock available for dispatch in period `t`: `W_{t-1}` plus the supplier arrival of
period `t`. -/
def whAvailable (N : Network n) (x : InitState n) (π : Policy n U) (u : U)
    (d : ℕ → DemandVec n) (t : ℕ) : ℝ :=
  x.W + ∑ s ∈ Finset.range t, (supArrival N x π u d s - ∑ i, π.dispatch s u d i)
    + supArrival N x π u d t

/-- Retailer net inventory `I_{i,t}` after the demand of period `t`:
`I_{i,t} = I_{i,t-1} + q_{i,t-L_i} - D_{i,t}`. -/
def netInv (N : Network n) (x : InitState n) (π : Policy n U) (u : U)
    (d : ℕ → DemandVec n) (i : Fin n) (t : ℕ) : ℝ :=
  x.I i + ∑ s ∈ Finset.range (t + 1), (retArrival N x π u d i s - (d s i : ℝ))

/-- The period cost (1):
`c_t = K₀ 1{q₀,t > 0} + ∑_i K_i 1{q_{i,t} > 0} + h W_t + ∑_i (H_i I_{i,t}⁺ + p I_{i,t}⁻)`. -/
def periodCost (N : Network n) (x : InitState n) (π : Policy n U) (u : U)
    (d : ℕ → DemandVec n) (t : ℕ) : ℝ :=
  N.K0 * (if 0 < π.order t u d then 1 else 0)
    + ∑ i, N.K i * (if 0 < π.dispatch t u d i then 1 else 0)
    + N.h * whStock N x π u d t
    + ∑ i, (N.H i * max (netInv N x π u d i t) 0 + N.p * max (-netInv N x π u d i t) 0)

/-- Feasibility: nonnegative orders and dispatches, and dispatches never exceeding the warehouse
stock available in that period (for every value of the auxiliary randomness and every demand
sequence). -/
def Feasible (N : Network n) (x : InitState n) (π : Policy n U) : Prop :=
  ∀ (u : U) (d : ℕ → DemandVec n) (t : ℕ), 0 ≤ π.order t u d ∧ (∀ i, 0 ≤ π.dispatch t u d i) ∧
    ∑ i, π.dispatch t u d i ≤ whAvailable N x π u d t

end Policy

/-- Extension of a finite history `z_0, …, z_{T-1}` to a sequence, by zeros after `T`. -/
def padHist {α : Type} [Zero α] (T : ℕ) (z : Fin T → α) : ℕ → α :=
  fun t => if ht : t < T then z ⟨t, ht⟩ else 0

/-- Expected total cost of periods `0, …, T-1`: the auxiliary randomness has law `ν`,
independent of the demands, and `D_0, …, D_{T-1}` are i.i.d. with law `μ`. (Costs of periods
before `T` only involve these demands.) -/
def expCost {U : Type} [MeasurableSpace U] (N : Network n) (x : InitState n) (π : Policy n U)
    (ν : Measure U) (T : ℕ) : ℝ≥0∞ :=
  ∫⁻ ω, ∑ t ∈ Finset.range T, ENNReal.ofReal (π.periodCost N x ω.1 (padHist T ω.2) t)
    ∂(ν.prod (Measure.pi fun _ : Fin T => N.μ))

/-- The long-run average cost (2): `C(π) = limsup_{T→∞} T⁻¹ 𝔼_π ∑_{t<T} c_t`. -/
def avgCost {U : Type} [MeasurableSpace U] (N : Network n) (x : InitState n) (π : Policy n U)
    (ν : Measure U) : ℝ≥0∞ :=
  Filter.limsup (fun T : ℕ => (T : ℝ≥0∞)⁻¹ * expCost N x π ν T) Filter.atTop

/-- The optimal cost (2): the infimum of `C(π)` over all nonanticipative, feasible
(measurable) policies, which may use auxiliary randomness independent of all demands. -/
def OPT (N : Network n) (x : InitState n) : ℝ≥0∞ :=
  ⨅ (U : Type) (_ : MeasurableSpace U) (ν : Measure U) (_ : IsProbabilityMeasure ν)
    (π : Policy n U) (_ : π.Nonanticipative ∧ π.IsMeasurable ∧ π.Feasible N x),
    avgCost N x π ν

/-- A deterministic policy: decisions are functions of the demand sequence only. -/
structure DetPolicy (n : ℕ) where
  order : ℕ → (ℕ → DemandVec n) → ℝ
  dispatch : ℕ → (ℕ → DemandVec n) → Fin n → ℝ

/-- A deterministic policy as a policy with trivial auxiliary randomness. -/
def DetPolicy.toPolicy (π : DetPolicy n) : Policy n Unit :=
  ⟨fun t _ d => π.order t d, fun t _ d => π.dispatch t d⟩

/-- `C(π)` for a deterministic policy. -/
def DetPolicy.avgCost (N : Network n) (x : InitState n) (π : DetPolicy n) : ℝ≥0∞ :=
  OWMR.avgCost N x π.toPolicy (Measure.dirac ())

end OWMR


