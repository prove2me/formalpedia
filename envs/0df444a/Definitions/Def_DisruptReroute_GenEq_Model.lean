-- Prove2me | Definitions.Def_DisruptReroute_GenEq_Model
-- name    : DisruptReroute_GenEq_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T04:30:43.532492+00:00
-- url     : https://prove2.me/theorems/8d2e43b2-1e5f-4892-89d4-dc777831d35f
-- title:
--   §§2–4, pp. 9–23 — supply chain markets, ex-post net worth and general equilibrium
-- statement:
--   A **supply chain network** adds reservation prices $p^m$, initial equity $w_i$, safety stock $\theta_i^m$, holding costs $\lambda_i^m$, realized net production costs $c_i$, rerouting costs $\iota_i^m$, back-order costs $b_i^m$, and demand and supply functions $d_m,s_m$ to the order quantities $o^m_{ij}$. The inverse market functions $d_m^{-1},s_m^{-1}$ are linked to those functions by the standing conditions.
--
--   Undelivered orders and unserved demands give $\bar r_i^m=\sum_j\gamma^m_{ij}$ and $\bar\sigma_i^m=(\sum_j\delta^m_{ji}-\theta_i^m)^+$. For each market, an **efficient rerouted supply** or **efficient switched demand** maximizes the paper's integral objective over the capacity box and allocates proportionally among firms quoting the same price or cost. A **partial equilibrium** requires an efficient allocation and a best response to every nonnegative unilateral price or cost deviation. The paper's partial-equilibrium net worth, $e_i^*(\Gamma,\Delta)$, uses the aggregate market quantities inside the inverse prices.
--
--   The **market stable state** is both the limit of the default cascade started at zero and a fixed point of the updates $\Phi^*,\Psi^*$. A **general equilibrium** combines that state with partial equilibria in every rerouting and sourcing market.
--
--   These definitions keep the market optimization, strategic choice, and default dynamics separate, allowing the propositions to assert their nontrivial connections.
--
--   **Formalization Note** Firms and goods use zero-based finite indices. Assumption 2.1 is applied to positive-order suppliers. Orders, stocks, holding, rerouting and back-order costs are nonnegative; initial equity is nonnegative. Inverse supply is nonnegative on the quantities used, with $s_m(0)\le 0$. Prices and costs for firms outside an active market follow the convention on p. 23. The integrals are over finite, bounded market boxes.
-- source:
--   Birge, Capponi & Chen, Disruption and Rerouting in Supply Chain Networks, SSRN 3669363 (version of October 31, 2022; Oper. Res. 2023, DOI 10.1287/opre.2022.2409), pp. 9–23, Assumptions 2.1–2.3 and 4.1–4.2, Definitions 2.1–2.2 and 3.1–3.4, (1)–(18); E-Companion, EC pp. 4, 9, (A.6), (A.14)

import Mathlib
import Definitions.Def_DisruptReroute_GenEq_OrderNetwork

open MeasureTheory Filter

namespace DisruptReroute.GenEq

noncomputable section

abbrev Matrix (N M : ℕ) := Fin M → Fin N → Fin N → ℝ
abbrev Profile (N M : ℕ) := Fin M → Fin N → ℝ

/-- The order network and the prices, inventories, costs, and market functions
    of §§2–4. The inverse market functions are data constrained by `Standing`. -/
structure Network (N M : ℕ) extends OrderNetwork N M where
  p : Fin M → ℝ
  w : Fin N → ℝ
  θ : Fin M → Fin N → ℝ
  holding : Fin M → Fin N → ℝ
  c : Fin N → ℝ
  ι : Fin M → Fin N → ℝ
  b : Fin M → Fin N → ℝ
  d : Fin M → ℝ → ℝ
  s : Fin M → ℝ → ℝ
  dInv : Fin M → ℝ → ℝ
  sInv : Fin M → ℝ → ℝ

def totalOrders {N M : ℕ} (net : Network N M) (m : Fin M) : ℝ :=
  ∑ i : Fin N, ∑ j : Fin N, net.o m i j

/-- The paper's standing market hypotheses, with the supplier reading of
    Assumption 2.1 and the inverse supply's required nonnegative domain. -/
def Standing {N M : ℕ} (net : Network N M) : Prop :=
  0 < N ∧ 0 < M ∧
  (∀ m i j, 0 ≤ net.o m i j) ∧
  (∀ i, 0 ≤ net.w i) ∧
  (∀ m i, 0 ≤ net.θ m i ∧ 0 ≤ net.holding m i ∧ 0 ≤ net.ι m i ∧ 0 ≤ net.b m i) ∧
  (∀ m i j, 0 < net.o m j i → net.θ m i ≤ net.o m j i) ∧
  (∀ m, 0 ≤ net.p m ∧
    ContDiffOn ℝ 2 (net.d m) {x | 0 < net.d m x} ∧
    ConcaveOn ℝ {x | 0 < net.d m x} (net.d m) ∧
    StrictAntiOn (net.d m) {x | 0 < net.d m x} ∧
    (∀ x, net.p m ≤ x → net.d m x = 0) ∧
    totalOrders net m ≤ net.d m 0 ∧
    (∀ x ∈ Set.Icc 0 (net.d m 0),
      net.dInv m x ∈ Set.Icc 0 (net.p m) ∧ net.d m (net.dInv m x) = x) ∧
    net.dInv m 0 = net.p m ∧
    ContinuousOn (net.dInv m) (Set.Icc 0 (net.d m 0))) ∧
  (∀ m, ContDiff ℝ 2 (net.s m) ∧
    ConcaveOn ℝ Set.univ (net.s m) ∧
    StrictMono (net.s m) ∧
    (∀ x, 0 < x → 0 < net.s m x) ∧
    net.s m 0 ≤ 0 ∧
    (∀ x ∈ Set.Icc 0 (totalOrders net m),
      0 ≤ net.sInv m x ∧ net.s m (net.sInv m x) = x) ∧
    ContinuousOn (net.sInv m) (Set.Icc 0 (totalOrders net m)))

def rbar {N M : ℕ} (Γ : Matrix N M) (m : Fin M) (i : Fin N) : ℝ :=
  ∑ j : Fin N, Γ m i j

def sbar {N M : ℕ} (net : Network N M) (Δ : Matrix N M)
    (m : Fin M) (i : Fin N) : ℝ :=
  max 0 ((∑ j : Fin N, Δ m j i) - net.θ m i)

def active (N : ℕ) (cap : Fin N → ℝ) : Finset (Fin N) :=
  Finset.univ.filter (fun i => 0 < cap i)

def marketTotal {N : ℕ} (cap : Fin N → ℝ) : ℝ :=
  ∑ i ∈ active N cap, cap i

def inBox {N : ℕ} (cap x : Fin N → ℝ) : Prop :=
  ∀ i, if i ∈ active N cap then 0 ≤ x i ∧ x i ≤ cap i else x i = 0

def proportional {N : ℕ} (cap price x : Fin N → ℝ) : Prop :=
  ∀ i ∈ active N cap, ∀ j ∈ active N cap,
    price i = price j → x i * cap j = x j * cap i

def rerouteObjective {N M : ℕ} (net : Network N M) (m : Fin M)
    (cap price x : Fin N → ℝ) : ℝ :=
  (∫ t in (0 : ℝ)..(∑ i ∈ active N cap, x i), net.dInv m t) -
    ∑ i ∈ active N cap, price i * x i

def switchObjective {N M : ℕ} (net : Network N M) (m : Fin M)
    (cap cost x : Fin N → ℝ) : ℝ :=
  (∑ i ∈ active N cap, cost i * x i) -
    ∫ t in (0 : ℝ)..(∑ i ∈ active N cap, x i), net.sInv m t

/-- Definition 2.1: argmax of consumer surplus on the whole capacity box,
    intersected with proportional allocation among equal-price firms. -/
def EfficientR {N M : ℕ} (net : Network N M) (m : Fin M)
    (cap price x : Fin N → ℝ) : Prop :=
  inBox cap x ∧ proportional cap price x ∧
  ∀ y, inBox cap y →
    rerouteObjective net m cap price y ≤ rerouteObjective net m cap price x

/-- Definition 2.2: argmax of the sourcing objective on the whole capacity box,
    intersected with proportional allocation among equal-cost firms. -/
def EfficientS {N M : ℕ} (net : Network N M) (m : Fin M)
    (cap cost x : Fin N → ℝ) : Prop :=
  inBox cap x ∧ proportional cap cost x ∧
  ∀ y, inBox cap y →
    switchObjective net m cap cost y ≤ switchObjective net m cap cost x

/-- Equation (A.6), the proposed greedy rerouting allocation. -/
def greedyR {N M : ℕ} (net : Network N M) (m : Fin M)
    (cap price : Fin N → ℝ) (i : Fin N) : ℝ :=
  min (cap i) ((cap i /
    (∑ j ∈ (active N cap).filter (fun j => price j = price i), cap j)) *
    max 0 (net.d m (price i) -
      ∑ j ∈ (active N cap).filter (fun j => price j < price i), cap j))

/-- Equation (A.14), the proposed greedy switching allocation. -/
def greedyS {N M : ℕ} (net : Network N M) (m : Fin M)
    (cap cost : Fin N → ℝ) (i : Fin N) : ℝ :=
  min (cap i) ((cap i /
    (∑ j ∈ (active N cap).filter (fun j => cost j = cost i), cap j)) *
    max 0 (net.s m (cost i) -
      ∑ j ∈ (active N cap).filter (fun j => cost j > cost i), cap j))

/-- Definition 3.1, with the price-dependent summand of (10) as payoff. -/
def PartialR {N M : ℕ} (net : Network N M) (m : Fin M)
    (cap price : Fin N → ℝ) : Prop :=
  (∀ i ∈ active N cap, 0 ≤ price i) ∧
  (∃ x, EfficientR net m cap price x) ∧
  ∀ i ∈ active N cap, ∀ price' : ℝ, 0 ≤ price' →
    ∀ x, EfficientR net m cap price x →
    ∀ x', EfficientR net m cap (Function.update price i price') x' →
      (price i - net.ι m i) * x i ≥ (price' - net.ι m i) * x' i

/-- Definition 3.2, with the switching-dependent summand of (10) as payoff. -/
def PartialS {N M : ℕ} (net : Network N M) (m : Fin M)
    (cap cost : Fin N → ℝ) : Prop :=
  (∀ i ∈ active N cap, 0 ≤ cost i) ∧
  (∃ x, EfficientS net m cap cost x) ∧
  ∀ i ∈ active N cap, ∀ cost' : ℝ, 0 ≤ cost' →
    ∀ x, EfficientS net m cap cost x →
    ∀ x', EfficientS net m cap (Function.update cost i cost') x' →
      (net.b m i - cost i) * x i ≥ (net.b m i - cost') * x' i

def priceStar {N M : ℕ} (net : Network N M) (Γ : Matrix N M)
    (m : Fin M) : ℝ :=
  net.dInv m (marketTotal (rbar Γ m))

def costStar {N M : ℕ} (net : Network N M) (Δ : Matrix N M)
    (m : Fin M) : ℝ :=
  net.sInv m (marketTotal (sbar net Δ m))

/-- Equation (10), evaluated at the full-capacity partial-equilibrium
    allocations and the aggregate market prices in (18). -/
def eStar {N M : ℕ} (net : Network N M) (Γ Δ : Matrix N M)
    (i : Fin N) : ℝ :=
  net.w i +
  (∑ m : Fin M, net.p m * ((∑ j : Fin N, net.o m i j) - rbar Γ m i)) -
  net.c i -
  (∑ m : Fin M, net.θ m i * net.holding m i) +
  (∑ m : Fin M, (priceStar net Γ m * rbar Γ m i - net.ι m i * rbar Γ m i)) -
  (∑ m : Fin M, net.b m i * sbar net Δ m i) +
  (∑ m : Fin M, (net.b m i * sbar net Δ m i -
    costStar net Δ m * sbar net Δ m i))

def PhiStar {N M : ℕ} (net : Network N M) (Γ Δ : Matrix N M) : Matrix N M :=
  fun m i j => if 0 ≤ eStar net Γ Δ j then 0 else net.o m i j

def PsiStar {N M : ℕ} (net : Network N M) (Γ Δ : Matrix N M) : Matrix N M :=
  fun m i j => if 0 ≤ eStar net Γ Δ i then 0 else net.o m i j

def cascade {N M : ℕ} (net : Network N M) (n : ℕ) :
    Matrix N M × Matrix N M :=
  (fun q : Matrix N M × Matrix N M =>
    (PhiStar net q.1 q.2, PsiStar net q.1 q.2))^[n] (0, 0)

/-- Definition 3.3: both the limit from zero and the fixed-point equation. -/
def IsMarketStableState {N M : ℕ} (net : Network N M)
    (Γ Δ : Matrix N M) : Prop :=
  Tendsto (cascade net) atTop (nhds (Γ, Δ)) ∧
  (Γ, Δ) = (PhiStar net Γ Δ, PsiStar net Γ Δ)

/-- Definition 3.4, including the off-market price convention of p. 23. -/
def IsGeneralEquilibrium {N M : ℕ} (net : Network N M)
    (prices costs : Profile N M) (Γ Δ : Matrix N M) : Prop :=
  (∀ m, PartialR net m (rbar Γ m) (prices m) ∧
    ∀ i ∉ active N (rbar Γ m), prices m i = priceStar net Γ m) ∧
  (∀ m, PartialS net m (sbar net Δ m) (costs m) ∧
    ∀ i ∉ active N (sbar net Δ m), costs m i = costStar net Δ m) ∧
  IsMarketStableState net Γ Δ

def Admissible {N M : ℕ} (net : Network N M) (Γ : Matrix N M) : Prop :=
  ∀ m i j, Γ m i j = 0 ∨ Γ m i j = net.o m i j

def InBounds {N M : ℕ} (net : Network N M) (Γ : Matrix N M) : Prop :=
  ∀ m i j, 0 ≤ Γ m i j ∧ Γ m i j ≤ net.o m i j

/-- Assumption 4.1 at the endogenous total, stated only for active sellers. -/
def MarginalRevenue {N M : ℕ} (net : Network N M) (m : Fin M)
    (cap : Fin N → ℝ) : Prop :=
  (active N cap).Nonempty →
    DifferentiableAt ℝ (fun r => r * net.dInv m r) (marketTotal cap) ∧
    ∀ i ∈ active N cap,
      net.ι m i < deriv (fun r => r * net.dInv m r) (marketTotal cap)

/-- Assumption 4.2 at the endogenous total, stated only for active buyers. -/
def MarginalCost {N M : ℕ} (net : Network N M) (m : Fin M)
    (cap : Fin N → ℝ) : Prop :=
  (active N cap).Nonempty →
    DifferentiableAt ℝ (fun x => x * net.sInv m x) (marketTotal cap) ∧
    ∀ i ∈ active N cap,
      deriv (fun x => x * net.sInv m x) (marketTotal cap) < net.b m i

end
end DisruptReroute.GenEq


