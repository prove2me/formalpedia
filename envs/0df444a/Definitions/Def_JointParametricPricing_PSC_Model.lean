-- Prove2me | Definitions.Def_JointParametricPricing_PSC_Model
-- name    : JointParametricPricing_PSC_Model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T08:47:32.385488+00:00
-- url     : https://prove2.me/theorems/e3551a72-f8b7-44dc-be54-5702643850c2
-- title:
--   Parametric network pricing, A1–A4, and the deterministic benchmark
-- statement:
--   There are positive numbers $n,m,q$ of products, resources, and parameters and a positive integer horizon $T$. Nonnegative $A$ and $C$ specify resource use and initial stock. Ordinary prices range over the complete compact box $P$ and parameters over a compact set $\Theta$ containing $\theta^*$; $\Theta$ need not be convex. Demand takes values in the nonnegative simplex with coordinate sum at most one, including no purchase. Its image $\Lambda_\theta$ is convex. Both inverse identities, local $C^2$ price/rate smoothness, $C^1$ parameter smoothness, the common inverse Lipschitz bound, A2's bounds relative to $\theta^*$, and both quadratic-form bounds on the rate-revenue Hessian are explicit. Smooth functions on compact domains are represented by local ambient representatives at points of those domains. There is no regularity requirement at off actions. A mixed ordinary/off action has its own categorical demand law, agrees with ordinary demand, and assigns zero probability to each off product; substitution among remaining products is unrestricted. The program maximizes $x\cdot p(x;\theta)$ over $x\in\Lambda_\theta$ with $Ax\le C/T$. Feasibility and compactness give the actual selected optimizer. A6 separately requires a positive closed-ball radius about its true optimal price inside $P$. The printed KKT predicate and active set deliberately use $C$, as printed, separately from the true dual program with $C/T$.
-- source:
--   Chen, Jasin and Duenyas (2021), Technical Note—Joint Learning and Optimization of Multi-Product Pricing with Finite Resource Capacity and Unknown Demand Parameters, DOI:10.1287/opre.2020.2078; held LBS manuscript/online appendix (published citation basis); §2, printed 5–10 / PDF 6–11; EC.2, printed ec3 / PDF 27

import Definitions.Def_JointParametricPricing_PSC_Experiment

open scoped BigOperators
noncomputable section

namespace JointParametricPricing.PSC

abbrev Sale (n : ℕ) := Option (Fin n)
abbrev Action (n : ℕ) := Fin n → Option ℝ

def ordinary {n : ℕ} (p : Vec n) : Action n := fun j => some (p j)
def allOff {n : ℕ} : Action n := fun _ => none

def saleVector {n : ℕ} : Sale n → Vec n
  | none => 0
  | some j => coordinate j

/-- Price-domain demand with A1--A4. Smoothness is local at the specified domains only. -/
structure Model (n m q : ℕ) where
  n_pos : 0 < n
  m_pos : 0 < m
  q_pos : 0 < q
  T : ℕ
  T_pos : 0 < T
  A : Matrix (Fin m) (Fin n) ℝ
  A_nonneg : ∀ i j, 0 ≤ A i j
  C : Fin m → ℝ
  C_nonneg : ∀ i, 0 ≤ C i
  lower : Vec n
  upper : Vec n
  price_nonempty : ({p : Vec n | ∀ j, lower j ≤ p j ∧ p j ≤ upper j}).Nonempty
  price_compact : IsCompact {p : Vec n | ∀ j, lower j ≤ p j ∧ p j ≤ upper j}
  Θ : Set (Vec q)
  theta_compact : IsCompact Θ
  thetaStar : Vec q
  thetaStar_mem : thetaStar ∈ Θ
  demand : Vec n → Vec q → Vec n
  inverse : Vec n → Vec q → Vec n
  omega : ℝ
  rbar : ℝ
  v : ℝ
  vbar : ℝ
  omega_pos : 0 < omega
  rbar_pos : 0 < rbar
  v_pos : 0 < v
  vbar_pos : 0 < vbar
  demand_simplex : ∀ θ ∈ Θ, ∀ p, (∀ j, lower j ≤ p j ∧ p j ≤ upper j) →
    (∀ j, 0 ≤ demand p θ j) ∧ ∑ j, demand p θ j ≤ 1
  rates_convex : ∀ θ ∈ Θ,
    Convex ℝ ((fun p => demand p θ) '' {p | ∀ j, lower j ≤ p j ∧ p j ≤ upper j})
  inverse_left : ∀ θ ∈ Θ, ∀ p, (∀ j, lower j ≤ p j ∧ p j ≤ upper j) →
    inverse (demand p θ) θ = p
  inverse_right : ∀ θ ∈ Θ, ∀ x ∈
    ((fun p => demand p θ) '' {p | ∀ j, lower j ≤ p j ∧ p j ≤ upper j}),
    (∀ j, lower j ≤ inverse x θ j ∧ inverse x θ j ≤ upper j) ∧ demand (inverse x θ) θ = x
  demand_C2 : ∀ θ ∈ Θ, ∀ p, (∀ j, lower j ≤ p j ∧ p j ≤ upper j) →
    ContDiffAt ℝ 2 (fun z => demand z θ) p
  inverse_C2 : ∀ θ ∈ Θ, ∀ x ∈
    ((fun p => demand p θ) '' {p | ∀ j, lower j ≤ p j ∧ p j ≤ upper j}),
    ContDiffAt ℝ 2 (fun z => inverse z θ) x
  parameter_C1 : ∀ p, (∀ j, lower j ≤ p j ∧ p j ≤ upper j) →
    ∀ θ ∈ Θ, ContDiffAt ℝ 1 (demand p) θ
  inverse_lipschitz : ∀ θ ∈ Θ, ∀ x ∈
    ((fun p => demand p θ) '' {p | ∀ j, lower j ≤ p j ∧ p j ≤ upper j}), ∀ y ∈
    ((fun p => demand p θ) '' {p | ∀ j, lower j ≤ p j ∧ p j ≤ upper j}),
    ‖inverse x θ - inverse y θ‖ ≤ omega * ‖x - y‖
  parameter_lipschitz : ∀ θ ∈ Θ, ∀ p, (∀ j, lower j ≤ p j ∧ p j ≤ upper j) →
    ‖demand p θ - demand p thetaStar‖ ≤ omega * ‖θ - thetaStar‖
  partial_lipschitz : ∀ θ ∈ Θ, ∀ p, (∀ j, lower j ≤ p j ∧ p j ≤ upper j) →
    ∀ i j, |coordDeriv (fun z => demand z θ j) p i -
      coordDeriv (fun z => demand z thetaStar j) p i| ≤ omega * ‖θ - thetaStar‖
  revenue_bound : ∀ θ ∈ Θ, ∀ x ∈
    ((fun p => demand p θ) '' {p | ∀ j, lower j ≤ p j ∧ p j ≤ upper j}),
    |∑ j, x j * inverse x θ j| ≤ rbar
  hessian_bounds : ∀ θ ∈ Θ, ∀ x ∈
    ((fun p => demand p θ) '' {p | ∀ j, lower j ≤ p j ∧ p j ≤ upper j}), ∀ z : Vec n,
    -vbar * ‖z‖ ^ 2 ≤ (∑ i, ∑ j, z i * secondPartial (fun y => ∑ l, y l * inverse y θ l) x i j * z j) ∧
    (∑ i, ∑ j, z i * secondPartial (fun y => ∑ l, y l * inverse y θ l) x i j * z j) ≤ -v * ‖z‖ ^ 2
  /-- Off is a tagged action, avoiding infinity times zero; mixed actions retain substitution. -/
  extendedDemand : Action n → Vec q → Vec n
  extended_agrees : ∀ θ ∈ Θ, ∀ p, (∀ j, lower j ≤ p j ∧ p j ≤ upper j) →
    extendedDemand (ordinary p) θ = demand p θ
  extended_simplex : ∀ θ ∈ Θ, ∀ a, (∀ j, ∀ p, a j = some p → lower j ≤ p ∧ p ≤ upper j) →
    (∀ j, 0 ≤ extendedDemand a θ j) ∧ ∑ j, extendedDemand a θ j ≤ 1
  off_zero : ∀ θ ∈ Θ, ∀ a j, a j = none → extendedDemand a θ j = 0

namespace Model
variable {n m q : ℕ}
def prices (M : Model n m q) : Set (Vec n) := {p | ∀ j, M.lower j ≤ p j ∧ p j ≤ M.upper j}
def rates (M : Model n m q) (θ : Vec q) : Set (Vec n) := (fun p => M.demand p θ) '' M.prices
def revenue (M : Model n m q) (θ : Vec q) (x : Vec n) : ℝ := ∑ j, x j * M.inverse x θ j

def program (M : Model n m q) (θ : Vec q) : CapacityProgram n m :=
  ⟨M.rates θ, M.revenue θ, M.A, fun i => M.C i / M.T⟩

theorem rates_compact (M : Model n m q) (θ : M.Θ) : IsCompact (M.rates θ) :=
  M.price_compact.image_of_continuousOn (fun p hp => (M.demand_C2 θ θ.property p hp).continuousAt.continuousWithinAt)

theorem revenue_continuous (M : Model n m q) (θ : M.Θ) : ContinuousOn (M.revenue θ) (M.rates θ) := by
  intro x hx
  apply ContinuousAt.continuousWithinAt
  have hi := (M.inverse_C2 θ θ.property x hx).continuousAt
  unfold revenue
  fun_prop

/-- The feasibility clause of A6, without Slater or positive capacities. -/
def Feasible (M : Model n m q) : Prop := ∀ θ : M.Θ, (M.program θ).feasible.Nonempty

def optimalRate (M : Model n m q) (h : M.Feasible) (θ : M.Θ) : Vec n :=
  (M.program θ).optimum (M.rates_compact θ) (h θ) (M.revenue_continuous θ)
def optimalPrice (M : Model n m q) (h : M.Feasible) (θ : M.Θ) : Vec n :=
  M.inverse (M.optimalRate h θ) θ

def A6 (M : Model n m q) (h : M.Feasible) (φ : ℝ) : Prop :=
  0 < φ ∧ Metric.closedBall (M.optimalPrice h ⟨M.thetaStar, M.thetaStar_mem⟩) φ ⊆ M.prices

def printedKKT (M : Model n m q) (h : M.Feasible) (θ : M.Θ) (μ : Fin m → ℝ) : Prop :=
  (∀ i, 0 ≤ μ i) ∧
  (∀ j, coordDeriv (M.revenue θ) (M.optimalRate h θ) j = ∑ i, M.A i j * μ i) ∧
  ∀ i, μ i * ((M.program θ).load (M.optimalRate h θ) i - M.C i) = 0

/-- Exactly the unnormalized active set printed in EC.2. -/
def printedActive (M : Model n m q) (h : M.Feasible) : Set (Fin m) :=
  {i | (M.program M.thetaStar).load (M.optimalRate h ⟨M.thetaStar, M.thetaStar_mem⟩) i = M.C i}
end Model
end JointParametricPricing.PSC


