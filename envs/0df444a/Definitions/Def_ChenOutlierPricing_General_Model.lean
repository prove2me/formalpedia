-- Prove2me | Definitions.Def_ChenOutlierPricing_General_Model
-- name    : ChenOutlierPricing_General_Model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T06:41:39.289706+00:00
-- url     : https://prove2.me/theorems/10b0d290-29de-40d2-bd5b-e6717cfff6c3
-- title:
--   Adaptive contamination, real inventory, and expected regret
-- statement:
--   Defines the paper-specific model over the general policy interface. Typical demand is strictly decreasing from 1 to 0 on the whole price interval; its inverse and both bi-Lipschitz bounds satisfy (A1), including the printed lower-demand/upper-price constants being at least one. Demand-coordinate revenue is C² on (0,1), with $0<\sigma^2\le-r''\le M^2$, as in (A2). Real initial inventory is $x_0T$, $0<x_0\le1$. The adversary sees past prices, sales, curves and outlier flags; it does not see the seller's seed or uncensored noise. Its measurable outlier curve is chosen before the current price. Sales are the printed inventory-censored demand and stop at depletion. Every admissible policy satisfies the almost-sure absolute corruption budget. Measurable prices and bounded sales, integrable price-conditioned mean-zero noise, and arbitrary exogenous randomness define admissible runs. There is no independent or history-conditioned mean-zero noise assumption. Clearance is the inverse at $x_0$, the optimum is a genuine continuous-interval revenue maximizer, and the fluid benchmark is $\sup_p p\min\{f_0(p),x_0\}$. Compactness and (A1) make this an attained maximum. Regret is $Tr^*$ minus the expectation of actual cumulative revenue. Outside valid models only, the maximizer selector defaults to the lower endpoint. Time uses elapsed zero-based indices.
-- source:
--   Chen and Wang, DOI 10.1287/opre.2022.2280, §3, supplied source.pdf pp. 10–13, (A1)–(A2), equations (2)–(5)

import Definitions.Def_ChenOutlierPricing_General_Policy

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace ChenOutlierPricing.General

structure Model where
  band : PriceBand
  demand : ℝ → ℝ
  inverse : ℝ → ℝ
  x₀ : ℝ
  LpLower : ℝ
  LpUpper : ℝ
  LdLower : ℝ
  LdUpper : ℝ
  sigmaSq : ℝ
  MSq : ℝ

noncomputable def demandRevenue (m : Model) (d : ℝ) : ℝ := d * m.inverse d

def Assumptions (m : Model) : Prop :=
  m.x₀ ∈ Set.Ioc 0 1 ∧
  StrictAntiOn m.demand (Set.Icc m.band.lo m.band.hi) ∧
  Set.MapsTo m.demand (Set.Icc m.band.lo m.band.hi) (Set.Icc 0 1) ∧
  m.demand m.band.lo = 1 ∧ m.demand m.band.hi = 0 ∧
  Set.MapsTo m.inverse (Set.Icc 0 1) (Set.Icc m.band.lo m.band.hi) ∧
  (∀ d ∈ Set.Icc (0 : ℝ) 1, m.demand (m.inverse d) = d) ∧
  0 < m.LpLower ∧ m.LpLower ≤ m.LpUpper ∧
  0 < m.LdLower ∧ m.LdLower ≤ m.LdUpper ∧
  1 ≤ m.LdLower ∧ 1 ≤ m.LpUpper ∧
  (∀ p ∈ Set.Icc m.band.lo m.band.hi, ∀ q ∈ Set.Icc m.band.lo m.band.hi,
    m.LpLower * |p-q| ≤ |m.demand p - m.demand q| ∧
      |m.demand p - m.demand q| ≤ m.LpUpper * |p-q|) ∧
  (∀ d ∈ Set.Icc (0 : ℝ) 1, ∀ e ∈ Set.Icc (0 : ℝ) 1,
    m.LdLower * |d-e| ≤ |m.inverse d - m.inverse e| ∧
      |m.inverse d - m.inverse e| ≤ m.LdUpper * |d-e|) ∧
  ContDiffOn ℝ 2 (demandRevenue m) (Set.Ioo 0 1) ∧
  0 < m.sigmaSq ∧ m.sigmaSq ≤ m.MSq ∧
  (∀ d ∈ Set.Ioo (0 : ℝ) 1,
    m.sigmaSq ≤ -deriv (deriv (demandRevenue m)) d ∧
    -deriv (deriv (demandRevenue m)) d ≤ m.MSq)

noncomputable def clearance (m : Model) : ℝ := m.inverse m.x₀

/-- Choose a true maximizer on the continuous interval; the default is outside
valid model use only. The source assumptions imply existence and uniqueness. -/
noncomputable def optimum (m : Model) : ℝ := by
  classical
  exact if h : ∃ p ∈ Set.Icc m.band.lo m.band.hi,
      ∀ q ∈ Set.Icc m.band.lo m.band.hi, q * m.demand q ≤ p * m.demand p
  then h.choose else m.band.lo

noncomputable def benchmark (m : Model) : ℝ :=
  sSup ((fun p => p * min (m.demand p) m.x₀) '' Set.Icc m.band.lo m.band.hi)

/-- The adversary sees past prices, sales, demand curves and outlier indicators. -/
structure Round where
  price : ℝ
  sales : ℝ
  outlier : Bool
  curve : ℝ → ℝ

abbrev FullHistory := List Round

def observed (h : FullHistory) : History := h.map (fun r => (r.price, r.sales))

/-- Exogenous randomness is independent of the seller's tape. Contamination is
chosen from the full past before the current price. Noise can depend on that price. -/
structure Environment (Ξ : Type) where
  corrupt : Ξ → FullHistory → Bool
  outlierDemand : Ξ → FullHistory → ℝ → ℝ
  noise : Ξ → FullHistory → ℝ → ℝ

def EnvironmentAdmissible {Ξ : Type} (B : PriceBand) (e : Environment Ξ) : Prop :=
  ∀ v h, Measurable (e.outlierDemand v h) ∧
    Set.MapsTo (e.outlierDemand v h) (Set.Icc B.lo B.hi) (Set.Icc 0 1)

noncomputable def stock (x : ℝ) (h : FullHistory) : ℝ :=
  x - (h.map Round.sales).sum

noncomputable def nextRound {Ξ : Type} (m : Model) (π : Policy) (e : Environment Ξ)
    (T : ℕ) (x : ℝ) (u : Tape) (v : Ξ) (h : FullHistory) : Round :=
  let p := π T x u (observed h)
  let b := e.corrupt v h
  let f := if b then e.outlierDemand v h else m.demand
  let ξ := e.noise v h p
  ⟨p, if stock x h ≤ 0 then 0 else min (f p + ξ) (stock x h), b, f⟩

noncomputable def trajectory {Ξ : Type} (m : Model) (π : Policy) (e : Environment Ξ)
    (T : ℕ) (x : ℝ) (u : Tape) (v : Ξ) : ℕ → FullHistory
  | 0 => []
  | n+1 => let h := trajectory m π e T x u v n
           h ++ [nextRound m π e T x u v h]

noncomputable def roundAt {Ξ : Type} (m : Model) (π : Policy) (e : Environment Ξ)
    (T : ℕ) (x : ℝ) (u : Tape) (v : Ξ) (n : ℕ) : Round :=
  nextRound m π e T x u v (trajectory m π e T x u v n)

noncomputable def noiseAt {Ξ : Type} (m : Model) (π : Policy) (e : Environment Ξ)
    (T : ℕ) (x : ℝ) (u : Tape) (v : Ξ) (n : ℕ) : ℝ :=
  let h := trajectory m π e T x u v n
  e.noise v h (π T x u (observed h))

/-- No independence or past-conditioned zero mean is imposed on customer noise.
The zero conditional mean given price is expressed by its defining integral identity. -/
def RunAdmissible {Ω Ξ : Type} [MeasurableSpace Ω] [MeasurableSpace Ξ] (m : Model) (π : Policy)
    (e : Environment Ξ) (T : ℕ) (x E : ℝ) (μ : Measure Ω) (U : Ω → Tape) (V : Ω → Ξ) : Prop :=
  IsProbabilityMeasure μ ∧ UniformTape μ U ∧ Measurable V ∧ IndepFun U V μ ∧
  EnvironmentAdmissible m.band e ∧
  (∀ n < T,
    let r := fun ω => roundAt m π e T x (U ω) (V ω) n
    let ξ := fun ω => noiseAt m π e T x (U ω) (V ω) n
    Measurable (fun ω => (r ω).price) ∧
    Measurable (fun ω => (r ω).sales) ∧
    Measurable (fun ω => (r ω).outlier) ∧
    Integrable ξ μ ∧
    (∀ᵐ ω ∂μ, (r ω).sales ∈ Set.Icc (0 : ℝ) 1 ∧
      (r ω).price ∈ Set.Icc m.band.lo m.band.hi) ∧
    (∀ A : Set ℝ, MeasurableSet A →
      ∫ ω in (fun ω => (r ω).price) ⁻¹' A, ξ ω ∂μ = 0)) ∧
  (∀ π' : Policy, PolicyAdmissible m.band π' → ∀ᵐ ω ∂μ,
    (∑ n ∈ Finset.range T,
      if (roundAt m π' e T x (U ω) (V ω) n).outlier then (1 : ℝ) else 0) ≤ E)

noncomputable def regret {Ω Ξ : Type} [MeasurableSpace Ω] (m : Model) (π : Policy)
    (e : Environment Ξ) (T : ℕ) (x : ℝ) (μ : Measure Ω) (U : Ω → Tape) (V : Ω → Ξ) : ℝ :=
  T * benchmark m - ∫ ω, ∑ n ∈ Finset.range T,
    let r := roundAt m π e T x (U ω) (V ω) n
    r.price * r.sales ∂μ

end ChenOutlierPricing.General


