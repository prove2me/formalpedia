-- Prove2me | Definitions.Def_CloseGaps_DPA_Model
-- name    : CloseGaps_DPA_Model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T02:32:37.462411+00:00
-- url     : https://prove2.me/theorems/6391c0f6-e68f-4e9d-ad0b-a904aaa51c5b
-- title:
--   Demand class and fluid benchmark
-- statement:
--   Regular decreasing demand, rate-space curvature, the off action, all deterministic feasible schedules, and the interior deterministic optimizer. The inverse is extended outside the feasible demand image only to express two-sided endpoint derivatives; its regularity bounds are imposed on that image. The off action is a separate measurable point. Optimizers are selected as suprema of the compact nonempty optimizing sets under the standing assumptions.
-- source:
--   Wang, Deng, and Ye (2014), Operations Research 62(2), 318–331, DOI 10.1287/opre.2013.1245, Assumption 1, equations (2), (5), (6), pp. 320–322 (PDF 3–5)

import Mathlib

open MeasureTheory Set
noncomputable section
open scoped Classical

namespace CloseGaps.DPA

/-- The Borel real prices with a separate measurable off action. -/
instance actionMeasurableSpace : MeasurableSpace (Option ℝ) :=
  MeasurableSpace.comap
    (fun p : Option ℝ => (p.elim (Sum.inl ()) Sum.inr : Unit ⊕ ℝ)) inferInstance

/-- Known coefficients of Assumption 1, not a parametric family of demands. -/
structure Coefficients where
  M : ℝ
  K : ℝ
  mL : ℝ
  mU : ℝ

def Coefficients.Positive (c : Coefficients) : Prop :=
  0 < c.M ∧ 0 < c.K ∧ 0 < c.mL ∧ 0 < c.mU

/-- Physical feasible price interval. `none` is the zero-demand off action. -/
structure Market where
  lo : ℝ
  hi : ℝ

def Market.Valid (a : Market) : Prop := a.lo < a.hi

def Market.feasible (a : Market) (p : Option ℝ) : Prop :=
  p.elim True (fun q => q ∈ Icc a.lo a.hi)

def actionRate (lam : ℝ → ℝ) (p : Option ℝ) : ℝ := p.elim 0 lam

def actionPrice (p : Option ℝ) : ℝ := p.getD 0

/-- Full regular demand class: curvature is in rate space. -/
def Regular (c : Coefficients) (a : Market) (lam : ℝ → ℝ) : Prop :=
  StrictAntiOn lam (Icc a.lo a.hi) ∧
  (∀ p ∈ Icc a.lo a.hi, 0 ≤ lam p ∧ |lam p| ≤ c.M) ∧
  (∀ p ∈ Icc a.lo a.hi, ∀ q ∈ Icc a.lo a.hi,
    |lam p - lam q| ≤ c.K * |p - q| ∧
    |p * lam p - q * lam q| ≤ c.K * |p - q|) ∧
  ∃ γ : ℝ → ℝ,
    (∀ p ∈ Icc a.lo a.hi, γ (lam p) = p) ∧
    (∀ q ∈ lam '' Icc a.lo a.hi, ∀ z ∈ lam '' Icc a.lo a.hi,
      |γ q - γ z| ≤ c.K * |q - z|) ∧
    (∀ q ∈ lam '' Icc a.lo a.hi,
      DifferentiableAt ℝ (fun z => z * γ z) q ∧
      DifferentiableAt ℝ (deriv (fun z => z * γ z)) q ∧
      -c.mL ≤ deriv (deriv (fun z => z * γ z)) q ∧
      deriv (deriv (fun z => z * γ z)) q ≤ -c.mU)

/-- Equation (2), over all measurable feasible schedules, including switching off. -/
def fluidRevenues (a : Market) (x T : ℝ) (lam : ℝ → ℝ) : Set ℝ :=
  {v | ∃ p : ℝ → Option ℝ, Measurable p ∧
    (∀ t ∈ Icc 0 T, a.feasible (p t)) ∧
    IntegrableOn (fun t => actionRate lam (p t)) (Ioc 0 T) ∧
    IntegrableOn (fun t => actionPrice (p t) * actionRate lam (p t)) (Ioc 0 T) ∧
    (∫ t in Ioc 0 T, actionRate lam (p t)) ≤ x ∧
    v = ∫ t in Ioc 0 T, actionPrice (p t) * actionRate lam (p t)}

def fluidValue (a : Market) (x T : ℝ) (lam : ℝ → ℝ) : ℝ :=
  sSup (fluidRevenues a x T lam)

def uOpt (a : Market) (lam : ℝ → ℝ) : ℝ :=
  sSup {p ∈ Icc a.lo a.hi | ∀ q ∈ Icc a.lo a.hi, q * lam q ≤ p * lam p}

def cOpt (a : Market) (x T : ℝ) (lam : ℝ → ℝ) : ℝ :=
  sSup {p ∈ Icc a.lo a.hi | ∀ q ∈ Icc a.lo a.hi,
    |lam p - x / T| ≤ |lam q - x / T|}

def dOpt (a : Market) (x T : ℝ) (lam : ℝ → ℝ) : ℝ :=
  max (uOpt a lam) (cOpt a x T lam)

/-- Standing interiority in the paragraph immediately before §4.2. -/
def InClass (c : Coefficients) (a : Market) (x T : ℝ) (lam : ℝ → ℝ) : Prop :=
  Regular c a lam ∧ dOpt a x T lam ∈ Ioo a.lo a.hi

/-- Multiplicative rescaling; translating prices would change revenue maximizers. -/
def normalizedMarket (a : Market) : Market :=
  ⟨a.lo / (a.hi - a.lo), a.hi / (a.hi - a.lo)⟩
def normalizedDemand (a : Market) (T : ℝ) (lam : ℝ → ℝ) (q : ℝ) : ℝ :=
  T * lam ((a.hi - a.lo) * q)

end CloseGaps.DPA


