-- Prove2me | Definitions.Def_CloseGaps_DPA_ControlledSales
-- name    : CloseGaps_DPA_ControlledSales
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T02:33:18.315155+00:00
-- url     : https://prove2.me/theorems/584c0c84-a45e-41ec-adbc-807b338ad3ff
-- title:
--   Nonanticipating pricing and inventory-stopped sales
-- statement:
--   Measurable rules based on time and past sale epochs; unit exponential interarrivals, inventory-stopped sales and expected revenue.
-- source:
--   Wang, Deng, and Ye (2014), Operations Research 62(2), 318–331, DOI 10.1287/opre.2013.1245, §3.2, equations (1)–(3), p. 321 (PDF 4)

import Definitions.Def_CloseGaps_DPA_Model
import Definitions.Def_QueueingFundamentals_Foundations_ArrivalProcess

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
noncomputable section
open scoped Classical

namespace CloseGaps.DPA

/-- A general nonanticipating price rule: current time and past sale epochs only. -/
structure PriceRule where
  price : (j : ℕ) → ℝ → (Fin j → ℝ) → Option ℝ
  measurable : ∀ j, Measurable (fun z : ℝ × (Fin j → ℝ) => price j z.1 z.2)

abbrev Noise := ℕ → ℝ

def clockLaw : Measure Noise := Measure.infinitePi (fun _ : ℕ => expMeasure 1)

def lastSale : (j : ℕ) → (Fin j → ℝ) → ℝ
  | 0, _ => 0
  | k + 1, h => h (Fin.last k)

def integratedRate (π : PriceRule) (lam : ℝ → ℝ) (n : ℝ)
    (j : ℕ) (h : Fin j → ℝ) (t : ℝ) : ℝ≥0∞ :=
  ∫⁻ s in Ioc (lastSale j h) t, ENNReal.ofReal (n * (π.price j s h).elim 0 lam)

/-- First attained threshold crossing. Nonempty crossing times alone do not suffice:
an instantaneous divergence immediately after a time must not manufacture a sale at that time. -/
def nextSale (π : PriceRule) (lam : ℝ → ℝ) (n : ℝ)
    (j : ℕ) (h : Fin j → ℝ) (e : ℝ) : Option ℝ := by
  classical
  let A := {t : ℝ | lastSale j h ≤ t ∧ ENNReal.ofReal e ≤ integratedRate π lam n j h t}
  exact if A.Nonempty ∧ sInf A ∈ A then some (sInf A) else none

/-- The stopped, size-n controlled Poisson construction, using unit exponential clocks. -/
def salesHistory (π : PriceRule) (lam : ℝ → ℝ) (n x : ℝ) (E : Noise) :
    (j : ℕ) → Option (Fin j → ℝ)
  | 0 => some Fin.elim0
  | j + 1 => if j < ⌊n * x⌋₊ then
      (salesHistory π lam n x E j).bind fun h =>
        (nextSale π lam n j h (E j)).map fun t => Fin.snoc h t
    else none

def saleEpoch (π : PriceRule) (lam : ℝ → ℝ) (n x : ℝ) (E : Noise) (j : ℕ) : WithTop ℝ :=
  (salesHistory π lam n x E j).elim ⊤ fun h => (lastSale j h : WithTop ℝ)

def salesBefore (π : PriceRule) (lam : ℝ → ℝ) (n x : ℝ) (E : Noise) (t : ℝ) : ℕ := by
  classical
  exact ((Finset.range ⌊n * x⌋₊).filter
    fun j => saleEpoch π lam n x E (j + 1) < (t : WithTop ℝ)).card

/-- The predictable price, including the forced off action after the stock cap. -/
def postedPrice (π : PriceRule) (lam : ℝ → ℝ) (n x : ℝ) (E : Noise) (t : ℝ) : Option ℝ :=
  let j := salesBefore π lam n x E t
  if j < ⌊n * x⌋₊ then (salesHistory π lam n x E j).bind (π.price j t) else none

/-- The stochastic sales integral is the sum of the prices at actual sales. -/
def pathRevenue (π : PriceRule) (lam : ℝ → ℝ) (n x T : ℝ) (E : Noise) : ℝ := by
  classical
  exact ∑ j ∈ Finset.range ⌊n * x⌋₊,
    (salesHistory π lam n x E (j + 1)).elim 0 fun h =>
      if lastSale (j + 1) h ≤ T then
        (π.price j (lastSale (j + 1) h) (Fin.init h)).getD 0 else 0

def expectedRevenue (π : PriceRule) (lam : ℝ → ℝ) (n x T : ℝ) : ℝ :=
  ∫ E, pathRevenue π lam n x T E ∂clockLaw

end CloseGaps.DPA


