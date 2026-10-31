-- Prove2me | Definitions.Def_MinBuying_Symmetry
-- name    : MinBuying_Symmetry
-- status  : Definition
-- author  : @mikeh
-- created : 2026-10-30T16:14:00.015303+00:00
-- url     : https://prove2.me/theorems/4169a883-fee9-4da0-a652-195e33b3effc
-- title:
--   Exchangeability, density-or-PMF affiliation, and threshold events
-- statement:
--   Defines exchangeability as invariance under every coordinate permutation. Affiliation is pointwise MTP2 of either a measurable nonnegative joint Lebesgue density or a probability mass function on real-valued vectors. This includes countably supported laws and does not replace affiliation by association or by the desired conditional comparison. Threshold events refer to the maximum valuation and one specified coordinate.
-- source:
--   Titing Cui, Michael L. Hamilton, Jourdain Lamperski, and Kasra Ganjizadeh Tari, Unit-Demand Pricing for Min-Buying Customers, September 27, 2026 manuscript, 47 PDF pages (main pp.1–27; companion ec1–ec20). https://doi.org/10.2139/ssrn.5178133 . Definition 1 pp.12–13; Eq.(9) p.14.

import Definitions.Def_MinBuying_Model

/-! Symmetry and affiliation from Section 3 of the source. Affiliation is
the density-or-mass-function MTP2 condition itself; no conditional monotonicity
or pricing conclusion is included in the definition. -/
noncomputable section
open MeasureTheory Set

namespace MinBuying

def permuteCoordinates {n : ℕ} (σ : Equiv.Perm (Fin n))
    (v : Valuations n) : Valuations n := fun i => v (σ i)

def Exchangeable {n : ℕ} (μ : JointLaw n) : Prop :=
  ∀ σ : Equiv.Perm (Fin n), Measure.map (permuteCoordinates σ) μ = μ

/-- Pointwise log-supermodularity, without requiring strictly positive mass. -/
def MTP2 {n : ℕ} (f : Valuations n → ℝ) : Prop :=
  ∀ v w : Valuations n,
    f v * f w ≤
      f (fun i => max (v i) (w i)) * f (fun i => min (v i) (w i))

/-- Definition 1 permits either a joint density or a probability mass function.
The PMF alternative includes countably supported laws, with no artificial
assumption that valuations are integer-valued or have a finite support. -/
def Affiliated {n : ℕ} (μ : JointLaw n) : Prop :=
  (∃ f : Valuations n → ℝ,
    Measurable f ∧ (∀ v, 0 ≤ f v) ∧ MTP2 f ∧
      μ = volume.withDensity (fun v => ENNReal.ofReal (f v))) ∨
  (∃ w : PMF (Valuations n),
    μ = w.toMeasure ∧ MTP2 (fun v => (w v).toReal))

/-- The maximum valuation exceeds the given threshold, expressed without
choosing a default maximum for an empty item set. -/
def upperMaximumEvent {n : ℕ} (t : ℝ) : Set (Valuations n) :=
  {v | ∃ j : Fin n, t ≤ v j}

def coordinateBelowAndUpperMaximumEvent {n : ℕ}
    (i : Fin n) (a t : ℝ) : Set (Valuations n) :=
  {v | v i < a ∧ v ∈ upperMaximumEvent t}

end MinBuying


