-- Prove2me | Definitions.Def_Kyprianou_Ch01_LampertiInverse
-- name    : Kyprianou_Ch01_LampertiInverse
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-14T00:13:05.543811+00:00
-- url     : https://prove2.me/theorems/f336ad4a-cb9e-4f89-89db-71b4f1c43237
-- title:
--   Equation (1.19): offspring jump law, inverse-speed clock and reverse Lamperti time-change
-- statement:
--   Kyprianou (2006), equation (1.19). The inverse occupation clock uses an extended-nonnegative integrand 1/X, so visits to zero generate infinite reciprocal occupation and force absorption at extinction. The time-change Y_t=X_(θ_t∧τ⁻₀) is defined by first negative passage. This fixes the earlier zero-state convention and remains subject to remote Lean elaboration.
-- source:
--   Kyprianou (2006), Chapter 1, pp. 25–26, equations (1.17)–(1.19).

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks

open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch01

variable {Ω : Type*}

/-- The compound-Poisson jump size is offspring count minus one. -/
noncomputable def offspringJumpLaw (offspring : PMF ℕ) : PMF ℤ :=
  offspring.map (fun n : ℕ => (n : ℤ) - 1)

/-- First strict negative passage, with infinity if no passage occurs. -/
noncomputable def firstNegativePassage
    (X : ℝ≥0 → Ω → ℤ) (ω : Ω) : WithTop ℝ≥0 :=
  by
    classical
    exact if ∃ t : ℝ≥0, 0 < t ∧ X t ω < 0 then
      ((sInf ({t : ℝ≥0 | 0 < t ∧ X t ω < 0} : Set ℝ≥0) : ℝ≥0) : WithTop ℝ≥0)
    else ⊤

/-- Equation (1.19): the extended inverse-speed occupation clock.
    ENNReal.inverse at zero is infinity. Time spent at state zero therefore
    causes I to become infinite, making the time-change absorb at extinction. -/
noncomputable def reciprocalOccupation
    (X : ℝ≥0 → Ω → ℤ) (t : ℝ≥0) (ω : Ω) : ℝ≥0∞ :=
  ∫⁻ s in (Set.Ioc (0 : ℝ) (t : ℝ)),
    (ENNReal.ofReal (X (Real.toNNReal s) ω : ℝ))⁻¹ ∂volume

/-- Right inverse θ_t=inf{s≥0: I_s>t}, including an absorbing zero. -/
noncomputable def inverseReciprocalOccupation
    (X : ℝ≥0 → Ω → ℤ) (t : ℝ≥0)
    (ω : Ω) : WithTop ℝ≥0 :=
  by
    classical
    exact if ∃ s : ℝ≥0, (t : ℝ≥0∞) < reciprocalOccupation X s ω then
      ((sInf ({s : ℝ≥0 | (t : ℝ≥0∞) < reciprocalOccupation X s ω} : Set ℝ≥0) : ℝ≥0) :
        WithTop ℝ≥0)
    else ⊤

/-- Reverse Lamperti map: Y_t=X_{θ_t ∧ τ⁻₀}, with zero on an infinite clock. -/
noncomputable def compoundPoissonToBranching
    (X : ℝ≥0 → Ω → ℤ) (t : ℝ≥0) (ω : Ω) : ℤ :=
  match min (inverseReciprocalOccupation X t ω)
      (firstNegativePassage X ω) with
  | none => 0
  | some s => X s ω

/-- Extinction time for a nonnegative integer-valued population. -/
noncomputable def populationExtinction
    (Y : ℝ≥0 → Ω → ℕ) (ω : Ω) : WithTop ℝ≥0 :=
  by
    classical
    exact if ∃ t : ℝ≥0, Y t ω = 0 then
      ((sInf ({t : ℝ≥0 | Y t ω = 0} : Set ℝ≥0) : ℝ≥0) : WithTop ℝ≥0)
    else ⊤

end Kyprianou.Ch01


