-- Prove2me | Definitions.Def_Kyprianou_Ch01_ForwardLampertiPaths
-- name    : Kyprianou_Ch01_ForwardLampertiPaths
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-14T00:15:34.528076+00:00
-- url     : https://prove2.me/theorems/15e76ad5-7bfd-4ee5-957a-eca15257bd0c
-- title:
--   Markov branching path transition law and stopped compound Poisson comparison process
-- statement:
--   Source-specific primitive definitions for Kyprianou equation (1.17), Chapter 1 p. 25. The Markov branching property is formulated as a genuine eventwise conditional transition law for the natural filtration under each initial-state measure, rather than only a one-time marginal. The comparison process is a compound Poisson driver started at an integer population, stopped on reaching the absorbing state zero. Neither the forward path-law equality nor the desired Poisson interarrival law is assumed.
-- source:
--   Kyprianou (2006), Chapter 1 §1.3.4, Definition 1.14 and equations (1.17)–(1.18), printed pp. 24–26.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

namespace Kyprianou.Ch01

/-- Eventwise form of the time-homogeneous Markov property under the
    initial-state law P_y. Conditioning events range over the path's own
    past, expressed by naturalSigma for the real-cast integer population. -/
def IsPopulationMarkovPath
    {Ω : Type*} [MeasurableSpace Ω]
    (Y : ℝ≥0 → Ω → ℕ)
    (P : ℕ → Measure Ω) (law : PopulationLaws) : Prop :=
  (∀ y : ℕ, IsProbabilityMeasure (P y)) ∧
  (∀ (y : ℕ) (t : ℝ≥0) (k : ℕ),
    P y {ω | Y t ω = k} = law y t k) ∧
  (∀ (y : ℕ) (s t : ℝ≥0) (k : ℕ)
      (A : Set Ω),
    @MeasurableSet Ω
        (naturalSigma (fun u ω => (Y u ω : ℝ)) s) A →
    P y (A ∩ {ω | Y (s + t) ω = k}) =
      ∑' z : ℕ, P y (A ∩ {ω | Y s ω = z}) * law z t k)

/-- First visit to zero of a lattice-valued path. Zero at initial time
    is an absorbing state for the stopped process. -/
noncomputable def firstNonpositiveLattice
    {Ω : Type*} (X : ℝ≥0 → Ω → ℤ) (ω : Ω) :
    WithTop ℝ≥0 := by
  classical
  exact if ∃ t : ℝ≥0, X t ω ≤ 0 then
    ((sInf ({t : ℝ≥0 | X t ω ≤ 0} : Set ℝ≥0) : ℝ≥0) : WithTop ℝ≥0)
  else ⊤

/-- An integer-valued compound Poisson process started at y and
    stopped on reaching zero, matching the book's forward construction. -/
noncomputable def stoppedIntegerCompoundPoisson
    {Ω : Type*}
    (y : ℕ) (arrival marks : ℕ → Ω → ℝ)
    (t : ℝ≥0) (ω : Ω) : ℤ :=
  let X := integerCompoundPoisson y arrival marks
  if firstNonpositiveLattice X ω ≤ (t : WithTop ℝ≥0)
    then 0 else X t ω

end Kyprianou.Ch01


