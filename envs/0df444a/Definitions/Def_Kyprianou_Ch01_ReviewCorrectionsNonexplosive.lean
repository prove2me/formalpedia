-- Prove2me | Definitions.Def_Kyprianou_Ch01_ReviewCorrectionsNonexplosive
-- name    : Kyprianou_Ch01_ReviewCorrectionsNonexplosive
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-15T10:18:59.090739+00:00
-- url     : https://prove2.me/theorems/b2cb8d93-d189-4a9b-8555-e019239ab0a0
-- title:
--   Chapter 1 reverse Lamperti certificate under explicit non-explosion
-- statement:
--   Exact source proposition for the reverse Lamperti construction with no offspring finite first-moment restriction, conditional on explicit non-explosion of the inverse-speed clock.
-- source:
--   Kyprianou (2006), §1.3.4 and Ch. 10; review correction.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ReviewCorrectionsExplicitUniverse
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false
universe u
namespace Kyprianou.Ch01

noncomputable def certificate_lampertiCompoundPoissonToBranchingLawNonexplosive : Prop :=
  ∀     {Ω : Type u} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (rate : ℝ≥0) (hrate : 0 < rate)
    (offspring : PMF ℕ) (hNoZeroJumps : offspring 1 = 0)
    (law : PopulationLaws)
    (hbranch : HasBranchingProperty law)
    (hMarkov : IsPopulationMarkovSemigroup law)
    (hInitial : ∀ y : ℕ, law y 0 = PMF.pure y)
    (hRates : IsBranchingRateGenerator law rate offspring)
    (arrival marks : ℕ → Ω → ℝ)
    (jumpLaw : Measure ℝ) [IsProbabilityMeasure jumpLaw]
    (hdriver : IsCompoundPoissonDriver
      arrival marks rate jumpLaw Q)
    (hSupport : jumpLaw
      {x : ℝ | ∃ k : ℕ, x = (k : ℝ) - 1} = 1)
    (hJumpMass : ∀ k : ℕ,
      jumpLaw ({((k : ℝ) - 1)} : Set ℝ) = offspring k)
    (hNoExplosion : ∀ y : ℕ, ∀ᵐ ω ∂Q,
      ∀ t : ℝ≥0, ∃ s : ℝ≥0,
        (t : ℝ≥0∞) <
          reciprocalOccupation
            (integerCompoundPoisson y arrival marks) s ω),
    ∀ (y : ℕ) (t : ℝ≥0) (k : ℕ),
      law y t k =
        Q {ω | (compoundPoissonToBranching
          (integerCompoundPoisson y arrival marks) t ω).toNat = k}

end Kyprianou.Ch01


