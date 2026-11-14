-- Prove2me | Definitions.Def_Kyprianou_Ch01_BranchingGenerator
-- name    : Kyprianou_Ch01_BranchingGenerator
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-14T00:13:39.748251+00:00
-- url     : https://prove2.me/theorems/c83ef446-3372-4157-b0e0-333f48596551
-- title:
--   CT Markov branching generator and lattice compound-Poisson random walk
-- statement:
--   The nonexplosive continuous-time branching law has Q-matrix Q(y,k)=λy p_(k+1−y) for k≠y with admissible k≥y−1, and Q(y,y)=−λy when p₁=0. The primitive generator is the right derivative at zero of each transition probability. Integer compound-Poisson paths are obtained by flooring a real-valued compound Poisson process with integer-supported marks. These primitives support the distributional reverse Lamperti correspondence, not an assumption of it.
-- source:
--   Kyprianou (2006), Chapter 1 §1.3.4, printed pp. 24–26, equations (1.17)–(1.19).

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Definitions.Def_Kyprianou_Ch01_LampertiInverse

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch01

/-- For offspring law p and life rate λ, the Q-matrix of the continuous-time
    Markov branching population at initial size y. The book assumes p₁=0,
    so a death always gives a genuine jump. -/
def IsBranchingRateGenerator
    (law : PopulationLaws) (rate : ℝ≥0) (offspring : PMF ℕ) : Prop :=
  ∀ (y k : ℕ),
    HasDerivWithinAt
      (fun t : ℝ => ((law y (Real.toNNReal t)) k).toReal)
      (if k = y then
        -((rate : ℝ) * (y : ℝ))
      else if y ≤ k + 1 then
        (rate : ℝ) * (y : ℝ) *
          (offspring (k + 1 - y)).toReal
      else 0)
      (Set.Ici 0) 0

/-- The lattice-valued random walk underlying the compound-Poisson process:
    the jump marks are almost surely integers by the jump-law hypothesis. -/
noncomputable def integerCompoundPoisson
    {Ω : Type*}
    (y : ℕ) (arrival marks : ℕ → Ω → ℝ)
    (t : ℝ≥0) (ω : Ω) : ℤ :=
  Int.floor ((y : ℝ) +
    ProbabilityTheory.compoundPoisson 0 arrival marks (t : ℝ) ω)

end Kyprianou.Ch01


