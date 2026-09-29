-- Prove2me | Definitions.Def_EthierKurtz_IsTwoTypeBranching
-- name    : EthierKurtz_IsTwoTypeBranching
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T07:15:33.806679+00:00
-- url     : https://prove2.me/theorems/02473335-f278-4d20-9aed-46dc0f9cc348
-- title:
--   Two-type branching-process law
-- statement:
--   A measurable càdlàg count-valued process satisfying the natural-past martingale problem for the two-type replacement generator on finite-support tests, with explicit residual integrability.
-- source:
--   Stewart N. Ethier and Thomas G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986 (held reprint 1986/2005). Chapter 9, Section 2, equation (2.1) and model conventions, printed pp. 392–393 (PDF pp. 401–402).

import Definitions.Def_EthierKurtz_HasCadlagPaths
import Definitions.Def_EthierKurtz_twoTypeGenerator

set_option autoImplicit true

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped NNReal ENNReal Topology BigOperators ContDiff

namespace EthierKurtz

/-- The nonexplosive count-valued process with generator (2.1), using the
finite-support core and natural-past martingale identities. Integrability is
explicit so that a totalized Bochner integral cannot make the condition vacuous. -/
def IsTwoTypeBranching {Ω : Type*} [MeasurableSpace Ω]
    (rate : Fin 2 → ℝ) (ρ : Fin 2 → Measure (ℕ × ℕ))
    (P : Measure Ω) (Z : ℝ≥0 → Ω → ℕ × ℕ) : Prop :=
  Measurable (fun p : ℝ≥0 × Ω => Z p.1 p.2) ∧ HasCadlagPaths Z ∧
  ∀ f : ℕ × ℕ → ℝ, (Function.support f).Finite →
    ∀ s t : ℝ≥0, s ≤ t →
    let D := fun w => f (Z t w) - f (Z s w) -
      ∫ u in (s : ℝ)..(t : ℝ), twoTypeGenerator rate ρ f (Z u.toNNReal w)
    Integrable D P ∧
    ∀ (k : ℕ) (r : Fin k → ℝ≥0), (∀ i, r i ≤ s) →
      ∀ h : Fin k → (ℕ × ℕ) → ℝ,
        (∀ i, Measurable (h i) ∧ ∃ C : ℝ, ∀ x, |h i x| ≤ C) →
        (∫ w, D w * ∏ i, h i (Z (r i) w) ∂P) = 0

end EthierKurtz


