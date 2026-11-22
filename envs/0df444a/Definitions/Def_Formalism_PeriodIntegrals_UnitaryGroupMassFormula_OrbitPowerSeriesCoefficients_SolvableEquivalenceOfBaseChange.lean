-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OrbitPowerSeriesCoefficients_SolvableEquivalenceOfBaseChange
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OrbitPowerSeriesCoefficients_SolvableEquivalenceOfBaseChange
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:15:28.525175+00:00
-- url     : https://prove2.me/theorems/137675fe-cf7d-44b2-be1b-fd5f5ded6f36
-- title:
--   Solvable Equivalence Of Base Change
-- statement:
--   Definitions and structural lemmas for Solvable Equivalence Of Base Change, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/OrbitPowerSeriesCoefficients/SolvableEquivalenceOfBaseChange.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical
namespace PI.OrbShared.Tri
open MvPowerSeries Finsupp
variable {K : Type*} [Field K] {σ : Type*} [Finite σ]
def IsTri (c : K) (a : σ → MvPowerSeries σ K) : Prop :=
  ∀ v (n : σ →₀ ℕ), n.degree ≤ 1 → coeff n (a v) = if n = single v 1 then c else 0
def P (a : σ → MvPowerSeries σ K) (d : σ →₀ ℕ) : MvPowerSeries σ K := d.prod fun s e => (a s) ^ e
variable {c : K} {a : σ → MvPowerSeries σ K}
def solvable_equivalence_of_base_change (c : K) (a : σ → MvPowerSeries σ K) (G : MvPowerSeries σ K) : ℕ → (σ →₀ ℕ) → K
  | 0 => fun _ => 0
  | k + 1 => fun m => if m.degree = k then
      (c ^ k)⁻¹ * (coeff m G - ∑ᶠ d, if d.degree < k then solvable_equivalence_of_base_change c a G k d * coeff m (P a d) else 0)
    else solvable_equivalence_of_base_change c a G k m
def sol (c : K) (a : σ → MvPowerSeries σ K) (G : MvPowerSeries σ K) : MvPowerSeries σ K :=
  fun m => solvable_equivalence_of_base_change c a G (m.degree + 1) m
end PI.OrbShared.Tri
end


