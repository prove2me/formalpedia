-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilQuotientHaar_BruhatDecomposition
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilQuotientHaar_BruhatDecomposition
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T12:39:29.771733+00:00
-- url     : https://prove2.me/theorems/9c37dd62-77f0-4633-abc8-202d57ebfefd
-- title:
--   Bruhat Decomposition
-- statement:
--   Definitions and structural lemmas for Bruhat Decomposition, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilQuotientHaar/BruhatDecomposition.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilQuotientHaar_HaarExist
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace QPK
namespace Bru
variable {G : Type} [TopologicalSpace G] [Group G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
def gf (μ : Measure G) (K : ℕ → Set G) (n : ℕ) (x : G) : ℝ≥0∞ :=
  μ ((fun s => s * x) ⁻¹' K n)
def Eset (μ : Measure G) (K : ℕ → Set G) (n : ℕ) : Set G :=
  {x | gf μ K n x ≠ 0 ∧ ∀ k < n, gf μ K k x = 0}
def bf (μ : Measure G) (K : ℕ → Set G) (x : G) : ℝ≥0∞ :=
  ∑' n, (Eset μ K n).indicator (fun y => (K n).indicator 1 y * (gf μ K n y)⁻¹) x
end Bru
end QPK


