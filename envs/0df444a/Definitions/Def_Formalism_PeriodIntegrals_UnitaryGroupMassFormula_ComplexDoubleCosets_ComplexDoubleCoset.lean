-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ComplexDoubleCosets_ComplexDoubleCoset
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ComplexDoubleCosets_ComplexDoubleCoset
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:49:18.098936+00:00
-- url     : https://prove2.me/theorems/fa23b8d3-1bc0-47f8-a4d3-7184f290aaeb
-- title:
--   Complex Double Coset
-- statement:
--   Definitions and structural lemmas for Complex Double Coset, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ComplexDoubleCosets/ComplexDoubleCoset.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ComplexDoubleCosets_CplxDC
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_FoldDCUnfold
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal NNReal
open Formalism.L2.SG.FoldBound Formalism.L2.SG.PoincareSeriesSquareIntegrable
namespace PI.PoincareSeriesInner.W
universe u
def cf : Fin 4 → ℂ := ![1, -1, Complex.I, -Complex.I]
def part (k : Fin 4) (z : ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (![z.re, -z.re, z.im, -z.im] k)
end PI.PoincareSeriesInner.W


