-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalDegreeSquareIntegrable_ContinuousToL2Map
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalDegreeSquareIntegrable_ContinuousToL2Map
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:57:28.386049+00:00
-- url     : https://prove2.me/theorems/6fde0c05-04de-46ad-8076-8973fc77ffa1
-- title:
--   Continuous To L2 Map
-- statement:
--   Definitions and structural lemmas for Continuous To L2 Map, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalDegreeSquareIntegrable/ContinuousToL2Map.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalDegreeSquareIntegrable_FormalDegreeFromOrthogonality
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PIW.HCFdeg
open MeasureTheory Filter Topology
section
variable {X H : Type} [MeasurableSpace X] {μ : Measure X} [NormedAddCommGroup H]
  [InnerProductSpace ℂ H]
def toL2Map (c : H →ₗ[ℂ] (X → ℂ)) (hL : ∀ v, MemLp (c v) 2 μ) : H →ₗ[ℂ] Lp ℂ 2 μ where
  toFun v := (hL v).toLp (c v)
  map_add' u v := by
    apply Lp.ext
    filter_upwards [(hL (u + v)).coeFn_toLp, Lp.coeFn_add ((hL u).toLp (c u)) ((hL v).toLp (c v)),
      (hL u).coeFn_toLp, (hL v).coeFn_toLp] with x h1 h2 h3 h4
    rw [h1, h2, Pi.add_apply, h3, h4, map_add, Pi.add_apply]
  map_smul' a u := by
    apply Lp.ext
    filter_upwards [(hL (a • u)).coeFn_toLp, Lp.coeFn_smul a ((hL u).toLp (c u)),
      (hL u).coeFn_toLp] with x h1 h2 h3
    rw [h1, RingHom.id_apply, h2, Pi.smul_apply, h3, map_smul, Pi.smul_apply]
end
end PIW.HCFdeg


