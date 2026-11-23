-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalDegreeSquareIntegrable_IntegrableCf
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalDegreeSquareIntegrable_IntegrableCf
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:57:07.2776+00:00
-- url     : https://prove2.me/theorems/769e787e-7828-4a47-beeb-19884a2177ff
-- title:
--   Integrable Cf
-- statement:
--   Definitions and structural lemmas for Integrable Cf, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalDegreeSquareIntegrable/IntegrableCf.lean

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
open MeasureTheory
open scoped InnerProductSpace ComplexConjugate
section Orth
variable {G : Type} [Group G] {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
def cf (π : G →* (H →L[ℂ] H)) (v w : H) : G → ℂ := fun g => ⟪w, π g v⟫_ℂ
def cfL (π : G →* (H →L[ℂ] H)) (w : H) : H →ₗ[ℂ] (G → ℂ) where
  toFun v := cf π v w
  map_add' a b := by funext g; simp [cf]
  map_smul' c a := by funext g; simp [cf]
variable [MeasurableSpace G] {μ : Measure G}
end Orth
end PIW.HCFdeg


