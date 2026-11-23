-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EagonNorthcottIntegral_DivisionLowersSecondDegree
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EagonNorthcottIntegral_DivisionLowersSecondDegree
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:10:25.226251+00:00
-- url     : https://prove2.me/theorems/08270435-9f8e-4b8b-a551-36cc5e26165d
-- title:
--   Division Lowers Second Degree
-- statement:
--   Definitions and structural lemmas for Division Lowers Second Degree, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/EagonNorthcottIntegral/DivisionLowersSecondDegree.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EagonNorthcottIntegral_DivisionPartitionTotal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.EagonNorthcottZ
open MvPolynomial
variable {D : ℕ}
abbrev Cnd (ι : Fin D → Fin D ⊕ Fin D) (i : Fin D) (m : (Fin D ⊕ Fin D) →₀ ℕ) : Prop :=
  0 < m (ι i) ∧ ∀ l, l < i → m (ι l) = 0
end PI.EagonNorthcottZ


