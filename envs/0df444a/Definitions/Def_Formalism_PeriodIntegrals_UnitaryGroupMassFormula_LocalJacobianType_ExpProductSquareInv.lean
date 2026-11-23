-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_ExpProductSquareInv
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_ExpProductSquareInv
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T08:54:37.97048+00:00
-- url     : https://prove2.me/theorems/11fb599b-589d-4bf0-9573-ddc133f2b107
-- title:
--   Exp Product Square Inv
-- statement:
--   Definitions and structural lemmas for Exp Product Square Inv, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalJacobianType/ExpProductSquareInv.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocJacTyp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianType_KitAbs
import Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_absV_mul
import Theorems.Thm_PI_UnitaryGroupMassFormula_LocJacTyp_absV_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.UnitaryGroupMassFormula.LocJacTyp
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain PI.LocJacTyp
open scoped Classical
section Count
end Count
section Real
open Real
variable (r : ℕ)
end Real
section Final
open Real
end Final
section AbsProd
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
def absVHom : Fv F v →* ℝ where
  toFun := absV v
  map_one' := absV_one v
  map_mul' := absV_mul v
end AbsProd
end PI.UnitaryGroupMassFormula.LocJacTyp


