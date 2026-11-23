-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_PsiTower
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_PsiTower
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:58:23.109252+00:00
-- url     : https://prove2.me/theorems/b1269fdb-12be-4b26-b7e0-0e9b396d54c6
-- title:
--   Psi Tower
-- statement:
--   Definitions and structural lemmas for Psi Tower, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalDualGenerator/PsiTower.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocDualGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_FpDualUnram
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDualGenerator_DualAtLMulUnit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel IsDedekindDomain NumberField Formalism.MainNotions.S.Loc
namespace PI.LocDualGen.Top
open PI.LocDualGen.W
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)} [Fact (resChar p).Prime]
abbrev qAlg (A : LocAt F E sig p) : Algebra ℚ_[resChar p] A.Ep :=
  ((algebraMap A.Fp A.Ep).comp (algebraMap ℚ_[resChar p] A.Fp)).toAlgebra
end PI.LocDualGen.Top


