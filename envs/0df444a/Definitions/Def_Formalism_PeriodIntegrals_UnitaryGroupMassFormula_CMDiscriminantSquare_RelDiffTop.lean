-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CMDiscriminantSquare_RelDiffTop
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CMDiscriminantSquare_RelDiffTop
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:12:27.831099+00:00
-- url     : https://prove2.me/theorems/0841a6ee-e804-4bf4-890c-3327f34d5db4
-- title:
--   Rel Diff Top
-- statement:
--   Definitions and structural lemmas for Rel Diff Top, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CMDiscriminantSquare/RelDiffTop.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_SiegelMassRatios_MassRatio
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
namespace PIW.CMDiscSq
def RelDiffTop : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E],
    Formalism.L2.SG.MassRatio.IsCMPair F E → differentIdeal (𝓞 F) (𝓞 E) = ⊤
def RelDegTwo : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E],
    Formalism.L2.SG.MassRatio.IsCMPair F E → Module.finrank F E = 2
end PIW.CMDiscSq


