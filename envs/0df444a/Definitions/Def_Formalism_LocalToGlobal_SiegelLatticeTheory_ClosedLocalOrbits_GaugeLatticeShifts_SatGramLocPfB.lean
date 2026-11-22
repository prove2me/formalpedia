-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_SatGramLocPfB
-- name    : Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_SatGramLocPfB
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:43:47.69485+00:00
-- url     : https://prove2.me/theorems/70bf924f-a2bc-410b-bbd1-38a0ca8e0ecd
-- title:
--   Sat Gram Loc Pf B
-- statement:
--   Definitions and structural lemmas for Sat Gram Loc Pf B, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/SatGramLocPfB.lean

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_SatGramLoc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open scoped TensorProduct
namespace Formalism.L2.SG.Pf.SatGramLoc
attribute [local instance] Algebra.TensorProduct.rightAlgebra
section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
abbrev rcIntAlg (v : HeightOneSpectrum (𝓞 F)) :
    Algebra (v.adicCompletionIntegers F) (E ⊗[F] v.adicCompletion F) :=
  ((algebraMap (v.adicCompletion F) (E ⊗[F] v.adicCompletion F)).comp
    (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F))).toAlgebra
end
end Formalism.L2.SG.Pf.SatGramLoc


