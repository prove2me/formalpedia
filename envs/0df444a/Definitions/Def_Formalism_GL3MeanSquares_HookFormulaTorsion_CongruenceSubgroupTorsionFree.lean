-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_CongruenceSubgroupTorsionFree
-- name    : Formalism_GL3MeanSquares_HookFormulaTorsion_CongruenceSubgroupTorsionFree
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T18:52:26.443905+00:00
-- url     : https://prove2.me/theorems/b14fc811-fa1b-48a3-8921-5b91cc9f2547
-- title:
--   Congruence Subgroup Torsion Free
-- statement:
--   Definitions and structural lemmas for Congruence Subgroup Torsion Free, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/CongruenceSubgroupTorsionFree.lean

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_CongruenceTorsion
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DifferenceStableUnderAction
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DifferentIdealConditions
import Definitions.Def_Formalism_FrobeniusOrbits_HostCorollaries
import Definitions.Def_Formalism_TameInertiaTowers_TowerFieldFoundations
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_gen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.HermitianLattices.StabilizerLevels
namespace PfB
section S1
open NumberField IsDedekindDomain
open scoped TensorProduct
section sep
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable (w : HeightOneSpectrum (𝓞 F))
noncomputable def owHom :
    (w.adicCompletionIntegers F) →+* E ⊗[F] w.adicCompletion F :=
  (Algebra.TensorProduct.includeRight (R := F) (A := E) (B := w.adicCompletion F)).toRingHom.comp
    (w.adicCompletionIntegers F).subtype
local notation "O" => (HeightOneSpectrum.adicCompletionIntegers F w)
end sep
section main
open Formalism.HermitianLattices.FiltrationBoundaryCriterion
end main
end S1
section S2
open NumberField IntermediateField
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
section
variable {e q d : ℕ} {L : Type} [Field L] [NumberField L] {ζ a b : L}
end
end S2
section S3
open NumberField IntermediateField Ideal IsDedekindDomain nonZeroDivisors
open scoped Pointwise
section gen
variable {E : Type} [Field E] [NumberField E]
end gen
section main
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition Formalism.HermitianLattices.FiltrationBoundaryCriterion
end main
end S3
end PfB
end Formalism.HermitianLattices.StabilizerLevels


