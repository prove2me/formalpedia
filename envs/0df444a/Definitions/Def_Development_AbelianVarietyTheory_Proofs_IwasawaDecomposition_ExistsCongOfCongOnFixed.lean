-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsCongOfCongOnFixed
-- name    : Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsCongOfCongOnFixed
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T16:51:57.326284+00:00
-- url     : https://prove2.me/theorems/ec10f0c1-5eb9-5561-ba94-867358b833ed
-- title:
--   Exists Cong Of Cong On Fixed
-- statement:
--   Definitions and structural lemmas for Exists Cong Of Cong On Fixed, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsCongOfCongOnFixed.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_MonodromyZeroOfWeilDeligneRepClassIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module GlobalTheory.WeilDeligne Pointwise
namespace GlobalTheory.InertiaMovesRoot
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}
end GlobalTheory.InertiaMovesRoot


