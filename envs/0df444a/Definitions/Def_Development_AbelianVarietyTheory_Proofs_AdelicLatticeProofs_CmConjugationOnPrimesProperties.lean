-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_CmConjugationOnPrimesProperties
-- name    : Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_CmConjugationOnPrimesProperties
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T09:21:22.424373+00:00
-- url     : https://prove2.me/theorems/e8826989-6bf7-4739-8338-04d4e3f38f9f
-- title:
--   Cm Conjugation On Primes Properties
-- statement:
--   Definitions and structural lemmas for Cm Conjugation On Primes Properties, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/CmConjugationOnPrimesProperties.lean

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_ThmBInHecke
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsPrimeInvolutionOfRingInvolution
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain NumberField.mixedEmbedding Complex Classical HeckeCharacterZeroLocus.ThmBIn
open scoped TensorProduct ContDiff nonZeroDivisors
namespace GlobalTheory
section ConjIdem
variable {F E : Type} [Field F] [Field E] [Algebra F E]
variable [NumberField F] [NumberField E]
end ConjIdem
end GlobalTheory


