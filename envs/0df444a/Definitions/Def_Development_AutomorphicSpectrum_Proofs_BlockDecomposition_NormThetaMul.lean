-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_NormThetaMul
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_NormThetaMul
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:24:58.577795+00:00
-- url     : https://prove2.me/theorems/ec646a98-7501-49bf-9074-724115f0cc6d
-- title:
--   Norm Theta Mul
-- statement:
--   Definitions and structural lemmas for Norm Theta Mul, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/NormThetaMul.lean

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_BinaryMassMeans_MeanVal
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_GaloisBoundSecond
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
namespace GlobalTheory.CompanionTheory.MassCount
variable {F : Type} [Field F] [NumberField F]
def emb [IsTotallyReal F] (w : InfinitePlace F) : F →+* ℝ :=
  InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal w)
end GlobalTheory.CompanionTheory.MassCount
end


