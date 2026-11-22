-- Prove2me | Definitions.Def_Formalism_ThetaLiftIndependence_ThetaOrbitSums_ChainScalar
-- name    : Formalism_ThetaLiftIndependence_ThetaOrbitSums_ChainScalar
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:03:58.282267+00:00
-- url     : https://prove2.me/theorems/89943458-5b66-4e83-b46f-9e3c4bc7ab2c
-- title:
--   Chain Scalar
-- statement:
--   Definitions and structural lemmas for Chain Scalar, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLiftIndependence/ThetaOrbitSums/ChainScalar.lean

import Definitions.Def_Formalism_ThetaLiftIndependence_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.ThetaLiftIndependence
namespace ChainScalarLemmas
variable {𝕜 : Type} [RCLike 𝕜] {E : ℕ → Type} [∀ j, NormedAddCommGroup (E j)]
    [∀ j, InnerProductSpace 𝕜 (E j)] [∀ j, FiniteDimensional 𝕜 (E j)]
end ChainScalarLemmas
end Formalism.ThetaLiftIndependence


