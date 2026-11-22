-- Prove2me | Definitions.Def_Formalism_ThetaLiftIndependence_ThetaOrbitSums_GaussOp
-- name    : Formalism_ThetaLiftIndependence_ThetaOrbitSums_GaussOp
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:03:30.485609+00:00
-- url     : https://prove2.me/theorems/9cd9ab2b-a4d2-43ed-8156-edfe31240d1c
-- title:
--   Gauss Op
-- statement:
--   Definitions and structural lemmas for Gauss Op, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLiftIndependence/ThetaOrbitSums/GaussOp.lean

import Definitions.Def_Formalism_ThetaLiftIndependence_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
namespace Formalism.ThetaLiftIndependence
namespace GaussOperatorLemmas
variable {𝔽 : Type} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽]
end GaussOperatorLemmas
end Formalism.ThetaLiftIndependence


