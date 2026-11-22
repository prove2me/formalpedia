-- Prove2me | Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_Newton
-- name    : Formalism_CyclotomicNorms_NonsquarefreeBounds_Newton
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:15:49.656823+00:00
-- url     : https://prove2.me/theorems/98dfcb60-4308-44bf-888b-8e4150daea62
-- title:
--   Newton
-- statement:
--   Definitions and structural lemmas for Newton, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CyclotomicNorms/NonsquarefreeBounds/Newton.lean

import Definitions.Def_Formalism_CyclotomicNorms_StatementA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Polynomial
noncomputable section
namespace Formalism.CyclotomicNorms
namespace NewtonPolygonValuation
variable {L : Type} [Field L] (v : AddValuation L (WithTop ℝ))
end NewtonPolygonValuation
open NewtonPolygonValuation
end Formalism.CyclotomicNorms


