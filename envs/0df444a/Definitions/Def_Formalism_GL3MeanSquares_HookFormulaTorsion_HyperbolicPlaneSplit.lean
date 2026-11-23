-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_HyperbolicPlaneSplit
-- name    : Formalism_GL3MeanSquares_HookFormulaTorsion_HyperbolicPlaneSplit
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:59:04.20352+00:00
-- url     : https://prove2.me/theorems/79622f7e-4cba-4103-8db9-ea20bd076306
-- title:
--   Hyperbolic Plane Split
-- statement:
--   Definitions and structural lemmas for Hyperbolic Plane Split, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/HyperbolicPlaneSplit.lean

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_InvariantSeriesBidegreeOneOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.HermitianLattices.IntegralLatticeDensity.PD
open Finset Formalism.HermitianLattices.IntegralLatticeDensity
section calculus
variable {M Q : Type} [AddCommGroup M] [AddCommGroup Q] {φ : M → Q}
variable {O : Type} [CommRing O] [StarRing O] [Module O M]
variable {Z : Type} [CommRing Z] [Module Z Q] {nm : O → Z}
end calculus
end Formalism.HermitianLattices.IntegralLatticeDensity.PD
namespace Formalism.HermitianLattices.IntegralLatticeDensity
open Finset PD
end Formalism.HermitianLattices.IntegralLatticeDensity


