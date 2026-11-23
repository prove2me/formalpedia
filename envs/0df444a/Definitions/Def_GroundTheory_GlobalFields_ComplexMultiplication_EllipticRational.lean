-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticRational
-- name    : GroundTheory_GlobalFields_ComplexMultiplication_EllipticRational
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:08:28.677155+00:00
-- url     : https://prove2.me/theorems/1d9221b6-b5c1-4e55-a542-fdb937b944af
-- title:
--   Elliptic Rational
-- statement:
--   Definitions and structural lemmas for Elliptic Rational, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/EllipticRational.lean

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticFunctions
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticConstant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology Set Polynomial
open scoped PeriodPair
noncomputable section
namespace GroundTheory.Global
namespace Elliptic
variable {L : PeriodPair}
end Elliptic
end GroundTheory.Global


