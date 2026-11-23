-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticDegree
-- name    : GroundTheory_GlobalFields_ComplexMultiplication_EllipticDegree
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:20:31.369614+00:00
-- url     : https://prove2.me/theorems/e3d2417f-ad02-453c-b338-c796a86e81bc
-- title:
--   Elliptic Degree
-- statement:
--   Definitions and structural lemmas for Elliptic Degree, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/EllipticDegree.lean

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticFunctions
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticConstant
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticRational
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_Residue
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_ResidueTheorem
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticResidues
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology Set
open scoped PeriodPair
noncomputable section
namespace GroundTheory.Global
namespace Elliptic
variable {L : PeriodPair}
variable (L) in

def torusOrder (f : ℂ → ℂ) (x : Torus L) : ℤ :=
  (meromorphicOrderAt f x.out).untopD 0
variable (L) in

def degree (f : ℂ → ℂ) : ℕ :=
  ∑ᶠ x : Torus L, (-torusOrder L f x).toNat
end Elliptic
end GroundTheory.Global


