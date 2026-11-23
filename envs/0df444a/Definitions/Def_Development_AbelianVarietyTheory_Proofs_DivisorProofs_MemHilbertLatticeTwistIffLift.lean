-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemHilbertLatticeTwistIffLift
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemHilbertLatticeTwistIffLift
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:07:12.209302+00:00
-- url     : https://prove2.me/theorems/7f088f29-c7a2-4c9b-a7df-6de9a721f746
-- title:
--   Mem Hilbert Lattice Twist Iff Lift
-- statement:
--   Definitions and structural lemmas for Mem Hilbert Lattice Twist Iff Lift, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MemHilbertLatticeTwistIffLift.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasLevelStd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open scoped Classical MatrixGroups nonZeroDivisors
namespace GlobalTheory.HilbFam.TwistMem
variable {F : Type} [Field F] [NumberField F]
end GlobalTheory.HilbFam.TwistMem


