-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DetMemSpanAdjugate
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DetMemSpanAdjugate
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:06:10.049492+00:00
-- url     : https://prove2.me/theorems/713dcff2-7ee9-49f0-9c52-9c3aaa3bea87
-- title:
--   Det Mem Span Adjugate
-- statement:
--   Definitions and structural lemmas for Det Mem Span Adjugate, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/DetMemSpanAdjugate.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
namespace GlobalTheory.FitSquare
variable {R : Type} [CommRing R]
section blocks
variable {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
end blocks
end GlobalTheory.FitSquare


