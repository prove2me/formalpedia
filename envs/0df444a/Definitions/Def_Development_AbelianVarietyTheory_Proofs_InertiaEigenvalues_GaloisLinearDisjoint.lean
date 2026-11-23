-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_GaloisLinearDisjoint
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_GaloisLinearDisjoint
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T13:44:06.825815+00:00
-- url     : https://prove2.me/theorems/64ab5a8d-20b9-4bda-8b52-2ea8ccd6cb74
-- title:
--   Galois Linear Disjoint
-- statement:
--   Definitions and structural lemmas for Galois Linear Disjoint, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/GaloisLinearDisjoint.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
namespace GlobalTheory.GalDisj
section
variable {k M F D : Type*} [Field k] [Field M] [Field F] [Field D] [Algebra k M] [Algebra k F]
  [Algebra k D] [Algebra M D] [Algebra F D] [IsScalarTower k M D] [IsScalarTower k F D]
end
end GlobalTheory.GalDisj


