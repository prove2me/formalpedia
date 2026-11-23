-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SpecLocalRingHomExtOfInjectiveLocalHom
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_SpecLocalRingHomExtOfInjectiveLocalHom
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:47:12.817235+00:00
-- url     : https://prove2.me/theorems/5f4e8d8e-4343-4eae-9ad5-27a616130fcf
-- title:
--   Spec Local Ring Hom Ext Of Injective Local Hom
-- statement:
--   Definitions and structural lemmas for Spec Local Ring Hom Ext Of Injective Local Hom, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SpecLocalRingHomExtOfInjectiveLocalHom.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_SRelOneOneIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor


