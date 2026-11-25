-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_PrimitiveSublatticesMoveWithIsometries
-- name    : Development_AbelianVarietyTheory_Proofs_FlagMeasures_PrimitiveSublatticesMoveWithIsometries
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T03:09:20.23562+00:00
-- url     : https://prove2.me/theorems/4019a790-3baa-4b18-9208-cf4ecdf3a838
-- title:
--   Primitive Sublattices Move With Isometries
-- statement:
--   Definitions and structural lemmas for Primitive Sublattices Move With Isometries, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/PrimitiveSublatticesMoveWithIsometries.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
namespace GlobalTheory.Mass.PrimMove
section
variable {R K : Type*} [CommRing R] [Field K] [StarRing K] [Algebra R K]
variable {V : Type*} [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
end
end GlobalTheory.Mass.PrimMove


