-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HaarTraceConjEqConstMulKernelImage
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_HaarTraceConjEqConstMulKernelImage
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T03:56:36.563821+00:00
-- url     : https://prove2.me/theorems/b566f572-395f-48ef-8fb2-724b236b2dad
-- title:
--   Haar Trace Conj Eq Const Mul Kernel Image
-- statement:
--   Definitions and structural lemmas for Haar Trace Conj Eq Const Mul Kernel Image, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/HaarTraceConjEqConstMulKernelImage.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped Pointwise ENNReal
namespace GlobalTheory.RowFubini
end GlobalTheory.RowFubini
namespace GlobalTheory.RowFubini
section Meas
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
  [BorelSpace G]
end Meas
end GlobalTheory.RowFubini
namespace GlobalTheory.RowFubini
section Top
variable {X : Type*} [Group X] [TopologicalSpace X] [IsTopologicalGroup X]
def conjSub (K : Subgroup X) (b : X) : Subgroup X := K.comap (MulAut.conj b⁻¹).toMonoidHom
end Top
end GlobalTheory.RowFubini
namespace GlobalTheory.RowFubini
end GlobalTheory.RowFubini


