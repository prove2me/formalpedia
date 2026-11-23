-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsOrthogonalIdempotentsOfSumMulEqOne
-- name    : Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsOrthogonalIdempotentsOfSumMulEqOne
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T18:51:48.229985+00:00
-- url     : https://prove2.me/theorems/f02f7571-e8c7-442f-a26a-e72b9f5ca419
-- title:
--   Exists Orthogonal Idempotents Of Sum Mul Eq One
-- statement:
--   Definitions and structural lemmas for Exists Orthogonal Idempotents Of Sum Mul Eq One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsOrthogonalIdempotentsOfSumMulEqOne.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.AdeleIdempotents
open IsDedekindDomain NumberField
def finiteComponent (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    AdeleRing (𝓞 F) F →+* v.adicCompletion F where
  toFun x := x.2 v
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
def infiniteComponent (F : Type) [Field F] [NumberField F] (w : InfinitePlace F) :
    AdeleRing (𝓞 F) F →+* w.Completion where
  toFun x := x.1 w
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
end GlobalTheory.AdeleIdempotents


