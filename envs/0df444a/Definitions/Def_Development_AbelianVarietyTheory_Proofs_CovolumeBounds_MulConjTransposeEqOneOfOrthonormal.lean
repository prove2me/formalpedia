-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_MulConjTransposeEqOneOfOrthonormal
-- name    : Development_AbelianVarietyTheory_Proofs_CovolumeBounds_MulConjTransposeEqOneOfOrthonormal
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:06:04.375692+00:00
-- url     : https://prove2.me/theorems/7c610ab5-1bd4-476d-b89b-7beb3d10e92a
-- title:
--   Mul Conj Transpose Eq One Of Orthonormal
-- statement:
--   Definitions and structural lemmas for Mul Conj Transpose Eq One Of Orthonormal, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/MulConjTransposeEqOneOfOrthonormal.lean

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
namespace GlobalTheory
section Ring
variable {R : Type*} [CommRing R]
abbrev subsetEnum {n : Type*} [LinearOrder n] {i : ℕ} (S : Set.powersetCard n i) : Fin i → n :=
  S.1.orderEmbOfFin S.2
end Ring
section Normed
variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [LinearOrder n] {i : ℕ}
end Normed
end GlobalTheory


