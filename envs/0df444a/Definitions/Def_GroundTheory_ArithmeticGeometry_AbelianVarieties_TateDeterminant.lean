-- Prove2me | Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_TateDeterminant
-- name    : GroundTheory_ArithmeticGeometry_AbelianVarieties_TateDeterminant
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:25:13.84215+00:00
-- url     : https://prove2.me/theorems/b79a411d-b8da-4890-b110-13a50c7f27a8
-- title:
--   Tate Determinant
-- statement:
--   Definitions and structural lemmas for Tate Determinant, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/TateDeterminant.lean

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_TateModule
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Arith.Abelian
open PadicInt
section Pairing
variable {A : Type*} [AddCommGroup A] {L : Type*} [Field L] (N : ℕ) (e : A → A → L)
end Pairing
section Determinant
variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime] {A : Type*} [AddCommGroup A]
end Determinant
end GroundTheory.Arith.Abelian


