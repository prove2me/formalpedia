-- Prove2me | Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_MulSingleMulApplySelf
-- name    : Formalism_LogVandermondeBounds_LogVandermondeProofs_MulSingleMulApplySelf
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:42:28.940811+00:00
-- url     : https://prove2.me/theorems/445fe220-40a1-4b7e-bca2-3a1496367233
-- title:
--   Mul Single Mul Apply Self
-- statement:
--   Definitions and structural lemmas for Mul Single Mul Apply Self, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/MulSingleMulApplySelf.lean

import Definitions.Def_Formalism_LogVandermondeBounds_FinrankFiberSumZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.LogVandermondeBounds.product_first_zeroth_parts
open Finset
section Core
variable {ι H K : Type} [Fintype ι] [DecidableEq ι] [Group H] [Fintype H] [DecidableEq H] [Field K]
def eps (a h : H) : K := if h = a then 1 else if h = 1 then -1 else 0
def bas (a : ι → {c : H // c ≠ 1}) (h : ι → H) : K := ∏ w, (eps ((a w : H)) (h w) : K)
end Core
section Main
variable {ι H X K : Type} [Fintype ι] [DecidableEq ι] [Group H] [Fintype H] [DecidableEq H]
  [Fintype X] [MulAction (ι → H) X] [Field K]
def restr (Q : Type) (e : Q × (ι → H) ≃ X) :
    ramSub ι H X K →ₗ[K] (Q × (ι → {c : H // c ≠ 1}) → K) where
  toFun φ p := (φ : X → K) (e (p.1, fun w => (p.2 w : H)))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
end Main
end Formalism.LogVandermondeBounds.product_first_zeroth_parts


