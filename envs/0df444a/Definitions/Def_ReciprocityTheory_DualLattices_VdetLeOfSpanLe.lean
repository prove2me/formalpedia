-- Prove2me | Definitions.Def_ReciprocityTheory_DualLattices_VdetLeOfSpanLe
-- name    : ReciprocityTheory_DualLattices_VdetLeOfSpanLe
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:17:18.014385+00:00
-- url     : https://prove2.me/theorems/4a6e1822-f40c-4b1b-a344-2ee6866b7682
-- title:
--   Vdet Le Of Span Le
-- statement:
--   Definitions and structural lemmas for Vdet Le Of Span Le, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/VdetLeOfSpanLe.lean

import Definitions.Def_ReciprocityTheory_DualLattices_ValuationDetEqOfSpanEq
import Definitions.Def_ReciprocityTheory_DualLattices_IsUnitDetOfSpanEq
import Definitions.Def_ReciprocityTheory_DualLattices_VIntCastLtOneOfDvd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
namespace ReciprocityTheory.PGsh.Up.U3
open ReciprocityTheory.PGsh.L2
variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C] {v : Valuation C NNReal}
variable {X : Type} [Fintype X] [DecidableEq X]
variable {p : ℕ} [hp : Fact p.Prime]
def finZ (p : ℕ) [NeZero p] : Fin p ≃ ZMod p where
  toFun i := ((i : ℕ) : ZMod p)
  invFun a := ⟨a.val, a.val_lt⟩
  left_inv i := Fin.ext (ZMod.val_cast_of_lt i.2)
  right_inv a := ZMod.natCast_zmod_val a
end ReciprocityTheory.PGsh.Up.U3


