-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardLiftMatrix
-- name    : Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardLiftMatrix
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:30:38.796932+00:00
-- url     : https://prove2.me/theorems/f537ce34-aa89-4729-acdc-bc28fd224a35
-- title:
--   Card Lift Matrix
-- statement:
--   Definitions and structural lemmas for Card Lift Matrix, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/CardLiftMatrix.lean

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardFiberMulCardRange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.HermitianLattices.Ext.L3.HermitianSublattices
open Matrix
section Abstract
variable {A Z : Type*} [AddCommGroup A] [AddCommGroup Z]
end Abstract
section Mat
variable {A A' : Type*} [CommRing A] [StarRing A] [CommRing A'] [StarRing A']
variable {m r : Type*} [Fintype m] [Fintype r] [DecidableEq m] [DecidableEq r]
def entSub (m r : Type*) (J : Ideal A) : AddSubgroup (Matrix m r A) where
  carrier := {Y | ∀ i j, Y i j ∈ J}
  zero_mem' := fun _ _ => J.zero_mem
  add_mem' := fun ha hb i j => J.add_mem (ha i j) (hb i j)
  neg_mem' := fun ha i j => J.neg_mem (ha i j)
def hermSub (r : Type*) (J : Ideal A) : AddSubgroup (Matrix r r A) where
  carrier := {S | Sᴴ = S ∧ ∀ i j, S i j ∈ J}
  zero_mem' := ⟨conjTranspose_zero, fun _ _ => J.zero_mem⟩
  add_mem' := fun ha hb => ⟨by rw [conjTranspose_add, ha.1, hb.1],
    fun i j => J.add_mem (ha.2 i j) (hb.2 i j)⟩
  neg_mem' := fun ha => ⟨by rw [conjTranspose_neg, ha.1], fun i j => J.neg_mem (ha.2 i j)⟩
def trH (r : Type*) (J : Ideal A) : entSub r r J →+ Matrix r r A :=
  AddMonoidHom.mk' (fun Y => Y.1 + Y.1ᴴ) (fun a b => by
    simp only [AddSubgroup.coe_add, conjTranspose_add]; abel)
end Mat
end Formalism.HermitianLattices.Ext.L3.HermitianSublattices


