-- Prove2me | Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_SemilinearImprimitiveBound
-- name    : OddOrder_GroupTheory_RepresentationTheory_SemilinearImprimitiveBound
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T04:40:35.811208+00:00
-- url     : https://prove2.me/theorems/ee56e779-64fa-4d0e-96a0-4a1d1de541d3
-- title:
--   The imprimitive order bound $|U|\le(p-1)^{q-1}$
-- statement:
--   Proves the order bound $|U|\le(p-1)^{q-1}$ for an abelian complement $U$ acting imprimitively on the chief factor, the foundation for the non-Galois branch of Peterfalvi (9.7)(a).
--
--   Main declarations: `blockScalarRatioHom` (The block-scalar ratio homomorphism).
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/GroupTheory/RepresentationTheory/SemilinearImprimitiveBound.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/RepresentationTheory/SemilinearImprimitiveBound.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finite.Prod
import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
import Mathlib.GroupTheory.Coset.Card

namespace OddOrder.RepresentationTheory

/-- **The block-scalar ratio homomorphism** in Peterfalvi (9.7.a):
`x ↦ (φ_{i+1}(x) / φ_0(x))_i`.

Normalizing all scalar coordinates by the zeroth one removes the common-scalar diagonal and leaves
`n` coordinates from an `n + 1` block system.  The target is a group because scalar values lie
in the commutative group `A`. -/
def blockScalarRatioHom {Ubar A : Type*} [Group Ubar] [CommGroup A] {n : ℕ}
    (φ : Fin (n + 1) → (Ubar →* A)) : Ubar →* (Fin n → A) where
  toFun x i := φ i.succ x / φ 0 x
  map_one' := by
    ext i
    simp
  map_mul' x y := by
    ext i
    simp only [Pi.mul_apply, map_mul, div_eq_mul_inv, mul_inv_rev]
    ac_rfl

end OddOrder.RepresentationTheory


