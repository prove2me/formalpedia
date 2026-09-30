-- Prove2me | Definitions.Def_TauCeti_NumberTheory_NumberField_Units_Signature_Integer
-- name    : TauCeti_NumberTheory_NumberField_Units_Signature_Integer
-- status  : Definition
-- author  : @riccardo.brasca
-- created : 2026-09-29T20:03:04.897523+00:00
-- url     : https://prove2.me/theorems/e7613631-d10f-46fd-a75e-c6d2c9291890
-- title:
--   The total sign homomorphism of a number field, valued in ℤˣ
-- statement:
--   For a number field $K$, the total sign homomorphism is
--
--   $$
--   K^\times\longrightarrow\prod_{\tau\text{ real}}\mathbb Z^\times,\qquad u\longmapsto(\operatorname{sgn}\tau(u))_\tau.
--   $$
--
--   It expresses the signature using the two-element integer-unit group, for the residue-and-sign description of ray classes.
--
--   **Formalization Note.** These foundational declarations are transplanted from the Tau Ceti contributors' [original source](https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/NumberField/Units/Signature/Integer.lean) (Apache-2.0, commit `948fe4751b1fe528b6d580c522ca5d743d47f185`), with compatibility adaptations for Lean 4.33.1. Mathematical proofs requiring separate theorem nodes are published separately.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/NumberField/Units/Signature/Integer.lean

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_Algebra_Order_Ring_Units
import Definitions.Def_TauCeti_NumberTheory_NumberField_Units_Signature_Basic
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Algebra.Order.Ring.Units
import Mathlib.Algebra.Ring.Int.Units
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.IndexNormal
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.Tactic.Group

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# The total sign homomorphism of a number field, valued in `ℤˣ`

`NumberField.fieldUnitSignature` records the sign of a field unit of `K` at each real place as a
class in `ℝˣ ⧸ Units.posSubgroup ℝ`.  Transporting each of those classes along the sign isomorphism
`Units.signEquiv` gives the same data in the concrete two-element group `ℤˣ`:

```text
signHom : Kˣ →* ({w : InfinitePlace K // w.IsReal} → ℤˣ).
```

This is the archimedean half of a multiplicative congruence in group-theoretic form: `x` is
totally positive exactly when `signHom x = 1`.  There is no second sign homomorphism here — this is
`NumberField.fieldUnitSignature` read in `ℤˣ`, and the two are interchangeable through
`Units.signEquiv`.

Surjectivity of `signHom` is not formal — it is weak approximation at the real places, and is
inherited from `NumberField.fieldUnitSignature_surjective`.  The composite
`(𝓞 K)ˣ → Kˣ → ({w // w.IsReal} → ℤˣ)` need *not* be surjective, and its failure to be so is
exactly the obstruction that separates the narrow class group from the wide one; nothing here
asserts otherwise.

## Main definitions

* `TauCeti.GlobalNumberFields.signHom`: the total sign homomorphism, valued in `ℤˣ`.

## Main results

* `TauCeti.GlobalNumberFields.signHom_apply_eq_one_iff` and
  `TauCeti.GlobalNumberFields.signHom_apply_eq_neg_one_iff`: the two possible signs, read off as
  positivity and negativity of the real embedding.
* `TauCeti.GlobalNumberFields.signHom_eq_one_iff`: an element lies in the kernel exactly when it
  is totally positive.
* `TauCeti.GlobalNumberFields.signHom_surjective`: every pattern of signs at the real places is
  realized by a field unit of `K`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §1.
-/

 section

open NumberField NumberField.InfinitePlace

namespace TauCeti.GlobalNumberFields

variable {K : Type*} [Field K]

/-- **The total sign homomorphism of a number field**: the signs of a field unit of `K` at all of
the real places at once, valued in the product of copies of `ℤˣ` indexed by those places.

It is `NumberField.fieldUnitSignature` with each component read through the sign isomorphism
`Units.signEquiv`, so it carries exactly the same information.

The domain is `Kˣ` rather than `K`, so that every value really is a sign: a formulation on `K`
would have to invent a sign for `0`. -/
noncomputable def signHom : Kˣ →* ({w : InfinitePlace K // w.IsReal} → ℤˣ) :=
  (MulEquiv.piCongrRight fun _ : {w : InfinitePlace K // w.IsReal} =>
    Units.signEquiv ℝ).toMonoidHom.comp fieldUnitSignature

/-- Componentwise evaluation of the total sign homomorphism. -/
@[simp] theorem signHom_apply (x : Kˣ) (w : {w : InfinitePlace K // w.IsReal}) :
    signHom x w = Units.signEquiv ℝ (fieldUnitSignature x w) := (rfl)

/-- **A sign is `1` exactly at a positive element.** -/
theorem signHom_apply_eq_one_iff (x : Kˣ) (w : {w : InfinitePlace K // w.IsReal}) :
    signHom x w = 1 ↔ 0 < embedding_of_isReal w.2 (x : K) := by
  rw [signHom_apply, fieldUnitSignature_apply, Units.signEquiv_mk_eq_one_iff]
  simp

/-- **A sign is `-1` exactly at a negative element.** -/
theorem signHom_apply_eq_neg_one_iff (x : Kˣ) (w : {w : InfinitePlace K // w.IsReal}) :
    signHom x w = -1 ↔ embedding_of_isReal w.2 (x : K) < 0 := by
  rw [signHom_apply, fieldUnitSignature_apply, Units.signEquiv_mk_eq_neg_one_iff]
  simp





end TauCeti.GlobalNumberFields

end
end


