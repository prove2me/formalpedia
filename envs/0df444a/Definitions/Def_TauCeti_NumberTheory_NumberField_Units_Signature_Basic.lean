-- Prove2me | Definitions.Def_TauCeti_NumberTheory_NumberField_Units_Signature_Basic
-- name    : TauCeti_NumberTheory_NumberField_Units_Signature_Basic
-- status  : Definition
-- author  : @riccardo.brasca
-- created : 2026-09-29T19:55:20.162985+00:00
-- url     : https://prove2.me/theorems/da0c9298-713e-4ce4-89c1-5a9dde35db82
-- title:
--   The signature map on the units of a number field
-- statement:
--   For a number field $K$, the signature homomorphism sends $u\in K^\times$ to its signs at all real embeddings:
--
--   $$
--   u\longmapsto\bigl(\operatorname{sgn}\tau(u)\bigr)_\tau.
--   $$
--
--   Here each sign is represented in the quotient of nonzero real numbers by the positive subgroup. This packages all real-place sign conditions.
--
--   **Formalization Note.** These foundational declarations are transplanted from the Tau Ceti contributors' [original source](https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/NumberField/Units/Signature/Basic.lean) (Apache-2.0, commit `948fe4751b1fe528b6d580c522ca5d743d47f185`), with compatibility adaptations for Lean 4.33.1. Mathematical proofs requiring separate theorem nodes are published separately.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/NumberField/Units/Signature/Basic.lean

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Algebra.Order.Ring.Units
import Mathlib.Algebra.Ring.Int.Units
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.IndexNormal
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
# The signature map on the units of a number field

The **signature** of a unit records its sign under each real embedding `K →+* ℝ`, as a class in the
sign group `ℝˣ ⧸ (posSubgroup ℝ)` (the positive units of `ℝ` form an index-`2` subgroup, so each
factor is the two-element sign group).

We build it first on the full multiplicative group `Kˣ` — `fieldUnitSignature`, whose kernel is the
totally positive units `totallyPositiveUnits` — and then restrict along `(𝓞 K)ˣ → Kˣ` to the
arithmetic unit group to obtain `unitSignature`, whose kernel is the totally positive integer units.

The integer-unit signature is the archimedean input to the narrow class group `Cl⁺(K)` (Layer 3 of
the multiquadratic roadmap): the *cokernel* of the signature — the full sign group modulo the
signatures realized by units — is what contributes the kernel of the surjection `Cl⁺(K) → Cl(K)`
between the narrow and ordinary class groups, and the `2`-rank of `Cl⁺(K)` is what the `t - 1`
genus-theory formula computes for a real quadratic field.

## Main definitions and results

* `NumberField.fieldUnitSignature`: the signature homomorphism on `Kˣ`, with
  `fieldUnitSignature_ker` computing its kernel as `totallyPositiveUnits`.
* `NumberField.unitSignature`: the signature homomorphism on `(𝓞 K)ˣ`, the restriction of
  `fieldUnitSignature`, with `unitSignature_ker` its kernel `totallyPositiveIntegerUnits` (defined
  in `TotallyPositive.lean`).
-/

 section

open NumberField InfinitePlace

namespace NumberField

variable {K : Type*} [Field K]

/-- The **signature homomorphism** on `Kˣ`: `u` is sent, at each real infinite place `w`, to the
class of its image `Units.map (embedding_of_isReal w) u` in the sign group
`ℝˣ ⧸ (posSubgroup ℝ)`. -/
noncomputable def fieldUnitSignature :
    Kˣ →* ({w : InfinitePlace K // w.IsReal} → ℝˣ ⧸ Units.posSubgroup ℝ) :=
  MonoidHom.pi fun w =>
    (QuotientGroup.mk' (Units.posSubgroup ℝ)).comp
      (Units.map (embedding_of_isReal w.2).toMonoidHom)

/-- Componentwise evaluation of the field-unit signature. -/
@[simp] theorem fieldUnitSignature_apply (u : Kˣ) (w : {w : InfinitePlace K // w.IsReal}) :
    fieldUnitSignature u w =
      (Units.map (embedding_of_isReal w.2).toMonoidHom u : ℝˣ ⧸ Units.posSubgroup ℝ) := by
  simp only [fieldUnitSignature, MonoidHom.pi_apply, MonoidHom.comp_apply, QuotientGroup.mk'_apply]





variable [NumberField K]











end NumberField

end
end


