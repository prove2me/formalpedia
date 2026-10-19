-- Prove2me | Definitions.Def_MIPRE_Foundations_LowDegree_NormalBasis
-- name    : MIPRE_Foundations_LowDegree_NormalBasis
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T00:49:33.466125+00:00
-- url     : https://prove2.me/theorems/09655be8-2d89-47a0-bade-7ea111480b22
-- title:
--   Definitions of NormalBasis: A self-dual normal basis exists in characteristic two and odd degree This is the existence half of blueprint…
-- statement:
--   The definitions of the module `MIPRE.Foundations.LowDegree.NormalBasis` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). A self-dual normal basis exists in characteristic two and odd degree. This is the existence half of blueprint `lem:self-dual-basis`: over a finite field of characteristic two, an extension of odd degree admits a basis that is simultaneously normal (a Frobenius orbit) and self-dual for the trace form. The argument is the short one. Fix the normal element `α` Mathlib's normal basis theorem supplies and let `c ∈ F[G]`, `G = Gal(K/F)`, be its Gram element, with `c_g = tr(α · gα)`. Writing `ofAlg a` for the element with normal-basis coordinates `a`, the Gram element transforms as `gramPair (ofAlg…
--
--   **Definitions** (2): `MIPRE.LowDegree.galStar` (The involution of the group algebra induced by `g ↦ g⁻¹`.); `MIPRE.LowDegree.gramPair` (The Gram element of a pair: its coefficient at `g` is `tr(x · g y)`.).
--
--   **Embedded lemmas** (2): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `coeff_galStar`, `coeff_gramPair`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.LowDegree.NormalBasis` (`MIPRE/Foundations/LowDegree/NormalBasis.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 2 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/LowDegree/NormalBasis.lean; blueprint lem:self-dual-basis-exists

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/NormalBasis.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finite.Trace
import Mathlib.FieldTheory.Galois.NormalBasis
import Mathlib.RingTheory.Trace.Basic
import Definitions.Def_MIPRE_Foundations_LowDegree_SelfDualize
import Definitions.Def_MIPRE_Foundations_LowDegree_SelfDual

/-!
# A self-dual normal basis exists in characteristic two and odd degree

This is the existence half of blueprint `lem:self-dual-basis`: over a finite field of
characteristic two, an extension of odd degree admits a basis that is simultaneously normal
(a Frobenius orbit) and self-dual for the trace form.

The argument is the short one. Fix the normal element `α` Mathlib's normal basis theorem
supplies and let `c ∈ F[G]`, `G = Gal(K/F)`, be its Gram element, with `c_g = tr(α · gα)`.
Writing `ofAlg a` for the element with normal-basis coordinates `a`, the Gram element
transforms as
`gramPair (ofAlg a) (ofAlg a) = a · τa · c`,
where `τ` is the involution induced by `g ↦ g⁻¹` (`gramPair_ofAlg`). Nondegeneracy of the
trace form makes `c` a unit (`isUnit_gram`), and `c` is `τ`-fixed, hence so is `c⁻¹`. Since
`|G| = [K : F]` is odd and the characteristic is two, squaring is bijective on `F[G]`
(`mul_self_bijective'`), so `exists_mul_involute_eq` of
`MIPRE.Foundations.LowDegree.SelfDualize` produces `a` with `a · τa = c⁻¹`. Then
`β = ofAlg a` has Gram element `1`, i.e. its Frobenius orbit is orthonormal.

What is *not* here is the `poly(k)` algorithm that produces such a basis; the blueprint's
`lem:self-dual-basis` still waits on that half.
-/

namespace MIPRE.LowDegree

open Finset

/-! ## Squaring on a group algebra, multiplicatively -/

section MulSelfDualize

variable {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G]
variable {F : Type*} [Field F] [Fintype F]

end MulSelfDualize

/-! ## The Gram element of a Frobenius orbit -/

section Existence

attribute [local instance] IsCyclic.commGroup

variable (F K : Type*) [Field F] [Fintype F] [Field K] [Algebra F K] [Finite K]
  [FiniteDimensional F K] [IsGalois F K]

/-- The involution of the group algebra induced by `g ↦ g⁻¹`. -/
noncomputable def galStar :
    MonoidAlgebra F (K ≃ₐ[F] K) ≃+* MonoidAlgebra F (K ≃ₐ[F] K) :=
  (MonoidAlgebra.domCongr F F (MulEquiv.inv (K ≃ₐ[F] K))).toRingEquiv

/-- The Gram element of a pair: its coefficient at `g` is `tr(x · g y)`. For `x = y` the
Gram matrix of the Frobenius orbit of `x` is the circulant this determines. -/
noncomputable def gramPair (x y : K) : MonoidAlgebra F (K ≃ₐ[F] K) :=
  .ofCoeff (Finsupp.equivFunOnFinite.symm fun g => Algebra.trace F K (x * g y))

variable {F K}

omit [Fintype F] [Finite K] [IsGalois F K] in
@[simp] theorem coeff_gramPair (x y : K) (g : K ≃ₐ[F] K) :
    (gramPair F K x y).coeff g = Algebra.trace F K (x * g y) := rfl

omit [Fintype F] [FiniteDimensional F K] [IsGalois F K] in
@[simp] theorem coeff_galStar (a : MonoidAlgebra F (K ≃ₐ[F] K)) (g : K ≃ₐ[F] K) :
    (galStar F K a).coeff g = a.coeff g⁻¹ := by
  simp [galStar]

/-! ## The Gram element is a unit -/

/-! ## A self-dual normal element, and the basis -/

variable (F K)

variable {F K}

variable (F K)

end Existence

end MIPRE.LowDegree


