-- Prove2me | Definitions.Def_TauCeti_RingTheory_NormTrace_Prod
-- name    : TauCeti_RingTheory_NormTrace_Prod
-- status  : Definition
-- author  : @riccardo.brasca
-- created : 2026-09-29T19:48:13.824494+00:00
-- url     : https://prove2.me/theorems/9cab5581-3b11-4677-9a8f-65a4445daccd
-- title:
--   Norms of binary products
-- statement:
--   For a product of two finite free algebras over a common commutative ring, multiplication acts independently on the factors, and the algebra norm satisfies
--
--   $$
--   N(x,y)=N_1(x)N_2(y).
--   $$
--
--   This is the binary product form of norm multiplicativity across components.
--
--   **Formalization Note.** These foundational declarations are transplanted from the Tau Ceti contributors' [original source](https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/RingTheory/NormTrace/Prod.lean) (Apache-2.0, commit `948fe4751b1fe528b6d580c522ca5d743d47f185`), with compatibility adaptations for Lean 4.33.1. Mathematical proofs requiring separate theorem nodes are published separately.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/RingTheory/NormTrace/Prod.lean

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Mathlib.RingTheory.Norm.Defs

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Norms of binary products

This file records the norm of an element of a product of two algebras, together with the
description of multiplication on such a product as a `LinearMap.prodMap`.  The dependent
finite-product analogues are in `TauCeti.RingTheory.NormTrace.Pi`, and the trace of a binary
product is Mathlib's `Algebra.trace_prod_apply`.
-/

 section

namespace TauCeti

section Lmul

variable {K : Type*} [CommSemiring K]
variable {A B : Type*} [Semiring A] [Semiring B] [Algebra K A] [Algebra K B]

/-- Multiplication by an element of a product of two algebras acts on the two factors
independently, so as a `K`-linear map it is the product of the multiplications by its
components. -/
theorem Algebra.lmul_prod (x : A × B) :
    Algebra.lmul K (A × B) x =
      LinearMap.prodMap (Algebra.lmul K A x.1) (Algebra.lmul K B x.2) :=
  LinearMap.ext fun _ ↦ rfl

end Lmul

section Norm

variable {K : Type*} [CommRing K]
variable {A B : Type*} [Ring A] [Ring B] [Algebra K A] [Algebra K B]

/-- The norm of an element of a product of two algebras is the product of its component norms. -/
@[simp]
theorem Algebra.norm_prod [Module.Free K A] [Module.Finite K A] [Module.Free K B]
    [Module.Finite K B] (x : A × B) :
    Algebra.norm K x = Algebra.norm K x.1 * Algebra.norm K x.2 := by
  rw [Algebra.norm_apply, Algebra.lmul_prod, LinearMap.det_prodMap, Algebra.norm_apply,
    Algebra.norm_apply]

end Norm

end TauCeti

end
end


