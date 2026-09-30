-- Prove2me | Definitions.Def_TauCeti_RingTheory_NormTrace_Pi
-- name    : TauCeti_RingTheory_NormTrace_Pi
-- status  : Definition
-- author  : @riccardo.brasca
-- created : 2026-09-29T19:48:14.261561+00:00
-- url     : https://prove2.me/theorems/22eb2dc5-cd7c-42b4-a329-0a78737ecea5
-- title:
--   Norms and traces of finite products
-- statement:
--   For a finite product of finite free algebras over a common commutative ring, the algebra norm of an element is the product of its component norms:
--
--   $$
--   N((x_i)_i)=\prod_i N_i(x_i).
--   $$
--
--   This describes norms on product decompositions such as the mixed embedding space.
--
--   **Formalization Note.** These foundational declarations are transplanted from the Tau Ceti contributors' [original source](https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/RingTheory/NormTrace/Pi.lean) (Apache-2.0, commit `948fe4751b1fe528b6d580c522ca5d743d47f185`), with compatibility adaptations for Lean 4.33.1. Mathematical proofs requiring separate theorem nodes are published separately.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/RingTheory/NormTrace/Pi.lean

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_LinearAlgebra_Pi
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.Trace
import Mathlib.RingTheory.Norm.Basic
import Mathlib.RingTheory.Trace.Basic

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Norms and traces of finite products

This file records the determinant, norm, and trace calculations for finite dependent products.
The scalar-extension identities used by the number-field local-global development live in
`TauCeti.RingTheory.NormTrace.BaseChange`.
-/

 section

namespace TauCeti

open scoped BigOperators

universe u v

variable {K : Type u} [CommRing K]

variable {ι : Type v} [Fintype ι]

open Module

section Norm

variable {L : ι → Type*} [∀ i, Ring (L i)] [∀ i, Algebra K (L i)]
  [∀ i, Module.Free K (L i)] [∀ i, Module.Finite K (L i)]

/-- The norm of an element of a finite dependent product is the product of its component norms. -/
@[simp]
theorem Algebra.norm_pi (x : ∀ i, L i) :
    Algebra.norm K x = ∏ i, Algebra.norm K (x i) := by
  rw [Algebra.norm_apply]
  have h : Algebra.lmul K (∀ i, L i) x =
      LinearMap.pi (fun i ↦ (Algebra.lmul K (L i) (x i)).comp (LinearMap.proj i)) := by
    ext y i
    simp [Algebra.lmul]
  rw [h]
  rw [LinearMap.det_pi_of_apply_eq_dependent
    (f := fun i ↦ Algebra.lmul K (L i) (x i)) (hT := by
    intro y i
    simp [Algebra.lmul])]
  simp_rw [Algebra.norm_apply]

end Norm

section Trace

variable {L : ι → Type*} [∀ i, CommRing (L i)] [∀ i, Algebra K (L i)]
  [∀ i, Module.Free K (L i)] [∀ i, Module.Finite K (L i)]



end Trace

end TauCeti

end
end


