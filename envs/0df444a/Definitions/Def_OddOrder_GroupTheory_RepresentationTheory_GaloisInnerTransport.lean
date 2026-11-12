-- Prove2me | Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_GaloisInnerTransport
-- name    : OddOrder_GroupTheory_RepresentationTheory_GaloisInnerTransport
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T05:07:56.08462+00:00
-- url     : https://prove2.me/theorems/d5cf130d-cf88-4942-8bce-e265fb66b285
-- title:
--   Galois transport of virtual-character inner products
-- statement:
--   Shows that the coefficientwise action of a ring automorphism $\sigma:\mathbb{C}\simeq+*\mathbb{C}$ on class functions is a $\mathbb{Z}$-isometry of the virtual character lattice of a finite group. The bundle consists of lemmas only.
--
--   The bundle also proves 2 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/GroupTheory/RepresentationTheory/GaloisInnerTransport.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/RepresentationTheory/GaloisInnerTransport.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_GaloisCharacter
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_InducedCharacter
import Definitions.Def_OddOrder_Algebra_GaloisRationalInteger

namespace OddOrder.RepresentationTheory.ClassFunction

open OddOrder.RepresentationTheory

variable {L : Type*} [Group L]

/-- **`mapRingEquiv` is a `ℤ`-isometry of `ZIrr`**: a coefficient automorphism preserves the inner
product of two virtual characters.  Unlike `ClassFunction.mapRingEquiv_inner`, no global
commutation with complex conjugation is needed: virtual-character values satisfy
`χ(g⁻¹) = star (χ(g))`, and the common inner product is a rational integer. -/
theorem inner_mapRingEquiv_eq_of_mem_ZIrr [Finite L] [Fintype L]
    [Invertible (Nat.card L : ℂ)]
    (σ : ℂ ≃+* ℂ) {φ η : ClassFunction L ℂ}
    (hφ : φ ∈ ZIrr L) (hη : η ∈ ZIrr L) :
    ClassFunction.inner (ClassFunction.mapRingEquiv σ φ)
        (ClassFunction.mapRingEquiv σ η)
      = ClassFunction.inner φ η := by
  have hstar (g : L) :
      star (ClassFunction.mapRingEquiv σ η g) = σ (star (η g)) := by
    rw [← OddOrder.Algebra.apply_inv_eq_star_of_mem_ZIrr
      (ClassFunction.mapRingEquiv_mem_ZIrr σ hη) g,
      ClassFunction.mapRingEquiv_apply,
      OddOrder.Algebra.apply_inv_eq_star_of_mem_ZIrr hη g]
  obtain ⟨m, hm⟩ := ClassFunction.inner_mem_ZIrr_int hφ hη
  have hsum :
      ClassFunction.innerSum (ClassFunction.mapRingEquiv σ φ)
          (ClassFunction.mapRingEquiv σ η)
        = σ (ClassFunction.innerSum φ η) := by
    rw [ClassFunction.innerSum, ClassFunction.innerSum, map_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    change σ (φ g) * star (σ (η g)) = σ (φ g * star (η g))
    have hg := hstar g
    change star (σ (η g)) = σ (star (η g)) at hg
    rw [hg, map_mul]
  calc
    ClassFunction.inner (ClassFunction.mapRingEquiv σ φ)
        (ClassFunction.mapRingEquiv σ η)
        = σ (ClassFunction.inner φ η) := by
      rw [ClassFunction.inner, ClassFunction.inner, hsum]
      have hcoef : σ (⅟(Nat.card L : ℂ)) = ⅟(Nat.card L : ℂ) := by
        simp [invOf_eq_inv, map_inv₀, map_natCast]
      calc
        ⅟(Nat.card L : ℂ) * σ (ClassFunction.innerSum φ η)
            = σ (⅟(Nat.card L : ℂ)) * σ (ClassFunction.innerSum φ η) := by rw [hcoef]
        _ = σ (⅟(Nat.card L : ℂ) * ClassFunction.innerSum φ η) := (map_mul σ _ _).symm
    _ = ClassFunction.inner φ η := by rw [hm]; simp

/-- **The Galois coefficient-constancy engine** (Coq `a_aut`): if a coefficient automorphism moves
`φ` only by a correction orthogonal to the transported test vector `η' = σ(η)`, then the integral
coefficient of `φ` along `η` transports to `η'` unchanged: `⟨φ, η⟩ = m ⟹ ⟨φ, η'⟩ = m`.  This is
the Peterfalvi (3.9.b)-type row/column constancy step of the (10.9)/(11.9.a) grid analyses. -/
theorem inner_eq_intCast_of_mapRingEquiv_eq_add [Fintype L]
    [Invertible (Nat.card L : ℂ)]
    (σ : ℂ ≃+* ℂ)
    {φ η η' correction : ClassFunction L ℂ} (m : ℤ)
    (hφZ : φ ∈ ZIrr L) (hηZ : η ∈ ZIrr L)
    (hφ : ClassFunction.mapRingEquiv σ φ = φ + correction)
    (hη : ClassFunction.mapRingEquiv σ η = η')
    (hm : ClassFunction.inner φ η = (m : ℂ))
    (hcorrection : ClassFunction.inner correction η' = 0) :
    ClassFunction.inner φ η' = (m : ℂ) := by
  have htransport := inner_mapRingEquiv_eq_of_mem_ZIrr σ hφZ hηZ
  rw [hφ, hη, ClassFunction.inner_add_left, hcorrection, add_zero, hm] at htransport
  simpa using htransport

end OddOrder.RepresentationTheory.ClassFunction


