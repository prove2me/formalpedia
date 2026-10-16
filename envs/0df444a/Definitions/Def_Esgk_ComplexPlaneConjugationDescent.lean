-- Prove2me | Definitions.Def_Esgk_ComplexPlaneConjugationDescent
-- name    : Esgk_ComplexPlaneConjugationDescent
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-10-16T04:46:39.789294+00:00
-- url     : https://prove2.me/theorems/516e064a-7730-4835-94ba-4d343a8f2990
-- title:
--   Coefficientwise complex conjugation of plane polynomials
-- statement:
--   This defines the ring isomorphism that applies complex conjugation to every coefficient of a complex bivariate polynomial.

-- Extracted dependency interfaces and their necessary proofs.
import Definitions.Def_Esgk_PlaneProjectiveHomogenization
import Mathlib
import Mathlib.Algebra.Star.Basic

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


noncomputable section

namespace Esgk

open PachDeZeeuw.Algebraic
open scoped ComplexConjugate

 
def complexPlanePolynomialConjugation : ComplexPlanePoly ≃+* ComplexPlanePoly := by
  let f : ComplexPlanePoly →+* ComplexPlanePoly := MvPolynomial.map (conj : ℂ →+* ℂ)
  have hf : Function.Bijective f := by
    refine ⟨MvPolynomial.map_injective (conj : ℂ →+* ℂ) ?_, ?_⟩
    · intro z w h
      simpa only [starRingEnd_self_apply] using congrArg (conj : ℂ → ℂ) h
    · intro p
      refine ⟨f p, ?_⟩
      change MvPolynomial.map (conj : ℂ →+* ℂ) (MvPolynomial.map (conj : ℂ →+* ℂ) p) = p
      rw [MvPolynomial.map_map]
      have hcomp : (conj : ℂ →+* ℂ).comp (conj : ℂ →+* ℂ) = RingHom.id ℂ := by
        ext z
        exact starRingEnd_self_apply z
      rw [hcomp, MvPolynomial.map_id]
  exact RingEquiv.ofBijective f hf


end Esgk


