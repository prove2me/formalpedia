-- Prove2me | Definitions.Def_Esgk_IrreduciblePlaneInfiniteVanishing
-- name    : Esgk_IrreduciblePlaneInfiniteVanishing
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-10-16T04:47:18.118308+00:00
-- url     : https://prove2.me/theorems/b5fd1b14-0a33-44d6-9363-0b4a15137978
-- title:
--   Divisibility from an infinite intersection of irreducible curves
-- statement:
--   For irreducible plane polynomials, this establishes divisibility when their zero sets have an infinite intersection under the stated hypotheses.

-- Extracted dependency interfaces and their necessary proofs.
import Definitions.Def_LeanFormalizations_PachDeZeeuw_AlgebraicPrelim
import Definitions.Def_LeanFormalizations_PachDeZeeuw_Bezout
import Mathlib

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


namespace Esgk

open PachDeZeeuw.Algebraic


theorem dvd_of_infinite_irreducible_zeroSet_intersection
    {C q : MvPolynomial (Fin 2) ℝ}
    (hC : Irreducible C)
    (hinf : (PlaneCurveZeroSet C ∩ PlaneCurveZeroSet q).Infinite) :
    C ∣ q := by
  by_cases hq : q = 0
  · simp [hq]
  · by_contra hCdvd
    have hnoinf : ¬ HasCommonInfiniteIrreducibleFactor C q := by
      intro hcommon
      rcases hcommon with ⟨h, hh, hhinf, hdivC, hdivq⟩
      have hassoc : Associated C h :=
        (hC.dvd_iff.mp hdivC).resolve_left hh.not_isUnit
      exact hCdvd ((hassoc.dvd_iff_dvd_left).2 hdivq)
    have hfinite :=
      (factorized_bezout_bound (d₁ := C.totalDegree) (d₂ := q.totalDegree)
        C q hC.ne_zero hq le_rfl le_rfl hnoinf).1
    exact (Set.not_infinite.mpr hfinite) hinf

end Esgk


