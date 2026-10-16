-- Prove2me | Definitions.Def_Esgk_PlaneAffineLinePolynomial
-- name    : Esgk_PlaneAffineLinePolynomial
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-10-16T04:48:42.013005+00:00
-- url     : https://prove2.me/theorems/1c3c59cf-c7b3-418c-9ba1-8ddf2fd43bcf
-- title:
--   The polynomial of an affine line
-- statement:
--   This defines the determinant polynomial $v_2(X-x_1)-v_1(Y-x_2)$ for the line through $x$ in direction $v$. When $v$ is nonzero, the polynomial is irreducible and its zero set is the stated affine line.

-- Extracted dependency interfaces and their necessary proofs.
import Definitions.Def_Esgk_IrreduciblePlaneInfiniteVanishing
import Definitions.Def_LeanFormalizations_PachDeZeeuw_AlgebraicPrelim
import Mathlib
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


namespace Esgk

open EuclideanGeometry
open PachDeZeeuw.Algebraic

 
noncomputable def affineLinePolynomial (x v : Point2) :
    MvPolynomial (Fin 2) ℝ :=
  MvPolynomial.C (v 1) * (MvPolynomial.X 0 - MvPolynomial.C (x 0)) -
    MvPolynomial.C (v 0) * (MvPolynomial.X 1 - MvPolynomial.C (x 1))

 
theorem affineLinePolynomial_eval (x v z : Point2) :
    MvPolynomial.eval (fun i ↦ z i) (affineLinePolynomial x v) =
      v 1 * (z 0 - x 0) - v 0 * (z 1 - x 1) := by
  simp [affineLinePolynomial]

 
theorem affineLinePolynomial_zeroSet_eq_line (x v : Point2) :
    PlaneCurveZeroSet (affineLinePolynomial x v) =
      {z : Point2 |
        v 1 * z 0 + (-v 0) * z 1 = v 1 * x 0 - v 0 * x 1} := by
  ext z
  change MvPolynomial.eval (fun i ↦ z i) (affineLinePolynomial x v) = 0 ↔ _
  rw [affineLinePolynomial_eval]
  constructor
  · intro h
    change v 1 * z 0 + (-v 0) * z 1 = v 1 * x 0 - v 0 * x 1
    ring_nf at h ⊢
    linarith
  · intro h
    change v 1 * z 0 + (-v 0) * z 1 = v 1 * x 0 - v 0 * x 1 at h
    ring_nf at h ⊢
    linarith

 
theorem affineLinePolynomial_direction_ne_zero
    {v : Point2} (hv : v ≠ 0) :
    (v 1, -v 0) ≠ (0, 0) := by
  intro hcoeff
  have hv1 : v 1 = 0 := congrArg Prod.fst hcoeff
  have hv0 : v 0 = 0 := by
    have h := congrArg Prod.snd hcoeff
    simpa using neg_eq_zero.mp h
  apply hv
  ext i
  fin_cases i
  · exact hv0
  · exact hv1


theorem affineLinePolynomial_irreducible
    {x v : Point2} (hv : v ≠ 0) :
    Irreducible (affineLinePolynomial x v) := by
  classical
  have hform : affineLinePolynomial x v =
      MvPolynomial.C (v 1) * MvPolynomial.X 0 +
        MvPolynomial.C (-v 0) * MvPolynomial.X 1 +
          MvPolynomial.C (v 0 * x 1 - v 1 * x 0) := by
    dsimp [affineLinePolynomial]
    rw [mul_sub, mul_sub, ← MvPolynomial.C_mul, ← MvPolynomial.C_mul]
    rw [MvPolynomial.C_sub, MvPolynomial.C_neg]
    ring_nf
  apply MvPolynomial.irreducible_of_totalDegree_eq_one
  · have hupper : (affineLinePolynomial x v).totalDegree ≤ 1 := by
      rw [hform]
      have hlin :
          ((MvPolynomial.C (v 1) * MvPolynomial.X 0 +
            MvPolynomial.C (-v 0) * MvPolynomial.X 1) :
            MvPolynomial (Fin 2) ℝ).totalDegree ≤ 1 := by
        calc
          _ ≤ max (MvPolynomial.totalDegree
                ((MvPolynomial.C (v 1) * MvPolynomial.X 0) :
                  MvPolynomial (Fin 2) ℝ))
              (MvPolynomial.totalDegree
                ((MvPolynomial.C (-v 0) * MvPolynomial.X 1) :
                  MvPolynomial (Fin 2) ℝ)) :=
            MvPolynomial.totalDegree_add _ _
          _ ≤ 1 := by
            apply max_le
            · have h := MvPolynomial.totalDegree_mul
                  (MvPolynomial.C (v 1) : MvPolynomial (Fin 2) ℝ)
                  (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℝ)
              simpa using h
            · have h := MvPolynomial.totalDegree_mul
                  (MvPolynomial.C (-v 0) : MvPolynomial (Fin 2) ℝ)
                  (MvPolynomial.X 1 : MvPolynomial (Fin 2) ℝ)
              simpa using h
      calc
        (MvPolynomial.C (v 1) * MvPolynomial.X 0 +
            MvPolynomial.C (-v 0) * MvPolynomial.X 1 +
              (MvPolynomial.C (v 0 * x 1 - v 1 * x 0) :
                MvPolynomial (Fin 2) ℝ)).totalDegree ≤
            max (MvPolynomial.totalDegree
              ((MvPolynomial.C (v 1) * MvPolynomial.X 0 +
                MvPolynomial.C (-v 0) * MvPolynomial.X 1) :
                MvPolynomial (Fin 2) ℝ))
              (MvPolynomial.totalDegree
                (MvPolynomial.C (v 0 * x 1 - v 1 * x 0) :
                  MvPolynomial (Fin 2) ℝ)) :=
          MvPolynomial.totalDegree_add
            (MvPolynomial.C (v 1) * MvPolynomial.X 0 +
              MvPolynomial.C (-v 0) * MvPolynomial.X 1)
            (MvPolynomial.C (v 0 * x 1 - v 1 * x 0) :
              MvPolynomial (Fin 2) ℝ)
        _ ≤ 1 := max_le hlin (by
          simpa only [MvPolynomial.totalDegree_C] using
            (show 0 ≤ 1 by omega))
    apply le_antisymm hupper
    have hzero0 : (0 : Fin 2 →₀ ℕ) ≠ Finsupp.single (0 : Fin 2) 1 := by
      intro h
      have hh := congrArg (fun d : Fin 2 →₀ ℕ ↦ d 0) h
      simp at hh
    have hzero1 : (0 : Fin 2 →₀ ℕ) ≠ Finsupp.single (1 : Fin 2) 1 := by
      intro h
      have hh := congrArg (fun d : Fin 2 →₀ ℕ ↦ d 1) h
      simp at hh
    have hcoeff0 :
        (affineLinePolynomial x v).coeff (Finsupp.single (0 : Fin 2) 1) =
          v 1 := by
      rw [hform]
      simp [hzero0]
    have hcoeff1 :
        (affineLinePolynomial x v).coeff (Finsupp.single (1 : Fin 2) 1) =
          -v 0 := by
      rw [hform]
      simp [hzero1]
    by_cases hv1 : v 1 = 0
    · have hv0 : v 0 ≠ 0 := by
        intro hv0
        apply hv
        ext i
        fin_cases i <;> assumption
      have hmem : Finsupp.single (1 : Fin 2) 1 ∈
          (affineLinePolynomial x v).support :=
        MvPolynomial.mem_support_iff.mpr (by
          rw [hcoeff1]
          exact neg_ne_zero.mpr hv0)
      simpa using MvPolynomial.le_totalDegree hmem
    · have hmem : Finsupp.single (0 : Fin 2) 1 ∈
          (affineLinePolynomial x v).support :=
        MvPolynomial.mem_support_iff.mpr (by
          rw [hcoeff0]
          exact hv1)
      simpa using MvPolynomial.le_totalDegree hmem
  · intro a ha
    apply isUnit_iff_ne_zero.mpr
    intro ha0
    have hzero0 : (0 : Fin 2 →₀ ℕ) ≠ Finsupp.single (0 : Fin 2) 1 := by
      intro h
      have hh := congrArg (fun d : Fin 2 →₀ ℕ ↦ d 0) h
      simp at hh
    have hzero1 : (0 : Fin 2 →₀ ℕ) ≠ Finsupp.single (1 : Fin 2) 1 := by
      intro h
      have hh := congrArg (fun d : Fin 2 →₀ ℕ ↦ d 1) h
      simp at hh
    have hcoeff0 :
        (affineLinePolynomial x v).coeff (Finsupp.single (0 : Fin 2) 1) =
          v 1 := by
      rw [hform]
      simp [hzero0]
    have hcoeff1 :
        (affineLinePolynomial x v).coeff (Finsupp.single (1 : Fin 2) 1) =
          -v 0 := by
      rw [hform]
      simp [hzero1]
    by_cases hv1 : v 1 = 0
    · have hv0 : v 0 ≠ 0 := by
        intro hv0
        apply hv
        ext i
        fin_cases i <;> assumption
      have hcoef :
          (affineLinePolynomial x v).coeff
              (Finsupp.single (1 : Fin 2) 1) ≠ 0 := by
        rw [hcoeff1]
        exact neg_ne_zero.mpr hv0
      rcases ha (Finsupp.single (1 : Fin 2) 1) with ⟨b, hb⟩
      apply hcoef
      rw [hb, ha0, zero_mul]
    · have hcoef :
          (affineLinePolynomial x v).coeff
              (Finsupp.single (0 : Fin 2) 1) ≠ 0 := by
        rw [hcoeff0]
        exact hv1
      rcases ha (Finsupp.single (0 : Fin 2) 1) with ⟨b, hb⟩
      apply hcoef
      rw [hb, ha0, zero_mul]

end Esgk


