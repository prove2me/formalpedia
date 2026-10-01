-- Prove2me | Definitions.Def_Yukon_a85eef42acfe35aea0456d85
-- name    : Yukon_a85eef42acfe35aea0456d85
-- status  : Definition
-- author  : @yukon
-- created : 2026-09-30T18:39:44.834934+00:00
-- url     : https://prove2.me/theorems/aa707c45-2671-4f09-85e0-7a1458dd3baf
-- title:
--   YukonModule.CompPoly.ToMathlib.Polynomial.BivariateMultiplicity.part0
-- statement:
--   Source module CompPoly.ToMathlib.Polynomial.BivariateMultiplicity.
-- source:
--   https://github.com/zksecurity/CompPoly/blob/641694629e4557520a1539b272ec338c9f3044c7/CompPoly/ToMathlib/Polynomial/BivariateMultiplicity.lean
--
--   yukon-proof-operation:c7e71ba5d2fa86299fafea1ad06920f963e46abbd2cf7c57d75f9afbae5b6c2c
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiMDUzNDJlZDk1YmEwMjRhMjZjMDI0MzJkNDc4NDQ0YzhmYzMxNTljNjE1YTdlZWE3YzVmM2VlZDFkNzhjYTY0NCIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmM3ZTcxYmE1ZDJmYTg2Mjk5ZmFmZWExYWQwNjkyMGY5NjNlNDZhYmJkMmNmN2M1N2Q3NWY5YWZiYWU1YjZjMmMiLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl9hODVlZWY0MmFjZmUzNWFlYTA0NTZkODUiLCJ2IjoyfQ]

/-
Copyright (c) 2026 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Definitions.Def_Yukon_df15ca12ddf2d8e2d1b3970a

public import Mathlib.RingTheory.Polynomial.Resultant.Basic


public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Aesop
public import Mathlib.Algebra.Polynomial.Bivariate
public import Mathlib.Data.Nat.Log
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Tactic.Cases
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Data.List.GetD
public import Mathlib.Algebra.GroupWithZero.Nat
public import Init
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.Algebra.Tropical.Basic
public import Mathlib.Algebra.Ring.TransferInstance
public import Mathlib.Algebra.Polynomial.Inductions
meta import Definitions.Def_Yukon_df15ca12ddf2d8e2d1b3970a
set_option backward.isDefEq.respectTransparency.types false
/-!
# Mathlib-Facing Bivariate Multiplicity Helpers

This file collects multiplicity- and discriminant-oriented helpers for Mathlib's
bivariate polynomial surface `R[X][Y]`.
-/

@[expose] public section

open Polynomial
open scoped Polynomial.Bivariate

namespace Polynomial.Bivariate

noncomputable section

variable {F : Type*}

section Semiring

variable [Semiring F]

/-- Root multiplicity of a bivariate polynomial at the origin. -/
def rootMultiplicity₀ [DecidableEq F] (f : F[X][Y]) : Option ℕ :=
  let deg := weightedDegree f 1 1
  match deg with
  | none => none
  | some deg =>
      List.min? <|
        List.filterMap
          (fun (i, j) ↦ if coeff f i j = 0 then none else some (i + j))
          (List.product (List.range deg.succ) (List.range deg.succ))

end Semiring

section CommSemiring

variable [CommSemiring F]

/-- Shift a bivariate polynomial by `(x, y)`. -/
def shift (f : F[X][Y]) (x y : F) : F[X][Y] :=
  (f.comp (Y + C (C y))).map (Polynomial.compRingHom (X + C x : F[X]))

variable [DecidableEq F]

/-- Root multiplicity (order of vanishing) of a bivariate polynomial at `(x, y)`. -/
def rootMultiplicity (f : F[X][Y]) (x y : F) : Option ℕ :=
  rootMultiplicity₀ (shift f x y)

/-- `rootMultiplicity₀ g` is at least `r` (vacuously so when `g = 0`, where it is `none`)
iff every coefficient of total degree `< r` vanishes. -/
theorem rootMultiplicity₀_ge_iff (g : F[X][Y]) (r : ℕ) :
    (∀ i j, i + j < r → coeff g i j = 0) ↔ ∀ m ∈ rootMultiplicity₀ g, r ≤ m := by
  obtain ⟨deg, hdeg⟩ : ∃ d, weightedDegree g 1 1 = some d :=
    ⟨natWeightedDegree g 1 1, weightedDegree_eq_natWeightedDegree⟩
  have hdegval : deg = natWeightedDegree g 1 1 := by
    have h := weightedDegree_eq_natWeightedDegree (f := g) (u := 1) (v := 1)
    rw [hdeg] at h; exact Option.some.inj h
  have hroot : rootMultiplicity₀ g =
      (List.filterMap (fun p : ℕ × ℕ ↦ if coeff g p.1 p.2 = 0 then none else some (p.1 + p.2))
        (List.range (deg + 1) ×ˢ List.range (deg + 1))).min? := by
    simp only [rootMultiplicity₀, hdeg]; rfl
  have grid_mem : ∀ i j, coeff g i j ≠ 0 →
      (i, j) ∈ List.range (deg + 1) ×ˢ List.range (deg + 1) := by
    intro i j hne
    have hi : i ≤ (g.coeff j).natDegree := le_natDegree_of_ne_zero (by simpa [coeff] using hne)
    have hbound : (g.coeff j).natDegree + j ≤ deg := by
      rw [hdegval]
      simpa [natWeightedDegree] using
        Finset.le_sup (f := fun m => 1 * (g.coeff m).natDegree + 1 * m)
          (Polynomial.mem_support_iff.mpr fun h => hne (by simp [coeff, h]))
    simp only [List.mem_product, List.mem_range]; omega
  rw [hroot]
  set L := List.filterMap (fun p : ℕ × ℕ ↦ if coeff g p.1 p.2 = 0 then none else some (p.1 + p.2))
      (List.range (deg + 1) ×ˢ List.range (deg + 1)) with hL
  constructor
  · intro H m hm
    rw [Option.mem_def] at hm
    have hmem := List.min?_mem hm
    rw [hL, List.mem_filterMap] at hmem
    obtain ⟨⟨i, j⟩, _, hsome⟩ := hmem
    by_cases hz : coeff g i j = 0
    · simp [hz] at hsome
    · simp only [hz, if_false, Option.some.injEq] at hsome
      subst hsome; by_contra hlt; exact hz (H i j (by omega))
  · intro H i j hij
    by_contra hne
    have hmem : i + j ∈ L := by
      rw [hL, List.mem_filterMap]; exact ⟨(i, j), grid_mem i j hne, by simp [hne]⟩
    obtain ⟨m₀, hm₀⟩ : ∃ m₀, L.min? = some m₀ := by
      cases hc : L.min? with
      | none => simp [List.min?_eq_none_iff.mp hc] at hmem
      | some m₀ => exact ⟨m₀, rfl⟩
    have hr := H m₀ (Option.mem_def.mpr hm₀)
    have hle := (List.min?_eq_some_iff.mp hm₀).2 _ hmem
    omega

end CommSemiring

section CommRing

variable [CommRing F]

/-- A discriminant-like helper in the outer `Y` variable.

Unlike Mathlib's univariate `discr`, this returns `0` for constant bivariate polynomials. -/
def discr_y (f : F[X][Y]) : F[X] :=
  if 0 < f.degree then
    (-1) ^ (f.natDegree * (f.natDegree - 1) / 2) * f.discr
  else
    0

end CommRing

end
end Polynomial.Bivariate


