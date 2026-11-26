-- Prove2me | Definitions.Def_FourierJacobi_Analysis_ValuationSeries
-- name    : FourierJacobi_Analysis_ValuationSeries
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T09:48:22.275273+00:00
-- url     : https://prove2.me/theorems/5631b174-9f82-573d-9606-9c362f4921c7
-- title:
--   Valuation Series
-- statement:
--   Definitions and structural lemmas for Valuation Series, from Abhishek Saha (abhisaha-git/fourier-jacobi-core-evaluation; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Explicit Fourier-Jacobi Haar-core evaluation and Abel limits development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/ValuationSeries.lean

import Definitions.Def_FourierJacobi_Algebra_RegionSum
import Definitions.Def_FourierJacobi_Valuations_Cartan
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
noncomputable section
namespace FourierJacobi.Analysis
open FourierJacobi.Valuations
set_option maxHeartbeats 2000000
def i0Shell (t d U V T : ℂ) (p : ℤ × ℤ × ℤ) : ℂ :=
  let ell := (cartanIndices 0 p.1 p.2.1 p.2.2 0).1
  let b := (cartanIndices 0 p.1 p.2.1 p.2.2 0).2
  (1 - t ^ 2) ^ 2 * d ^ p.1 *
    t ^ (3 * p.1 + 2 * p.2.1 + 2 * p.2.2 + 3 * ell + 4 * b) *
    (T * U) ^ (ell / 2) * (T * V) ^ b
abbrev I0PositiveRow (tail : Bool) :=
  {p : ℤ × ℤ × ℤ // 0 ≤ p.1 ∧ -2 * p.1 ≤ p.2.1 ∧
    if tail then p.2.2 < -p.1 else -p.1 ≤ p.2.2}
def i0PositiveRowEquiv (tail : Bool) : (ℕ × ℕ × ℕ) ≃ I0PositiveRow tail where
  toFun n := ⟨((n.1 : ℤ), (n.2.1 : ℤ) - 2 * n.1,
    if tail then -(n.1 : ℤ) - n.2.2 - 1 else (n.2.2 : ℤ) - n.1), by
      cases tail <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega⟩
  invFun p := (p.val.1.toNat, (p.val.2.1 + 2 * p.val.1).toNat,
    (if tail then -p.val.1 - p.val.2.2 - 1 else p.val.2.2 + p.val.1).toNat)
  left_inv n := by
    rcases n with ⟨k, j, h⟩
    cases tail <;> simp only [Bool.false_eq_true, ↓reduceIte, Prod.mk.injEq]
    all_goals omega
  right_inv p := by
    apply Subtype.ext
    rcases p with ⟨⟨k, j, h⟩, hk, hj, hh⟩
    change 0 ≤ k at hk
    change -2 * k ≤ j at hj
    change (if tail then h < -k else -k ≤ h) at hh
    cases tail
    · change ((k.toNat : ℤ), ((j + 2 * k).toNat : ℤ) - 2 * k.toNat,
        ((h + k).toNat : ℤ) - k.toNat) = (k, j, h)
      simp only [Bool.false_eq_true, ↓reduceIte] at hh
      simp only [Prod.mk.injEq]
      omega
    · change ((k.toNat : ℤ), ((j + 2 * k).toNat : ℤ) - 2 * k.toNat,
        -(k.toNat : ℤ) - (-k - h - 1).toNat - 1) = (k, j, h)
      simp only [↓reduceIte] at hh
      simp only [Prod.mk.injEq]
      omega
@[simp] theorem i0PositiveRowEquiv_val (tail : Bool) (n : ℕ × ℕ × ℕ) :
    (i0PositiveRowEquiv tail n).val = ((n.1 : ℤ), (n.2.1 : ℤ) - 2 * n.1,
      if tail then -(n.1 : ℤ) - n.2.2 - 1 else (n.2.2 : ℤ) - n.1) := rfl
abbrev I0NegativeRow (tail : Bool) :=
  {p : ℤ × ℤ × ℤ // p.1 < 0 ∧ 0 ≤ p.2.1 ∧
    if tail then p.2.2 < 0 else 0 ≤ p.2.2}
def i0NegativeRowEquiv (tail : Bool) : (ℕ × ℕ × ℕ) ≃ I0NegativeRow tail where
  toFun n := ⟨(-(n.1 : ℤ) - 1, (n.2.1 : ℤ),
    if tail then -(n.2.2 : ℤ) - 1 else (n.2.2 : ℤ)), by
      cases tail <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega⟩
  invFun p := ((-p.val.1 - 1).toNat, p.val.2.1.toNat,
    (if tail then -p.val.2.2 - 1 else p.val.2.2).toNat)
  left_inv n := by
    rcases n with ⟨k, j, h⟩
    cases tail <;> simp only [Bool.false_eq_true, ↓reduceIte, Prod.mk.injEq]
    all_goals omega
  right_inv p := by
    apply Subtype.ext
    rcases p with ⟨⟨k, j, h⟩, hk, hj, hh⟩
    change k < 0 at hk
    change 0 ≤ j at hj
    change (if tail then h < 0 else 0 ≤ h) at hh
    cases tail
    · change (-((-k - 1).toNat : ℤ) - 1, (j.toNat : ℤ), (h.toNat : ℤ)) = (k, j, h)
      simp only [Bool.false_eq_true, ↓reduceIte] at hh
      simp only [Prod.mk.injEq]
      omega
    · change (-((-k - 1).toNat : ℤ) - 1, (j.toNat : ℤ),
        -((-h - 1).toNat : ℤ) - 1) = (k, j, h)
      simp only [↓reduceIte] at hh
      simp only [Prod.mk.injEq]
      omega
end FourierJacobi.Analysis


