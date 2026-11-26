-- Prove2me | Definitions.Def_FourierJacobi_Analysis_I0Complete
-- name    : FourierJacobi_Analysis_I0Complete
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T09:51:18.561038+00:00
-- url     : https://prove2.me/theorems/d7cf3083-faf7-4b2d-8279-ccb91b45853e
-- title:
--   I0 Complete
-- statement:
--   Definitions and structural lemmas for I0 Complete, from Abhishek Saha (abhisaha-git/fourier-jacobi-core-evaluation; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Explicit Fourier-Jacobi Haar-core evaluation and Abel limits development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I0Complete.lean

import Definitions.Def_FourierJacobi_Analysis_ValuationSeries
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Theorems.Thm_FourierJacobi_Analysis_i0NegativeRowEquiv_val
attribute [local simp] FourierJacobi.Analysis.i0NegativeRowEquiv_val


set_option autoImplicit false
noncomputable section
namespace FourierJacobi.Analysis
open FourierJacobi.Valuations
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
abbrev I0UpperRow (neg : Bool) :=
  {p : ℤ × ℤ × ℤ // (if neg then p.1 < 0 else 0 ≤ p.1) ∧
    p.2.1 < (if neg then 0 else -2 * p.1) ∧
    (if neg then p.2.1 else p.1 + p.2.1) ≤ p.2.2 ∧ p.2.1 ≤ 2 * p.2.2}
abbrev I0MiddleRow (neg : Bool) :=
  {p : ℤ × ℤ × ℤ // (if neg then p.1 < 0 else 0 ≤ p.1) ∧
    p.2.1 < (if neg then 0 else -2 * p.1) ∧
    (if neg then p.2.1 else p.1 + p.2.1) ≤ p.2.2 ∧ 2 * p.2.2 < p.2.1}
abbrev I0LowerRow (neg : Bool) :=
  {p : ℤ × ℤ × ℤ // (if neg then p.1 < 0 else 0 ≤ p.1) ∧
    p.2.1 < (if neg then 0 else -2 * p.1) ∧
    p.2.2 < (if neg then p.2.1 else p.1 + p.2.1)}
def i0MiddleRowEquiv (neg : Bool) : (ℕ × ℕ × ℕ) ≃ I0MiddleRow neg where
  toFun n := ⟨(if neg then -(n.1 : ℤ) - 1 else n.1,
    -(if neg then 0 else 2 * (n.1 : ℤ)) - 2 * n.2.1 - n.2.2 - 1,
    -(if neg then 0 else (n.1 : ℤ)) - n.2.1 - n.2.2 - 1), by
      cases neg <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega⟩
  invFun p := ((if neg then -p.val.1 - 1 else p.val.1).toNat,
    (p.val.2.2 - p.val.2.1 - (if neg then 0 else p.val.1)).toNat,
    (p.val.2.1 - 2 * p.val.2.2 - 1).toNat)
  left_inv n := by
    rcases n with ⟨m, j, h⟩
    cases neg <;> simp only [Bool.false_eq_true, ↓reduceIte, Prod.mk.injEq] <;> omega
  right_inv p := by
    apply Subtype.ext
    rcases p with ⟨⟨k, j, h⟩, hk, hj, hh, hc⟩
    change (if neg then k < 0 else 0 ≤ k) at hk
    change j < (if neg then 0 else -2 * k) at hj
    change (if neg then j else k + j) ≤ h at hh
    change 2 * h < j at hc
    cases neg
    · change 0 ≤ k at hk
      change j < -2 * k at hj
      change k + j ≤ h at hh
      change ((k.toNat : ℤ), -(2 * (k.toNat : ℤ)) - 2 * (h - j - k).toNat -
        (j - 2 * h - 1).toNat - 1,
        -(k.toNat : ℤ) - (h - j - k).toNat - (j - 2 * h - 1).toNat - 1) = (k, j, h)
      simp only [Prod.mk.injEq]
      omega
    · change k < 0 at hk
      change j < 0 at hj
      change j ≤ h at hh
      change (-((-k - 1).toNat : ℤ) - 1, -(0 : ℤ) - 2 * (h - j - 0).toNat -
        (j - 2 * h - 1).toNat - 1,
        -0 - ((h - j - 0).toNat : ℤ) - (j - 2 * h - 1).toNat - 1) = (k, j, h)
      simp only [Prod.mk.injEq]
      omega
def i0LowerRowEquiv (neg : Bool) : (ℕ × ℕ × ℕ) ≃ I0LowerRow neg where
  toFun n := ⟨(if neg then -(n.1 : ℤ) - 1 else n.1,
    -(if neg then 0 else 2 * (n.1 : ℤ)) - n.2.1 - 1,
    -(if neg then 0 else (n.1 : ℤ)) - n.2.1 - n.2.2 - 2), by
      cases neg <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega⟩
  invFun p := ((if neg then -p.val.1 - 1 else p.val.1).toNat,
    (-p.val.2.1 - (if neg then 0 else 2 * p.val.1) - 1).toNat,
    ((if neg then 0 else p.val.1) + p.val.2.1 - p.val.2.2 - 1).toNat)
  left_inv n := by
    rcases n with ⟨m, j, h⟩
    cases neg <;> simp only [Bool.false_eq_true, ↓reduceIte, Prod.mk.injEq] <;> omega
  right_inv p := by
    apply Subtype.ext
    rcases p with ⟨⟨k, j, h⟩, hk, hj, hh⟩
    change (if neg then k < 0 else 0 ≤ k) at hk
    change j < (if neg then 0 else -2 * k) at hj
    change h < (if neg then j else k + j) at hh
    cases neg
    · change 0 ≤ k at hk
      change j < -2 * k at hj
      change h < k + j at hh
      change ((k.toNat : ℤ), -(2 * (k.toNat : ℤ)) - (-j - 2 * k - 1).toNat - 1,
        -(k.toNat : ℤ) - (-j - 2 * k - 1).toNat - (k + j - h - 1).toNat - 2) = (k, j, h)
      simp only [Prod.mk.injEq]
      omega
    · change k < 0 at hk
      change j < 0 at hj
      change h < j at hh
      change (-((-k - 1).toNat : ℤ) - 1, -0 - ((-j - 0 - 1).toNat : ℤ) - 1,
        -0 - ((-j - 0 - 1).toNat : ℤ) - (0 + j - h - 1).toNat - 2) = (k, j, h)
      simp only [Prod.mk.injEq]
      omega
def i0UpperRowEquiv (neg : Bool) : (Fin 2 × ℕ × ℕ × ℕ) ≃ I0UpperRow neg where
  toFun n := ⟨(if neg then -(n.2.1 : ℤ) - 1 else n.2.1,
    -(if neg then 0 else 2 * (n.2.1 : ℤ)) - 2 * n.2.2.1 - n.1.val - 1,
    -(if neg then 0 else (n.2.1 : ℤ)) - n.2.2.1 - n.1.val + n.2.2.2), by
      have he := n.1.isLt
      cases neg <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega⟩
  invFun p :=
    let s := -p.val.2.1 - (if neg then 0 else 2 * p.val.1) - 1
    (⟨(s % 2).toNat, by omega⟩,
      (if neg then -p.val.1 - 1 else p.val.1).toNat,
      (s / 2).toNat,
      (p.val.2.2 + (if neg then 0 else p.val.1) + s / 2 + s % 2).toNat)
  left_inv n := by
    rcases n with ⟨e, m, j, h⟩
    have he := e.isLt
    cases neg <;> simp only [Bool.false_eq_true, ↓reduceIte, Prod.mk.injEq, Fin.ext_iff]
    all_goals omega
  right_inv p := by
    apply Subtype.ext
    rcases p with ⟨⟨k, j, h⟩, hk, hj, hh, hc⟩
    change (if neg then k < 0 else 0 ≤ k) at hk
    change j < (if neg then 0 else -2 * k) at hj
    change (if neg then j else k + j) ≤ h at hh
    change j ≤ 2 * h at hc
    cases neg
    · change 0 ≤ k at hk
      change j < -2 * k at hj
      change k + j ≤ h at hh
      let s : ℤ := -j - 2 * k - 1
      change ((k.toNat : ℤ), -(2 * (k.toNat : ℤ)) - 2 * (s / 2).toNat -
        (s % 2).toNat - 1,
        -(k.toNat : ℤ) - (s / 2).toNat - (s % 2).toNat +
          (h + k + s / 2 + s % 2).toNat) = (k, j, h)
      simp only [Prod.mk.injEq]
      dsimp [s]
      omega
    · change k < 0 at hk
      change j < 0 at hj
      change j ≤ h at hh
      let s : ℤ := -j - 0 - 1
      change (-((-k - 1).toNat : ℤ) - 1, -(0 : ℤ) - 2 * (s / 2).toNat - (s % 2).toNat - 1,
        -0 - ((s / 2).toNat : ℤ) - (s % 2).toNat +
          (h + 0 + s / 2 + s % 2).toNat) = (k, j, h)
      simp only [Prod.mk.injEq]
      dsimp [s]
      omega
def i0KRatio (neg : Bool) (t d V T : ℂ) : ℂ :=
  if neg then T * V * t / d else d * T * V * t
def i0KInitial (neg : Bool) (t d V T : ℂ) : ℂ :=
  if neg then T * V * t / d else 1
def i0Region (i : Fin 10) : Set (ℤ × ℤ × ℤ) :=
  match i.val with
  | 0 => {p | 0 ≤ p.1 ∧ -2 * p.1 ≤ p.2.1 ∧ -p.1 ≤ p.2.2}
  | 1 => {p | 0 ≤ p.1 ∧ -2 * p.1 ≤ p.2.1 ∧ p.2.2 < -p.1}
  | 2 => {p | 0 ≤ p.1 ∧ p.2.1 < -2 * p.1 ∧ p.1 + p.2.1 ≤ p.2.2 ∧ p.2.1 ≤ 2 * p.2.2}
  | 3 => {p | 0 ≤ p.1 ∧ p.2.1 < -2 * p.1 ∧ p.1 + p.2.1 ≤ p.2.2 ∧ 2 * p.2.2 < p.2.1}
  | 4 => {p | 0 ≤ p.1 ∧ p.2.1 < -2 * p.1 ∧ p.2.2 < p.1 + p.2.1}
  | 5 => {p | p.1 < 0 ∧ 0 ≤ p.2.1 ∧ 0 ≤ p.2.2}
  | 6 => {p | p.1 < 0 ∧ 0 ≤ p.2.1 ∧ p.2.2 < 0}
  | 7 => {p | p.1 < 0 ∧ p.2.1 < 0 ∧ p.2.1 ≤ p.2.2 ∧ p.2.1 ≤ 2 * p.2.2}
  | 8 => {p | p.1 < 0 ∧ p.2.1 < 0 ∧ p.2.1 ≤ p.2.2 ∧ 2 * p.2.2 < p.2.1}
  | _ => {p | p.1 < 0 ∧ p.2.1 < 0 ∧ p.2.2 < p.2.1}
def i0RegionIndex (p : ℤ × ℤ × ℤ) : Fin 10 :=
  if 0 ≤ p.1 then
    if -2 * p.1 ≤ p.2.1 then
      if -p.1 ≤ p.2.2 then 0 else 1
    else if p.2.2 < p.1 + p.2.1 then 4
    else if p.2.1 ≤ 2 * p.2.2 then 2 else 3
  else
    if 0 ≤ p.2.1 then
      if 0 ≤ p.2.2 then 5 else 6
    else if p.2.2 < p.2.1 then 9
    else if p.2.1 ≤ 2 * p.2.2 then 7 else 8
end FourierJacobi.Analysis


