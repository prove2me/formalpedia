-- Prove2me | Definitions.Def_Paley11987Support_032
-- name    : Paley11987Support_032
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-23T01:38:31.753194+00:00
-- url     : https://prove2.me/theorems/8704907f-44c5-419a-b2b7-194b3b6ab1c2
-- title:
--   The Paley core construction
-- statement:
--   Defines the Paley-core construction together with the quadratic-character identities required to construct its core data.
--
--   **Formalization Note.** This is the definition interface for the supplied proof module CompactDRTPaley.
-- source:
--   User-supplied paley11987_complete_proof.zip, SHA256 fe0ca82767dc3fbdfbd49761a4a7746918039d0c0c741580ac5685bce3104dd7; source module CompactDRTPaley, SHA256 bff98e590c33fec98bc9259e30ceb3688ec975506a3250f731b79ca2952dde04

import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.GroupWithZero.Units.Equiv
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Paley11987Support_000
import Definitions.Def_Paley11987Support_001
import Definitions.Def_Paley11987Support_002
import Definitions.Def_Paley11987Support_003
import Definitions.Def_Paley11987Support_004
import Definitions.Def_Paley11987Support_005
import Definitions.Def_Paley11987Support_006
import Definitions.Def_Paley11987Support_007
import Definitions.Def_Paley11987Support_008
import Definitions.Def_Paley11987Support_009
import Definitions.Def_Paley11987Support_010
import Definitions.Def_Paley11987Support_011
import Definitions.Def_Paley11987Support_012
import Definitions.Def_Paley11987Support_013
import Definitions.Def_Paley11987Support_014
import Definitions.Def_Paley11987Support_015
import Definitions.Def_Paley11987Support_016
import Definitions.Def_Paley11987Support_017
import Definitions.Def_Paley11987Support_018
import Definitions.Def_Paley11987Support_019
import Definitions.Def_Paley11987Support_020
import Definitions.Def_Paley11987Support_021
import Definitions.Def_Paley11987Support_022
import Definitions.Def_Paley11987Support_023
import Definitions.Def_Paley11987Support_024
import Definitions.Def_Paley11987Support_025
import Definitions.Def_Paley11987Support_026
import Definitions.Def_Paley11987Support_027
import Definitions.Def_Paley11987Support_028
import Definitions.Def_Paley11987Support_029
import Definitions.Def_Paley11987Support_030
import Definitions.Def_Paley11987Support_031

set_option autoImplicit false
set_option Elab.async false
section z48

namespace CompactDRT
open Finset
noncomputable section
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem quadratic_neg (hm : quadraticChar F (-1) = -1) (z : F) :
    quadraticChar F (-z) = -quadraticChar F z := by
  rw [show -z = (-1) * z by ring, map_mul, hm]
  ring

theorem quadratic_correlation_one (hc : ringChar F ≠ 2)
    (hm : quadraticChar F (-1) = -1) :
    ∑ z : F, quadraticChar F z * quadraticChar F (z - 1) = -1 := by
  have hj := jacobiSum_nontrivial_inv (quadraticChar_ne_one hc)
  rw [(quadraticChar_isQuadratic F).inv, hm] at hj
  have hneg : ∀ z : F, quadraticChar F (z - 1) = -quadraticChar F (1 - z) := by
    intro z
    rw [show z - 1 = -(1 - z) by ring]
    exact quadratic_neg hm (1 - z)
  simp_rw [hneg, mul_neg]
  rw [Finset.sum_neg_distrib]
  change -jacobiSum (quadraticChar F) (quadraticChar F) = -1
  rw [hj]
  norm_num

theorem quadratic_correlation (hc : ringChar F ≠ 2)
    (hm : quadraticChar F (-1) = -1) (x y : F) (hxy : x ≠ y) :
    ∑ z : F, quadraticChar F (z - x) * quadraticChar F (z - y) = -1 := by
  have hd : y - x ≠ 0 := sub_ne_zero.mpr hxy.symm
  let e : F ≃ F := (Equiv.mulLeft₀ (y - x) hd).trans (Equiv.addLeft x)
  calc
    _ = ∑ u : F, quadraticChar F ((y - x) * u) *
        quadraticChar F ((y - x) * (u - 1)) := by
      rw [← e.sum_comp]
      apply Finset.sum_congr rfl
      intro u _
      congr 1 <;> congr 1 <;> simp only [e, Equiv.trans_apply, Equiv.mulLeft₀_apply]
      all_goals change x + (y - x) * u - _ = _
      all_goals ring
    _ = ∑ u : F, quadraticChar F u * quadraticChar F (u - 1) := by
      apply Finset.sum_congr rfl
      intro u _
      rw [map_mul, map_mul]
      calc
        _ = quadraticChar F (y - x) ^ 2 *
            (quadraticChar F u * quadraticChar F (u - 1)) := by ring
        _ = _ := by rw [quadraticChar_sq_one hd, one_mul]
    _ = -1 := quadratic_correlation_one hc hm

theorem quadratic_square_sum (x : F) :
    ∑ z : F, quadraticChar F (z - x) * quadraticChar F (z - x) =
      (Fintype.card F : ℤ) - 1 := by
  have hterm : ∀ z : F, quadraticChar F z * quadraticChar F z = 1 - delta 0 z := by
    intro z
    by_cases hz : z = 0
    · subst z; simp [quadraticChar_zero]
    · have hs := quadraticChar_sq_one hz
      simpa [pow_two, delta, Ne.symm hz] using hs
  calc
    _ = ∑ z : F, quadraticChar F z * quadraticChar F z :=
      (Equiv.subRight x).sum_comp (fun z => quadraticChar F z * quadraticChar F z)
    _ = ∑ z : F, (1 - delta 0 z) := by simp_rw [hterm]
    _ = _ := by simp [Finset.sum_sub_distrib]

def paleyCore (hc : ringChar F ≠ 2) (hm : quadraticChar F (-1) = -1) : Core F where
  sign x y := quadraticChar F (y - x)
  diag x := by simp [quadraticChar_zero]
  skew x y := by
    rw [show x - y = -(y - x) by ring]
    exact quadratic_neg hm (y - x)
  off x y hxy := quadraticChar_dichotomy (sub_ne_zero.mpr hxy.symm)
  row x := by
    calc
      _ = ∑ z : F, quadraticChar F z := (Equiv.subRight x).sum_comp (quadraticChar F)
      _ = 0 := quadraticChar_sum_zero hc
  gram x y := by
    by_cases hxy : x = y
    · subst y
      simpa using quadratic_square_sum x
    · simpa [delta, hxy] using quadratic_correlation hc hm x y hxy















end
end CompactDRT
end z48


