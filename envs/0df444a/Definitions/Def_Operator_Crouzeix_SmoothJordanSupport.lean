-- Prove2me | Definitions.Def_Operator_Crouzeix_SmoothJordanSupport
-- name    : Operator_Crouzeix_SmoothJordanSupport
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:30:31.494982+00:00
-- url     : https://prove2.me/theorems/af7a04a4-590b-5a6d-9c3b-a0ec27ea611d
-- title:
--   Smooth Jordan Support
-- statement:
--   Definitions and structural lemmas for Smooth Jordan Support, from Ezzeri Esa (savarin/lean-operator-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Crouzeix-Palencia theorem, von Neumann inequality, and unitary power dilation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanSupport.lean

import Definitions.Def_Operator_Crouzeix_SmoothApprox
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Topology.Order.IntermediateValue
set_option autoImplicit false
open Complex Set
open scoped Real
theorem SmoothJordanDomain.carrier_nonempty
    (Omega : SmoothJordanDomain) : Omega.carrier.Nonempty := by
  have hfrontier : (frontier Omega.carrier).Nonempty :=
    ⟨Omega.boundaryParam 0, by
      rw [← Omega.boundaryParam_range]
      exact mem_range_self 0⟩
  by_contra hnot
  have hempty : Omega.carrier = ∅ := not_nonempty_iff_eq_empty.mp hnot
  rw [hempty, frontier_empty] at hfrontier
  exact hfrontier.ne_empty rfl
noncomputable def SmoothJordanDomain.reverseOrientation
    (Omega : SmoothJordanDomain) : SmoothJordanDomain where
  carrier := Omega.carrier
  isOpen_carrier := Omega.isOpen_carrier
  strictConvex_carrier := Omega.strictConvex_carrier
  boundaryParam := fun t ↦ Omega.boundaryParam (2 * Real.pi - t)
  boundaryParam_periodic := by
    intro t
    calc
      Omega.boundaryParam (2 * Real.pi - (t + 2 * Real.pi)) =
          Omega.boundaryParam (-t) := by
            congr 1
            ring_nf
      _ = Omega.boundaryParam (2 * Real.pi - t) :=
        Omega.boundaryParam_periodic.sub_eq'.symm
  boundaryParam_contDiff :=
    Omega.boundaryParam_contDiff.comp (contDiff_const.sub contDiff_id)
  boundaryParam_range := by
    apply Set.Subset.antisymm
    · rintro z ⟨t, rfl⟩
      rw [← Omega.boundaryParam_range]
      exact mem_range_self (2 * Real.pi - t)
    · intro z hz
      rw [← Omega.boundaryParam_range] at hz
      obtain ⟨u, rfl⟩ := hz
      refine ⟨2 * Real.pi - u, ?_⟩
      ring_nf
  boundaryParam_injOn := by
    intro x hx y hy hxy
    let r : ℝ → ℝ := fun t ↦ if t = 0 then 0 else 2 * Real.pi - t
    have hr_mem : ∀ t ∈ Ico (0 : ℝ) (2 * Real.pi),
        r t ∈ Ico (0 : ℝ) (2 * Real.pi) := by
      intro t ht
      by_cases ht0 : t = 0
      · subst t
        simp only [r, if_pos, mem_Ico, le_refl, true_and]
        positivity
      · have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
        simp only [r, ht0, if_false, mem_Ico]
        exact ⟨(sub_pos.mpr ht.2).le, sub_lt_self _ htpos⟩
    have hparam : ∀ t ∈ Ico (0 : ℝ) (2 * Real.pi),
        Omega.boundaryParam (2 * Real.pi - t) =
          Omega.boundaryParam (r t) := by
      intro t _ht
      by_cases ht0 : t = 0
      · subst t
        simp only [sub_zero, r, if_pos]
        simpa only [zero_add] using Omega.boundaryParam_periodic 0
      · simp only [ht0, ↓reduceIte, r]
    have hr_eq : r x = r y := by
      apply Omega.boundaryParam_injOn (hr_mem x hx) (hr_mem y hy)
      rw [← hparam x hx, ← hparam y hy]
      exact hxy
    by_cases hx0 : x = 0
    · by_cases hy0 : y = 0
      · exact hx0.trans hy0.symm
      · subst x
        simp only [r, if_pos, hy0, if_false] at hr_eq
        have : 0 < 2 * Real.pi - y := sub_pos.mpr hy.2
        linarith
    · by_cases hy0 : y = 0
      · subst y
        simp only [r, hx0, if_false, if_pos] at hr_eq
        have : 0 < 2 * Real.pi - x := sub_pos.mpr hx.2
        linarith
      · simp only [r, hx0, hy0, if_false] at hr_eq
        linarith
  boundaryParam_regular := by
    intro t
    rw [deriv_comp_const_sub]
    exact neg_ne_zero.mpr (Omega.boundaryParam_regular (2 * Real.pi - t))
noncomputable def SmoothJordanDomain.orientationPointSupport
    (Omega : SmoothJordanDomain) : ℂ :=
  Classical.choose Omega.carrier_nonempty
noncomputable def SmoothJordanDomain.canonicalOrientation
    (Omega : SmoothJordanDomain) : SmoothJordanDomain :=
  if ((starRingEnd ℂ) (-I * deriv Omega.boundaryParam 0) *
      (Omega.orientationPointSupport - Omega.boundaryParam 0)).re ≤ 0 then
    Omega
  else
    Omega.reverseOrientation


