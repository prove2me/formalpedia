-- Prove2me | solution 1 for AllOnesLab.irreducible_allOnes_of_irreducible_allOnesP
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T20:57:56.924082+00:00
-- url     : https://prove2.me/submissions/4cbcf368-f5e5-4c9c-82c6-c2fb21923729

import Definitions.Def_AllOnesLab_Defs
import Definitions.Def_AllOnesLab_Basic
import Theorems.Thm_AllOnesLab_P_natDegree
import Theorems.Thm_AllOnesLab_allOnes_natDegree
import Theorems.Thm_AllOnesLab_allOnesP_eq_comp
section
open Polynomial
namespace AllOnesLab
private lemma natDegree_comp_P (a : (ZMod 2)[X]) : (a.comp P).natDegree = 2 * a.natDegree := by
  rw [natDegree_comp, P_natDegree, Nat.mul_comm]
private lemma isUnit_of_isUnit_comp_P {a : (ZMod 2)[X]} (h : IsUnit (a.comp P)) : IsUnit a := by
  have hdeg : a.natDegree = 0 := by
    have h0 := natDegree_eq_zero_of_isUnit h
    rw [natDegree_comp_P] at h0
    omega
  have ha : a ≠ 0 := by
    rintro rfl
    rw [zero_comp] at h
    simp at h
  obtain ⟨c, hc⟩ := natDegree_eq_zero.mp hdeg
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [map_zero] at hc
    exact ha hc.symm
  rw [← hc, isUnit_C]
  exact isUnit_iff_ne_zero.mpr hc0
end AllOnesLab
end

set_option autoImplicit true
open Polynomial
open AllOnesLab
namespace AllOnesLab
theorem _root_.solution (n : ℕ) (hn : 2 ≤ n)
    (h : Irreducible (allOnesP n)) : Irreducible (allOnes n) := by
  constructor
  · exact not_isUnit_of_natDegree_pos _ (by rw [allOnes_natDegree]; omega)
  · intro a b hab
    have hcomp : allOnesP n = a.comp P * b.comp P := by
      rw [allOnesP_eq_comp, hab, mul_comp]
    rcases h.isUnit_or_isUnit hcomp with hu | hu
    · exact Or.inl (isUnit_of_isUnit_comp_P hu)
    · exact Or.inr (isUnit_of_isUnit_comp_P hu)
end AllOnesLab
