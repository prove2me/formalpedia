-- Prove2me | Definitions.Def_ReciprocityTheory_SemistableReduction_FinrankRestrictTotalDegree
-- name    : ReciprocityTheory_SemistableReduction_FinrankRestrictTotalDegree
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:24:20.219654+00:00
-- url     : https://prove2.me/theorems/78be5b7c-084f-4b41-9e2f-aac3261494f9
-- title:
--   Finrank Restrict Total Degree
-- statement:
--   Definitions and structural lemmas for Finrank Restrict Total Degree, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/FinrankRestrictTotalDegree.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_ComapInclusionIsLocalHom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.MultiplicativeHeights
noncomputable def degreeLeEquivAntidiag (D e : ℕ) :
    {α : Fin D →₀ ℕ // α.degree ≤ e} ≃
      ((Finset.univ : Finset (Fin (D + 1))).finsuppAntidiag e) where
  toFun α := ⟨Finsupp.equivFunOnFinite.symm (Fin.cons (e - α.1.degree) (⇑α.1)), by
    rw [Finset.mem_finsuppAntidiag]
    refine ⟨?_, Finset.subset_univ _⟩
    rw [Fin.sum_univ_succ]
    simp only [Finsupp.coe_equivFunOnFinite_symm, Fin.cons_zero, Fin.cons_succ]
    rw [← Finsupp.degree_eq_sum]
    have := α.2
    omega⟩
  invFun β := ⟨Finsupp.equivFunOnFinite.symm (Fin.tail ⇑β.1), by
    have h := (Finset.mem_finsuppAntidiag.mp β.2).1
    rw [Fin.sum_univ_succ] at h
    rw [Finsupp.degree_eq_sum]
    simp only [Finsupp.coe_equivFunOnFinite_symm, Fin.tail]
    omega⟩
  left_inv α := by
    apply Subtype.ext
    ext i
    simp
  right_inv β := by
    apply Subtype.ext
    ext i
    have h := (Finset.mem_finsuppAntidiag.mp β.2).1
    rw [Fin.sum_univ_succ] at h
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Finsupp.coe_equivFunOnFinite_symm, Fin.cons_zero]
      rw [Finsupp.degree_eq_sum]
      simp only [Finsupp.coe_equivFunOnFinite_symm, Fin.tail]
      omega
    · simp [Fin.tail]
end ReciprocityTheory.MultiplicativeHeights


