-- Prove2me | solution 1 for AaronsonAmbainis.DetBij.exists_lowest_Qmat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:40:04.472212+00:00
-- url     : https://prove2.me/submissions/45f59e12-fb85-4bda-b998-4bfb5c75fe5b

import Definitions.Def_AaronsonAmbainis_DetBij_Identity
import Definitions.Def_AaronsonAmbainis_DetBij_Perm
import Theorems.Thm_AaronsonAmbainis_DetBij_exists_isLowest
import Theorems.Thm_AaronsonAmbainis_DetBij_det_Pmat_mul_det_agMatrix
import Theorems.Thm_AaronsonAmbainis_DetBij_constantCoeff_det_Pmat
import Theorems.Thm_AaronsonAmbainis_DetBij_constantCoeff_det_Umat


set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.DetBij
open Finset MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace AaronsonAmbainis.DetBij
theorem _root_.solution (hU : LowestUnit) (hB : LowestBound) (g : Cube ι → Bool)
    (A : Cube ι → Finset ι) (hA : ∀ x : Ones g, IsWing g x.1 (A x.1)) :
    ∃ m : ι →₀ ℕ, m ∈ (Qmat g A).det.support ∧ ∀ j, m j ≤ bdry g j := by
  obtain ⟨hp, hbound⟩ := hB ι g
  have hdet := det_Pmat_mul_det_agMatrix g A hA
  have hP : (Pmat g A).det ≠ 0 := by
    intro h
    have h1 := constantCoeff_det_Pmat g A
    rw [h, map_zero] at h1
    exact zero_ne_one h1
  have hQ : (Qmat g A).det ≠ 0 := by
    intro h
    rw [h, mul_zero] at hdet
    exact (mul_ne_zero hP hp) hdet
  obtain ⟨m, hm⟩ := exists_isLowest _ hQ
  refine ⟨m, hm.1, hbound m ?_⟩
  have h1 : IsLowest ((Umat g A).det * (Qmat g A).det) m :=
    (hU ι _ _ (constantCoeff_det_Umat g A) m).mpr hm
  rw [← hdet] at h1
  exact (hU ι _ _ (constantCoeff_det_Pmat g A) m).mp h1
end AaronsonAmbainis.DetBij
