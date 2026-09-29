-- Prove2me | Definitions.Def_mme_dwz_table2_completed_fine_words
-- name    : mme_dwz_table2_completed_fine_words
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-08-26T09:55:13.871303+00:00
-- url     : https://prove2.me/theorems/5c43159c-64ce-4436-899b-7ed726ab2ac9
-- title:
--   Canonical X/Y fine-word completion of a Table-2 Z word
-- statement:
--   Given a retained Table-2 component word and a pointwise fine $Z$ word whose two grades coarsen to the row's $Z$ degree, choose at every position one of the valid local X/Y completions. The resulting functions provide left and right fine-grade words in all three modes: mode $0$ is the selected $X$ split, mode $1$ is the selected $Y$ split, and mode $2$ is definitionally the supplied $Z$ split.
--
--   The accompanying completion structure stores the X/Y coarse equations and the two CW half-support equations at each position. This is grade-level data only; it does not duplicate the X/Y tensor spaces or assert a hole mask.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Section 5.1 component decomposition and Section 6.1 Additional Zeroing-Out Step 1, printed pp. 45--52 (PDF pp. 46--53), specialized to Table 2; https://arxiv.org/abs/2210.10173

import Theorems.Thm_mme_dwz_table2_fine_z_pair_has_xy_completion
import Definitions.Def_mme_CW_square_five_grade_certificate

open MME

universe u

namespace MME.DWZStep2Source

set_option autoImplicit false
set_option warningAsError true

structure FineXYCompletion (s : Fin 15) (zLeft zRight : Fin 3) where
  xLeft : Fin 3
  xRight : Fin 3
  yLeft : Fin 3
  yRight : Fin 3
  x_coarse : xLeft.val + xRight.val = MME.DWZSquare.shapeX s
  y_coarse : yLeft.val + yRight.val = MME.DWZSquare.shapeY s
  left_support : xLeft.val + yLeft.val + zLeft.val = 2
  right_support : xRight.val + yRight.val + zRight.val = 2

noncomputable def fineXYCompletion
    (s : Fin 15) (zLeft zRight : Fin 3)
    (hZ : MME.DWZTable2Counts.coarseOf (zLeft, zRight) =
      MME.DWZSquare.shapeZ s) : FineXYCompletion s zLeft zRight := by
  classical
  let h := mme_dwz_table2_fine_z_pair_has_xy_completion s zLeft zRight hZ
  let xLeft := Classical.choose h
  let h₁ := Classical.choose_spec h
  let xRight := Classical.choose h₁
  let h₂ := Classical.choose_spec h₁
  let yLeft := Classical.choose h₂
  let h₃ := Classical.choose_spec h₂
  let yRight := Classical.choose h₃
  let hs := Classical.choose_spec h₃
  exact ⟨xLeft, xRight, yLeft, yRight,
    hs.1, hs.2.1, hs.2.2.1, hs.2.2.2⟩

noncomputable def completedFineLeft
    {Position : Type u} (outer : Position → Fin 15)
    (z : Position → Fin 3 × Fin 3)
    (hZ : ∀ t, MME.DWZTable2Counts.coarseOf (z t) =
      MME.DWZSquare.shapeZ (outer t)) :
    Fin 3 → Position → Fin 3 := fun i t ↦
  let c := fineXYCompletion (outer t) (z t).1 (z t).2 (hZ t)
  ![c.xLeft, c.yLeft, (z t).1] i

noncomputable def completedFineRight
    {Position : Type u} (outer : Position → Fin 15)
    (z : Position → Fin 3 × Fin 3)
    (hZ : ∀ t, MME.DWZTable2Counts.coarseOf (z t) =
      MME.DWZSquare.shapeZ (outer t)) :
    Fin 3 → Position → Fin 3 := fun i t ↦
  let c := fineXYCompletion (outer t) (z t).1 (z t).2 (hZ t)
  ![c.xRight, c.yRight, (z t).2] i

end MME.DWZStep2Source


