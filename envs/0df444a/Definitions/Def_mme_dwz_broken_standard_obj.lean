-- Prove2me | Definitions.Def_mme_dwz_broken_standard_obj
-- name    : mme_dwz_broken_standard_obj
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-08-26T09:14:09.27674+00:00
-- url     : https://prove2.me/theorems/285cdf6d-5b02-4697-ac38-5e8ab577e795
-- title:
--   Literal nonhole mask on the DWZ Table-2 standard tensor
-- statement:
--   Fix a field $K$, an integral scale $m\geq0$, and one broken copy of the Duan--Wu--Zhou Table-2 standard-form tensor. Every canonical $Z$-basis word $W$ of the complete standard tensor determines a literal useful small-block label $\ell(W)$ carrying its complete fine left/right grade word. Define the surviving-word predicate by
--
--   $$
--   W\text{ survives }\Longleftrightarrow \ell(W)\in\operatorname{nonholes}(C).
--   $$
--
--   The broken standard grading places every $X$- and $Y$-mode vector in class zero and places a canonical $Z$-basis word in class zero exactly when it survives. The broken standard tensor $T_C^*(m)$ is the all-zero block of this grading. Consequently this definition deletes precisely the unavailable fine $Z$ blocks recorded by $C$ while retaining the shared $X$ and $Y$ mode spaces; it does not form a direct sum or duplicate either shared mode. The construction includes $m=0$.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Definitions 5.2--5.5 and Definition 6.3, PDF pp. 47--49 / printed pp. 46--48, specialized to Section 6.3/Table 2; https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_dwz_table2_standard_z_basis
import Definitions.Def_mme_basis_z_allowed_projection
import Definitions.Def_mme_dwz_hole_cover_data
import Theorems.Thm_mme_dwz_grouped_allowed_words_useful_certificate

open MME Module

universe u

namespace MME.DWZComponentRestriction

set_option autoImplicit false
set_option warningAsError true

noncomputable def groupedUsefulBlock
    (m : ℕ) (W : GroupedAllowedWords.{u} m) :
    MME.DWZTable2StandardForm.UsefulBlock m (groupedOuter (m := m)) :=
  ⟨groupedFineZ W, mme_dwz_grouped_allowed_words_useful_certificate m W⟩

def groupedWordSurvives
    (m : ℕ)
    (copy : MME.DWZSquare.BrokenBlockCopy
      (MME.DWZTable2StandardForm.UsefulBlock m
        (groupedOuter (m := m))))
    (W : GroupedAllowedWords.{u} m) : Prop :=
  groupedUsefulBlock m W ∈ copy.nonholes

noncomputable def dwzBrokenStandardGrading
    (K : Type u) [Field K] (m : ℕ)
    (copy : MME.DWZSquare.BrokenBlockCopy
      (MME.DWZTable2StandardForm.UsefulBlock m
        (groupedOuter (m := m)))) :
    (dwzTable2StandardObj K m).TypeGrading 2 := by
  letI : DecidablePred (groupedWordSurvives m copy) :=
    Classical.decPred _
  exact (dwzTable2StandardObj K m).basisZAllowedGrading
    (dwzTable2StandardZBasis K m) (groupedWordSurvives m copy)

noncomputable def dwzBrokenStandardObj
    (K : Type u) [Field K] (m : ℕ)
    (copy : MME.DWZSquare.BrokenBlockCopy
      (MME.DWZTable2StandardForm.UsefulBlock m
        (groupedOuter (m := m)))) : TensorObj K 3 :=
  (dwzBrokenStandardGrading K m copy).blockSubtensor (fun _ ↦ 0)

end MME.DWZComponentRestriction


