-- Prove2me | Definitions.Def_mme_dwz_table2_standard_z_basis
-- name    : mme_dwz_table2_standard_z_basis
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-08-26T09:05:24.64478+00:00
-- url     : https://prove2.me/theorems/6e58b2f6-84cf-4c8b-9977-83c31f6e0e8c
-- title:
--   Canonical grouped available-word basis of the complete Table-2 standard tensor
-- statement:
--   Fix a field $K$ and an integral scale $m\geq0$. The $Z$ mode of the complete Table-2 standard-form tensor
--
--   $$
--   T^*(m)=\bigotimes_{s=0}^{14}T_s^{\otimes n_s m}[\widetilde\alpha_s]
--   $$
--
--   has a canonical basis indexed by families that choose one available canonical component word in every row $s$. It is the heterogeneous tensor-product basis formed from the available-word basis of each of the fifteen restricted component factors.
--
--   The index family retains the exact source coordinate word and hence its literal useful fine-pair label. The construction keeps the standard tensor as one ordered Kronecker product with shared $X$ and $Y$ modes; it introduces neither a tensor direct sum nor a retained/hole mask.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Definitions 5.2--5.4 and Definition 6.3, specialized to Section 6.3/Table 2; https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_kronFin_mode_pi_basis
import Definitions.Def_mme_dwz_table2_standard_obj
import Definitions.Def_mme_dwz_restricted_component_z_basis

open MME Module

universe u

namespace MME.DWZComponentRestriction

set_option autoImplicit false
set_option warningAsError true

/-- The canonical grouped available-word basis of the complete Table-2
standard object's actual Z mode. -/
noncomputable def dwzTable2StandardZBasis
    (K : Type u) [Field K] (m : ℕ) :
    Basis (GroupedAllowedWords.{u} m) K
      ((dwzTable2StandardObj K m).V 2) := by
  unfold dwzTable2StandardObj
  exact MME.TensorObj.kronFinModePiBasis 15
    (fun s ↦ restrictedComponentPower K s m) 2
    (fun s ↦ restrictedComponentZBasis K s m)

end MME.DWZComponentRestriction


