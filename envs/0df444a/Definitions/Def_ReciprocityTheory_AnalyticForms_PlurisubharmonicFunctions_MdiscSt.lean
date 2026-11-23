-- Prove2me | Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
-- name    : ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:07:30.343116+00:00
-- url     : https://prove2.me/theorems/d4f30684-a1aa-4dd7-94fc-120403ddda51
-- title:
--   Mdisc St
-- statement:
--   Definitions and structural lemmas for Mdisc St, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/MdiscSt.lean

import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscPos
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.AnForm.A
open Matrix
open scoped ComplexOrder
variable {D : ℕ}
noncomputable def colMap (j : Fin D) : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] (Fin D → ℂ) where
  toFun X := fun i => X i j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
noncomputable def mdiscML :
    MultilinearMap ℂ (fun _ : Fin D => Matrix (Fin D) (Fin D) ℂ) ℂ :=
  ∑ σ : Equiv.Perm (Fin D), (1 / (D.factorial : ℂ)) •
    ((Matrix.detRowAlternating (R := ℂ) (n := Fin D)).toMultilinearMap.compLinearMap
      colMap).domDomCongr σ
end ReciprocityTheory.AnForm.A


