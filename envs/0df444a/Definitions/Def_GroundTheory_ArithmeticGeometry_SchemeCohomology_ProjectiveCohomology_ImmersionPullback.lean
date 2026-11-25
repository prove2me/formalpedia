-- Prove2me | Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjectiveCohomology_ImmersionPullback
-- name    : GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjectiveCohomology_ImmersionPullback
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T00:30:22.571982+00:00
-- url     : https://prove2.me/theorems/91a51b13-d528-4438-a280-9a3303f5aa4e
-- title:
--   Immersion Pullback
-- statement:
--   Definitions and structural lemmas for Immersion Pullback, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProjectiveCohomology/ImmersionPullback.lean

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_EtaleCompletion_QcohZariski
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_InvertibleDual
import Theorems.Thm_GroundTheory_Arith_Etale_pullbackUnitApp_bijective
import Theorems.Thm_GroundTheory_Arith_Etale_pullbackUnitApp_comp
import Theorems.Thm_GroundTheory_Arith_Etale_pullbackUnitApp_comp_hom
import Theorems.Thm_GroundTheory_Arith_Etale_pullbackUnitApp_res

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Arith.SchemeCoh
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Limits MonoidalCategory
open GroundTheory.Arith.Etale (pullbackUnitApp pullbackUnitApp_res pullbackUnitApp_comp
  pullbackUnitApp_comp_hom pullbackUnitApp_bijective)
universe u
noncomputable section
variable {Y Z : Scheme.{u}}
instance final_opensMap (f : Y ⟶ Z) : (Opens.map f.base).Final :=
  Functor.final_of_exists_of_isFiltered _ (fun _ => ⟨⊤, ⟨homOfLE le_top⟩⟩)
    (fun _ _ => ⟨_, 𝟙 _, rfl⟩)
set_option backward.isDefEq.respectTransparency.types false in

def pullbackUnitIso (f : Y ⟶ Z) :
    (Scheme.Modules.pullback f).obj (SheafOfModules.unit Z.ringCatSheaf) ≅
      SheafOfModules.unit Y.ringCatSheaf :=
  let e := asIso (C := SheafOfModules Y.ringCatSheaf)
    (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom)
  ⟨e.hom, e.inv, e.hom_inv_id, e.inv_hom_id⟩
def unitOne (Z : Scheme.{u}) (O : Z.Opens) : Γ(SheafOfModules.unit Z.ringCatSheaf, O) :=
  (1 : Γ(Z, O))
abbrev appR (j : Y ⟶ Z) (V : Z.Opens) : ringOn Z V →+* ringOn Y (j ⁻¹ᵁ V) := (j.app V).hom
end
end GroundTheory.Arith.SchemeCoh


