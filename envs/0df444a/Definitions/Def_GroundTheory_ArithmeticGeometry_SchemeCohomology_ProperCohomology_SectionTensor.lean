-- Prove2me | Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProperCohomology_SectionTensor
-- name    : GroundTheory_ArithmeticGeometry_SchemeCohomology_ProperCohomology_SectionTensor
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T05:10:49.983631+00:00
-- url     : https://prove2.me/theorems/890850f5-c9c8-43c2-8077-a4088b7aea0c
-- title:
--   Section Tensor
-- statement:
--   Definitions and structural lemmas for Section Tensor, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProperCohomology/SectionTensor.lean

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProperCohomology_RestrictTensor
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_ext

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
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace MonoidalCategory TensorProduct
universe u
noncomputable section
variable {X : Scheme.{u}}
def homOfPreMod {M S : X.Modules} (g : (preMod X).obj M ⟶ (preMod X).obj S) : M ⟶ S :=
  inv ((sheafifyModAdj X).counit.app M) ≫ ((sheafifyModAdj X).homEquiv _ _).symm g
variable (M L : X.Modules) (s : Γ(L, ⊤))
def tensorSection : (preMod X).obj M ⟶ (preMod X).obj M ⊗ (preMod X).obj L :=
  PresheafOfModules.homMk
    { app := fun U => AddCommGrpCat.ofHom
        { toFun := fun m => (m : ((preMod X).obj M).obj U) ⊗ₜ
            resM ((preMod X).obj L) (le_top : U.unop ≤ ⊤) s
          map_zero' := zero_tmul _ _
          map_add' := fun a b => add_tmul _ _ _ }
      naturality := fun U V g => by
        ext m
        change (((preMod X).obj M).map g m) ⊗ₜ resM ((preMod X).obj L) (le_top : V.unop ≤ ⊤) s =
          (((preMod X).obj M).map g m) ⊗ₜ ((preMod X).obj L).map g
            (resM ((preMod X).obj L) (le_top : U.unop ≤ ⊤) s)
        congr 1
        change ((preMod X).obj L).map (homOfLE (le_top : V.unop ≤ ⊤)).op s =
          ((preMod X).obj L).map g (((preMod X).obj L).map (homOfLE (le_top : U.unop ≤ ⊤)).op s)
        exact PresheafOfModules.map_comp_apply ((preMod X).obj L) (homOfLE (le_top : U.unop ≤ ⊤)).op g s }
    (fun U r m => (smul_tmul' r m _).symm)
def mulSection : M ⟶ M ⊗ L :=
  homOfPreMod (tensorSection M L s ≫ tensorToSheaf M L)
end
end GroundTheory.Arith.SchemeCoh


