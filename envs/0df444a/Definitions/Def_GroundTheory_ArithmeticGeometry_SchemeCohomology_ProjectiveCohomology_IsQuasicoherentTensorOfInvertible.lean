-- Prove2me | Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjectiveCohomology_IsQuasicoherentTensorOfInvertible
-- name    : GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjectiveCohomology_IsQuasicoherentTensorOfInvertible
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T04:29:29.099578+00:00
-- url     : https://prove2.me/theorems/d4ba1608-e031-5ebc-b3c1-5b9f86b72a88
-- title:
--   Is Quasicoherent Tensor Of Invertible
-- statement:
--   Definitions and structural lemmas for Is Quasicoherent Tensor Of Invertible, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProjectiveCohomology/IsQuasicoherentTensorOfInvertible.lean

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjectiveCohomology_QcohLocal
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_InvertibleDual
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_val_add
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_val_mkSection
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_val_neg
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_val_sub
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_val_zero
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_isIso_dualEval
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Arith.SchemeCoh.ProjTwist.val_add
attribute [local simp] GroundTheory.Arith.SchemeCoh.ProjTwist.val_mkSection
attribute [local simp] GroundTheory.Arith.SchemeCoh.ProjTwist.val_neg
attribute [local simp] GroundTheory.Arith.SchemeCoh.ProjTwist.val_sub
attribute [local simp] GroundTheory.Arith.SchemeCoh.ProjTwist.val_zero


set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Arith.SchemeCoh
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Limits MonoidalCategory
universe u
noncomputable section
variable {X : Scheme.{u}}
def tensorBasisMap (M L : X.Modules) {U : X.Opens} (s : ((preMod X).obj L).obj (op U))
    {V : X.Opens} (h : V ≤ U) : Γ(M, V) →+ Γ(M ⊗ L, V) where
  toFun m := (tensorToSheaf M L).app (op V)
    ((show ((preMod X).obj M).obj (op V) from m) ⊗ₜ resM ((preMod X).obj L) h s :
      ((preMod X).obj M ⊗ (preMod X).obj L).obj (op V))
  map_zero' := by
    change (tensorToSheaf M L).app (op V) ((0 : ((preMod X).obj M).obj (op V)) ⊗ₜ
      resM ((preMod X).obj L) h s : ((preMod X).obj M ⊗ (preMod X).obj L).obj (op V)) = 0
    rw [TensorProduct.zero_tmul]
    exact map_zero _
  map_add' m m' := by
    change (tensorToSheaf M L).app (op V) (((show ((preMod X).obj M).obj (op V) from m) +
      (show ((preMod X).obj M).obj (op V) from m')) ⊗ₜ resM ((preMod X).obj L) h s :
        ((preMod X).obj M ⊗ (preMod X).obj L).obj (op V)) = _
    rw [TensorProduct.add_tmul]
    exact map_add _ _ _
variable {M M' L : X.Modules} {U V : X.Opens} {s : ((preMod X).obj L).obj (op U)}
section General
variable {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
  {F : C ⥤ D} [F.Monoidal] {G : D ⥤ C} (adj : F ⊣ G) [IsIso adj.counit]
abbrev counitTensor (a b : D) : F.obj (G.obj a ⊗ G.obj b) ⟶ a ⊗ b :=
  ((Functor.Monoidal.μIso F (G.obj a) (G.obj b)).symm ≪≫
    (asIso (adj.counit.app a) ⊗ᵢ asIso (adj.counit.app b))).hom
end General
def tensorDualIso (hL : IsInvertibleSheaf L) : L ⊗ dualSheaf L ≅ 𝟙_ X.Modules :=
  β_ L (dualSheaf L) ≪≫ @asIso _ _ _ _ (dualEval L) (isIso_dualEval hL)
def dualTensorIso (hL : IsInvertibleSheaf L) : dualSheaf L ⊗ L ≅ 𝟙_ X.Modules :=
  @asIso _ _ _ _ (dualEval L) (isIso_dualEval hL)
def tensorEquivOfInvertible (hL : IsInvertibleSheaf L) : X.Modules ≌ X.Modules :=
  CategoryTheory.Equivalence.mk (tensorRight L) (tensorRight (dualSheaf L))
    (NatIso.ofComponents (fun M => (ρ_ M).symm ≪≫ whiskerLeftIso M (tensorDualIso hL).symm ≪≫
      (α_ M L (dualSheaf L)).symm) (by
        intro M N f
        simp
        rw [rightUnitor_inv_naturality_assoc, ← whisker_exchange_assoc,
          associator_inv_naturality_left]))
    (NatIso.ofComponents (fun M => α_ M (dualSheaf L) L ≪≫ whiskerLeftIso M (dualTensorIso hL) ≪≫
      ρ_ M) (by
        intro M N f
        simp
        rw [associator_naturality_left_assoc, ← whisker_exchange_assoc, rightUnitor_naturality]))
end
end GroundTheory.Arith.SchemeCoh


