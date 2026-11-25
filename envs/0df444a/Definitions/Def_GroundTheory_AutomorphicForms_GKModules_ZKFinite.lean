-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_GKModules_ZKFinite
-- name    : GroundTheory_AutomorphicForms_GKModules_ZKFinite
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T00:02:59.652623+00:00
-- url     : https://prove2.me/theorems/76a8c3e9-3d26-4c6e-9abf-67908dcadb82
-- title:
--   ZKFinite
-- statement:
--   Definitions and structural lemmas for ZKFinite, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GKModules/ZKFinite.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_RightRegular
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_AdL_apply
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_Ad_bracket
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_Ad_one
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_Ad
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_bracket
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_rightDerivEnd
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_rightTranslateEnd
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_derivLie_apply
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_coe_restrict_apply
import Theorems.Thm_P2M_GroundTheory_Automorphic_IsExpLieAlgebra_rightUAction___d9062316eb7b
import Theorems.Thm_P2M_GroundTheory_Automorphic_IsExpLieAlgebra_uAction___195cbae0e32a
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.AdL_apply
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.Ad_one
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.coe_Ad
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.coe_bracket
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.coe_rightDerivEnd
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.coe_rightTranslateEnd
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.derivLie_apply
attribute [local simp] GroundTheory.Automorphic.UnitaryRep.coe_restrict_apply
attribute [local simp] P2M_GroundTheory_Automorphic_IsExpLieAlgebra_rightUAction___d9062316eb7b
attribute [local simp] P2M_GroundTheory_Automorphic_IsExpLieAlgebra_uAction___195cbae0e32a


set_option autoImplicit false
namespace GroundTheory.Automorphic
open NormedSpace Set Filter Topology
open scoped Manifold ContDiff
set_option linter.unusedSectionVars false
attribute [local instance 100] LieRing.ofAssociativeRing
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
variable {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}
namespace IsExpLieAlgebra
variable (h : IsExpLieAlgebra G 𝔤)
noncomputable def AdLie (g : G) : h.lieSubalgebra →ₗ⁅ℝ⁆ h.lieSubalgebra where
  toFun X := h.toLie (h.Ad g (h.ofLie X))
  map_add' X Y := by
    apply Subtype.ext
    show ((h.Ad g (h.ofLie X + h.ofLie Y) : 𝔤) : 𝔸) = _
    rw [map_add]; rfl
  map_smul' r X := by
    apply Subtype.ext
    show ((h.Ad g (r • h.ofLie X) : 𝔤) : 𝔸) = _
    rw [map_smul]; rfl
  map_lie' {X Y} := by
    apply Subtype.ext
    show ((h.Ad g (h.bracket (h.ofLie X) (h.ofLie Y)) : 𝔤) : 𝔸) = _
    rw [Ad_bracket]; rfl
noncomputable def AdU (g : G) :
    UniversalEnvelopingAlgebra ℝ h.lieSubalgebra →ₐ[ℝ] UniversalEnvelopingAlgebra ℝ h.lieSubalgebra :=
  UniversalEnvelopingAlgebra.lift ℝ ((UniversalEnvelopingAlgebra.ι ℝ).comp (h.AdLie g))
@[simp] theorem AdU_ι (g : G) (X : h.lieSubalgebra) :
    h.AdU g (UniversalEnvelopingAlgebra.ι ℝ X) = UniversalEnvelopingAlgebra.ι ℝ (h.AdLie g X) :=
  UniversalEnvelopingAlgebra.lift_ι_apply ℝ _ X
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
theorem rightTranslateEnd_mul (a b : G) :
    h.rightTranslateEnd (F := F) a * h.rightTranslateEnd b = h.rightTranslateEnd (a * b) :=
  LinearMap.ext fun f => Subtype.ext (funext fun g => by simp [rightTranslate, mul_assoc])
theorem rightTranslateEnd_one : h.rightTranslateEnd (F := F) 1 = 1 :=
  LinearMap.ext fun f => Subtype.ext (funext fun g => by simp [rightTranslate])
theorem rightTranslateEnd_mul_inv (a : G) :
    h.rightTranslateEnd (F := F) a * h.rightTranslateEnd a⁻¹ = 1 := by
  rw [rightTranslateEnd_mul, mul_inv_cancel, rightTranslateEnd_one]
theorem rightTranslateEnd_inv_mul (a : G) :
    h.rightTranslateEnd (F := F) a⁻¹ * h.rightTranslateEnd a = 1 := by
  rw [rightTranslateEnd_mul, inv_mul_cancel, rightTranslateEnd_one]
def conjTranslate (a : G) :
    Module.End ℂ (h.smoothFuns (F := F)) →ₐ[ℝ] Module.End ℂ (h.smoothFuns (F := F)) where
  toFun T := h.rightTranslateEnd a⁻¹ * T * h.rightTranslateEnd a
  map_one' := by rw [mul_one, rightTranslateEnd_inv_mul]
  map_mul' S T := by
    calc h.rightTranslateEnd a⁻¹ * (S * T) * h.rightTranslateEnd a
        = h.rightTranslateEnd a⁻¹ * S * (h.rightTranslateEnd a * h.rightTranslateEnd a⁻¹) * T *
            h.rightTranslateEnd a := by rw [rightTranslateEnd_mul_inv]; simp only [mul_one, mul_assoc]
      _ = _ := by simp only [mul_assoc]
  map_zero' := by simp
  map_add' S T := by simp [mul_add, add_mul]
  commutes' r := by
    simp only [Algebra.algebraMap_eq_smul_one, mul_smul_comm, smul_mul_assoc, mul_one]
    rw [rightTranslateEnd_inv_mul]
variable (K : Subgroup G)
def zkSpan (f : h.smoothFuns (F := F)) : Submodule ℂ (h.smoothFuns (F := F)) :=
  Submodule.span ℂ (range fun p : h.centerU × K =>
    h.rightUAction (p.1 : UniversalEnvelopingAlgebra ℝ h.lieSubalgebra) (h.rightTranslateEnd (p.2 : G) f))
def zSpan (f : h.smoothFuns (F := F)) : Submodule ℂ (h.smoothFuns (F := F)) :=
  Submodule.span ℂ ((fun z => h.rightUAction z f) '' (h.centerU : Set _))
end IsExpLieAlgebra
end GroundTheory.Automorphic


