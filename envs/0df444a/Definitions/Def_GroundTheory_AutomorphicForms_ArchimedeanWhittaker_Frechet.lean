-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_ArchimedeanWhittaker_Frechet
-- name    : GroundTheory_AutomorphicForms_ArchimedeanWhittaker_Frechet
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T00:55:55.609963+00:00
-- url     : https://prove2.me/theorems/903caf34-46e7-47d0-9370-58c3cf885545
-- title:
--   Frechet
-- statement:
--   Definitions and structural lemmas for Frechet, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ArchimedeanWhittaker/Frechet.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_ArchimedeanWhittaker_ContinuousMultilinearOfFiniteDimensional
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_AdL_apply
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_Ad_one
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_Ad
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_bracket
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_rightDerivEnd
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_rightTranslateEnd
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_derivLie_apply
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_wordOp_add
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_wordOp_smul
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_coe_restrict_apply
import Theorems.Thm_P2M_GroundTheory_Automorphic_IsExpLieAlgebra_gkModule___apply_5d0ada4687d5
import Theorems.Thm_P2M_GroundTheory_Automorphic_IsExpLieAlgebra_gkModule___apply_af7e43e2c7fe
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
attribute [local simp] P2M_GroundTheory_Automorphic_IsExpLieAlgebra_gkModule___apply_5d0ada4687d5
attribute [local simp] P2M_GroundTheory_Automorphic_IsExpLieAlgebra_gkModule___apply_af7e43e2c7fe
attribute [local simp] P2M_GroundTheory_Automorphic_IsExpLieAlgebra_rightUAction___d9062316eb7b
attribute [local simp] P2M_GroundTheory_Automorphic_IsExpLieAlgebra_uAction___195cbae0e32a


set_option autoImplicit false
namespace GroundTheory.Automorphic
open NormedSpace Set Filter Topology Asymptotics
open scoped ContDiff
namespace IsExpLieAlgebra
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
variable {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸} (h : IsExpLieAlgebra G 𝔤)
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (π : BanachRep G E)
noncomputable def wordSeminorm (Y : Σ k, Fin k → 𝔤) : Seminorm ℂ (h.smoothVectors π) :=
  Seminorm.of (fun v => ‖h.wordOp π Y.2 (v : E)‖)
    (fun v w => by
      simp only [Submodule.coe_add]
      rw [h.wordOp_add π v.2 w.2]
      exact norm_add_le _ _)
    (fun c v => by
      simp only [Submodule.coe_smul]
      rw [h.wordOp_smul π v.2, norm_smul])
def SmoothFrechet : Type _ := h.smoothVectors π
noncomputable instance : AddCommGroup (h.SmoothFrechet π) :=
  inferInstanceAs (AddCommGroup (h.smoothVectors π))
noncomputable instance : Module ℂ (h.SmoothFrechet π) :=
  inferInstanceAs (Module ℂ (h.smoothVectors π))
noncomputable def smoothSeminormFamily : SeminormFamily ℂ (h.SmoothFrechet π) (Σ k, Fin k → 𝔤) :=
  fun Y => h.wordSeminorm π Y
noncomputable instance : TopologicalSpace (h.SmoothFrechet π) :=
  (h.smoothSeminormFamily π).moduleFilterBasis.topology
theorem withSeminorms_smoothFrechet : WithSeminorms (h.smoothSeminormFamily π) := ⟨rfl⟩
instance : IsTopologicalAddGroup (h.SmoothFrechet π) :=
  (h.withSeminorms_smoothFrechet π).topologicalAddGroup
instance : ContinuousSMul ℂ (h.SmoothFrechet π) :=
  (h.withSeminorms_smoothFrechet π).continuousSMul
def IsSmoothContinuous (l : h.smoothVectors π →ₗ[ℂ] ℂ) : Prop :=
  ∃ (s : Finset (Σ k, Fin k → 𝔤)) (C : ℝ), ∀ v, ‖l v‖ ≤ C * ∑ Y ∈ s, ‖h.wordOp π Y.2 (v : E)‖
end IsExpLieAlgebra
end GroundTheory.Automorphic
namespace GroundTheory.Automorphic
open NormedSpace Set Filter Topology Asymptotics
open scoped ContDiff
namespace IsExpLieAlgebra
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
variable {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸} (h : IsExpLieAlgebra G 𝔤)
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (π : BanachRep G E)
variable {h π}
variable (h π) in

def smoothMap {v : E} (hv : h.IsSmoothVector π v) (g : G) : h.smoothVectors π :=
  ⟨π g v, h.isSmoothVector_map π hv g⟩
end IsExpLieAlgebra
end GroundTheory.Automorphic


