-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_CartanBasis
-- name    : GroundTheory_AutomorphicForms_HarishChandraRegularity_CartanBasis
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T00:15:46.880914+00:00
-- url     : https://prove2.me/theorems/0b0394db-3fe3-48da-a4f7-2b227179a4cc
-- title:
--   Cartan Basis
-- statement:
--   Definitions and structural lemmas for Cartan Basis, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraRegularity/CartanBasis.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Casimir
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsLie
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_AdL_apply
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
open Matrix
set_option linter.unusedSectionVars false
attribute [local instance 100] LieRing.ofAssociativeRing
section TraceForm
variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (L : LieSubalgebra ℝ (Matrix ι ι 𝕜))
noncomputable def traceForm : LinearMap.BilinForm ℝ L :=
  LinearMap.mk₂ ℝ (fun X Y => RCLike.re (trace ((X : Matrix ι ι 𝕜) * (Y : Matrix ι ι 𝕜))))
    (fun X₁ X₂ Y => by simp [Matrix.add_mul, trace_add])
    (fun r X Y => by simp [trace_smul, RCLike.smul_re])
    (fun X Y₁ Y₂ => by simp [Matrix.mul_add, trace_add])
    (fun r X Y => by simp [trace_smul, RCLike.smul_re])
variable {L}
end TraceForm
section Positivity
variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι] [DecidableEq ι]
end Positivity
section Cartan
variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (L : LieSubalgebra ℝ (Matrix ι ι 𝕜))
def skewPart : Submodule ℝ L where
  carrier := {X | (X : Matrix ι ι 𝕜)ᴴ = -(X : Matrix ι ι 𝕜)}
  add_mem' {X Y} hX hY := by
    change ((X : Matrix ι ι 𝕜) + (Y : Matrix ι ι 𝕜))ᴴ = -((X : Matrix ι ι 𝕜) + (Y : Matrix ι ι 𝕜))
    rw [conjTranspose_add, hX, hY, neg_add]
  zero_mem' := by
    change (0 : Matrix ι ι 𝕜)ᴴ = -(0 : Matrix ι ι 𝕜)
    simp
  smul_mem' r X hX := by
    change (r • (X : Matrix ι ι 𝕜))ᴴ = -(r • (X : Matrix ι ι 𝕜))
    rw [conjTranspose_smul, star_trivial, hX, smul_neg]
def hermPart : Submodule ℝ L where
  carrier := {X | (X : Matrix ι ι 𝕜)ᴴ = (X : Matrix ι ι 𝕜)}
  add_mem' {X Y} hX hY := by
    change ((X : Matrix ι ι 𝕜) + (Y : Matrix ι ι 𝕜))ᴴ = ((X : Matrix ι ι 𝕜) + (Y : Matrix ι ι 𝕜))
    rw [conjTranspose_add, hX, hY]
  zero_mem' := by
    change (0 : Matrix ι ι 𝕜)ᴴ = (0 : Matrix ι ι 𝕜)
    simp
  smul_mem' r X hX := by
    change (r • (X : Matrix ι ι 𝕜))ᴴ = (r • (X : Matrix ι ι 𝕜))
    rw [conjTranspose_smul, star_trivial, hX]
variable {L}
end Cartan
section MaxCompact
variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι] [DecidableEq ι]
def maxCompact (G : Subgroup (Matrix ι ι 𝕜)ˣ) : Subgroup G where
  carrier := {g | ((g : (Matrix ι ι 𝕜)ˣ) : Matrix ι ι 𝕜) ∈ Matrix.unitaryGroup ι 𝕜}
  mul_mem' {a b} ha hb := by
    change ((a : (Matrix ι ι 𝕜)ˣ) : Matrix ι ι 𝕜) * ((b : (Matrix ι ι 𝕜)ˣ) : Matrix ι ι 𝕜) ∈
      Matrix.unitaryGroup ι 𝕜
    exact Submonoid.mul_mem _ ha hb
  one_mem' := by
    change ((1 : (Matrix ι ι 𝕜)ˣ) : Matrix ι ι 𝕜) ∈ Matrix.unitaryGroup ι 𝕜
    rw [Units.val_one]
    exact Submonoid.one_mem _
  inv_mem' {a} ha := by
    change (((a : (Matrix ι ι 𝕜)ˣ)⁻¹ : (Matrix ι ι 𝕜)ˣ) : Matrix ι ι 𝕜) ∈ Matrix.unitaryGroup ι 𝕜
    have hmul : ((a : (Matrix ι ι 𝕜)ˣ) : Matrix ι ι 𝕜) *
        star ((a : (Matrix ι ι 𝕜)ˣ) : Matrix ι ι 𝕜) = 1 := Matrix.mem_unitaryGroup_iff.1 ha
    rw [Units.inv_eq_of_mul_eq_one_right hmul]
    exact Unitary.star_mem ha
end MaxCompact
section Groups
open NormedSpace
open scoped Matrix.Norms.L2Operator
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
end Groups
end GroundTheory.Automorphic


