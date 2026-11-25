-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolic
-- name    : GroundTheory_AutomorphicForms_InductionParabolic
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T11:04:15.430803+00:00
-- url     : https://prove2.me/theorems/b87202a8-e471-4cd9-9406-c042f512a384
-- title:
--   Induction Parabolic
-- statement:
--   Definitions and structural lemmas for Induction Parabolic, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/InductionParabolic.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_Induction
import Definitions.Def_GroundTheory_AutomorphicForms_InductionJacquet
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolicLocal
import Theorems.Thm_GroundTheory_Automorphic_Cartan_dominantEquivDoubleCoset_apply
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
import Theorems.Thm_GroundTheory_Automorphic_Measures_adUnipotentHom_apply
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_conj_mem_unipotentRadical
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_leviProj_inv_mul_mem
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_leviProj_leviIncl
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_mem_unipotentRadical_iff_leviProj
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_modularCharacter_eq_one_of_mem
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_unipotentRadical_le_blockUpper
import Theorems.Thm_GroundTheory_Automorphic_coinvariantsTranslate_mk
import Theorems.Thm_GroundTheory_Automorphic_frobenius_apply
import Theorems.Thm_GroundTheory_Automorphic_frobenius_symm_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.Cartan.dominantEquivDoubleCoset_apply
attribute [local simp] GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk
attribute [local simp] GroundTheory.Automorphic.Measures.adUnipotentHom_apply
attribute [local simp] GroundTheory.Automorphic.coinvariantsTranslate_mk
attribute [local simp] GroundTheory.Automorphic.frobenius_apply
attribute [local simp] GroundTheory.Automorphic.frobenius_symm_apply


set_option autoImplicit false
noncomputable section
namespace GroundTheory.Automorphic
namespace Parabolic
open Matrix Iwasawa GLnLocal Topology Filter Set MeasureTheory Measure
open scoped NNReal
section Twist
variable {G : Type*} [Group G] {W : Type*} [AddCommGroup W] [Module ℂ W]
def twist (χ : G →* ℂ) (σ : Representation ℂ G W) : Representation ℂ G W where
  toFun g := χ g • σ g
  map_one' := by simp
  map_mul' g h := by rw [map_mul, map_mul, smul_mul_smul_comm]
@[simp]
theorem twist_apply (χ : G →* ℂ) (σ : Representation ℂ G W) (g : G) (w : W) :
    twist χ σ g w = χ g • σ g w := rfl
end Twist
variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  (n : ℕ) {α : Type*} [LinearOrder α] (β : Fin n → α)
def sqrtModular : blockUpper F n β →* ℂ where
  toFun p := ((NNReal.sqrt (modularCharacter p) : ℝ) : ℂ)
  map_one' := by simp
  map_mul' p q := by simp [NNReal.sqrt_mul]
def invSqrtModular : blockUpper F n β →* ℂ where
  toFun p := (sqrtModular F n β p)⁻¹
  map_one' := by simp
  map_mul' p q := by rw [map_mul, mul_inv]
variable {F n β}
theorem sqrtModular_mul_invSqrtModular (p : blockUpper F n β) :
    sqrtModular F n β p * invSqrtModular F n β p = 1 := by
  have h : sqrtModular F n β p * sqrtModular F n β p⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel, map_one]
  exact mul_inv_cancel₀ (left_ne_zero_of_mul_eq_one h)
theorem sqrtModular_of_mem (u : blockUpper F n β)
    (hu : (u : GL (Fin n) F) ∈ unipotentRadical F n β) : sqrtModular F n β u = 1 := by
  show ((NNReal.sqrt (modularCharacter u) : ℝ) : ℂ) = 1
  rw [modularCharacter_eq_one_of_mem u hu]
  simp
theorem sqrtModular_leviProj (p : blockUpper F n β) :
    sqrtModular F n β (leviIncl (leviProj F n β p)) = sqrtModular F n β p := by
  have h := sqrtModular_of_mem _ (leviProj_inv_mul_mem p)
  rw [map_mul, map_inv] at h
  exact (inv_mul_eq_one₀ (left_ne_zero_of_mul_eq_one
    (sqrtModular_mul_invSqrtModular (leviIncl (leviProj F n β p))))).1 h
section ParabolicInduction
variable {W : Type*} [AddCommGroup W] [Module ℂ W]
variable (F n β) in

def inflateTwist (σ : Representation ℂ (levi F n β) W) : Representation ℂ (blockUpper F n β) W :=
  twist (sqrtModular F n β) (σ.comp (leviProj F n β))
@[simp]
theorem inflateTwist_apply (σ : Representation ℂ (levi F n β) W) (p : blockUpper F n β) (w : W) :
    inflateTwist F n β σ p w = sqrtModular F n β p • σ (leviProj F n β p) w := rfl
variable (F n β) in

abbrev parabolicIndSpace (σ : Representation ℂ (levi F n β) W) : Submodule ℂ (GL (Fin n) F → W) :=
  indSpace (blockUpper F n β) (inflateTwist F n β σ)
variable (F n β) in

abbrev parabolicInd (σ : Representation ℂ (levi F n β) W) :
    Representation ℂ (GL (Fin n) F) (parabolicIndSpace F n β σ) :=
  indRep (blockUpper F n β) (inflateTwist F n β σ)
end ParabolicInduction
section Jacquet
variable {V : Type*} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) F) V)
variable (F n β) in

abbrev JacquetModule : Type _ :=
  Representation.Coinvariants (π.comp (unipotentRadical F n β).subtype)
omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem levi_conj_mem (m : levi F n β) :
    ∀ u ∈ unipotentRadical F n β,
      (m : GL (Fin n) F) * u * (m : GL (Fin n) F)⁻¹ ∈ unipotentRadical F n β :=
  fun _ hu => conj_mem_unipotentRadical (levi_le_blockUpper m.2) hu
variable (F n β) in

def jacquetAction : Representation ℂ (levi F n β) (JacquetModule F n β π) where
  toFun m := coinvariantsTranslate π _ (m : GL (Fin n) F) (levi_conj_mem m)
  map_one' := Representation.Coinvariants.hom_ext (LinearMap.ext fun v => by simp)
  map_mul' m m' := Representation.Coinvariants.hom_ext (LinearMap.ext fun v => by
    simp [Module.End.mul_apply])
omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
@[simp]
theorem jacquetAction_mk (m : levi F n β) (v : V) :
    jacquetAction F n β π m (Representation.Coinvariants.mk _ v) =
      Representation.Coinvariants.mk _ (π m v) := rfl
variable (F n β) in

def jacquetRep : Representation ℂ (levi F n β) (JacquetModule F n β π) :=
  twist ((invSqrtModular F n β).comp leviIncl) (jacquetAction F n β π)
theorem jacquetRep_mk (m : levi F n β) (v : V) :
    jacquetRep F n β π m (Representation.Coinvariants.mk _ v) =
      invSqrtModular F n β (leviIncl m) • Representation.Coinvariants.mk _ (π m v) := rfl
theorem mk_apply_levi (m : levi F n β) (v : V) :
    Representation.Coinvariants.mk (π.comp (unipotentRadical F n β).subtype) (π m v) =
      sqrtModular F n β (leviIncl m) • jacquetRep F n β π m (Representation.Coinvariants.mk _ v) := by
  rw [jacquetRep_mk, smul_smul, sqrtModular_mul_invSqrtModular, one_smul]
variable {π} {V' : Type*} [AddCommGroup V'] [Module ℂ V'] {π' : Representation ℂ (GL (Fin n) F) V'}
  {V'' : Type*} [AddCommGroup V''] [Module ℂ V''] {π'' : Representation ℂ (GL (Fin n) F) V''}
variable (F n β) in

def restrictN (f : Representation.IntertwiningMap π π') :
    Representation.IntertwiningMap (π.comp (unipotentRadical F n β).subtype)
      (π'.comp (unipotentRadical F n β).subtype) :=
  ⟨f.toLinearMap, fun u => f.isIntertwining' u⟩
variable (F n β) in

def jacquetMap (f : Representation.IntertwiningMap π π') :
    Representation.IntertwiningMap (jacquetRep F n β π) (jacquetRep F n β π') :=
  ⟨Representation.Coinvariants.map _ _ (restrictN F n β f), fun m =>
    Representation.Coinvariants.hom_ext (LinearMap.ext fun v => by
      simp only [LinearMap.coe_comp, Function.comp_apply, jacquetRep_mk, map_smul,
        Representation.Coinvariants.map_mk]
      congr 2
      exact Representation.IntertwiningMap.isIntertwining _ _ f (m : GL (Fin n) F) v)⟩
variable {W : Type*} [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (levi F n β) W)
omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem leviIncl_coe (m : levi F n β) :
    ((leviIncl m : blockUpper F n β) : GL (Fin n) F) = m := rfl
variable (F n β π) in

def jacquetAdjunction :
    Representation.IntertwiningMap (π.comp (blockUpper F n β).subtype) (inflateTwist F n β σ) ≃ₗ[ℂ]
      Representation.IntertwiningMap (jacquetRep F n β π) σ where
  toFun φ := ⟨Representation.Coinvariants.lift _ φ.toLinearMap fun u => LinearMap.ext fun v => by
      have huP := unipotentRadical_le_blockUpper u.2
      have h := Representation.IntertwiningMap.isIntertwining _ _ φ ⟨u, huP⟩ v
      simp only [MonoidHom.coe_comp, Subgroup.coe_subtype, Function.comp_apply,
        inflateTwist_apply] at h
      simp only [LinearMap.coe_comp, Function.comp_apply, MonoidHom.coe_comp,
        Subgroup.coe_subtype, Representation.IntertwiningMap.toLinearMap_apply]
      have hl : leviProj F n β ⟨(u : GL (Fin n) F), huP⟩ = 1 :=
        (mem_unipotentRadical_iff_leviProj (p := ⟨(u : GL (Fin n) F), huP⟩)).1 u.2
      rw [h, sqrtModular_of_mem _ u.2, hl, map_one, one_smul, Module.End.one_apply],
    fun m => Representation.Coinvariants.hom_ext (LinearMap.ext fun v => by
      have h := Representation.IntertwiningMap.isIntertwining _ _ φ (leviIncl m) v
      simp only [MonoidHom.coe_comp, Subgroup.coe_subtype, Function.comp_apply,
        inflateTwist_apply, leviProj_leviIncl, leviIncl_coe] at h
      simp only [LinearMap.coe_comp, Function.comp_apply, jacquetRep_mk, map_smul,
        Representation.Coinvariants.lift_mk, Representation.IntertwiningMap.toLinearMap_apply]
      rw [h, smul_smul, mul_comm, sqrtModular_mul_invSqrtModular, one_smul])⟩
  map_add' φ ψ := Representation.IntertwiningMap.ext (Representation.Coinvariants.hom_ext
    (LinearMap.ext fun v => rfl))
  map_smul' c φ := Representation.IntertwiningMap.ext (Representation.Coinvariants.hom_ext
    (LinearMap.ext fun v => rfl))
  invFun ψ := ⟨ψ.toLinearMap ∘ₗ Representation.Coinvariants.mk _, fun p => LinearMap.ext fun v => by
      simp only [LinearMap.coe_comp, Function.comp_apply, MonoidHom.coe_comp,
        Subgroup.coe_subtype, inflateTwist_apply, Representation.IntertwiningMap.toLinearMap_apply]
      set m := leviProj F n β p
      have hu := leviProj_inv_mul_mem p
      have hp : (p : GL (Fin n) F) = (m : GL (Fin n) F) *
          (((leviIncl m)⁻¹ * p : blockUpper F n β) : GL (Fin n) F) := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv, leviIncl_coe, mul_inv_cancel_left]
      rw [hp, map_mul, Module.End.mul_apply, mk_apply_levi, mk_apply_of_mem π _ hu,
        map_smul, Representation.IntertwiningMap.isIntertwining _ _ ψ, sqrtModular_leviProj]⟩
  left_inv φ := Representation.IntertwiningMap.ext (LinearMap.ext fun v => rfl)
  right_inv ψ := Representation.IntertwiningMap.ext (Representation.Coinvariants.hom_ext
    (LinearMap.ext fun v => rfl))
variable (F n β) in

def frobeniusParabolic (hπ : IsSmooth π) :
    Representation.IntertwiningMap π (parabolicInd F n β σ) ≃ₗ[ℂ]
      Representation.IntertwiningMap (jacquetRep F n β π) σ :=
  (frobenius (blockUpper F n β) (inflateTwist F n β σ) hπ).trans (jacquetAdjunction F n β π σ)
variable (F n β π) in

def jacquetFixedMap (K : Subgroup (GL (Fin n) F)) :
    fixedVectors π K →ₗ[ℂ] fixedVectors (jacquetAction F n β π) (K.subgroupOf (levi F n β)) :=
  ((Representation.Coinvariants.mk _).comp (fixedVectors π K).subtype).codRestrict _
    fun x m hm => by
      simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype,
        jacquetAction_mk]
      rw [x.2 m (Subgroup.mem_subgroupOf.1 hm)]
end Jacquet
end Parabolic
end GroundTheory.Automorphic


