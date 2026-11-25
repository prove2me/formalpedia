-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_StableConjInvariant
-- name    : GroundTheory_AutomorphicForms_StableConjInvariant
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T01:47:37.399594+00:00
-- url     : https://prove2.me/theorems/c2f544bc-8abf-4de1-834d-b6ce0d4d54bc
-- title:
--   Stable Conj Invariant
-- statement:
--   Definitions and structural lemmas for Stable Conj Invariant, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/StableConjInvariant.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_StableConjTorus
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_Isometric_trans
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_adjointEquiv_adjointEquiv
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_adjointEquiv_inv
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_adjointEquiv_mul
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_adjointEquiv_one
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_mem_unitaryGroup_iff_adjointEquiv
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_mem_unitaryGroup_iff_adjointEquiv_mul
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_restrict_apply
import Theorems.Thm_GroundTheory_Automorphic_TorusE_ext
import Theorems.Thm_GroundTheory_Automorphic_TorusE_val_inv
import Theorems.Thm_GroundTheory_Automorphic_TorusE_val_mem
import Theorems.Thm_GroundTheory_Automorphic_TorusE_val_mk
import Theorems.Thm_GroundTheory_Automorphic_TorusE_val_mul
import Theorems.Thm_GroundTheory_Automorphic_TorusE_val_one
import Theorems.Thm_GroundTheory_Automorphic_conj_conj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.HermitianForm.restrict_apply
attribute [local simp] GroundTheory.Automorphic.TorusE.val_inv
attribute [local simp] GroundTheory.Automorphic.TorusE.val_mk
attribute [local simp] GroundTheory.Automorphic.TorusE.val_mul
attribute [local simp] GroundTheory.Automorphic.TorusE.val_one
attribute [local simp] GroundTheory.Automorphic.conj_conj


set_option autoImplicit false
namespace GroundTheory.Automorphic
open Module
theorem mul_comm_of_mul_inv_comm {G : Type*} [Group G] {a x : G} (hx : x * a⁻¹ = a⁻¹ * x) :
    a * x = x * a := by
  calc a * x = a * (x * a⁻¹) * a := by group
    _ = a * (a⁻¹ * x) * a := by rw [hx]
    _ = x * a := by group
variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {V : Type*} [AddCommGroup V] [Module E V] [FiniteDimensional E V]
namespace HermitianForm
variable (h : HermitianForm F E V)
omit [FiniteDimensional E V] in

theorem adjointEquiv_mem_torusE {γ t : V ≃ₗ[E] V} (hγ : γ ∈ h.unitaryGroup)
    (ht : t ∈ torusE γ) : h.adjointEquiv t ∈ torusE γ := by
  rw [mem_torusE] at *
  have h1 := congrArg h.adjointEquiv ht
  rw [adjointEquiv_mul, adjointEquiv_mul, (h.mem_unitaryGroup_iff_adjointEquiv γ).1 hγ] at h1
  exact mul_comm_of_mul_inv_comm h1
omit [FiniteDimensional E V] in

theorem conj_mem_unitaryGroup_iff {γ : V ≃ₗ[E] V} (hγ : γ ∈ h.unitaryGroup) (g : V ≃ₗ[E] V) :
    g * γ * g⁻¹ ∈ h.unitaryGroup ↔ h.adjointEquiv g * g ∈ torusE γ := by
  have hγ' := (h.mem_unitaryGroup_iff_adjointEquiv γ).1 hγ
  rw [mem_unitaryGroup_iff_adjointEquiv_mul, mem_torusE, adjointEquiv_mul, adjointEquiv_mul,
    adjointEquiv_inv, hγ']
  set A := h.adjointEquiv g
  constructor
  · intro hX
    calc γ * (A * g) = γ * A * ((A⁻¹ * (γ⁻¹ * A)) * (g * γ * g⁻¹)) * g := by rw [hX]; group
      _ = A * g * γ := by group
  · intro hc
    calc A⁻¹ * (γ⁻¹ * A) * (g * γ * g⁻¹) = A⁻¹ * γ⁻¹ * ((A * g) * γ) * g⁻¹ := by group
      _ = A⁻¹ * γ⁻¹ * (γ * (A * g)) * g⁻¹ := by rw [hc]
      _ = 1 := by group
variable (γ : h.unitaryGroup) [Fact (IsRegularSemisimple (γ : V ≃ₗ[E] V))]
noncomputable def torusStar : TorusE (γ : V ≃ₗ[E] V) →* TorusE (γ : V ≃ₗ[E] V) where
  toFun t := TorusE.mk (h.adjointEquiv t.val) (h.adjointEquiv_mem_torusE γ.2 t.val_mem)
  map_one' := TorusE.ext (by simp [adjointEquiv_one])
  map_mul' a b := by
    rw [mul_comm a b]
    exact TorusE.ext (by simp [adjointEquiv_mul])
@[simp] theorem val_torusStar (t : TorusE (γ : V ≃ₗ[E] V)) :
    (h.torusStar γ t).val = h.adjointEquiv t.val := rfl
noncomputable def torusNorm : TorusE (γ : V ≃ₗ[E] V) →* TorusE (γ : V ≃ₗ[E] V) :=
  h.torusStar γ * MonoidHom.id _
theorem torusNorm_apply (t : TorusE (γ : V ≃ₗ[E] V)) : h.torusNorm γ t = h.torusStar γ t * t :=
  rfl
noncomputable def selfAdjointTorus : Subgroup (TorusE (γ : V ≃ₗ[E] V)) :=
  MonoidHom.eqLocus (h.torusStar γ) (MonoidHom.id _)
noncomputable def normTorus : Subgroup (TorusE (γ : V ≃ₗ[E] V)) :=
  (h.torusNorm γ).range
abbrev centralizerTorusFirstCohomology := h.selfAdjointTorus γ ⧸ (h.normTorus γ).subgroupOf (h.selfAdjointTorus γ)
noncomputable def torusF : Subgroup (TorusE (γ : V ≃ₗ[E] V)) :=
  (h.torusNorm γ).ker
theorem mk_eq_mk_iff (c c' : h.selfAdjointTorus γ) :
    (QuotientGroup.mk c : h.centralizerTorusFirstCohomology γ) = QuotientGroup.mk c' ↔
      ∃ t, (c' : TorusE (γ : V ≃ₗ[E] V)) = c * h.torusNorm γ t := by
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨t, ?_⟩
    rw [ht]
    simp
  · rintro ⟨t, ht⟩
    refine ⟨t, ?_⟩
    simp [ht]
noncomputable def normOf (g : V ≃ₗ[E] V) (hg : g * γ * g⁻¹ ∈ h.unitaryGroup) :
    h.selfAdjointTorus γ :=
  ⟨TorusE.mk (h.adjointEquiv g * g) ((h.conj_mem_unitaryGroup_iff γ.2 g).1 hg),
    TorusE.ext (by simp [adjointEquiv_mul, adjointEquiv_adjointEquiv])⟩
@[simp] theorem val_normOf (g : V ≃ₗ[E] V) (hg : g * γ * g⁻¹ ∈ h.unitaryGroup) :
    (h.normOf γ g hg : TorusE (γ : V ≃ₗ[E] V)).val = h.adjointEquiv g * g := rfl
noncomputable def invOf (g : V ≃ₗ[E] V) (hg : g * γ * g⁻¹ ∈ h.unitaryGroup) : h.centralizerTorusFirstCohomology γ :=
  QuotientGroup.mk (h.normOf γ g hg)
noncomputable def stableInv (γ' : V ≃ₗ[E] V) : h.centralizerTorusFirstCohomology γ := by
  classical
  exact if H : ∃ g : V ≃ₗ[E] V, g * γ * g⁻¹ = γ' ∧ γ' ∈ h.unitaryGroup then
    h.invOf γ H.choose (by rw [H.choose_spec.1]; exact H.choose_spec.2) else 1
noncomputable def twistOf (c : h.selfAdjointTorus γ) : HermitianForm F E V :=
  h.twist (c : TorusE (γ : V ≃ₗ[E] V)).val (congrArg TorusE.val c.2)
theorem twistOf_apply (c : h.selfAdjointTorus γ) (x y : V) :
    (h.twistOf γ c).toSesq x y = h.toSesq ((c : TorusE (γ : V ≃ₗ[E] V)).val x) y := rfl
theorem twistOf_isometric_of_mk_eq {c c' : h.selfAdjointTorus γ}
    (hcc : (QuotientGroup.mk c : h.centralizerTorusFirstCohomology γ) = QuotientGroup.mk c') :
    Isometric (h.twistOf γ c) (h.twistOf γ c') := by
  rw [mk_eq_mk_iff] at hcc
  obtain ⟨t, ht⟩ := hcc
  have hc : (c : TorusE (γ : V ≃ₗ[E] V)) * h.torusNorm γ t =
      h.torusStar γ t * c * t := by
    rw [torusNorm_apply]
    simp only [mul_comm, mul_left_comm]
  refine Isometric.symm ⟨t.val, fun x y => ?_⟩
  rw [twistOf_apply, twistOf_apply, ← h.toSesq_adjointEquiv_left t.val, ht, hc]
  rfl
def InKernel (x : h.centralizerTorusFirstCohomology γ) : Prop :=
  Quotient.liftOn' x (fun c => Isometric (h.twistOf γ c) h) fun c c' hr => propext (by
    have hcc : (QuotientGroup.mk c : h.centralizerTorusFirstCohomology γ) = QuotientGroup.mk c' := Quotient.sound hr
    exact ⟨fun H => (h.twistOf_isometric_of_mk_eq γ hcc).symm.trans H,
      fun H => (h.twistOf_isometric_of_mk_eq γ hcc).trans H⟩)
end HermitianForm
end GroundTheory.Automorphic


