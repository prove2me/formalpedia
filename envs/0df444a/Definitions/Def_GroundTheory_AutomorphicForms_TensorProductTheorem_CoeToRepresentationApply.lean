-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_CoeToRepresentationApply
-- name    : GroundTheory_AutomorphicForms_TensorProductTheorem_CoeToRepresentationApply
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T00:25:43.2628+00:00
-- url     : https://prove2.me/theorems/de113e77-90cb-43bf-8dc7-edb685d55839
-- title:
--   Coe To Representation Apply
-- statement:
--   Definitions and structural lemmas for Coe To Representation Apply, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/CoeToRepresentationApply.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_GKModule
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_AdL_apply
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_Ad_one
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_Ad
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_bracket
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_derivLie_apply
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_IsEquivalent_symm
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_coe_restrict_apply
import Theorems.Thm_P2M_GroundTheory_Automorphic_IsExpLieAlgebra_gkModule___apply_5d0ada4687d5
import Theorems.Thm_P2M_GroundTheory_Automorphic_IsExpLieAlgebra_gkModule___apply_af7e43e2c7fe
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
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.derivLie_apply
attribute [local simp] GroundTheory.Automorphic.UnitaryRep.coe_restrict_apply
attribute [local simp] P2M_GroundTheory_Automorphic_IsExpLieAlgebra_gkModule___apply_5d0ada4687d5
attribute [local simp] P2M_GroundTheory_Automorphic_IsExpLieAlgebra_gkModule___apply_af7e43e2c7fe
attribute [local simp] P2M_GroundTheory_Automorphic_IsExpLieAlgebra_uAction___195cbae0e32a


set_option autoImplicit false
noncomputable section
namespace GroundTheory.Automorphic
attribute [local instance 100] LieRing.ofAssociativeRing
open Set Module
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
variable {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}
namespace IsExpLieAlgebra
variable {h : IsExpLieAlgebra G 𝔤} {K : Subgroup G} {V : Type*} [AddCommGroup V] [Module ℂ V]
def GKModule.rep (M : h.GKModule K V) :
    Representation ℂ (FreeMonoid (h.lieSubalgebra ⊕ K)) V :=
  FreeMonoid.lift (Sum.elim (fun X => M.ρ X) fun k => M.σ k)
@[simp] theorem GKModule.rep_of_inl (M : h.GKModule K V) (X : h.lieSubalgebra) :
    M.rep (FreeMonoid.of (Sum.inl X)) = M.ρ X :=
  rfl
@[simp] theorem GKModule.rep_of_inr (M : h.GKModule K V) (k : K) :
    M.rep (FreeMonoid.of (Sum.inr k)) = M.σ k :=
  rfl
def GKModule.IsIrreducible (M : h.GKModule K V) : Prop := M.rep.IsIrreducible
section SubQuot
variable (M : h.GKModule K V) (U : Subrepresentation M.rep) (U₀ : Submodule ℂ U.toSubmodule)
  (hU₀ : ∀ a, U₀ ≤ U₀.comap (U.toRepresentation a))
abbrev quotRep : Representation ℂ (FreeMonoid (h.lieSubalgebra ⊕ K)) (U.toSubmodule ⧸ U₀) :=
  U.toRepresentation.quotient U₀ hU₀
theorem quotRep_mk (a : FreeMonoid (h.lieSubalgebra ⊕ K)) (u : U.toSubmodule) :
    quotRep M U U₀ hU₀ a (Submodule.Quotient.mk u) =
      Submodule.Quotient.mk (U.toRepresentation a u) :=
  rfl
theorem exists_form_extend (φ : Dual ℂ (U.toSubmodule ⧸ U₀)) :
    ∃ ψ : Dual ℂ V, ∀ u : U.toSubmodule, φ (Submodule.Quotient.mk u) = ψ u := by
  obtain ⟨ψ, hψ⟩ := LinearMap.exists_extend (φ ∘ₗ U₀.mkQ)
  exact ⟨ψ, fun u => (LinearMap.congr_fun hψ u).symm⟩
theorem coe_toRepresentation_apply (a : FreeMonoid (h.lieSubalgebra ⊕ K)) (u : U.toSubmodule) :
    ((U.toRepresentation a u : U.toSubmodule) : V) = M.rep a u :=
  rfl
def subQuotρ : h.lieSubalgebra →ₗ⁅ℝ⁆ Module.End ℂ (U.toSubmodule ⧸ U₀) where
  toFun X := quotRep M U U₀ hU₀ (FreeMonoid.of (Sum.inl X))
  map_add' X Y := by
    refine Submodule.linearMap_qext _ (LinearMap.ext fun u => ?_)
    simp only [LinearMap.comp_apply, Submodule.mkQ_apply, quotRep_mk, LinearMap.add_apply,
      ← Submodule.Quotient.mk_add]
    congr 1
    refine Subtype.ext ?_
    simp only [Submodule.coe_add, coe_toRepresentation_apply, GKModule.rep_of_inl, map_add,
      LinearMap.add_apply]
  map_smul' r X := by
    refine Submodule.linearMap_qext _ (LinearMap.ext fun u => ?_)
    simp only [LinearMap.comp_apply, Submodule.mkQ_apply, quotRep_mk, LinearMap.smul_apply,
      RingHom.id_apply]
    rw [← Submodule.Quotient.mk_smul]
    congr 1
    refine Subtype.ext ?_
    rw [Submodule.coe_smul_of_tower]
    simp only [coe_toRepresentation_apply, GKModule.rep_of_inl, map_smul, LinearMap.smul_apply]
  map_lie' {X Y} := by
    refine Submodule.linearMap_qext _ (LinearMap.ext fun u => ?_)
    simp only [LinearMap.comp_apply, Submodule.mkQ_apply, quotRep_mk,
      LieRing.of_associative_ring_bracket, LinearMap.sub_apply, Module.End.mul_apply,
      ← Submodule.Quotient.mk_sub]
    congr 1
    refine Subtype.ext ?_
    simp only [Submodule.coe_sub, coe_toRepresentation_apply, GKModule.rep_of_inl, LieHom.map_lie,
      LieRing.of_associative_ring_bracket, LinearMap.sub_apply, Module.End.mul_apply]
def subQuotσ : Representation ℂ K (U.toSubmodule ⧸ U₀) where
  toFun k := quotRep M U U₀ hU₀ (FreeMonoid.of (Sum.inr k))
  map_one' := by
    refine Submodule.linearMap_qext _ (LinearMap.ext fun u => ?_)
    simp only [LinearMap.comp_apply, Submodule.mkQ_apply, quotRep_mk, Module.End.one_apply]
    congr 1
    refine Subtype.ext ?_
    simp only [coe_toRepresentation_apply, GKModule.rep_of_inr, map_one, Module.End.one_apply]
  map_mul' k₁ k₂ := by
    refine Submodule.linearMap_qext _ (LinearMap.ext fun u => ?_)
    simp only [LinearMap.comp_apply, Submodule.mkQ_apply, quotRep_mk, Module.End.mul_apply]
    congr 1
    refine Subtype.ext ?_
    simp only [coe_toRepresentation_apply, GKModule.rep_of_inr, map_mul, Module.End.mul_apply]
theorem subQuotρ_mk (X : h.lieSubalgebra) (u : U.toSubmodule) :
    subQuotρ M U U₀ hU₀ X (Submodule.Quotient.mk u) =
      Submodule.Quotient.mk (U.toRepresentation (FreeMonoid.of (Sum.inl X)) u) :=
  rfl
theorem subQuotσ_mk (k : K) (u : U.toSubmodule) :
    subQuotσ M U U₀ hU₀ k (Submodule.Quotient.mk u) =
      Submodule.Quotient.mk (U.toRepresentation (FreeMonoid.of (Sum.inr k)) u) :=
  rfl
theorem subQuot_locallyFinite (q : U.toSubmodule ⧸ U₀) :
    FiniteDimensional ℂ (Submodule.span ℂ (range fun k : K => subQuotσ M U U₀ hU₀ k q)) := by
  obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  have hfin := M.locallyFinite u
  set S : Submodule ℂ U.toSubmodule :=
    Submodule.span ℂ (range fun k : K => U.toRepresentation (FreeMonoid.of (Sum.inr k)) u)
  have hS : FiniteDimensional ℂ S := by
    have hle : S.map U.toSubmodule.subtype ≤ Submodule.span ℂ (range fun k : K => M.σ k u) := by
      rw [Submodule.map_span_le]
      rintro _ ⟨k, rfl⟩
      exact Submodule.subset_span ⟨k, rfl⟩
    have : FiniteDimensional ℂ (S.map U.toSubmodule.subtype) :=
      Submodule.finiteDimensional_of_le hle
    exact LinearEquiv.finiteDimensional
      (Submodule.equivMapOfInjective _ U.toSubmodule.injective_subtype S).symm
  have hle : Submodule.span ℂ (range fun k : K =>
      subQuotσ M U U₀ hU₀ k (Submodule.Quotient.mk u)) ≤ S.map U₀.mkQ := by
    rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    exact ⟨_, Submodule.subset_span ⟨k, rfl⟩, rfl⟩
  exact Submodule.finiteDimensional_of_le hle
theorem subQuot_hasContinuousCoeff : Representation.HasContinuousCoeff (subQuotσ M U U₀ hU₀) := by
  intro φ q
  obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  obtain ⟨ψ, hψ⟩ := exists_form_extend M U U₀ φ
  have : (fun k : K => φ (subQuotσ M U U₀ hU₀ k (Submodule.Quotient.mk u))) =
      fun k => ψ (M.σ k u) := by
    funext k
    rw [subQuotσ_mk, hψ]
    rfl
  rw [this]
  exact M.hasContinuousCoeff ψ u
theorem subQuot_hasDerivAt (X : 𝔤) (hX : ∀ t : ℝ, h.expG (t • X) ∈ K)
    (φ : Dual ℂ (U.toSubmodule ⧸ U₀)) (q : U.toSubmodule ⧸ U₀) :
    HasDerivAt (fun t : ℝ => φ (subQuotσ M U U₀ hU₀ ⟨h.expG (t • X), hX t⟩ q))
      (φ (subQuotρ M U U₀ hU₀ (h.toLie X) q)) 0 := by
  obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  obtain ⟨ψ, hψ⟩ := exists_form_extend M U U₀ φ
  have h1 : (fun t : ℝ => φ (subQuotσ M U U₀ hU₀ ⟨h.expG (t • X), hX t⟩
      (Submodule.Quotient.mk u))) = fun t => ψ (M.σ ⟨h.expG (t • X), hX t⟩ u) := by
    funext t
    rw [subQuotσ_mk, hψ]
    rfl
  have h2 : φ (subQuotρ M U U₀ hU₀ (h.toLie X) (Submodule.Quotient.mk u)) =
      ψ (M.ρ (h.toLie X) u) := by
    rw [subQuotρ_mk, hψ]
    rfl
  rw [h1, h2]
  exact M.hasDerivAt_coeff X hX ψ u
theorem subQuot_map_ρ (k : K) (X : 𝔤) (q : U.toSubmodule ⧸ U₀) :
    subQuotσ M U U₀ hU₀ k (subQuotρ M U U₀ hU₀ (h.toLie X) q) =
      subQuotρ M U U₀ hU₀ (h.toLie (h.Ad k X)) (subQuotσ M U U₀ hU₀ k q) := by
  obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rw [subQuotρ_mk, subQuotσ_mk, subQuotσ_mk, subQuotρ_mk]
  congr 1
  exact Subtype.ext (M.map_ρ k X u)
def GKModule.subQuot : h.GKModule K (U.toSubmodule ⧸ U₀) where
  ρ := subQuotρ M U U₀ hU₀
  σ := subQuotσ M U U₀ hU₀
  locallyFinite := subQuot_locallyFinite M U U₀ hU₀
  hasContinuousCoeff := subQuot_hasContinuousCoeff M U U₀ hU₀
  hasDerivAt_coeff := subQuot_hasDerivAt M U U₀ hU₀
  map_ρ := subQuot_map_ρ M U U₀ hU₀
end SubQuot
end IsExpLieAlgebra
end GroundTheory.Automorphic


