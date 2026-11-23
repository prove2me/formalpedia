-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DualityClausesOfMulEquiv
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DualityClausesOfMulEquiv
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:20:34.987079+00:00
-- url     : https://prove2.me/theorems/c745b679-d4e1-426c-a8e5-dc5c24a2830a
-- title:
--   Duality Clauses Of Mul Equiv
-- statement:
--   Definitions and structural lemmas for Duality Clauses Of Mul Equiv, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/DualityClausesOfMulEquiv.lean

import Mathlib
import Definitions.Def_Formalism_GaloisCohomology_LocalTateDualityK
import Definitions.Def_ReciprocityTheory_Hypotheses_GalCoh
import Theorems.Thm_Formalism_GaloisCohomology_scalRep_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GaloisCohomology.scalRep_apply


set_option autoImplicit false
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology
noncomputable section
namespace GlobalTheory.CohTransport
section Res
variable {R : Type*} [CommRing R]
  {Γ Γ' : Type*} [Group Γ] [TopologicalSpace Γ] [Group Γ'] [TopologicalSpace Γ']
  {N : Type*} [AddCommGroup N] [Module R N] [TopologicalSpace N]
  [IsTopologicalAddGroup N] [ContinuousConstSMul R N]
  (σ : Representation R Γ N) (σ' : Representation R Γ' N) (φ : Γ' →* Γ)
  (hσ : ∀ g n, σ' g n = σ (φ g) n)
def rh0 : H0 σ →ₗ[R] H0 σ' :=
  Submodule.inclusion fun m hm g => by
    show σ' g m = m
    rw [hσ]; exact hm (φ g)
@[simp] theorem rh0_coe (m : H0 σ) : ((rh0 σ σ' φ hσ m : H0 σ') : N) = m := rfl
variable (hφ : Continuous φ)
def rz1 : Z1 σ →ₗ[R] Z1 σ' where
  toFun f := ⟨f.1 ∘ φ, f.2.1.comp hφ, fun g h => by
    simp only [Function.comp_apply, map_mul, hσ]; exact f.2.2 _ _⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
def rh1 : H1 σ →ₗ[R] H1 σ' :=
  Submodule.mapQ _ _ (rz1 σ σ' φ hσ hφ) fun f hf => by
    obtain ⟨m, hm⟩ := (mem_coboundaries1 σ _).1 hf
    refine (mem_coboundaries1 _ _).2 ⟨m, fun h => ?_⟩
    show f.1 (φ h) = σ' h m - m
    rw [hσ]; exact hm (φ h)
def rz2 : Z2 σ →ₗ[R] Z2 σ' where
  toFun f := ⟨fun p => f.1 (φ p.1, φ p.2), f.2.1.comp (hφ.prodMap hφ), fun g h k => by
    simp only [map_mul, hσ]; exact f.2.2 _ _ _⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
def rh2 : H2 σ →ₗ[R] H2 σ' :=
  Submodule.mapQ _ _ (rz2 σ σ' φ hσ hφ) fun f hf => by
    obtain ⟨c, hc, hcf⟩ := (separated_dvr_second_cohomology_mem σ _).1 hf
    refine (separated_dvr_second_cohomology_mem _ _).2 ⟨c ∘ φ, hc.comp hφ, ?_⟩
    funext p
    obtain ⟨g, h⟩ := p
    have e := congrFun hcf (φ g, φ h)
    simp only [Submodule.coe_subtype] at e
    change _ = f.1 (φ g, φ h)
    rw [← e]
    simp [d1_apply, hσ, map_mul]
end Res
section Equiv
variable {R : Type*} [CommRing R]
  {Γ Γ' : Type*} [Group Γ] [TopologicalSpace Γ] [Group Γ'] [TopologicalSpace Γ']
  {N : Type*} [AddCommGroup N] [Module R N] [TopologicalSpace N]
  [IsTopologicalAddGroup N] [ContinuousConstSMul R N]
  (σ : Representation R Γ N) (σ' : Representation R Γ' N) (e : Γ' ≃* Γ)
  (he : Continuous e) (he' : Continuous e.symm)
theorem symm_rel (hσ : ∀ g n, σ' g n = σ (e g) n) : ∀ g n, σ g n = σ' (e.symm g) n := fun g n => by
  rw [hσ, MulEquiv.apply_symm_apply]
def eq0 (hσ : ∀ g n, σ' g n = σ (e g) n) : H0 σ ≃ₗ[R] H0 σ' :=
  LinearEquiv.ofLinear (rh0 σ σ' e.toMonoidHom hσ)
    (rh0 σ' σ e.symm.toMonoidHom (symm_rel σ σ' e hσ)) (by ext; rfl) (by ext; rfl)
def eq1 (hσ : ∀ g n, σ' g n = σ (e g) n) : H1 σ ≃ₗ[R] H1 σ' :=
  LinearEquiv.ofLinear (rh1 σ σ' e.toMonoidHom hσ he)
    (rh1 σ' σ e.symm.toMonoidHom (symm_rel σ σ' e hσ) he')
    (LinearMap.ext fun x => Submodule.Quotient.induction_on _ x fun f =>
      congrArg Submodule.Quotient.mk (Subtype.ext (funext fun g => by
        show f.1 (e.symm (e g)) = f.1 g
        rw [MulEquiv.symm_apply_apply])))
    (LinearMap.ext fun x => Submodule.Quotient.induction_on _ x fun f =>
      congrArg Submodule.Quotient.mk (Subtype.ext (funext fun g => by
        show f.1 (e (e.symm g)) = f.1 g
        rw [MulEquiv.apply_symm_apply])))
def eq2 (hσ : ∀ g n, σ' g n = σ (e g) n) : H2 σ ≃ₗ[R] H2 σ' :=
  LinearEquiv.ofLinear (rh2 σ σ' e.toMonoidHom hσ he)
    (rh2 σ' σ e.symm.toMonoidHom (symm_rel σ σ' e hσ) he')
    (LinearMap.ext fun x => Submodule.Quotient.induction_on _ x fun f =>
      congrArg Submodule.Quotient.mk (Subtype.ext (funext fun p => by
        show f.1 (e.symm (e p.1), e.symm (e p.2)) = f.1 p
        rw [MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply])))
    (LinearMap.ext fun x => Submodule.Quotient.induction_on _ x fun f =>
      congrArg Submodule.Quotient.mk (Subtype.ext (funext fun p => by
        show f.1 (e (e.symm p.1), e (e.symm p.2)) = f.1 p
        rw [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply])))
end Equiv
end GlobalTheory.CohTransport


