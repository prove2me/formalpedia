-- Prove2me | solution 1 for AlgebraicGeometry.FramedPolarisedAbelianScheme.isReframe_mk_of_forall_eq_sum_baseScalar_smul_pullbackLocalSection
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/f73fc764-f4e7-5e03-97f8-096d24143da8

import Definitions.Def_AlgebraicGeometry_ThetaReframe
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_bijective_unit_app_of_le_opensRange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_FramedPolarisedAbelianScheme_isReframe_mk_of_forall_eq_sum_baseScalar_smul_pullbackLocalSection

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation
open scoped BigOperators

attribute [local instance] MvPolynomial.gradedAlgebra

namespace K76H7

section

variable {S : Type} [CommRing S] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S)) (M : A.Modules)

theorem appLE_top_top {X Y : Scheme.{0}} (g : X ⟶ Y) : g.appLE ⊤ ⊤ le_top = g.appTop :=
  (Scheme.Hom.app_eq_appLE g).symm

theorem appLE_top_top_apply {X Y : Scheme.{0}} (g : X ⟶ Y) (y : Γ(Y, ⊤)) :
    (g.appLE ⊤ ⊤ le_top).hom y = g.appTop.hom y := by
  rw [appLE_top_top]

theorem fst_app_appLE (w : S) :
    (pullback.fst f (𝟙 (Spec (CommRingCat.of S)))).app ⊤
        ((f.appLE ⊤ ⊤ le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom w)) =
      baseScalar f (𝟙 (Spec (CommRingCat.of S))) w := by
  rw [appLE_top_top_apply]
  change ((f.appTop ≫ (pullback.fst f (𝟙 (Spec (CommRingCat.of S)))).appTop).hom
      ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom w)) = _
  rw [← Scheme.Hom.comp_appTop, pullback.condition, Category.comp_id]
  rfl

theorem pullbackLocalSection_sum {X Y : Scheme.{0}} (φ : X ⟶ Y) (L : Y.Modules) (U : Y.Opens)
    {ι : Type} (s : Finset ι) (x : ι → Γ(L, U)) :
    Scheme.Modules.pullbackLocalSection φ (∑ j ∈ s, x j) = ∑ j ∈ s, Scheme.Modules.pullbackLocalSection φ (x j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Scheme.Modules.pullbackLocalSection_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Scheme.Modules.pullbackLocalSection_add, ih]

scoped instance isIso_fst_id : IsIso (pullback.fst f (𝟙 (Spec (CommRingCat.of S)))) := inferInstance

theorem pullbackLocalSection_fst_injective :
    Function.Injective (fun s : Γ(M, ⊤) =>
      (Scheme.Modules.pullbackLocalSection (pullback.fst f (𝟙 (Spec (CommRingCat.of S)))) s :
        Γ((Scheme.Modules.pullback (pullback.fst f (𝟙 (Spec (CommRingCat.of S))))).obj M,
          (pullback.fst f (𝟙 (Spec (CommRingCat.of S)))) ⁻¹ᵁ ⊤))) := by
  have hV : (⊤ : A.Opens) ≤ (pullback.fst f (𝟙 (Spec (CommRingCat.of S)))).opensRange := by
    intro x _
    obtain ⟨y, hy⟩ := (Scheme.homeoOfIso (asIso (pullback.fst f (𝟙 (Spec (CommRingCat.of S)))))).surjective x
    exact ⟨y, hy⟩
  exact (Scheme.Modules.bijective_unit_app_of_le_opensRange (pullback.fst f (𝟙 (Spec (CommRingCat.of S)))) M ⊤ hV).1

end

end K76H7
p2m_reactivate "P2MW.S_AlgebraicGeometry_FramedPolarisedAbelianScheme_isReframe_mk_of_forall_eq_sum_baseScalar_smul_pullbackLocalSection.K76H7"

open K76H7 in
theorem solution
    {g N n : ℕ} {δ : Fin g → ℕ} [hδ : ∀ i, NeZero (δ i)] (e : Fin (N + 1) ≃ ((i : Fin g) → ZMod (δ i)))
    {S : Type} [CommRing S] (X : FramedPolarisedAbelianScheme g N n S)
    (P : Scheme.Modules.ProjPresentation X.pol X.f N) (h₁ : IsClosedImmersion P.toProj)
    (h₂ : Scheme.Modules.IsSectionBasis X.f X.pol P.σ)
    (τ τ' : ((i : Fin g) → ZMod (δ i)) →
      Γ((Scheme.Modules.pullback (pullback.fst X.f (𝟙 (Spec (CommRingCat.of S))))).obj X.pol, ⊤))
    (hτ : ∀ i : Fin (N + 1), τ (e i) =
      (Scheme.Modules.pullbackLocalSection (pullback.fst X.f (𝟙 (Spec (CommRingCat.of S)))) (X.frame.σ i) :
        Γ((Scheme.Modules.pullback (pullback.fst X.f (𝟙 (Spec (CommRingCat.of S))))).obj X.pol,
          (pullback.fst X.f (𝟙 (Spec (CommRingCat.of S)))) ⁻¹ᵁ ⊤)))
    (hτ' : ∀ i : Fin (N + 1), τ' (e i) =
      (Scheme.Modules.pullbackLocalSection (pullback.fst X.f (𝟙 (Spec (CommRingCat.of S)))) (P.σ i) :
        Γ((Scheme.Modules.pullback (pullback.fst X.f (𝟙 (Spec (CommRingCat.of S))))).obj X.pol,
          (pullback.fst X.f (𝟙 (Spec (CommRingCat.of S)))) ⁻¹ᵁ ⊤)))
    (W : Matrix (Fin (N + 1)) (Fin (N + 1)) S)
    (hW : ∀ i : Fin (N + 1), τ' (e i) =
      ∑ j : Fin (N + 1), Polarisation.baseScalar X.f (𝟙 (Spec (CommRingCat.of S))) (W i j) • τ (e j)) :
    X.IsReframe W ⟨X.toPolarisedAbelianScheme, P, h₁, h₂⟩ := by
  refine ⟨P, h₁, h₂, rfl, fun i => ?_⟩
  apply K76H7.pullbackLocalSection_fst_injective X.f X.pol
  change Scheme.Modules.pullbackLocalSection (pullback.fst X.f (𝟙 (Spec (CommRingCat.of S)))) (P.σ i) =
    Scheme.Modules.pullbackLocalSection (pullback.fst X.f (𝟙 (Spec (CommRingCat.of S)))) (∑ j : Fin (N + 1),
      ((X.f.appLE ⊤ ⊤ le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom (W i j))) • X.frame.σ j)
  rw [K76H7.pullbackLocalSection_sum, ← hτ' i, hW i]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Scheme.Modules.pullbackLocalSection_smul, K76H7.fst_app_appLE, hτ j]
  rfl

end S_AlgebraicGeometry_FramedPolarisedAbelianScheme_isReframe_mk_of_forall_eq_sum_baseScalar_smul_pullbackLocalSection
end P2MW
export P2MW.S_AlgebraicGeometry_FramedPolarisedAbelianScheme_isReframe_mk_of_forall_eq_sum_baseScalar_smul_pullbackLocalSection (solution)
