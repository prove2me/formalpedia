-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Hom.eq_of_map_pullbackLocalSection_topToSections_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/dd191613-89e1-5517-8534-3d1efe9ed639

import Mathlib
import Definitions.Def_PresheafOfModules_ExteriorPower
import Definitions.Def_AlgebraicGeometry_ModulesDet
import Definitions.Def_AlgebraicGeometry_KaehlerModule
import Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection
import Definitions.Def_NeronModelInfra_TopFormOrder
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_topToSections_bijective_of_isAffineOpen
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Hom_eq_of_map_pullbackLocalSection_topToSections_eq

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

open TopologicalSpace

namespace BenchOB3

theorem sec_ext {X : Scheme.{u}} (M : X.Modules) {ι : Type u} (Wi : ι → X.Opens) (V : X.Opens)
    (hle : ∀ i, Wi i ≤ V) (hcover : ∀ x ∈ V, ∃ i, x ∈ Wi i) (s t : Γ(M, V))
    (h : ∀ i, M.presheaf.map (homOfLE (hle i)).op s = M.presheaf.map (homOfLE (hle i)).op t) : s = t :=
  TopCat.Sheaf.eq_of_locally_eq' ⟨M.presheaf, Scheme.Modules.isSheaf M⟩ Wi V (fun i => homOfLE (hle i))
    (fun x hx => by obtain ⟨i, hi⟩ := hcover x hx; exact Opens.mem_iSup.mpr ⟨i, hi⟩) s t h

theorem app_naturality {X : Scheme.{u}} {M N : X.Modules} (θ : M ⟶ N) {V W : X.Opens} (i : W ⟶ V)
    (x : Γ(M, V)) :
    N.presheaf.map i.op (θ.app V x) = θ.app W (M.presheaf.map i.op x) := by
  have h := θ.mapPresheaf.naturality i.op
  have h' := congrFun (congrArg (fun f => (ConcreteCategory.hom f : Γ(M, V) → Γ(N, W))) h) x
  exact h'.symm

theorem algebraMap_comm {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    {X Y : Scheme.{u}} (gY : Y ⟶ Spec (CommRingCat.of A)) (gX : X ⟶ Spec (CommRingCat.of B))
    (φ : X ⟶ Y) (hφ : φ ≫ gY = gX ≫ Spec.map (CommRingCat.ofHom (algebraMap A B)))
    (U : Y.Opens) (W : X.Opens) (hWU : W ≤ φ ⁻¹ᵁ U) (a : A) :
    (φ.appLE U W hWU) ((gY.constToPresheaf.app (op U)) a) =
      (gX.constToPresheaf.app (op W)) (algebraMap A B a) := by
  have hc : ∀ {h₁ h₂ : X ⟶ Spec (CommRingCat.of A)} (_ : h₁ = h₂) (e₁ : W ≤ h₁ ⁻¹ᵁ ⊤)
      (e₂ : W ≤ h₂ ⁻¹ᵁ ⊤), h₁.appLE ⊤ W e₁ = h₂.appLE ⊤ W e₂ := by
    rintro _ _ rfl _ _; rfl
  have h1 : gY.constToPresheaf.app (op U) ≫ φ.appLE U W hWU =
      CommRingCat.ofHom (algebraMap A B) ≫ gX.constToPresheaf.app (op W) := by
    change ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ gY.appLE ⊤ U le_top) ≫ φ.appLE U W hWU =
      CommRingCat.ofHom (algebraMap A B) ≫
        ((Scheme.ΓSpecIso (CommRingCat.of B)).inv ≫ gX.appLE ⊤ W le_top)
    rw [Category.assoc, Scheme.Hom.appLE_comp_appLE, hc hφ _ le_top,
      ← Scheme.Hom.appLE_comp_appLE _ _ ⊤ ⊤ W le_top le_top]
    have h2 : (Spec.map (CommRingCat.ofHom (algebraMap A B))).appLE ⊤ ⊤ le_top =
        (Spec.map (CommRingCat.ofHom (algebraMap A B))).appTop := by
      simp [Scheme.Hom.appLE]
    rw [h2, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality, Category.assoc]
  have := congrFun (congrArg (fun f => (ConcreteCategory.hom f : A → Γ(X, W))) h1) a
  simpa using this

end BenchOB3

theorem solution
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    {X Y : Scheme.{u}} (gY : Y ⟶ Spec (CommRingCat.of A)) (gX : X ⟶ Spec (CommRingCat.of B))
    (φ : X ⟶ Y) (hφ : φ ≫ gY = gX ≫ Spec.map (CommRingCat.ofHom (algebraMap A B))) (d : ℕ)
    (θ θ' : (Scheme.Modules.pullback φ).obj (gY.topDifferentials d) ⟶ gX.topDifferentials d)
    (hθ : ∀ (U : Y.Opens) (hU : IsAffineOpen U) (W : X.Opens) (hW : IsAffineOpen W) (hWU : W ≤ φ ⁻¹ᵁ U),
        letI := gY.sectionsAlgebra U; letI := gX.sectionsAlgebra W
        letI : Algebra Γ(Y, U) Γ(X, W) := (φ.appLE U W hWU).hom.toAlgebra
        ∀ [Algebra A Γ(X, W)] [IsScalarTower A B Γ(X, W)] [IsScalarTower A Γ(Y, U) Γ(X, W)]
          (η : ⋀[Γ(Y, U)]^d (gY.kaehlerPresheaf.obj (op U))),
          (gX.topDifferentials d).presheaf.map (homOfLE hWU).op
              (θ.app (φ ⁻¹ᵁ U) (Scheme.Modules.pullbackLocalSection φ (gY.topToSections d U η))) =
            gX.topToSections d W (NeronModelInfra.TopFormOrder.topFormMap A B Γ(Y, U) Γ(X, W) d η))
    (hθ' : ∀ (U : Y.Opens) (hU : IsAffineOpen U) (W : X.Opens) (hW : IsAffineOpen W) (hWU : W ≤ φ ⁻¹ᵁ U),
        letI := gY.sectionsAlgebra U; letI := gX.sectionsAlgebra W
        letI : Algebra Γ(Y, U) Γ(X, W) := (φ.appLE U W hWU).hom.toAlgebra
        ∀ [Algebra A Γ(X, W)] [IsScalarTower A B Γ(X, W)] [IsScalarTower A Γ(Y, U) Γ(X, W)]
          (η : ⋀[Γ(Y, U)]^d (gY.kaehlerPresheaf.obj (op U))),
          (gX.topDifferentials d).presheaf.map (homOfLE hWU).op
              (θ'.app (φ ⁻¹ᵁ U) (Scheme.Modules.pullbackLocalSection φ (gY.topToSections d U η))) =
            gX.topToSections d W (NeronModelInfra.TopFormOrder.topFormMap A B Γ(Y, U) Γ(X, W) d η)) :
    θ = θ' := by

  have key : ∀ (U : Y.Opens) (hU : IsAffineOpen U) (s : Γ(gY.topDifferentials d, U)),
      θ.app (φ ⁻¹ᵁ U) (Scheme.Modules.pullbackLocalSection φ s) =
        θ'.app (φ ⁻¹ᵁ U) (Scheme.Modules.pullbackLocalSection φ s) := by
    intro U hU s
    obtain ⟨η, rfl⟩ := (gY.topToSections_bijective_of_isAffineOpen d hU).2 s
    refine BenchOB3.sec_ext (gX.topDifferentials d)
      (fun i : {W : X.affineOpens // (W : X.Opens) ≤ φ ⁻¹ᵁ U} => (i.1 : X.Opens)) (φ ⁻¹ᵁ U)
      (fun i => i.2) ?_ _ _ ?_
    · intro x hx
      obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWU⟩ :=
        X.isBasis_affineOpens.exists_subset_of_mem_open hx (φ ⁻¹ᵁ U).2
      exact ⟨⟨⟨W, hW⟩, hWU⟩, hxW⟩
    · rintro ⟨⟨W, hW⟩, hWU⟩
      letI := gY.sectionsAlgebra U; letI := gX.sectionsAlgebra W
      letI : Algebra Γ(Y, U) Γ(X, W) := (φ.appLE U W hWU).hom.toAlgebra
      letI : Algebra A Γ(X, W) :=
        ((algebraMap Γ(Y, U) Γ(X, W)).comp (algebraMap A Γ(Y, U))).toAlgebra
      haveI : IsScalarTower A Γ(Y, U) Γ(X, W) := IsScalarTower.of_algebraMap_eq' rfl
      haveI : IsScalarTower A B Γ(X, W) :=
        IsScalarTower.of_algebraMap_eq' (RingHom.ext fun a => BenchOB3.algebraMap_comm gY gX φ hφ U W hWU a)
      exact (hθ U hU W hW hWU η).trans (hθ' U hU W hW hWU η).symm

  apply Scheme.Modules.pullback_hom_ext
  intro U s
  refine BenchOB3.sec_ext (gX.topDifferentials d)
    (fun i : {U' : Y.affineOpens // (U' : Y.Opens) ≤ U} => φ ⁻¹ᵁ (i.1 : Y.Opens)) (φ ⁻¹ᵁ U)
    (fun i => fun x hx => i.2 hx) ?_ _ _ ?_
  · intro x hx
    obtain ⟨_, ⟨U', hU', rfl⟩, hxU', hU'U⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open hx U.2
    exact ⟨⟨⟨U', hU'⟩, hU'U⟩, hxU'⟩
  · rintro ⟨⟨U', hU'⟩, hU'U⟩
    rw [BenchOB3.app_naturality, BenchOB3.app_naturality,
      Scheme.Modules.map_homOfLE_pullbackLocalSection φ hU'U]
    exact key U' hU' _

end S_AlgebraicGeometry_Scheme_Hom_eq_of_map_pullbackLocalSection_topToSections_eq
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Hom_eq_of_map_pullbackLocalSection_topToSections_eq (solution)
