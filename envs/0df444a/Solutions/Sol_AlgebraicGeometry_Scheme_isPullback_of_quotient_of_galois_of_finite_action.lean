-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.isPullback_of_quotient_of_galois_of_finite_action
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/e184b5cf-f8d1-5e56-9e9b-01efa0d47b49

import Mathlib
import Theorems.Thm_Algebra_bijective_tensorProduct_lift_of_forall_iff_mem_range_of_galois
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_isPullback_of_quotient_of_galois_of_finite_action

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

universe u v

namespace GaloisCartAux

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))

noncomputable def φ (U : X.affineOpens) : CommRingCat.of R ⟶ Γ(X, U.1) :=
  (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appLE ⊤ U.1 (by simp)

lemma fromSpec_comp (U : X.affineOpens) : U.2.fromSpec ≫ f = Spec.map (φ f U) := by
  rw [φ, Spec.map_comp, ← Scheme.isoSpec_Spec_inv, ← IsAffineOpen.fromSpec_top]
  exact (IsAffineOpen.SpecMap_appLE_fromSpec f (isAffineOpen_top _) U.2 (by simp)).symm

lemma φ_comp_appLE_eq {Y : Scheme.{u}} {S : Type u} [CommRing S] (g : Y ⟶ X) (h : Y ⟶ Spec (CommRingCat.of S))
    (t : CommRingCat.of R ⟶ CommRingCat.of S) (hsq : g ≫ f = h ≫ Spec.map t)
    (U : X.affineOpens) (W : Y.affineOpens) (e : W.1 ≤ g ⁻¹ᵁ U.1) :
    φ f U ≫ g.appLE U.1 W.1 e = t ≫ φ h W := by
  apply Spec.map_injective
  rw [Spec.map_comp, Spec.map_comp, ← fromSpec_comp, ← fromSpec_comp, ← Category.assoc,
    IsAffineOpen.SpecMap_appLE_fromSpec g U.2 W.2 e, Category.assoc, hsq, Category.assoc]

lemma appLE_self_of_eq_id {Y : Scheme.{u}} (g : Y ⟶ Y) (hg : g = 𝟙 Y) (W : Y.Opens) (e : W ≤ g ⁻¹ᵁ W) :
    g.appLE W W e = 𝟙 _ := by
  subst hg
  have he : homOfLE e = 𝟙 W := Subsingleton.elim _ _
  rw [Scheme.Hom.appLE, he]
  erw [op_id, Y.presheaf.map_id, Category.comp_id]
  simp

lemma appLE_self_of_eq_comp {Y : Scheme.{u}} (g g₁ g₂ : Y ⟶ Y) (hg : g = g₁ ≫ g₂) (W : Y.Opens)
    (e : W ≤ g ⁻¹ᵁ W) (e₁ : W ≤ g₁ ⁻¹ᵁ W) (e₂ : W ≤ g₂ ⁻¹ᵁ W) :
    g.appLE W W e = g₂.appLE W W e₂ ≫ g₁.appLE W W e₁ := by
  subst hg
  rw [Scheme.Hom.appLE_comp_appLE]

lemma isPullback_fromSpec_appLE {Y : Scheme.{u}} (q : Y ⟶ X) (V : X.affineOpens) (hV : IsAffineOpen (q ⁻¹ᵁ V.1)) :
    IsPullback hV.fromSpec (Spec.map (q.appLE V.1 (q ⁻¹ᵁ V.1) le_rfl)) q V.2.fromSpec := by
  refine (IsOpenImmersion.isPullback (Spec.map (q.appLE V.1 (q ⁻¹ᵁ V.1) le_rfl)) hV.fromSpec V.2.fromSpec q ?_ ?_).flip
  · exact (IsAffineOpen.SpecMap_appLE_fromSpec q V.2 hV le_rfl).symm
  · rw [IsAffineOpen.opensRange_fromSpec, IsAffineOpen.opensRange_fromSpec]

end GaloisCartAux

open GaloisCartAux in
theorem solution
    (𝒪 : Type) [CommRing 𝒪] (𝒪' : Type) [CommRing 𝒪'] [Algebra 𝒪 𝒪'] [Module.Finite 𝒪 𝒪'] [Module.Free 𝒪 𝒪']
    [Module.FaithfullyFlat 𝒪 𝒪']
    (G : Type) [Group G] [Finite G] (τ : G →* (𝒪' ≃ₐ[𝒪] 𝒪'))
    (hgal : Function.Bijective fun x : 𝒪' ⊗[𝒪] 𝒪' => fun σ : G =>
      Algebra.TensorProduct.lmul' (S := 𝒪') 𝒪
        (Algebra.TensorProduct.map (AlgHom.id 𝒪 𝒪') ((τ σ : 𝒪' ≃ₐ[𝒪] 𝒪') : 𝒪' →ₐ[𝒪] 𝒪') x))
    (M' : Scheme.{0}) (πM' : M' ⟶ Spec (CommRingCat.of 𝒪'))
    (ρ : G → (M' ≅ M')) (hρ1 : (ρ 1).hom = 𝟙 M') (hρmul : ∀ σ σ' : G, (ρ (σ * σ')).hom = (ρ σ).hom ≫ (ρ σ').hom)
    (hρπ : ∀ σ : G, (ρ σ).hom ≫ πM' = πM' ≫ Spec.map (CommRingCat.ofHom ((τ σ : 𝒪' ≃ₐ[𝒪] 𝒪') : 𝒪' →+* 𝒪')))
    (M : Scheme.{0}) (πM : M ⟶ Spec (CommRingCat.of 𝒪)) (q : M' ⟶ M)
    (hq : ∀ σ : G, (ρ σ).hom ≫ q = q)
    (hqπ : q ≫ πM = πM' ≫ Spec.map (CommRingCat.ofHom (algebraMap 𝒪 𝒪')))
    (haff : IsAffineHom q)
    (hinj : ∀ V : M.Opens, Function.Injective (q.app V))
    (hrange : ∀ V : M.Opens, Set.range (q.app V) =
      {t | ∀ σ : G, (ρ σ).hom.appLE (q ⁻¹ᵁ V) (q ⁻¹ᵁ V)
        (by rw [← Scheme.Hom.comp_preimage, hq σ]) t = t}) :
    CategoryTheory.IsPullback q πM' πM (Spec.map (CommRingCat.ofHom (algebraMap 𝒪 𝒪'))) := by
  classical
  haveI := haff

  let 𝒰 : M.OpenCover := Scheme.Cover.mkOfCovers M.affineOpens (fun V => Spec Γ(M, V.1)) (fun V => V.2.fromSpec)
    (fun x => by
      have hx : x ∈ (⨆ U : M.affineOpens, (U : M.Opens)) := by rw [iSup_affineOpens_eq_top]; trivial
      obtain ⟨V, hV⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
      obtain ⟨y, hy⟩ := V.2.range_fromSpec.ge hV
      exact ⟨V, y, hy⟩)
  refine Scheme.isPullback_of_openCover q πM' πM _ 𝒰 fun V => ?_

  have hU' : IsAffineOpen (q ⁻¹ᵁ V.1) := V.2.preimage q
  let U' : M'.affineOpens := ⟨q ⁻¹ᵁ V.1, hU'⟩
  letI algC : Algebra 𝒪 Γ(M, V.1) := (φ πM V).hom.toAlgebra
  letI algBA : Algebra 𝒪' Γ(M', q ⁻¹ᵁ V.1) := (φ πM' U').hom.toAlgebra
  letI algA : Algebra 𝒪 Γ(M', q ⁻¹ᵁ V.1) := ((φ πM' U').hom.comp (algebraMap 𝒪 𝒪')).toAlgebra
  haveI : IsScalarTower 𝒪 𝒪' Γ(M', q ⁻¹ᵁ V.1) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have algC_def : ∀ r : 𝒪, algebraMap 𝒪 Γ(M, V.1) r = (φ πM V).hom r := fun _ => rfl
  have algBA_def : ∀ b : 𝒪', algebraMap 𝒪' Γ(M', q ⁻¹ᵁ V.1) b = (φ πM' U').hom b := fun _ => rfl
  have algA_def : ∀ r : 𝒪, algebraMap 𝒪 Γ(M', q ⁻¹ᵁ V.1) r = (φ πM' U').hom (algebraMap 𝒪 𝒪' r) := fun _ => rfl

  let ιr : Γ(M, V.1) ⟶ Γ(M', q ⁻¹ᵁ V.1) := q.appLE V.1 (q ⁻¹ᵁ V.1) le_rfl
  have hιcomm : ∀ r : 𝒪, ιr.hom (algebraMap 𝒪 Γ(M, V.1) r) = algebraMap 𝒪 Γ(M', q ⁻¹ᵁ V.1) r := by
    intro r
    rw [algC_def, algA_def, ← CommRingCat.comp_apply,
      φ_comp_appLE_eq πM q πM' (CommRingCat.ofHom (algebraMap 𝒪 𝒪')) hqπ V U' le_rfl]
    rfl
  let ι : Γ(M, V.1) →ₐ[𝒪] Γ(M', q ⁻¹ᵁ V.1) := ⟨ιr.hom, hιcomm⟩
  have ι_apply : ∀ c, ι c = ιr.hom c := fun _ => rfl

  have hle : ∀ σ : G, q ⁻¹ᵁ V.1 ≤ (ρ σ).hom ⁻¹ᵁ (q ⁻¹ᵁ V.1) := fun σ => by
    rw [← Scheme.Hom.comp_preimage, hq σ]
  let θr : G → (Γ(M', q ⁻¹ᵁ V.1) →+* Γ(M', q ⁻¹ᵁ V.1)) := fun σ =>
    ((ρ σ).hom.appLE (q ⁻¹ᵁ V.1) (q ⁻¹ᵁ V.1) (hle σ)).hom
  have θr_one : θr 1 = RingHom.id _ := by
    change ((ρ 1).hom.appLE (q ⁻¹ᵁ V.1) (q ⁻¹ᵁ V.1) (hle 1)).hom = _
    rw [appLE_self_of_eq_id _ hρ1]
    rfl
  have θr_mul : ∀ σ σ' : G, θr (σ * σ') = (θr σ).comp (θr σ') := by
    intro σ σ'
    change ((ρ (σ * σ')).hom.appLE _ _ (hle (σ * σ'))).hom =
      ((ρ σ').hom.appLE _ _ (hle σ') ≫ (ρ σ).hom.appLE _ _ (hle σ)).hom
    rw [appLE_self_of_eq_comp _ _ _ (hρmul σ σ')]
  let θ : G → (Γ(M', q ⁻¹ᵁ V.1) ≃+* Γ(M', q ⁻¹ᵁ V.1)) := fun σ =>
    RingEquiv.ofRingHom (θr σ) (θr σ⁻¹) (by rw [← θr_mul, mul_inv_cancel, θr_one])
      (by rw [← θr_mul, inv_mul_cancel, θr_one])
  have θ_apply : ∀ σ a, θ σ a = θr σ a := fun _ _ => rfl
  have hθ1 : θ 1 = RingEquiv.refl _ := by
    ext a; rw [θ_apply, θr_one]; rfl
  have hθmul : ∀ σ σ' : G, θ (σ * σ') = (θ σ').trans (θ σ) := by
    intro σ σ'; ext a; rw [θ_apply, θr_mul]; rfl
  have hθτ : ∀ (σ : G) (l : 𝒪') (a : Γ(M', q ⁻¹ᵁ V.1)),
      θ σ (algebraMap 𝒪' _ l * a) = algebraMap 𝒪' _ (τ σ l) * θ σ a := by
    intro σ l a
    rw [map_mul]
    congr 1
    rw [θ_apply, algBA_def, algBA_def]
    change (φ πM' U' ≫ (ρ σ).hom.appLE (q ⁻¹ᵁ V.1) (q ⁻¹ᵁ V.1) (hle σ)).hom l = _
    rw [φ_comp_appLE_eq πM' (ρ σ).hom πM' (CommRingCat.ofHom ((τ σ : 𝒪' ≃ₐ[𝒪] 𝒪') : 𝒪' →+* 𝒪')) (hρπ σ) U' U' (hle σ)]
    rfl

  have hι : Function.Injective ι := by
    intro x y hxy
    rw [ι_apply, ι_apply] at hxy
    apply hinj V.1
    change (q.app V.1).hom x = (q.app V.1).hom y
    rwa [Scheme.Hom.app_eq_appLE]
  have hιG : ∀ a : Γ(M', q ⁻¹ᵁ V.1), (∀ σ : G, θ σ a = a) ↔ a ∈ Set.range ι := by
    intro a
    have hr := Set.ext_iff.mp (hrange V.1) a
    constructor
    · intro h
      obtain ⟨c, hc⟩ := hr.mpr (fun σ => h σ)
      refine ⟨c, ?_⟩
      rw [ι_apply, ← hc]
      change (q.appLE V.1 (q ⁻¹ᵁ V.1) le_rfl).hom c = (q.app V.1).hom c
      rw [Scheme.Hom.appLE_eq_app]
    · rintro ⟨c, rfl⟩ σ
      have : ι c ∈ Set.range (q.app V.1) := ⟨c, by rw [ι_apply]; change (q.app V.1).hom c = (q.appLE V.1 (q ⁻¹ᵁ V.1) le_rfl).hom c; rw [Scheme.Hom.appLE_eq_app]⟩
      exact (Set.ext_iff.mp (hrange V.1) (ι c)).mp this σ

  have hbij := Algebra.bijective_tensorProduct_lift_of_forall_iff_mem_range_of_galois 𝒪 𝒪' G τ hgal
    Γ(M', q ⁻¹ᵁ V.1) θ hθ1 hθmul hθτ Γ(M, V.1) ι hι hιG
  let Φ := Algebra.TensorProduct.lift (ι : Γ(M, V.1) →ₐ[𝒪] Γ(M', q ⁻¹ᵁ V.1))
    (IsScalarTower.toAlgHom 𝒪 𝒪' Γ(M', q ⁻¹ᵁ V.1)) (fun c l => Commute.all _ _)
  let eΦ : Γ(M, V.1) ⊗[𝒪] 𝒪' ≃+* Γ(M', q ⁻¹ᵁ V.1) := RingEquiv.ofBijective Φ.toRingHom hbij
  have eΦ_tmul : ∀ c b, eΦ (c ⊗ₜ b) = ιr.hom c * (φ πM' U').hom b := fun c b => by
    change Φ (c ⊗ₜ b) = _
    rw [Algebra.TensorProduct.lift_tmul]; rfl

  have hpo : IsPushout (CommRingCat.ofHom (algebraMap 𝒪 Γ(M, V.1))) (CommRingCat.ofHom (algebraMap 𝒪 𝒪'))
      ιr (φ πM' U') := by
    refine (CommRingCat.isPushout_tensorProduct 𝒪 Γ(M, V.1) 𝒪').of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _)
      eΦ.toCommRingCatIso ?_ ?_ ?_ ?_
    · simp
    · simp
    · ext c
      change eΦ (c ⊗ₜ 1) = ιr.hom c
      rw [eΦ_tmul, map_one, mul_one]
    · ext b
      change eΦ (1 ⊗ₜ b) = (φ πM' U').hom b
      rw [eΦ_tmul, map_one, one_mul]
  have hSpec := isPullback_SpecMap_of_isPushout _ _ _ _ hpo

  have P0 := isPullback_fromSpec_appLE q V hU'
  refine hSpec.of_iso P0.isoPullback (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · erw [Iso.refl_hom, Category.comp_id]
    exact (P0.isoPullback_hom_snd).symm
  · erw [Iso.refl_hom, Category.comp_id]
    change Spec.map (φ πM' U') = P0.isoPullback.hom ≫ pullback.fst q V.2.fromSpec ≫ πM'
    rw [P0.isoPullback_hom_fst_assoc]
    exact (fromSpec_comp πM' U').symm
  · erw [Iso.refl_hom, Category.comp_id, Category.id_comp]
    exact (fromSpec_comp πM V).symm
  · simp

end S_AlgebraicGeometry_Scheme_isPullback_of_quotient_of_galois_of_finite_action
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_isPullback_of_quotient_of_galois_of_finite_action (solution)
