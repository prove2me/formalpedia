-- Prove2me | solution 1 for AlgebraicGeometry.exists_forall_geomFibreH0Finrank_tensorPow_eq_hilbertFunctionOf_of_point_geomFibre
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/017203e5-c05d-59b6-bd7d-7c7c4607d4a5

import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_HilbertFunctor
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_projPresentation_pullback_sigma_eq_toProj_eq
import Theorems.Thm_AlgebraicGeometry_HilbertFunctor_exists_forall_geomFibreH0Finrank_tensorPow_eq_hilbertFunctionOf_of_point
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_geomFibreH0Finrank_eq_of_isPullback
import Theorems.Thm_AlgebraicGeometry_ProjSpace_map_preimage_basicOpen_X
import Theorems.Thm_AlgebraicGeometry_ProjSpace_restrictFun_app_app_awayToSection_eq_app_awayToSection_map
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_forall_geomFibreH0Finrank_tensorPow_eq_hilbertFunctionOf_of_point_geomFibre
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left"

set_option autoImplicit false
open MvPolynomial CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.HilbertFunctor NeronModelInfra GoodReductionJacobian
p2m_open "CategoryTheory.MonoidalCategory"
attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace F3Sol

universe u

theorem smul_map_eq_of_eq {X : Scheme.{u}} (M : X.Modules) {W W' : X.Opens} (ρ : W' ⟶ W) (e : W = W')
    (s t : Γ(M, ⊤)) (g : Γ(X, W))
    (h : g • M.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op s = M.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op t) :
    (X.presheaf.map ρ.op g) • M.presheaf.map (homOfLE (le_top : W' ≤ ⊤)).op s =
      M.presheaf.map (homOfLE (le_top : W' ≤ ⊤)).op t := by
  subst e
  have hρ : ρ = 𝟙 _ := Subsingleton.elim _ _
  rw [hρ, op_id, CategoryTheory.Functor.map_id]
  exact h

theorem descend {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] {X : Scheme.{u}}
    {f₁ : X ⟶ Spec (.of R)} {M : X.Modules} {N : ℕ} (𝔓 : M.ProjPresentation f₁ N)
    (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A))
    (hφ : 𝔓.toProj = φ ≫ ProjSpace.map R A N) :
    ∃ 𝔓' : M.ProjPresentation (φ ≫ ProjSpace.π A N) N, (∀ i, 𝔓'.σ i = 𝔓.σ i) ∧ 𝔓'.toProj = φ := by
  obtain ⟨σ, toProj, hπ, frame, ratio⟩ := 𝔓
  dsimp only at hφ
  subst hφ
  have hpre : ∀ i : Fin (N + 1),
      (φ ≫ ProjSpace.map R A N) ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i) =
        φ ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A) (MvPolynomial.X i) := by
    intro i
    rw [← ProjSpace.map_preimage_basicOpen_X R A N i]
    rfl
  refine ⟨{ σ := σ
            toProj := φ
            toProj_π := rfl
            frame := ?_
            app_ratio_smul := ?_ }, fun i => rfl, rfl⟩
  · intro i V hV
    exact frame i V (by rw [hpre]; exact hV)
  · intro i j
    have hle : Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A) (MvPolynomial.X i) ≤
        ProjSpace.map R A N ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i) :=
      (ProjSpace.map_preimage_basicOpen_X R A N i).symm.le
    have key := AlgebraicGeometry.ProjSpace.restrictFun_app_app_awayToSection_eq_app_awayToSection_map
      (𝟙 _) A (𝟙 _) (ProjSpace.map R A N) (by simp) 1 (MvPolynomial.X j) (MvPolynomial.isHomogeneous_X R j) i
      (by simpa using hle)
    have key' : ((Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A)).presheaf.map (homOfLE hle).op)
        ((ProjSpace.map R A N).app _ (Proj.awayToSection _ (MvPolynomial.X i) (ProjSpace.ratio R N i j))) =
        Proj.awayToSection _ (MvPolynomial.X i) (ProjSpace.ratio A N i j) := by
      have k := key
      erw [Scheme.Hom.id_app, Scheme.Hom.id_app] at k
      convert k using 3
      all_goals first
        | rfl
        | (erw [CategoryTheory.id_apply]
           congr 1
           apply HomogeneousLocalization.val_injective
           simp [ProjSpace.ratio, HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.val_mk, MvPolynomial.map_X])
    have T := smul_map_eq_of_eq M ((TopologicalSpace.Opens.map φ.base).map (homOfLE hle)) (hpre i) (σ i) (σ j) _ (ratio i j)
    convert T using 2
    rw [← key', Scheme.Hom.comp_app]
    have nat0 := Scheme.Hom.naturality φ (homOfLE hle).op
    have h2 := CategoryTheory.ConcreteCategory.congr_hom nat0
      ((ProjSpace.map R A N).app _ (Proj.awayToSection _ (MvPolynomial.X i) (ProjSpace.ratio R N i j)))
    rw [CategoryTheory.comp_apply, CategoryTheory.comp_apply] at h2
    refine h2.trans ?_
    rfl

noncomputable def powIso {X Y : Scheme.{u}} (p : X ⟶ Y) (𝓜 : Y.Modules) (𝓜' : X.Modules)
    (η : (Scheme.Modules.pullback p).obj 𝓜 ≅ 𝓜') :
    ∀ d : ℕ, (Scheme.Modules.pullback p).obj
        (Nat.rec (motive := fun _ => Y.Modules) (𝟙_ Y.Modules) (fun _ M => M ⊗ 𝓜) d) ≅
        Nat.rec (motive := fun _ => X.Modules) (𝟙_ X.Modules) (fun _ M => M ⊗ 𝓜') d
  | 0 => Scheme.Modules.pullbackTensorUnitObjIso p
  | d + 1 => Scheme.Modules.pullbackTensorObjIso p _ 𝓜 ≪≫ (powIso p 𝓜 𝓜' η d ⊗ᵢ η)

end F3Sol

end

open F3Sol in

theorem solution
    (S : Type) [CommRing S] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of S))
    (𝓛X : X.Modules) (hX₁ : Scheme.Modules.IsInvertible 𝓛X)
    {n : ℕ} (𝔓 : Scheme.Modules.ProjPresentation 𝓛X f n)
    (S' : Type) [CommRing S'] (ψ : S →+* S')
    (Z : Scheme.{0}) (ι : Z ⟶ pullback f (Spec.map (CommRingCat.ofHom ψ)))
    (j : pullback f (Spec.map (CommRingCat.ofHom ψ)) ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) S'))
    (hj₁ : j ≫ ProjSpace.π S' n = pullback.snd f (Spec.map (CommRingCat.ofHom ψ)))
    (hj₂ : (letI : Algebra S S' := ψ.toAlgebra; j ≫ ProjSpace.map S S' n) =
      pullback.fst f (Spec.map (CommRingCat.ofHom ψ)) ≫ 𝔓.toProj)
    (k : Type) [Field k] [IsAlgClosed k] (sk : S' →+* k)
    (P' : Polynomial ℚ) (m' : ℕ) (q : Point k n (hilbertFunctionOf n P' m'))
    (Zk : Scheme.{0}) (ιk : Zk ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)) (hιk : IsClosedImmersion ιk)
    (e : Zk ⟶ Z)
    (he₁ : IsPullback e (ιk ≫ ProjSpace.π k n) (ι ≫ pullback.snd f (Spec.map (CommRingCat.ofHom ψ)))
      (Spec.map (CommRingCat.ofHom sk)))
    (he₂ : (letI : Algebra S' k := sk.toAlgebra; ιk ≫ ProjSpace.map S' k n) = e ≫ ι ≫ j)
    (hZk : ∀ d : ℕ, m' ≤ d → ∀ (F : MvPolynomial (Fin (n + 1)) k) (hF : F.IsHomogeneous d),
      (F ∈ q.I ↔ ∀ i : Fin (n + 1),
        (ιk.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i)))
          ((Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i))
            (HomogeneousLocalization.mk
              { deg := d
                num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩
                den := ⟨MvPolynomial.X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr (MvPolynomial.isHomogeneous_X_pow i d)⟩
                den_mem := ⟨d, rfl⟩ })) = 0)) :
    ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
      Scheme.Modules.geomFibreH0Finrank (ι ≫ pullback.snd f (Spec.map (CommRingCat.ofHom ψ)))
        (Nat.rec (motive := fun _ => Z.Modules) (𝟙_ Z.Modules)
          (fun _ M => M ⊗ (Scheme.Modules.pullback (ι ≫ pullback.fst f (Spec.map (CommRingCat.ofHom ψ)))).obj 𝓛X) d) k sk =
      hilbertFunctionOf n P' m' d := by
  letI instSS' : Algebra S S' := ψ.toAlgebra
  letI instS'k : Algebra S' k := sk.toAlgebra

  obtain ⟨𝔓a, -, h𝔓a⟩ :=
    AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_projPresentation_pullback_sigma_eq_toProj_eq
      (pullback.fst f (Spec.map (CommRingCat.ofHom ψ))) 𝔓
  obtain ⟨𝔓b, -, h𝔓b⟩ := descend 𝔓a j (by rw [h𝔓a]; exact hj₂.symm)
  obtain ⟨𝔓c, -, h𝔓c⟩ :=
    AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_projPresentation_pullback_sigma_eq_toProj_eq (e ≫ ι) 𝔓b
  obtain ⟨𝔓d, -, h𝔓d⟩ := descend 𝔓c ιk (by rw [h𝔓c, h𝔓b, Category.assoc]; exact he₂.symm)

  have h𝓛k : Scheme.Modules.IsInvertible
      ((Scheme.Modules.pullback (e ≫ ι)).obj
        ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom ψ)))).obj 𝓛X)) :=
    (hX₁.pullback _).pullback _
  obtain ⟨d₀, hd₀⟩ :=
    AlgebraicGeometry.HilbertFunctor.exists_forall_geomFibreH0Finrank_tensorPow_eq_hilbertFunctionOf_of_point
      n P' m' k q Zk ιk hιk hZk _ h𝓛k 𝔓d h𝔓d
  refine ⟨d₀, fun d hd => ?_⟩

  have η : (Scheme.Modules.pullback e).obj
        ((Scheme.Modules.pullback (ι ≫ pullback.fst f (Spec.map (CommRingCat.ofHom ψ)))).obj 𝓛X) ≅
      (Scheme.Modules.pullback (e ≫ ι)).obj
        ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom ψ)))).obj 𝓛X) :=
    (Scheme.Modules.pullbackComp e (ι ≫ pullback.fst f (Spec.map (CommRingCat.ofHom ψ)))).app 𝓛X ≪≫
      eqToIso (by rw [Category.assoc]) ≪≫
      ((Scheme.Modules.pullbackComp (e ≫ ι) (pullback.fst f (Spec.map (CommRingCat.ofHom ψ)))).app 𝓛X).symm
  have key := AlgebraicGeometry.Scheme.Modules.geomFibreH0Finrank_eq_of_isPullback sk
    (ι ≫ pullback.snd f (Spec.map (CommRingCat.ofHom ψ))) (ιk ≫ ProjSpace.π k n) e he₁ _ _
    (powIso e _ _ η d) k (RingHom.id k)
  rw [RingHom.id_comp] at key
  rw [← key]
  exact hd₀ d hd

end S_AlgebraicGeometry_exists_forall_geomFibreH0Finrank_tensorPow_eq_hilbertFunctionOf_of_point_geomFibre
end P2MW
export P2MW.S_AlgebraicGeometry_exists_forall_geomFibreH0Finrank_tensorPow_eq_hilbertFunctionOf_of_point_geomFibre (solution)
