-- Prove2me | solution 1 for AlgebraicGeometry.SmallExtension.exists_isInvertible_pullback_iso_of_isPicObstructionCocycle_of_forall_mem_range
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/32829f2c-0569-5c95-8540-e3da4aebd2df

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_CechPicardObstruction
import Theorems.Thm_AlgebraicGeometry_IsPullback_surjective_app_and_ker_app_eq_map_ker_of_isAffineOpen
import Theorems.Thm_AlgebraicGeometry_SmallExtension_isFibreReading_zero_add_mul_neg_restrict_and_exists_isFibreReading
import Theorems.Thm_AlgebraicGeometry_SmallExtension_exists_mem_map_range_and_isFibreReading_of_isAffineOpen
import Theorems.Thm_AlgebraicGeometry_SmallExtension_IsFibreReading_eq_zero_of_isFibreReading_zero_of_flat
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_CechTrivialisation_exists_isInvertible_transition_eq
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_CechTrivialisation_nonempty_iso_of_transition_eq
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_CechTrivialisation_comap_transition
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_SmallExtension_exists_isInvertible_pullback_iso_of_isPicObstructionCocycle_of_forall_mem_range
p2m_attr_erase "instance" "PresheafOfModules.ExteriorPower.instModulePresheafAb AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensSubtypeForallMinMemAddSubgroupFamilies AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instModulePreGlue AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensSubtypeForallMinMemAddSubgroupFamilies PresheafOfModules.instMonoidalClosed PresheafOfModules.InternalHom.instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies PresheafOfModules.InternalHom.instModuleCarrierObjOppositeRingCatCompCommRingCatForget₂RingHomCarrierCarrierAbPresheaf PresheafOfModules.InternalHom.instSMulCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies AlgebraicGeometry.Scheme.PresheafOfModules.symmetricCategory SheafOfModules.instFaithfulRingSheafPModToPMod SheafOfModules.symmetricCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalClosed SheafOfModules.instFullRingSheafPModToPMod SheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.Modules.symmetricCategory SheafOfModules.monoidalClosed SheafOfModules.instIsLocalizationPModRingSheafSheafifyFunctorPresheafW SheafOfModules.sheafifyFunctor_monoidal AlgebraicGeometry.Scheme.Modules.monoidalClosed AlgebraicGeometry.instMonoidalPresheafOfModulesModulesSheafify AlgebraicGeometry.Scheme.Modules.monoidalCategory PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf_obj PresheafOfModules.exteriorPower_map_ιMulti PresheafOfModules.ExteriorPower.appₗ_apply AlgebraicGeometry.Scheme.Modules.exteriorPower_obj AlgebraicGeometry.Scheme.Modules.glueComponent_glueMk AlgebraicGeometry.Scheme.Modules.UnitCocycle.mk.injEq AlgebraicGeometry.Scheme.Modules.UnitCocycle.mk.sizeOf_spec AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left PresheafOfModules.InternalHom.presheaf_map_apply PresheafOfModules.InternalHom.curryFamily_app PresheafOfModules.InternalHom.add_app PresheafOfModules.InternalHom.smul_app PresheafOfModules.InternalHom.zero_app PresheafOfModules.ihomObj_map_val PresheafOfModules.ihomFunctor_map PresheafOfModules.InternalHom.restrict_app PresheafOfModules.InternalHom.postcomp_app PresheafOfModules.InternalHom.neg_app PresheafOfModules.curry'_app_val PresheafOfModules.InternalHom.presheaf_obj PresheafOfModules.ihomFunctor_obj PresheafOfModules.ihomObj_obj PresheafOfModules.InternalHom.sub_app PresheafOfModules.ihomMap_app_val SheafOfModules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_ofRelEffDivisor AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_I"
p2m_attr_erase "simp" "AlgebraicGeometry.mapOnProdOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.mk.sizeOf_spec AlgebraicGeometry.RelEffCartierDiv.mk.injEq AlgebraicGeometry.mapOnProdOver_snd AlgebraicGeometry.mapOnProdOver_fst AlgebraicGeometry.mapOnProdOver_snd_assoc AlgebraicGeometry.mapOnProdOver_id AlgebraicCurve.RelEffDivisor.mk.sizeOf_spec AlgebraicCurve.mapOnProd_fst AlgebraicCurve.mapOnProd_fst_assoc AlgebraicCurve.mapOnProd_snd AlgebraicCurve.UnivDivisorPack.mk.injEq AlgebraicCurve.RelEffDivisor.mk.injEq AlgebraicCurve.UnivDivisorPack.mk.sizeOf_spec AlgebraicCurve.mapOnProd_snd_assoc AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing AlgebraicGeometry.SmallExtension AlgebraicGeometry.Scheme.TwoAffineOpenCover Opposite TopologicalSpace"

universe u

namespace PV1P2

lemma presheaf_map_op_apply_eq {Y : Scheme.{u}} {U V : Y.Opens} (f g : U ⟶ V) (x : Y.presheaf.obj (op V)) :
    (Y.presheaf.map f.op).hom x = (Y.presheaf.map g.op).hom x := by
  rw [Subsingleton.elim f g]

lemma app_res {X Y : Scheme.{u}} (g : X ⟶ Y) {U V : Y.Opens} (h : V ≤ U) (x : Y.presheaf.obj (op U)) :
    (g.app V).hom ((Y.presheaf.map (homOfLE h).op).hom x) =
      (X.presheaf.map (homOfLE (g.preimage_mono h : g ⁻¹ᵁ V ≤ g ⁻¹ᵁ U)).op).hom ((g.app U).hom x) := by
  have e := congrArg (fun φ => φ.hom x) (Scheme.Hom.naturality g (U := V) (U' := U) (homOfLE h).op)
  simp only [CategoryTheory.comp_apply] at e
  exact e.trans (presheaf_map_op_apply_eq _ _ _)

lemma corr {R : Type*} [CommRing R] (A B C e0 e1 e2 : R)
    (hd0 : (A * B * C - 1) * e0 = 0) (hd1 : (A * B * C - 1) * e1 = 0) (hd2 : (A * B * C - 1) * e2 = 0)
    (h01 : e0 * e1 = 0) (h02 : e0 * e2 = 0) (h12 : e1 * e2 = 0) :
    A * (1 - e2) * (B * (1 - e0)) * (C * (1 + e1)) - 1 = (A * B * C - 1) + e1 + -e0 + -e2 := by
  linear_combination hd1 - hd0 - hd2 + (A * B * C) * h02 - (A * B * C) * h12 - (A * B * C) * h01 +
    (A * B * C * e2) * h01

theorem main
    {B₁ B₀ : Type u} [CommRing B₁] [IsLocalRing B₁] [CommRing B₀]
    (π : B₁ →+* B₀) (hπ : Function.Surjective π)
    (hsmall : RingHom.ker π * maximalIdeal B₁ = ⊥) (hI : RingHom.ker π ≤ maximalIdeal B₁)
    (V : Type u) [AddCommGroup V] [Module (ResidueField B₁) V] [Module.Finite (ResidueField B₁) V]
    [Module B₁ V] [IsScalarTower B₁ (ResidueField B₁) V]
    (ι : V →ₗ[B₁] B₁) (hι : Function.Injective ι)
    (hιI : LinearMap.range ι = Submodule.restrictScalars B₁ (RingHom.ker π))
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B₁)) [IsSeparated f] [Flat f]
    {X₀ : Scheme.{u}} (f₀ : X₀ ⟶ Spec (CommRingCat.of B₀)) (g : X₀ ⟶ X) [IsAffineHom g]
    (hg : IsPullback g f₀ f (Spec.map (CommRingCat.ofHom π)))
    {Xk : Scheme.{u}} (fk : Xk ⟶ Spec (CommRingCat.of (ResidueField B₁))) (i : Xk ⟶ X) [IsAffineHom i]
    (hi : IsPullback i fk f (Spec.map (CommRingCat.ofHom (residue B₁))))
    (𝒰 : X.OrderedAffineCover)
    (𝓛₀ : X₀.Modules)
    (c : Module.Dual (ResidueField B₁) V →ₗ[ResidueField B₁] (OModulePresheaf.unit fk).cochain (𝒰.comap i) 2)
    (hc : IsPicObstructionCocycle V ι f fk i g 𝒰 𝓛₀ c)
    (hcob : ∀ ξ : Module.Dual (ResidueField B₁) V,
      c ξ ∈ LinearMap.range ((OModulePresheaf.unit fk).d (𝒰.comap i) 1)) :
    ∃ 𝓛 : X.Modules, Scheme.Modules.IsInvertible 𝓛 ∧ Nonempty ((Scheme.Modules.pullback g).obj 𝓛 ≅ 𝓛₀) := by
  classical
  obtain ⟨τ₀, u, u', hu, huu', hδ⟩ := hc

  haveI hdiag : IsAffineHom (pullback.diagonal (terminal.from X)) := by
    have e : terminal.from X = f ≫ terminal.from _ := terminal.hom_ext _ _
    rw [e]; infer_instance
  have haff : ∀ {n : ℕ} (s : 𝒰.Idx n), IsAffineOpen (𝒰.inter s) := fun s =>
    IsAffineOpen.iInf fun j => 𝒰.isAffineOpen _

  have hJJ0 : RingHom.ker π * RingHom.ker π = ⊥ :=
    le_bot_iff.mp ((Ideal.mul_mono_right hI).trans hsmall.le)
  have hnil : IsNilpotent (RingHom.ker π) := ⟨2, by rw [pow_two]; exact hJJ0⟩
  have H2 := fun (U : X.Opens) (hU : IsAffineOpen U) =>
    AlgebraicGeometry.IsPullback.surjective_app_and_ker_app_eq_map_ker_of_isAffineOpen π hπ hnil f f₀ g hg U hU
  have hrange : (LinearMap.range ι : Ideal B₁) = RingHom.ker π := by
    rw [hιI]; exact Submodule.restrictScalars_self _

  have hJker : ∀ (U : X.Opens), IsAffineOpen U → ∀ x : Γ(X, U),
      (letI := algebraOfHom f U; x ∈ Ideal.map (algebraMap B₁ Γ(X, U)) (LinearMap.range ι)) →
      (g.app U).hom x = 0 := by
    intro U hU x hx
    letI := algebraOfHom f U
    rw [hrange, ← (H2 U hU).2] at hx
    exact hx
  have hker0 : ∀ (U : X.Opens), IsAffineOpen U → ∀ x y : Γ(X, U),
      (g.app U).hom x = 0 → (g.app U).hom y = 0 → x * y = 0 := by
    intro U hU x y hx hy
    letI := algebraOfHom f U
    have hx' : x ∈ (RingHom.ker π).map (algebraMap B₁ Γ(X, U)) := by rw [← (H2 U hU).2]; exact hx
    have hy' : y ∈ (RingHom.ker π).map (algebraMap B₁ Γ(X, U)) := by rw [← (H2 U hU).2]; exact hy
    have hxy := Ideal.mul_mem_mul hx' hy'
    rwa [← Ideal.map_mul, hJJ0, Ideal.map_bot, Ideal.mem_bot] at hxy

  have hread_ker : ∀ (U : X.Opens), IsAffineOpen U → ∀ (W : Xk.Opens) (hW : W ≤ i ⁻¹ᵁ U) (x : Γ(X, U))
      (w : Module.Dual (ResidueField B₁) V →ₗ[ResidueField B₁] (OModulePresheaf.unit fk).obj W),
      IsFibreReading V ι f fk i U W hW x w → (g.app U).hom x = 0 := by
    intro U hU W hW x w hx
    obtain ⟨n, v, s, hs, -⟩ := hx
    refine hJker U hU x ?_
    letI := algebraOfHom f U
    rw [← hs]
    refine Ideal.sum_mem _ fun j _ => Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ⟨v j, rfl⟩)

  obtain ⟨η, hη⟩ : ∃ η : Module.Dual (ResidueField B₁) V →ₗ[ResidueField B₁] (OModulePresheaf.unit fk).cochain (𝒰.comap i) 1,
      ∀ ξ, (OModulePresheaf.unit fk).d (𝒰.comap i) 1 (η ξ) = c ξ := by
    obtain ⟨η, hη⟩ := Module.projective_lifting_property
      ((OModulePresheaf.unit fk).d (𝒰.comap i) 1).rangeRestrict
      (c.codRestrict _ hcob) (LinearMap.surjective_rangeRestrict _)
    exact ⟨η, fun ξ => by simpa [Subtype.ext_iff] using congrArg (fun φ => (φ ξ : _)) hη⟩

  have hε : ∀ s : 𝒰.Idx 1, ∃ ε : Γ(X, 𝒰.inter s),
      (letI := algebraOfHom f (𝒰.inter s); ε ∈ Ideal.map (algebraMap B₁ Γ(X, 𝒰.inter s)) (LinearMap.range ι)) ∧
      IsFibreReading V ι f fk i (𝒰.inter s) ((𝒰.comap i).inter s) (𝒰.comap_inter_le i s) ε
        ((LinearMap.proj s).comp η) := fun s =>
    AlgebraicGeometry.SmallExtension.exists_mem_map_range_and_isFibreReading_of_isAffineOpen V ι f fk i hi
      (𝒰.inter s) (haff s) ((𝒰.comap i).inter s) (𝒰.comap_inter_le i s) (𝒰.le_comap_inter i s) _
  choose ε hεmem hεread using hε
  have hgε : ∀ s, (g.app (𝒰.inter s)).hom (ε s) = 0 := fun s => hJker _ (haff s) _ (hεmem s)

  let uc : ∀ s : 𝒰.Idx 1, Γ(X, 𝒰.inter s) := fun s => u s * (1 - ε s)
  let uc' : ∀ s : 𝒰.Idx 1, Γ(X, 𝒰.inter s) := fun s => u' s * (1 + ε s)
  have hucc : ∀ s, uc s * uc' s = 1 := by
    intro s
    have h2 := hker0 _ (haff s) _ _ (hgε s) (hgε s)
    show u s * (1 - ε s) * (u' s * (1 + ε s)) = 1
    linear_combination (u s * u' s) * (-h2) + huu' s

  have RC := fun (U : X.Opens) (W : Xk.Opens) (hW : W ≤ i ⁻¹ᵁ U) =>
    AlgebraicGeometry.SmallExtension.isFibreReading_zero_add_mul_neg_restrict_and_exists_isFibreReading
      V ι f fk i U W hW
  have hδc0 : ∀ r : 𝒰.Idx 2, (X.presheaf.map (homOfLE (𝒰.inter_le_inter_face r 2)).op).hom (uc (𝒰.face r 2)) * (X.presheaf.map (homOfLE (𝒰.inter_le_inter_face r 0)).op).hom (uc (𝒰.face r 0)) * (X.presheaf.map (homOfLE (𝒰.inter_le_inter_face r 1)).op).hom (uc' (𝒰.face r 1)) - 1 = 0 := by
    intro r
    have hgres : ∀ j : Fin 3, (g.app (𝒰.inter r)).hom ((X.presheaf.map (homOfLE (𝒰.inter_le_inter_face r j)).op).hom (ε (𝒰.face r j))) = 0 := by
      intro j; rw [app_res, hgε, map_zero]
    have hgδ : (g.app (𝒰.inter r)).hom ((X.presheaf.map (homOfLE (𝒰.inter_le_inter_face r 2)).op).hom (u (𝒰.face r 2)) * (X.presheaf.map (homOfLE (𝒰.inter_le_inter_face r 0)).op).hom (u (𝒰.face r 0)) * (X.presheaf.map (homOfLE (𝒰.inter_le_inter_face r 1)).op).hom (u' (𝒰.face r 1)) - 1) = 0 :=
      hread_ker _ (haff r) _ _ _ _ (hδ r)
    have hd0 := hker0 _ (haff r) _ _ hgδ (hgres 0)
    have hd1 := hker0 _ (haff r) _ _ hgδ (hgres 1)
    have hd2 := hker0 _ (haff r) _ _ hgδ (hgres 2)
    have h01 := hker0 _ (haff r) _ _ (hgres 0) (hgres 1)
    have h02 := hker0 _ (haff r) _ _ (hgres 0) (hgres 2)
    have h12 := hker0 _ (haff r) _ _ (hgres 1) (hgres 2)
    have key : (X.presheaf.map (homOfLE (𝒰.inter_le_inter_face r 2)).op).hom (uc (𝒰.face r 2)) * (X.presheaf.map (homOfLE (𝒰.inter_le_inter_face r 0)).op).hom (uc (𝒰.face r 0)) * (X.presheaf.map (homOfLE (𝒰.inter_le_inter_face r 1)).op).hom (uc' (𝒰.face r 1)) - 1 =
        ((X.presheaf.map (homOfLE (𝒰.inter_le_inter_face r 2)).op).hom (u (𝒰.face r 2)) * (X.presheaf.map (homOfLE (𝒰.inter_le_inter_face r 0)).op).hom (u (𝒰.face r 0)) * (X.presheaf.map (homOfLE (𝒰.inter_le_inter_face r 1)).op).hom (u' (𝒰.face r 1)) - 1) + (X.presheaf.map (homOfLE (𝒰.inter_le_inter_face r 1)).op).hom (ε (𝒰.face r 1)) + -(X.presheaf.map (homOfLE (𝒰.inter_le_inter_face r 0)).op).hom (ε (𝒰.face r 0)) + -(X.presheaf.map (homOfLE (𝒰.inter_le_inter_face r 2)).op).hom (ε (𝒰.face r 2)) := by
      simp only [uc, uc', map_mul, map_sub, map_add, map_one]
      exact corr _ _ _ _ _ _ hd0 hd1 hd2 h01 h02 h12
    rw [key]

    let Rm : Fin 3 → (Module.Dual (ResidueField B₁) V →ₗ[ResidueField B₁]
        (OModulePresheaf.unit fk).obj ((𝒰.comap i).inter r)) := fun j =>
      ((OModulePresheaf.unit fk).res ((𝒰.comap i).inter_le_inter_face r j)).comp
        ((LinearMap.proj (𝒰.face r j)).comp η)
    have Rj : ∀ j : Fin 3, IsFibreReading V ι f fk i (𝒰.inter r) ((𝒰.comap i).inter r) (𝒰.comap_inter_le i r)
        ((X.presheaf.map (homOfLE (𝒰.inter_le_inter_face r j)).op).hom (ε (𝒰.face r j))) (Rm j) := fun j =>
      (RC _ _ (𝒰.comap_inter_le i (𝒰.face r j))).2.2.2.2.1 _ _ _ _ (𝒰.inter_le_inter_face r j)
        ((𝒰.comap i).inter_le_inter_face r j) (𝒰.comap_inter_le i r) (hεread (𝒰.face r j))
    obtain ⟨-, hadd, -, hneg, -, -⟩ := RC (𝒰.inter r) ((𝒰.comap i).inter r) (𝒰.comap_inter_le i r)
    have Rtot := hadd _ _ _ _ (hadd _ _ _ _ (hadd _ _ _ _ (hδ r) (Rj 1)) (hneg _ _ (Rj 0))) (hneg _ _ (Rj 2))
    have hw0 : (LinearMap.proj r).comp c + Rm 1 + -Rm 0 + -Rm 2 = 0 := by
      apply LinearMap.ext
      intro ξ
      show c ξ r +
          (OModulePresheaf.unit fk).res ((𝒰.comap i).inter_le_inter_face r 1) (η ξ ((𝒰.comap i).face r 1)) +
          -((OModulePresheaf.unit fk).res ((𝒰.comap i).inter_le_inter_face r 0) (η ξ ((𝒰.comap i).face r 0))) +
          -((OModulePresheaf.unit fk).res ((𝒰.comap i).inter_le_inter_face r 2) (η ξ ((𝒰.comap i).face r 2))) = 0
      have e0 : ((-1 : ℤ) ^ ((0 : Fin 3) : ℕ)) = 1 := by norm_num
      have e1 : ((-1 : ℤ) ^ ((1 : Fin 3) : ℕ)) = -1 := by norm_num
      have e2 : ((-1 : ℤ) ^ ((2 : Fin 3) : ℕ)) = 1 := by norm_num
      have hd := congrFun (hη ξ) r
      rw [OModulePresheaf.d_apply, Fin.sum_univ_three, e0, e1, e2, one_zsmul, one_zsmul, neg_one_zsmul] at hd
      erw [← hd]
      abel
    rw [hw0] at Rtot
    exact AlgebraicGeometry.SmallExtension.IsFibreReading.eq_zero_of_isFibreReading_zero_of_flat V ι hι f fk i hi
      (𝒰.inter r) (haff r) ((𝒰.comap i).inter r) (𝒰.comap_inter_le i r) (𝒰.le_comap_inter i r) _ Rtot

  have hcoc : ∀ r : 𝒰.Idx 2, (X.presheaf.map (homOfLE (𝒰.inter_le_inter_face r 2)).op).hom (uc (𝒰.face r 2)) * (X.presheaf.map (homOfLE (𝒰.inter_le_inter_face r 0)).op).hom (uc (𝒰.face r 0)) = (X.presheaf.map (homOfLE (𝒰.inter_le_inter_face r 1)).op).hom (uc (𝒰.face r 1)) := by
    intro r
    have h1 : (X.presheaf.map (homOfLE (𝒰.inter_le_inter_face r 1)).op).hom (uc (𝒰.face r 1)) * (X.presheaf.map (homOfLE (𝒰.inter_le_inter_face r 1)).op).hom (uc' (𝒰.face r 1)) = 1 := by rw [← map_mul, hucc, map_one]
    have h := hδc0 r
    calc (X.presheaf.map (homOfLE (𝒰.inter_le_inter_face r 2)).op).hom (uc (𝒰.face r 2)) * (X.presheaf.map (homOfLE (𝒰.inter_le_inter_face r 0)).op).hom (uc (𝒰.face r 0)) = (X.presheaf.map (homOfLE (𝒰.inter_le_inter_face r 2)).op).hom (uc (𝒰.face r 2)) * (X.presheaf.map (homOfLE (𝒰.inter_le_inter_face r 0)).op).hom (uc (𝒰.face r 0)) * ((X.presheaf.map (homOfLE (𝒰.inter_le_inter_face r 1)).op).hom (uc (𝒰.face r 1)) * (X.presheaf.map (homOfLE (𝒰.inter_le_inter_face r 1)).op).hom (uc' (𝒰.face r 1))) := by rw [h1, mul_one]
      _ = ((X.presheaf.map (homOfLE (𝒰.inter_le_inter_face r 2)).op).hom (uc (𝒰.face r 2)) * (X.presheaf.map (homOfLE (𝒰.inter_le_inter_face r 0)).op).hom (uc (𝒰.face r 0)) * (X.presheaf.map (homOfLE (𝒰.inter_le_inter_face r 1)).op).hom (uc' (𝒰.face r 1)) - 1) * (X.presheaf.map (homOfLE (𝒰.inter_le_inter_face r 1)).op).hom (uc (𝒰.face r 1)) + (X.presheaf.map (homOfLE (𝒰.inter_le_inter_face r 1)).op).hom (uc (𝒰.face r 1)) := by ring
      _ = (X.presheaf.map (homOfLE (𝒰.inter_le_inter_face r 1)).op).hom (uc (𝒰.face r 1)) := by rw [h, zero_mul, zero_add]

  obtain ⟨𝓛, hinv, τL, hτL⟩ :=
    AlgebraicGeometry.Scheme.Modules.CechTrivialisation.exists_isInvertible_transition_eq 𝒰 uc uc' hucc hcoc
  refine ⟨𝓛, hinv, ?_⟩

  refine AlgebraicGeometry.Scheme.Modules.CechTrivialisation.nonempty_iso_of_transition_eq (𝒰.comap g)
    ((Scheme.Modules.pullback g).obj 𝓛) 𝓛₀ (τL.comap g) τ₀ fun s => ?_
  rw [AlgebraicGeometry.Scheme.Modules.CechTrivialisation.comap_transition g 𝒰 𝓛 τL s, hτL, ← hu s]
  congr 1
  show (g.app (𝒰.inter s)).hom (u s * (1 - ε s)) = (g.app (𝒰.inter s)).hom (u s)
  rw [map_mul, map_sub, map_one, hgε, sub_zero, mul_one]

end PV1P2

theorem solution
    {B₁ B₀ : Type u} [CommRing B₁] [IsLocalRing B₁] [CommRing B₀]
    (π : B₁ →+* B₀) (hπ : Function.Surjective π)
    (hsmall : RingHom.ker π * maximalIdeal B₁ = ⊥) (hI : RingHom.ker π ≤ maximalIdeal B₁)

    (V : Type u) [AddCommGroup V] [Module (ResidueField B₁) V] [Module.Finite (ResidueField B₁) V]
    [Module B₁ V] [IsScalarTower B₁ (ResidueField B₁) V]
    (ι : V →ₗ[B₁] B₁) (hι : Function.Injective ι)
    (hιI : LinearMap.range ι = Submodule.restrictScalars B₁ (RingHom.ker π))

    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B₁)) [IsSeparated f] [Flat f]
    {X₀ : Scheme.{u}} (f₀ : X₀ ⟶ Spec (CommRingCat.of B₀)) (g : X₀ ⟶ X) [IsAffineHom g]
    (hg : IsPullback g f₀ f (Spec.map (CommRingCat.ofHom π)))
    {Xk : Scheme.{u}} (fk : Xk ⟶ Spec (CommRingCat.of (ResidueField B₁))) (i : Xk ⟶ X) [IsAffineHom i]
    (hi : IsPullback i fk f (Spec.map (CommRingCat.ofHom (residue B₁))))
    (𝒰 : X.OrderedAffineCover)
    (𝓛₀ : X₀.Modules)
    (c : Module.Dual (ResidueField B₁) V →ₗ[ResidueField B₁] (OModulePresheaf.unit fk).cochain (𝒰.comap i) 2)
    (hc : IsPicObstructionCocycle V ι f fk i g 𝒰 𝓛₀ c)
    (hcob : ∀ ξ : Module.Dual (ResidueField B₁) V,
      c ξ ∈ LinearMap.range ((OModulePresheaf.unit fk).d (𝒰.comap i) 1)) :
    ∃ 𝓛 : X.Modules, Scheme.Modules.IsInvertible 𝓛 ∧ Nonempty ((Scheme.Modules.pullback g).obj 𝓛 ≅ 𝓛₀) :=
  PV1P2.main π hπ hsmall hI V ι hι hιI f f₀ g hg fk i hi 𝒰 𝓛₀ c hc hcob

end S_AlgebraicGeometry_SmallExtension_exists_isInvertible_pullback_iso_of_isPicObstructionCocycle_of_forall_mem_range
end P2MW
export P2MW.S_AlgebraicGeometry_SmallExtension_exists_isInvertible_pullback_iso_of_isPicObstructionCocycle_of_forall_mem_range (solution)
