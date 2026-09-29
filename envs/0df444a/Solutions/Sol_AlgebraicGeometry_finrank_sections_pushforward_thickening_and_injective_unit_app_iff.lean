-- Prove2me | solution 1 for AlgebraicGeometry.finrank_sections_pushforward_thickening_and_injective_unit_app_iff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/fc1998c0-1f64-56e2-b5a2-9afc47ea4de7

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicCurve_RelCartier
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isFinite_and_finrank_subschemeIota_ker_pow_of_comp_eq_id
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isInvertible_ker_of_comp_eq_id
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_invModule
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_pow
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_app_eq_of_exact_of_app_eq_zero
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_Hom_mono_iff_injective
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_epi_unit_app_tensor_invModule_pow_and_exists_shortExact
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_finrank_sections_pushforward_thickening_and_injective_unit_app_iff
p2m_attr_erase "instance" "AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd AlgebraicGeometry.isClosedImmersion_graphOver PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback SheafOfModules.isIso_ihomModelToIhom"
p2m_attr_erase "simp" "AlgebraicGeometry.prodKerGraph_one AlgebraicGeometry.fibrePowOver.proj_comp AlgebraicGeometry.prodKerGraph_zero AlgebraicGeometry.RelEffCartierDiv.empty_I AlgebraicGeometry.fibrePowOver.proj_comp_assoc AlgebraicGeometry.graphOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.toPoint_comp AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc AlgebraicGeometry.graphOver_fst AlgebraicGeometry.RelEffCartierDiv.ofPoint_I AlgebraicGeometry.graphOver_snd AlgebraicGeometry.graphOver_snd_assoc AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec AlgebraicCurve.SymmetricPowerPackage.mk.injEq PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply"

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry"

noncomputable section

namespace FibreKerAux

open TopologicalSpace Opposite

section Sheaf

universe v' u' w x

variable {C : Type u'} [Category.{v'} C] {FC : C → C → Type*} {CC : C → Type w}
variable [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC]
variable [HasLimitsOfSize.{x, x} C] [(forget C).ReflectsIsomorphisms]
variable [PreservesLimitsOfSize.{x, x} (forget C)]
variable {T : TopCat.{x}} (F : TopCat.Sheaf C T)

theorem sections_eq_of_eq_bot {W : Opens T} (h : W = ⊥) (s t : ToType (F.1.obj (op W))) :
    s = t :=
  F.eq_of_locally_eq' (fun i : Empty => i.elim) W (fun i => i.elim) (h.le.trans bot_le) s t
    (fun i => i.elim)

theorem bijective_pi_restrict {ι : Type*} (U : ι → Opens T) (W : Opens T) (hUW : ∀ i, U i ≤ W)
    (hW : W ≤ iSup U) (hdisj : ∀ i j, i ≠ j → U i ⊓ U j = ⊥) :
    Function.Bijective fun (s : ToType (F.1.obj (op W))) (i : ι) =>
      F.1.map (homOfLE (hUW i)).op s := by
  classical
  constructor
  · intro s t hst
    exact F.eq_of_locally_eq' U W (fun i => homOfLE (hUW i)) hW s t (fun i => congrFun hst i)
  · intro sf
    have hc : TopCat.Presheaf.IsCompatible F.1 U sf := by
      intro i j
      by_cases hij : i = j
      · subst hij
        exact congrArg (fun f : U i ⊓ U i ⟶ U i => F.1.map f.op (sf i)) (Subsingleton.elim _ _)
      · exact sections_eq_of_eq_bot F (hdisj i j hij) _ _
    obtain ⟨s, hs, -⟩ := F.existsUnique_gluing' U W (fun i => homOfLE (hUW i)) hW sf hc
    exact ⟨s, funext hs⟩

end Sheaf

theorem restrict_surjective_of_discrete {Z : Scheme.{u}} [DiscreteTopology Z] (N : Z.Modules)
    {W W' : Z.Opens} (h : W ≤ W') :
    Function.Surjective (N.presheaf.map (homOfLE h).op) := by
  intro a
  let W₂ : Z.Opens := ⟨(W' : Set Z) \ (W : Set Z), isOpen_discrete _⟩
  let U : Bool → Z.Opens := fun b => cond b W W₂
  have hUW : ∀ b, U b ≤ W' := by
    rintro (_ | _)
    · exact fun z hz => hz.1
    · exact h
  have hW : W' ≤ iSup U := by
    intro z hz
    by_cases hzW : z ∈ W
    · exact Opens.mem_iSup.2 ⟨true, hzW⟩
    · exact Opens.mem_iSup.2 ⟨false, ⟨hz, hzW⟩⟩
  have hdisj : ∀ b b', b ≠ b' → U b ⊓ U b' = ⊥ := by
    rintro (_ | _) (_ | _) hbb <;> simp only [ne_eq, not_true_eq_false] at hbb
    · rw [eq_bot_iff]; rintro z ⟨hz1, hz2⟩; exact (hz1.2 hz2).elim
    · rw [eq_bot_iff]; rintro z ⟨hz1, hz2⟩; exact (hz2.2 hz1).elim
  let F : TopCat.Sheaf Ab Z := ⟨N.presheaf, N.isSheaf⟩
  let sf : ∀ b, ToType (F.1.obj (op (U b))) := fun b =>
    match b with
    | true => a
    | false => (0 : Γ(N, W₂))
  obtain ⟨s, hs⟩ := (bijective_pi_restrict F U W' hUW hW hdisj).2 sf
  exact ⟨s, congrFun hs true⟩

theorem finite_and_discrete_of_finite {k : Type u} [Field k] {Z : Scheme.{u}} [IsAffine Z]
    (φ : k →+* Γ(Z, ⊤)) (hφ : φ.Finite) : Finite Z ∧ DiscreteTopology Z := by
  letI : Algebra k Γ(Z, ⊤) := φ.toAlgebra
  haveI : Module.Finite k Γ(Z, ⊤) := hφ
  haveI : IsArtinianRing Γ(Z, ⊤) := IsArtinianRing.of_finite k Γ(Z, ⊤)
  let e : Z ≃ₜ PrimeSpectrum Γ(Z, ⊤) := Scheme.homeoOfIso Z.isoSpec
  exact ⟨Finite.of_equiv _ e.symm.toEquiv, e.discreteTopology_iff.2 inferInstance⟩

section PiDecomp

variable {k : Type u} [Field k] {Z : Scheme.{u}}

abbrev modK (M : Z.Modules) (W : Z.Opens) (ψ : k →+* Γ(Z, W)) : Module k Γ(M, W) :=
  Module.compHom Γ(M, W) ψ

def resHom (ψ₀ : k →+* Γ(Z, ⊤)) (W : Z.Opens) : k →+* Γ(Z, W) :=
  (Z.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op).hom.comp ψ₀

theorem resHom_apply (ψ₀ : k →+* Γ(Z, ⊤)) (W : Z.Opens) (r : k) :
    resHom ψ₀ W r = (Z.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op).hom (ψ₀ r) := rfl

def restrictₖ (M : Z.Modules) (ψ₀ : k →+* Γ(Z, ⊤)) (W : Z.Opens) :
    letI := modK M ⊤ ψ₀; letI := modK M W (resHom ψ₀ W)
    Γ(M, ⊤) →ₗ[k] Γ(M, W) :=
  letI := modK M ⊤ ψ₀; letI := modK M W (resHom ψ₀ W)
  { toFun := fun s => M.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op s
    map_add' := fun a b => map_add _ a b
    map_smul' := fun r s => by
      show M.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op (ψ₀ r • s)
        = resHom ψ₀ W r • M.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op s
      rw [Scheme.Modules.map_smul]
      rfl }

theorem restrictₖ_apply (M : Z.Modules) (ψ₀ : k →+* Γ(Z, ⊤)) (W : Z.Opens) (s : Γ(M, ⊤)) :
    restrictₖ M ψ₀ W s = M.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op s := rfl

def piEquiv (M : Z.Modules) (ψ₀ : k →+* Γ(Z, ⊤)) {ι : Type u} (U : ι → Z.Opens)
    (hcov : (⊤ : Z.Opens) ≤ iSup U) (hdisj : ∀ a b, a ≠ b → U a ⊓ U b = ⊥) :
    letI := modK M ⊤ ψ₀; letI := fun a => modK M (U a) (resHom ψ₀ (U a))
    Γ(M, ⊤) ≃ₗ[k] (∀ a, Γ(M, U a)) :=
  letI := modK M ⊤ ψ₀; letI := fun a => modK M (U a) (resHom ψ₀ (U a))
  LinearEquiv.ofBijective (LinearMap.pi fun a => restrictₖ M ψ₀ (U a))
    (bijective_pi_restrict (⟨M.presheaf, M.isSheaf⟩ : TopCat.Sheaf Ab Z) U ⊤ (fun _ => le_top)
      hcov hdisj)

end PiDecomp

theorem exists_addEquiv_of_trivial {Z : Scheme.{u}} (M : Z.Modules) (V : Z.Opens)
    (e : (Scheme.Modules.pullback V.ι).obj M ≅ SheafOfModules.unit V.toScheme.ringCatSheaf)
    (W : V.toScheme.Opens) :
    ∃ τ : Γ(M, V.ι ''ᵁ W) ≃+ Γ((SheafOfModules.unit Z.ringCatSheaf : Z.Modules), V.ι ''ᵁ W),
      ∀ (c : Γ(Z, V.ι ''ᵁ W)) (m : Γ(M, V.ι ''ᵁ W)), τ (c • m) = c • τ m := by
  let θ : M.restrict V.ι ⟶ SheafOfModules.unit V.toScheme.ringCatSheaf :=
    ((Scheme.Modules.restrictFunctorIsoPullback V.ι).app M).hom ≫ e.hom
  let τ₀ := Scheme.Modules.Hom.app θ W
  haveI : IsIso τ₀ := inferInstance
  let τ : Γ(M, V.ι ''ᵁ W) ≃+ Γ((SheafOfModules.unit Z.ringCatSheaf : Z.Modules), V.ι ''ᵁ W) :=
    AddEquiv.ofBijective
      (show Γ(M, V.ι ''ᵁ W) →+ Γ((SheafOfModules.unit Z.ringCatSheaf : Z.Modules), V.ι ''ᵁ W)
        from τ₀.hom)
      (ConcreteCategory.bijective_of_isIso τ₀)
  refine ⟨τ, fun c m => ?_⟩
  have key := Scheme.Modules.Hom.app_smul θ (show Γ(V.toScheme, W) from c)
    (show Γ(M.restrict V.ι, W) from m)
  have hβ : (V.ι.appIso W).inv.hom c = c := by
    rw [Scheme.Opens.ι_appIso]
    rfl
  calc τ (c • m) = τ₀.hom ((V.ι.appIso W).inv.hom c • m) := by rw [hβ]; rfl
    _ = _ := key

theorem finite_and_finrank_sections_pushforward
    {k : Type u} [Field k] {Z X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k))
    (i : Z ⟶ X) (hZ : IsFinite (i ≫ x))
    (N : Z.Modules) (hN : Scheme.Modules.IsInvertible N) (t : Spec (CommRingCat.of k)) :
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom x
      ((Scheme.Modules.pushforward i).obj N) ⊤
    Module.Finite k Γ((Scheme.Modules.pushforward i).obj N, ⊤) ∧
      Module.finrank k Γ((Scheme.Modules.pushforward i).obj N, ⊤) = (i ≫ x).finrank t := by
  classical
  haveI := hZ
  obtain ⟨hZaff, hfinTop⟩ := (HasAffineProperty.iff_of_isAffine (P := @IsFinite)).mp hZ
  haveI : IsAffine Z := hZaff

  let φ : CommRingCat.of k ⟶ Γ(Z, ⊤) := (Scheme.ΓSpecIso (.of k)).inv ≫ (i ≫ x).appTop
  have hφfin : φ.hom.Finite :=
    RingHom.Finite.comp hfinTop
      (RingHom.Finite.of_surjective _
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of k)).inv).surjective)
  have hφflat : φ.hom.Flat := by
    letI := φ.hom.toAlgebra
    exact (inferInstance : Module.Flat k Γ(Z, ⊤))
  obtain ⟨hZfin, hZdisc⟩ := finite_and_discrete_of_finite φ.hom hφfin

  let P : X.Modules := (Scheme.Modules.pushforward i).obj N

  have hdeg : (i ≫ x).finrank t = (letI := φ.hom.toAlgebra; Module.finrank k Γ(Z, ⊤)) := by
    have hfac : i ≫ x = Z.isoSpec.hom ≫ Spec.map φ := by
      rw [Spec.map_comp, ← Scheme.isoSpec_Spec_inv, Scheme.isoSpec_hom_naturality_assoc,
        Iso.hom_inv_id, Category.comp_id]
    haveI : IsFinite (Spec.map φ) := (IsFinite.SpecMap_iff φ).2 hφfin
    haveI : Flat (Spec.map φ) := Flat.SpecMap_iff.2 hφflat
    rw [hfac, Scheme.Hom.finrank_comp_left_of_isIso, Scheme.Hom.finrank_SpecMap_eq_finrank hφfin hφflat]
    letI := φ.hom.toAlgebra
    simp only [RingHom.finrank, Module.rankAtStalk_eq_finrank_of_free]
    rfl

  let ψ₀ : k →+* Γ(Z, ⊤) := by
    letI := Scheme.TwoAffineOpenCover.algebraOfHom x ⊤
    exact (i.app ⊤).hom.comp (algebraMap k Γ(X, ⊤))
  have hψ₀ : ψ₀ = φ.hom := by
    refine RingHom.ext fun r => ?_
    change (i.app ⊤).hom ((x.appLE ⊤ ⊤ le_top).hom ((Scheme.ΓSpecIso (.of k)).inv.hom r)) =
      ((i ≫ x).appTop).hom ((Scheme.ΓSpecIso (.of k)).inv.hom r)
    have h1 : x.appLE ⊤ ⊤ le_top = x.appTop := (Scheme.Hom.app_eq_appLE x).symm
    rw [h1, Scheme.Hom.comp_appTop]
    rfl

  haveI : Fintype Z := Fintype.ofFinite Z
  choose V hzV eV using hN.exists_trivialization
  let pt : Z → Z.Opens := fun z => ⟨{z}, isOpen_discrete _⟩
  let Wz : ∀ z : Z, (V z).toScheme.Opens := fun z => (V z).ι ⁻¹ᵁ (pt z)
  let U : Z → Z.Opens := fun z => (V z).ι ''ᵁ (Wz z)
  have hU : ∀ z, (U z : Set Z) = {z} := by
    intro z
    have h := (V z).ι.image_preimage_eq_opensRange_inf (pt z)
    rw [Scheme.Opens.opensRange_ι] at h
    have h' := congrArg (fun W : Z.Opens => (W : Set Z)) h
    simp only [TopologicalSpace.Opens.coe_inf] at h'
    refine h'.trans ?_
    exact Set.inter_eq_right.2 (Set.singleton_subset_iff.2 (hzV z))
  have hzU : ∀ z, z ∈ U z := fun z => by
    show z ∈ (U z : Set Z)
    rw [hU]
    exact Set.mem_singleton z
  have hcov : (⊤ : Z.Opens) ≤ iSup U := fun z _ => TopologicalSpace.Opens.mem_iSup.2 ⟨z, hzU z⟩
  have hdisj : ∀ a b, a ≠ b → U a ⊓ U b = ⊥ := by
    intro a b hab
    apply TopologicalSpace.Opens.ext
    simp only [TopologicalSpace.Opens.coe_inf, TopologicalSpace.Opens.coe_bot, hU]
    exact Set.singleton_inter_eq_empty.2 (by simpa using hab)

  let O : Z.Modules := SheafOfModules.unit Z.ringCatSheaf
  letI instN : Module k Γ(N, ⊤) := modK N ⊤ ψ₀
  letI instO : Module k Γ(O, ⊤) := modK O ⊤ ψ₀
  letI instNz : ∀ z, Module k Γ(N, U z) := fun z => modK N (U z) (resHom ψ₀ (U z))
  letI instOz : ∀ z, Module k Γ(O, U z) := fun z => modK O (U z) (resHom ψ₀ (U z))
  let eN := piEquiv N ψ₀ U hcov hdisj
  let eO := piEquiv O ψ₀ U hcov hdisj

  have eτ : ∀ z, Nonempty (Γ(N, U z) ≃ₗ[k] Γ(O, U z)) := by
    intro z
    obtain ⟨τ, hτ⟩ := exists_addEquiv_of_trivial N (V z) (eV z).some (Wz z)
    exact ⟨τ.toLinearEquiv fun r m => hτ (resHom ψ₀ (U z) r) m⟩

  letI : Algebra k Γ(Z, ⊤) := φ.hom.toAlgebra
  haveI : Module.Finite k Γ(Z, ⊤) := hφfin
  let ι₀ : Γ(O, ⊤) ≃ₗ[k] Γ(Z, ⊤) :=
    { toFun := fun s => show Γ(Z, ⊤) from s
      invFun := fun s => show Γ(O, ⊤) from s
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun r s => by
        show ψ₀ r * (show Γ(Z, ⊤) from s) = φ.hom r * (show Γ(Z, ⊤) from s)
        rw [hψ₀] }
  haveI : Module.Finite k Γ(O, ⊤) := Module.Finite.equiv ι₀.symm
  haveI hOz : ∀ z, Module.Finite k Γ(O, U z) := fun z =>
    Module.Finite.of_surjective
      ((LinearMap.proj z : (∀ a, Γ(O, U a)) →ₗ[k] Γ(O, U z)).comp eO.toLinearMap)
      ((Function.surjective_eval z).comp eO.surjective)
  haveI hNz : ∀ z, Module.Finite k Γ(N, U z) := fun z => Module.Finite.equiv (eτ z).some.symm
  haveI hNfin : Module.Finite k Γ(N, ⊤) := Module.Finite.equiv eN.symm
  have hrank : Module.finrank k Γ(N, ⊤) = Module.finrank k Γ(Z, ⊤) := by
    rw [eN.finrank_eq, ← ι₀.finrank_eq, eO.finrank_eq, Module.finrank_pi_fintype,
      Module.finrank_pi_fintype]
    exact Finset.sum_congr rfl fun z _ => (eτ z).some.finrank_eq

  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom x P ⊤
  haveI hfinP : Module.Finite k Γ(P, ⊤) := hNfin
  refine ⟨hfinP, ?_⟩
  rw [hdeg]
  exact hrank

end FibreKerAux

end

open FibreKerAux in

theorem solution
    {K : Type u} [Field K] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of K))
    [IsSeparated x] [SmoothOfRelativeDimension 1 x]
    (σ : Spec (CommRingCat.of K) ⟶ X) (hσ : σ ≫ x = 𝟙 _)
    (L : X.Modules) (hL : Scheme.Modules.IsInvertible L) (r n d : ℕ) (hd : d + n = r) :
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom x
      ((Scheme.Modules.pushforward ((σ.ker ^ n).subschemeι)).obj
        ((Scheme.Modules.pullback ((σ.ker ^ n).subschemeι)).obj (L ⊗ (σ.ker ^ r).invModule))) ⊤
    (Module.Finite K Γ((Scheme.Modules.pushforward ((σ.ker ^ n).subschemeι)).obj
          ((Scheme.Modules.pullback ((σ.ker ^ n).subschemeι)).obj (L ⊗ (σ.ker ^ r).invModule)), ⊤) ∧
      Module.finrank K Γ((Scheme.Modules.pushforward ((σ.ker ^ n).subschemeι)).obj
          ((Scheme.Modules.pullback ((σ.ker ^ n).subschemeι)).obj (L ⊗ (σ.ker ^ r).invModule)), ⊤) = n) ∧
    (Function.Injective (((Scheme.Modules.pullbackPushforwardAdjunction ((σ.ker ^ n).subschemeι)).unit.app
          (L ⊗ (σ.ker ^ r).invModule)).app ⊤) ↔
        Subsingleton Γ(L ⊗ (σ.ker ^ d).invModule, ⊤)) := by
  classical
  obtain ⟨hZ, hdegn, -, -⟩ :=
    Scheme.Hom.isFinite_and_finrank_subschemeIota_ker_pow_of_comp_eq_id (p := x) σ hσ n
  have h𝓘 : σ.ker.IsInvertible := Scheme.Hom.isInvertible_ker_of_comp_eq_id σ hσ
  have hG : Scheme.Modules.IsInvertible (L ⊗ (σ.ker ^ r).invModule) :=
    hL.tensor (Scheme.IdealSheafData.IsInvertible.isInvertible_invModule (h𝓘.pow r))
  have hN : Scheme.Modules.IsInvertible
      ((Scheme.Modules.pullback ((σ.ker ^ n).subschemeι)).obj (L ⊗ (σ.ker ^ r).invModule)) :=
    hG.pullback _
  obtain ⟨hfin, hrk⟩ := finite_and_finrank_sections_pushforward x ((σ.ker ^ n).subschemeι) hZ _ hN
    (IsLocalRing.closedPoint K)
  refine ⟨⟨hfin, hrk.trans (hdegn _)⟩, ?_⟩

  obtain ⟨-, ι, w, hSE⟩ :=
    Scheme.IdealSheafData.IsInvertible.epi_unit_app_tensor_invModule_pow_and_exists_shortExact
      σ.ker h𝓘 L hL r n d hd
  haveI := hSE.mono_f
  have hιinj : Function.Injective (ι.app ⊤) :=
    (Scheme.Modules.Hom.mono_iff_injective ι).1 hSE.mono_f ⊤
  have hcomp : ∀ c, ((Scheme.Modules.pullbackPushforwardAdjunction ((σ.ker ^ n).subschemeι)).unit.app
      (L ⊗ (σ.ker ^ r).invModule)).app ⊤ (ι.app ⊤ c) = 0 := fun c => by
    show (ι ≫ (Scheme.Modules.pullbackPushforwardAdjunction ((σ.ker ^ n).subschemeι)).unit.app
      (L ⊗ (σ.ker ^ r).invModule)).app ⊤ c = 0
    rw [w, Scheme.Modules.Hom.zero_app]
    first
    | rfl
    | simp
  constructor
  · intro hinj
    refine ⟨fun a b => hιinj (hinj ?_)⟩
    rw [hcomp, hcomp]
  · intro hsub a b hab
    have h0 : ((Scheme.Modules.pullbackPushforwardAdjunction ((σ.ker ^ n).subschemeι)).unit.app
        (L ⊗ (σ.ker ^ r).invModule)).app ⊤ (a - b) = 0 := by
      rw [map_sub, hab, sub_self]
    obtain ⟨e, he⟩ := Scheme.Modules.exists_app_eq_of_exact_of_app_eq_zero
      (ShortComplex.mk ι _ w) hSE.exact ⊤ (a - b) h0
    haveI : Subsingleton Γ((ShortComplex.mk ι _ w).X₁, ⊤) := hsub
    have he0 : e = 0 := Subsingleton.elim _ _
    rw [he0, map_zero] at he
    exact sub_eq_zero.1 he.symm

end S_AlgebraicGeometry_finrank_sections_pushforward_thickening_and_injective_unit_app_iff
end P2MW
export P2MW.S_AlgebraicGeometry_finrank_sections_pushforward_thickening_and_injective_unit_app_iff (solution)
