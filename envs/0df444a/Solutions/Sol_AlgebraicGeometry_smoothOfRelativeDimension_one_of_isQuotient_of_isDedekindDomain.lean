-- Prove2me | solution 1 for AlgebraicGeometry.smoothOfRelativeDimension_one_of_isQuotient_of_isDedekindDomain
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/0b43eb96-3c98-50ee-a17a-c0ec7d807402

import Mathlib
import Theorems.Thm_AlgebraicGeometry_smoothOfRelativeDimension_one_SpecMap_of_isInvariant_of_isDedekindDomain
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_smoothOfRelativeDimension_one_of_isQuotient_of_isDedekindDomain
p2m_attr_erase "instance" "TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AdicCompletion.instIsLocalRingMaximalIdeal"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AdicCompletion.map_smul_of AdicCompletion.algebraMap_of AdicCompletion.stabilizer_smul_of AdicCompletion.evalₐ_mapₐ AdicCompletion.mapAlgEquivOfBijective_apply AdicCompletion.levelMapₐ_mk AdicCompletion.mapₐ_of AdicCompletion.mapAlgEquiv_symm_apply AdicCompletion.mapAlgEquiv_apply AdicCompletion.evalₐ_ofLevelwiseEquiv AdicCompletion.evalₐ_levelwiseHom AdicCompletion.localizationEquiv_of AdicCompletion.evalₐ_ofLevelwiseEquiv_symm Localization.AtPrime.quotientPowEquiv_mk AdicCompletion.tensorRingEquiv_tmul AdicCompletion.completionOfAlgHom_apply AdicCompletion.completionBaseChangeHom_of AdicCompletion.tensorRingHom_tmul"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace WildQuotSmooth21

section SecMap

variable {M X : Scheme.{0}} (π : M ⟶ X) (V : X.Opens)

theorem le_preimage_of_comp_eq {f : M ⟶ M} (hf : f ≫ π = π) : π ⁻¹ᵁ V ≤ f ⁻¹ᵁ (π ⁻¹ᵁ V) := by
  rw [← Scheme.Hom.comp_preimage, hf]

noncomputable def secMap (f : M ⟶ M) (hf : f ≫ π = π) : Γ(M, π ⁻¹ᵁ V) →+* Γ(M, π ⁻¹ᵁ V) :=
  (f.appLE (π ⁻¹ᵁ V) (π ⁻¹ᵁ V) (le_preimage_of_comp_eq π V hf)).hom

theorem secMap_apply (f : M ⟶ M) (hf : f ≫ π = π) (a : Γ(M, π ⁻¹ᵁ V)) :
    secMap π V f hf a = f.appLE (π ⁻¹ᵁ V) (π ⁻¹ᵁ V) (le_preimage_of_comp_eq π V hf) a := rfl

theorem secMap_congr {f g : M ⟶ M} (h : f = g) (hf : f ≫ π = π) (hg : g ≫ π = π) :
    secMap π V f hf = secMap π V g hg := by
  subst h; rfl

theorem appLE_id_self (U : M.Opens) (e : U ≤ (𝟙 M) ⁻¹ᵁ U) : (𝟙 M :).appLE U U e = 𝟙 _ := by
  rw [Scheme.Hom.appLE, Scheme.Hom.id_app]
  have h0 : (homOfLE e).op = 𝟙 (Opposite.op U) := Subsingleton.elim _ _
  rw [h0]
  erw [CategoryTheory.Functor.map_id]
  exact Category.comp_id _

theorem secMap_id (h : 𝟙 M ≫ π = π) : secMap π V (𝟙 M) h = RingHom.id _ := by
  apply RingHom.ext
  intro a
  rw [secMap_apply, appLE_id_self]
  rfl

theorem secMap_comp (f g : M ⟶ M) (hf : f ≫ π = π) (hg : g ≫ π = π) (hfg : (f ≫ g) ≫ π = π) :
    secMap π V (f ≫ g) hfg = (secMap π V f hf).comp (secMap π V g hg) := by
  have hc := Scheme.Hom.appLE_comp_appLE f g (π ⁻¹ᵁ V) (π ⁻¹ᵁ V) (π ⁻¹ᵁ V)
    (le_preimage_of_comp_eq π V hg) (le_preimage_of_comp_eq π V hf)
  apply RingHom.ext
  intro a
  change ((f ≫ g).appLE _ _ _) a = (f.appLE _ _ _) ((g.appLE _ _ _) a)
  rw [← hc]
  rfl

theorem secMap_appLE (f : M ⟶ M) (hf : f ≫ π = π) (s : Γ(X, V)) :
    secMap π V f hf (π.appLE V (π ⁻¹ᵁ V) le_rfl s) = π.appLE V (π ⁻¹ᵁ V) le_rfl s := by
  have h1 := Scheme.Hom.appLE_comp_appLE f π V (π ⁻¹ᵁ V) (π ⁻¹ᵁ V) le_rfl (le_preimage_of_comp_eq π V hf)
  have h2 : ∀ (k : M ⟶ X) (hk : k = π) (p : π ⁻¹ᵁ V ≤ k ⁻¹ᵁ V),
      k.appLE V (π ⁻¹ᵁ V) p = π.appLE V (π ⁻¹ᵁ V) le_rfl := by
    intro k hk p; subst hk; rfl
  have h3 : π.appLE V (π ⁻¹ᵁ V) le_rfl ≫ f.appLE _ _ (le_preimage_of_comp_eq π V hf) =
      π.appLE V (π ⁻¹ᵁ V) le_rfl := by
    rw [h1]; exact h2 _ hf _
  change (π.appLE V (π ⁻¹ᵁ V) le_rfl ≫ f.appLE _ _ (le_preimage_of_comp_eq π V hf)) s = _
  rw [h3]

end SecMap

section AffineSmooth

variable {R : CommRingCat.{0}} {Y : Scheme.{0}} (q : Y ⟶ Spec R) (U : Y.Opens)

theorem le_preimage_top : U ≤ q ⁻¹ᵁ ⊤ := le_top

theorem smooth_SpecMap_appLE_iff (hU : IsAffineOpen U) :
    SmoothOfRelativeDimension 1 (Spec.map (q.appLE ⊤ U (le_preimage_top q U))) ↔
      SmoothOfRelativeDimension 1 (U.ι ≫ q) := by
  have htop := isAffineOpen_top (Spec R)
  have e := IsAffineOpen.SpecMap_appLE_fromSpec q htop hU (le_preimage_top q U)
  haveI : IsIso htop.fromSpec := by rw [IsAffineOpen.fromSpec_top]; infer_instance
  rw [← MorphismProperty.cancel_right_of_respectsIso (@SmoothOfRelativeDimension 1) _ htop.fromSpec, e,
    ← IsAffineOpen.isoSpec_inv_ι, Category.assoc,
    MorphismProperty.cancel_left_of_respectsIso (@SmoothOfRelativeDimension 1)]

end AffineSmooth

section BaseIso

variable {B : Type} [CommRing B] {R' : CommRingCat.{0}} (f : Γ(Spec (CommRingCat.of B), ⊤) ⟶ R')

theorem smooth_SpecMap_comp_ΓSpecIso_inv_iff :
    SmoothOfRelativeDimension 1 (Spec.map ((Scheme.ΓSpecIso (CommRingCat.of B)).inv ≫ f)) ↔
      SmoothOfRelativeDimension 1 (Spec.map f) := by
  rw [Spec.map_comp, MorphismProperty.cancel_right_of_respectsIso (@SmoothOfRelativeDimension 1)]

end BaseIso

theorem affine_step
    {B : Type} [CommRing B] [IsDedekindDomain B]
    {M X : Scheme.{0}}
    (G : Type) [Group G] [Fintype G] (ρ : G →* Aut M)
    (hW : ∀ 𝔭 : Ideal B, 𝔭.IsMaximal →
      ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W)
        (_ : IsAdicComplete (IsLocalRing.maximalIdeal W) W) (_ : IsAlgClosed (IsLocalRing.ResidueField W))
        (_ : Algebra B W), Module.Flat B W ∧ (IsLocalRing.maximalIdeal W).comap (algebraMap B W) = 𝔭)
    (π : M ⟶ X) (πX : X ⟶ Spec (CommRingCat.of B)) [SmoothOfRelativeDimension 1 (π ≫ πX)]
    (hπ : ∀ g : G, (ρ g).hom ≫ π = π) [IsAffineHom π]
    (hsec_inj : ∀ V : X.Opens, Function.Injective (π.app V))
    (hsec : ∀ V : X.Opens, Set.range (π.app V) =
        {s | ∀ g : G, (ρ g).hom.appLE (π ⁻¹ᵁ V) (π ⁻¹ᵁ V)
          (by rw [← Scheme.Hom.comp_preimage, hπ g]) s = s})
    (V : X.Opens) (hV : IsAffineOpen V) :
    SmoothOfRelativeDimension 1 (V.ι ≫ πX) := by
  classical
  have hUaff : IsAffineOpen (π ⁻¹ᵁ V) := hV.preimage π

  let ι₀ : CommRingCat.of B ⟶ Γ(Spec (CommRingCat.of B), ⊤) := (Scheme.ΓSpecIso (CommRingCat.of B)).inv
  let φS : Γ(Spec (CommRingCat.of B), ⊤) ⟶ Γ(X, V) := πX.appLE ⊤ V (le_preimage_top πX V)
  let ψ : Γ(X, V) ⟶ Γ(M, π ⁻¹ᵁ V) := π.appLE V (π ⁻¹ᵁ V) le_rfl
  have hψ : ψ = π.app V := Scheme.Hom.appLE_eq_app π
  letI algBS : Algebra B Γ(X, V) := (ι₀ ≫ φS).hom.toAlgebra
  letI algSA : Algebra Γ(X, V) Γ(M, π ⁻¹ᵁ V) := ψ.hom.toAlgebra
  letI algBA : Algebra B Γ(M, π ⁻¹ᵁ V) := (ι₀ ≫ φS ≫ ψ).hom.toAlgebra
  haveI : IsScalarTower B Γ(X, V) Γ(M, π ⁻¹ᵁ V) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl

  letI act : MulSemiringAction G Γ(M, π ⁻¹ᵁ V) :=
    { smul := fun g a => secMap π V (ρ g⁻¹).hom (hπ g⁻¹) a
      one_smul := fun a => by
        change secMap π V (ρ 1⁻¹).hom (hπ 1⁻¹) a = a
        rw [secMap_congr π V (show (ρ 1⁻¹).hom = 𝟙 M by rw [inv_one, map_one]; rfl) (hπ 1⁻¹)
          (Category.id_comp π), secMap_id]
        rfl
      mul_smul := fun g h a => by
        change secMap π V (ρ (g * h)⁻¹).hom (hπ (g * h)⁻¹) a =
          secMap π V (ρ g⁻¹).hom (hπ g⁻¹) (secMap π V (ρ h⁻¹).hom (hπ h⁻¹) a)
        have hcomp : ((ρ g⁻¹).hom ≫ (ρ h⁻¹).hom) ≫ π = π := by rw [Category.assoc, hπ, hπ]
        rw [secMap_congr π V (show (ρ (g * h)⁻¹).hom = (ρ g⁻¹).hom ≫ (ρ h⁻¹).hom by
          rw [mul_inv_rev, map_mul, Aut.Aut_mul_def]; rfl) (hπ (g * h)⁻¹) hcomp,
          secMap_comp π V _ _ (hπ g⁻¹) (hπ h⁻¹) hcomp]
        rfl
      smul_zero := fun g => map_zero _
      smul_add := fun g => map_add _
      smul_one := fun g => map_one _
      smul_mul := fun g => map_mul _ }
  have hsmul : ∀ (g : G) (a : Γ(M, π ⁻¹ᵁ V)), g • a = secMap π V (ρ g⁻¹).hom (hπ g⁻¹) a := fun _ _ => rfl

  have hfixS : ∀ (g : G) (s : Γ(X, V)), g • algebraMap Γ(X, V) Γ(M, π ⁻¹ᵁ V) s = algebraMap _ _ s :=
    fun g s => secMap_appLE π V _ _ s
  haveI : SMulCommClass G Γ(X, V) Γ(M, π ⁻¹ᵁ V) :=
    ⟨fun g s a => by rw [Algebra.smul_def, Algebra.smul_def, smul_mul', hfixS]⟩
  haveI : SMulCommClass G B Γ(M, π ⁻¹ᵁ V) :=
    ⟨fun g b a => by
      rw [Algebra.smul_def, Algebra.smul_def, smul_mul', IsScalarTower.algebraMap_apply _ Γ(X, V), hfixS]⟩
  haveI : FaithfulSMul Γ(X, V) Γ(M, π ⁻¹ᵁ V) := by
    rw [faithfulSMul_iff_algebraMap_injective]
    change Function.Injective ψ.hom
    rw [hψ]; exact hsec_inj V
  haveI : Algebra.IsInvariant Γ(X, V) Γ(M, π ⁻¹ᵁ V) G := by
    refine ⟨fun a ha => ?_⟩
    have ha' : a ∈ Set.range (π.app V) := by
      rw [hsec V]
      intro g
      have h := ha g⁻¹
      rw [hsmul, secMap_congr π V (show (ρ g⁻¹⁻¹).hom = (ρ g).hom by rw [inv_inv]) _ (hπ g)] at h
      exact h
    obtain ⟨s, hs⟩ := ha'
    exact ⟨s, by rw [← hs, ← hψ]; rfl⟩

  haveI : SmoothOfRelativeDimension 1 ((π ⁻¹ᵁ V).ι ≫ π ≫ πX) :=
    inferInstanceAs (SmoothOfRelativeDimension (0 + 1) ((π ⁻¹ᵁ V).ι ≫ π ≫ πX))
  haveI : SmoothOfRelativeDimension 1 (Spec.map (CommRingCat.ofHom (algebraMap B Γ(M, π ⁻¹ᵁ V)))) := by
    have hc : CommRingCat.ofHom (algebraMap B Γ(M, π ⁻¹ᵁ V)) =
        ι₀ ≫ (π ≫ πX).appLE ⊤ (π ⁻¹ᵁ V) (le_preimage_top (π ≫ πX) (π ⁻¹ᵁ V)) := by
      rw [← Scheme.Hom.appLE_comp_appLE π πX ⊤ V (π ⁻¹ᵁ V) (le_preimage_top πX V) le_rfl]; rfl
    rw [hc, smooth_SpecMap_comp_ΓSpecIso_inv_iff]
    exact (smooth_SpecMap_appLE_iff (π ≫ πX) (π ⁻¹ᵁ V) hUaff).mpr inferInstance

  have key := AlgebraicGeometry.smoothOfRelativeDimension_one_SpecMap_of_isInvariant_of_isDedekindDomain
    (B := B) (S := Γ(X, V)) (A := Γ(M, π ⁻¹ᵁ V)) G hW
  have hcS : CommRingCat.ofHom (algebraMap B Γ(X, V)) = ι₀ ≫ φS := rfl
  rw [hcS, smooth_SpecMap_comp_ΓSpecIso_inv_iff] at key
  exact (smooth_SpecMap_appLE_iff πX V hV).mp key

end WildQuotSmooth21

theorem solution
    {B : Type} [CommRing B] [IsDedekindDomain B]
    {M X : Scheme.{0}} (πM : M ⟶ Spec (CommRingCat.of B)) [SmoothOfRelativeDimension 1 πM]
    (G : Type) [Group G] [Fintype G] (ρ : G →* Aut M) (hρ : ∀ g : G, (ρ g).hom ≫ πM = πM)
    (hW : ∀ 𝔭 : Ideal B, 𝔭.IsMaximal →
      ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W)
        (_ : IsAdicComplete (IsLocalRing.maximalIdeal W) W) (_ : IsAlgClosed (IsLocalRing.ResidueField W))
        (_ : Algebra B W), Module.Flat B W ∧ (IsLocalRing.maximalIdeal W).comap (algebraMap B W) = 𝔭)
    (π : M ⟶ X) (πX : X ⟶ Spec (CommRingCat.of B)) (hπX : π ≫ πX = πM)
    (hπ : ∀ g : G, (ρ g).hom ≫ π = π) [IsAffineHom π] [Surjective π]
    (hsec_inj : ∀ V : X.Opens, Function.Injective (π.app V))
    (hsec : ∀ V : X.Opens, Set.range (π.app V) =
        {s | ∀ g : G, (ρ g).hom.appLE (π ⁻¹ᵁ V) (π ⁻¹ᵁ V)
          (by rw [← Scheme.Hom.comp_preimage, hπ g]) s = s})
    (haff : ∀ U : M.Opens, IsAffineOpen U → (∀ g : G, (ρ g).hom ⁻¹ᵁ U = U) →
        ∃ V : X.Opens, IsAffineOpen V ∧ π ⁻¹ᵁ V = U) :
    SmoothOfRelativeDimension 1 πX := by
  subst hπX
  exact IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension 1)
    (fun W : X.affineOpens => (W : X.Opens)) (iSup_affineOpens_eq_top X)
    (fun W => WildQuotSmooth21.affine_step G ρ hW π πX hπ hsec_inj hsec W.1 W.2)

end S_AlgebraicGeometry_smoothOfRelativeDimension_one_of_isQuotient_of_isDedekindDomain
end P2MW
export P2MW.S_AlgebraicGeometry_smoothOfRelativeDimension_one_of_isQuotient_of_isDedekindDomain (solution)
