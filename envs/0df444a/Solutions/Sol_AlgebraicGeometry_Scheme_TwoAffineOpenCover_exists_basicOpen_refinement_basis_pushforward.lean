-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_basicOpen_refinement_basis_pushforward
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/cbbb14fa-6075-57fc-9094-3c919391b810

import Mathlib
import Theorems.Thm_Module_exists_forall_notMem_and_linearIndependent_and_smul_mem_span_of_finrank_baseChange_eq
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_baseChange_sections_linearEquiv_pushforward_tensorUnit_of_affineOpen_le
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_forall_exists_basis_map_eq_of_forall_isAffineOpen
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_basicOpen_refinement_basis_pushforward

set_option autoImplicit false

universe u v w

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_basicOpen_refinement_basis_pushforward.AlgebraicGeometry CategoryTheory.MonoidalCategory Opposite TopologicalSpace"
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_basicOpen_refinement_basis_pushforward.AlgebraicGeometry CategoryTheory.MonoidalCategory Opposite TopologicalSpace TensorProduct"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.basicOpen_res Scheme.Modules.pushforward basicOpen_eq_bot_iff Scheme.Hom Flat.SpecMap_iff IsAffineOpen.opensRange_fromSpec IsFinite Spec IsIntegral Spec.map Scheme Scheme.Hom.finrank_SpecMap_eq_finrank IsOpenImmersion LocallyOfFinitePresentation.SpecMap_iff Flat Scheme.Hom.finrank_of_isPullback IsFinite.SpecMap_iff Scheme.basicOpen_mul IsAffineOpen Scheme.Modules Scheme.Hom.app_eq_appLE LocallyOfFinitePresentation IsAffineHom IsOpenImmersion.isPullback IsIntegral.component_integral Scheme.Modules.forall_exists_basis_map_eq_of_forall_isAffineOpen"
namespace EXREF
namespace Dict
p2m_open "AlgebraicGeometry"

section affine

variable {A B : CommRingCat.{u}} (φ : A ⟶ B)

def Bmod (_φ : A ⟶ B) : Type u := B
noncomputable scoped instance : CommRing (Bmod φ) := inferInstanceAs (CommRing B)
noncomputable scoped instance algB : Algebra A (Bmod φ) := φ.hom.toAlgebra

lemma algebraMap_Bmod (a : A) : algebraMap A (Bmod φ) a = (φ.hom a : B) := rfl

theorem finite_Bmod [IsFinite (Spec.map φ)] : Module.Finite A (Bmod φ) := by
  have h : φ.hom.Finite := (IsFinite.SpecMap_iff φ).mp inferInstance
  exact h

theorem flat_Bmod [Flat (Spec.map φ)] : Module.Flat A (Bmod φ) := by
  have h : φ.hom.Flat := Flat.SpecMap_iff.mp inferInstance
  exact h

theorem finitePresentation_Bmod [IsFinite (Spec.map φ)] [LocallyOfFinitePresentation (Spec.map φ)] :
    Module.FinitePresentation A (Bmod φ) := by
  have h : φ.hom.FinitePresentation := (LocallyOfFinitePresentation.SpecMap_iff φ).mp inferInstance
  haveI : Algebra.FinitePresentation A (Bmod φ) := h
  haveI := finite_Bmod φ
  exact Module.FinitePresentation.of_finite_of_finitePresentation A (Bmod φ)

theorem finrank_Bmod [IsFinite (Spec.map φ)] [Flat (Spec.map φ)] (n : ℕ)
    (hn : ∀ p : Spec A, (Spec.map φ).finrank p = n)
    (K : Type u) [Field K] [Algebra A K] : Module.finrank K (K ⊗[A] Bmod φ) = n := by
  haveI := finite_Bmod φ
  haveI := flat_Bmod φ
  let I : Ideal A := RingHom.ker (algebraMap A K)
  haveI hI : I.IsPrime := RingHom.ker_isPrime _
  have hrk : Module.rankAtStalk (R := A) (Bmod φ) ⟨I, hI⟩ = n := by
    have h1 := hn ⟨I, hI⟩
    rw [Scheme.Hom.finrank_SpecMap_eq_finrank ((IsFinite.SpecMap_iff φ).mp inferInstance)
      (Flat.SpecMap_iff.mp inferInstance)] at h1
    exact h1
  let ψ : I.ResidueField →+* K := Ideal.ResidueField.lift I (algebraMap A K) le_rfl (by
    intro a ha
    simp only [Submonoid.mem_comap, IsUnit.mem_submonoid_iff]
    exact isUnit_iff_ne_zero.mpr (fun h0 => ha (by simpa [I, RingHom.mem_ker] using h0)))
  letI : Algebra I.ResidueField K := ψ.toAlgebra
  haveI : IsScalarTower A I.ResidueField K := IsScalarTower.of_algebraMap_eq (fun a =>
    (Ideal.ResidueField.lift_algebraMap I (algebraMap A K) le_rfl _ a).symm)
  let e : K ⊗[A] Bmod φ ≃ₗ[K] K ⊗[I.ResidueField] (I.ResidueField ⊗[A] Bmod φ) :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange A I.ResidueField K K (Bmod φ)).symm
  rw [e.finrank_eq, Module.finrank_baseChange, Ideal.finrank_fiber_eq_rankAtStalk, hrk]

end affine

variable {X Y : Scheme.{u}} (π : Y ⟶ X)

noncomputable abbrev chartMap (U : X.Opens) : Γ(X, U) ⟶ Γ(Y, π ⁻¹ᵁ U) := π.appLE U (π ⁻¹ᵁ U) le_rfl

theorem chartMap_apply (U : X.Opens) (a : Γ(X, U)) : chartMap π U a = π.app U a := by
  rw [chartMap, ← Scheme.Hom.app_eq_appLE]

theorem isPullback_chart {U : X.Opens} (hU : IsAffineOpen U) [IsAffineHom π] :
    IsPullback (hU.preimage π).fromSpec (Spec.map (chartMap π U)) π hU.fromSpec :=
  (IsOpenImmersion.isPullback (Spec.map (chartMap π U)) (hU.preimage π).fromSpec hU.fromSpec π
    (hU.SpecMap_appLE_fromSpec π (hU.preimage π) le_rfl).symm
    (by rw [IsAffineOpen.opensRange_fromSpec, IsAffineOpen.opensRange_fromSpec])).flip

noncomputable def sectionsEquiv (U : X.Opens) :
    Γ((Scheme.Modules.pushforward π).obj (𝟙_ Y.Modules), U) ≃ₗ[Γ(X, U)] Bmod (chartMap π U) where
  toFun s := (show Γ(Y, π ⁻¹ᵁ U) from s)
  invFun b := (show Γ((Scheme.Modules.pushforward π).obj (𝟙_ Y.Modules), U) from (show Γ(Y, π ⁻¹ᵁ U) from b))
  map_add' _ _ := rfl
  map_smul' a s := by
    change π.app U a * (show Γ(Y, π ⁻¹ᵁ U) from s) = (chartMap π U) a * (show Γ(Y, π ⁻¹ᵁ U) from s)
    rw [chartMap_apply]
  left_inv _ := rfl
  right_inv _ := rfl

theorem finite_sections_pushforward_unit [IsFinite π] {U : X.Opens} (hU : IsAffineOpen U) :
    Module.Finite Γ(X, U) Γ((Scheme.Modules.pushforward π).obj (𝟙_ Y.Modules), U) := by
  have hsq := isPullback_chart π hU
  haveI : IsFinite (Spec.map (chartMap π U)) := MorphismProperty.of_isPullback hsq inferInstance
  haveI := finite_Bmod (chartMap π U)
  exact Module.Finite.equiv (sectionsEquiv π U).symm

theorem flat_sections_pushforward_unit [IsAffineHom π] [Flat π] {U : X.Opens} (hU : IsAffineOpen U) :
    Module.Flat Γ(X, U) Γ((Scheme.Modules.pushforward π).obj (𝟙_ Y.Modules), U) := by
  have hsq := isPullback_chart π hU
  haveI : Flat (Spec.map (chartMap π U)) := MorphismProperty.of_isPullback hsq inferInstance
  haveI := flat_Bmod (chartMap π U)
  exact Module.Flat.of_linearEquiv (sectionsEquiv π U)

theorem projective_sections_pushforward_unit [IsFinite π] [Flat π] [LocallyOfFinitePresentation π]
    {U : X.Opens} (hU : IsAffineOpen U) :
    Module.Projective Γ(X, U) Γ((Scheme.Modules.pushforward π).obj (𝟙_ Y.Modules), U) := by
  have hsq := isPullback_chart π hU
  haveI : IsFinite (Spec.map (chartMap π U)) := MorphismProperty.of_isPullback hsq inferInstance
  haveI : Flat (Spec.map (chartMap π U)) := MorphismProperty.of_isPullback hsq inferInstance
  haveI : LocallyOfFinitePresentation (Spec.map (chartMap π U)) := MorphismProperty.of_isPullback hsq inferInstance
  haveI := finite_Bmod (chartMap π U)
  haveI := flat_Bmod (chartMap π U)
  haveI := finitePresentation_Bmod (chartMap π U)
  haveI : Module.Projective Γ(X, U) (Bmod (chartMap π U)) := Module.Flat.projective_of_finitePresentation
  exact Module.Projective.of_equiv (sectionsEquiv π U).symm

theorem finrank_baseChange_sections_pushforward_unit [IsFinite π] [Flat π] [LocallyOfFinitePresentation π]
    (d : ℕ) (hd : ∀ x : X, π.finrank x = d) {U : X.Opens} (hU : IsAffineOpen U)
    (K : Type u) [Field K] [Algebra Γ(X, U) K] :
    Module.finrank K (K ⊗[Γ(X, U)] Γ((Scheme.Modules.pushforward π).obj (𝟙_ Y.Modules), U)) = d := by
  have hsq := isPullback_chart π hU
  haveI : IsFinite (Spec.map (chartMap π U)) := MorphismProperty.of_isPullback hsq inferInstance
  haveI : Flat (Spec.map (chartMap π U)) := MorphismProperty.of_isPullback hsq inferInstance
  have hn' : ∀ p : Spec Γ(X, U), (Spec.map (chartMap π U)).finrank p = d := fun p => by
    rw [Scheme.Hom.finrank_of_isPullback _ _ _ _ hsq, hd]
  rw [← finrank_Bmod (chartMap π U) d hn' K]
  exact LinearEquiv.finrank_eq (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl K K) (sectionsEquiv π U))

end AlgebraicGeometry.EXREF.Dict
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_basicOpen_refinement_basis_pushforward.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_basicOpen_refinement_basis_pushforward.AlgebraicGeometry.EXREF P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_basicOpen_refinement_basis_pushforward.AlgebraicGeometry.EXREF.Dict"
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_basicOpen_refinement_basis_pushforward.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_basicOpen_refinement_basis_pushforward.AlgebraicGeometry.EXREF"
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_basicOpen_refinement_basis_pushforward.AlgebraicGeometry"

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_basicOpen_refinement_basis_pushforward.AlgebraicGeometry Opposite TopologicalSpace"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.basicOpen_res Scheme.Modules.pushforward basicOpen_eq_bot_iff Scheme.Hom Flat.SpecMap_iff IsAffineOpen.opensRange_fromSpec IsFinite Spec IsIntegral Spec.map Scheme Scheme.Hom.finrank_SpecMap_eq_finrank IsOpenImmersion LocallyOfFinitePresentation.SpecMap_iff Flat Scheme.Hom.finrank_of_isPullback IsFinite.SpecMap_iff Scheme.basicOpen_mul IsAffineOpen Scheme.Modules Scheme.Hom.app_eq_appLE LocallyOfFinitePresentation IsAffineHom IsOpenImmersion.isPullback IsIntegral.component_integral Scheme.Modules.forall_exists_basis_map_eq_of_forall_isAffineOpen"
namespace EXREF
namespace Topo
p2m_open "AlgebraicGeometry"

variable {X : Scheme.{u}}

theorem compl_finite_of_nonempty
    (hX : ∀ Z : Set X, IsClosed Z → Z ≠ Set.univ → Z.Finite ∧ ∀ z ∈ Z, IsClosed ({z} : Set X))
    (O : X.Opens) (hO : (O : Set X).Nonempty) :
    ((O : Set X)ᶜ).Finite ∧ ∀ z ∈ (O : Set X)ᶜ, IsClosed ({z} : Set X) := by
  refine hX _ O.isOpen.isClosed_compl ?_
  intro h
  obtain ⟨x, hx⟩ := hO
  have : x ∈ (O : Set X)ᶜ := h ▸ Set.mem_univ x
  exact this hx

theorem exists_finset_isMaximal {U : X.Opens} (hU : IsAffineOpen U) {T : Set X} (hT : T.Finite)
    (hTU : T ⊆ U) (hTc : ∀ z ∈ T, IsClosed ({z} : Set X)) :
    ∃ S : Finset (Ideal Γ(X, U)), (∀ 𝔭 ∈ S, 𝔭.IsMaximal) ∧
      ∀ f : Γ(X, U), (∀ 𝔭 ∈ S, f ∉ 𝔭) → T ⊆ X.basicOpen f := by
  classical
  let ι : hT.toFinset → Ideal Γ(X, U) := fun x =>
    (hU.primeIdealOf ⟨x.1, hTU (hT.mem_toFinset.mp x.2)⟩).asIdeal
  refine ⟨Finset.univ.image ι, ?_, ?_⟩
  · intro 𝔭 h𝔭
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp h𝔭
    exact hU.primeIdealOf_isMaximal_of_isClosed _ (hTc _ (hT.mem_toFinset.mp x.2))
  · intro f hf z hz
    have hz' : z ∈ hT.toFinset := hT.mem_toFinset.mpr hz
    have h1 : f ∉ ι ⟨z, hz'⟩ := hf _ (Finset.mem_image_of_mem ι (Finset.mem_univ _))

    have h2 : hU.primeIdealOf ⟨z, hTU hz⟩ ∈ PrimeSpectrum.basicOpen f :=
      (PrimeSpectrum.mem_basicOpen _ _).mpr h1
    rw [← hU.fromSpec_preimage_basicOpen] at h2
    have h3 : hU.fromSpec (hU.primeIdealOf ⟨z, hTU hz⟩) ∈ X.basicOpen f := h2
    rwa [hU.fromSpec_primeIdealOf] at h3

theorem exists_finset_isMaximal' {U : X.Opens} (hU : IsAffineOpen U) {Z : Set X} (hZ : IsClosed Z)
    (hfin : (Z ∩ (U : Set X)).Finite) :
    ∃ S : Finset (Ideal Γ(X, U)), (∀ 𝔭 ∈ S, 𝔭.IsMaximal) ∧
      ∀ f : Γ(X, U), (∀ 𝔭 ∈ S, f ∉ 𝔭) → Z ∩ (U : Set X) ⊆ X.basicOpen f := by
  classical
  let ι : hfin.toFinset → Ideal Γ(X, U) := fun x =>
    (hU.primeIdealOf ⟨x.1, (hfin.mem_toFinset.mp x.2).2⟩).asIdeal
  refine ⟨(Finset.univ.image ι).filter Ideal.IsMaximal, fun 𝔭 h𝔭 => (Finset.mem_filter.mp h𝔭).2, ?_⟩
  intro f hf z hz

  have hne : (hU.primeIdealOf ⟨z, hz.2⟩).asIdeal ≠ ⊤ := (hU.primeIdealOf ⟨z, hz.2⟩).isPrime.ne_top
  obtain ⟨𝔪, h𝔪, hle⟩ := Ideal.exists_le_maximal _ hne

  let q : PrimeSpectrum Γ(X, U) := ⟨𝔪, h𝔪.isPrime⟩
  let y : X := hU.fromSpec q
  have hyU : y ∈ (U : Set X) := hU.range_fromSpec ▸ Set.mem_range_self q
  have hspec : z ⤳ y := by
    have h1 : hU.primeIdealOf ⟨z, hz.2⟩ ⤳ q := (PrimeSpectrum.le_iff_specializes _ _).mp hle
    have h2 := h1.map hU.fromSpec.continuous
    rwa [hU.fromSpec_primeIdealOf] at h2
  have hyZ : y ∈ Z := hspec.mem_closed hZ hz.1
  have hq : hU.primeIdealOf ⟨y, hyU⟩ = q := by
    apply hU.fromSpec.isOpenEmbedding.injective
    rw [hU.fromSpec_primeIdealOf]
  have hyfin : y ∈ hfin.toFinset := hfin.mem_toFinset.mpr ⟨hyZ, hyU⟩
  have h𝔪S : 𝔪 ∈ (Finset.univ.image ι).filter Ideal.IsMaximal := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨⟨y, hyfin⟩, Finset.mem_univ _, ?_⟩, h𝔪⟩
    change (hU.primeIdealOf ⟨y, hyU⟩).asIdeal = 𝔪
    rw [hq]
  have h1 : f ∉ (hU.primeIdealOf ⟨z, hz.2⟩).asIdeal := fun h => hf 𝔪 h𝔪S (hle h)
  have h2 : hU.primeIdealOf ⟨z, hz.2⟩ ∈ PrimeSpectrum.basicOpen f := (PrimeSpectrum.mem_basicOpen _ _).mpr h1
  rw [← hU.fromSpec_preimage_basicOpen] at h2
  have h3 : hU.fromSpec (hU.primeIdealOf ⟨z, hz.2⟩) ∈ X.basicOpen f := h2
  rwa [hU.fromSpec_primeIdealOf] at h3

theorem sup_basicOpen_eq_top {U0 U1 : X.Opens} (h : U0 ⊔ U1 = ⊤) (f₀ : Γ(X, U0)) (f₁ : Γ(X, U1))
    (h₁ : ∀ x ∈ (U1 : Set X), x ∉ (U0 : Set X) → x ∈ X.basicOpen f₁)
    (h₀ : ∀ x ∈ (U0 : Set X), x ∉ X.basicOpen f₁ → x ∈ X.basicOpen f₀) :
    X.basicOpen f₀ ⊔ X.basicOpen f₁ = ⊤ := by
  apply top_le_iff.mp
  intro x _
  rw [Opens.mem_sup]
  have hx : x ∈ U0 ⊔ U1 := h ▸ trivial
  rw [Opens.mem_sup] at hx
  by_cases h0 : x ∈ (U0 : Set X)
  · by_cases hf : x ∈ X.basicOpen f₁
    · exact Or.inr hf
    · exact Or.inl (h₀ x h0 hf)
  · rcases hx with hx | hx
    · exact absurd hx h0
    · exact Or.inr (h₁ x hx h0)

noncomputable def refinedCover (𝒱 : X.TwoAffineOpenCover) (f₀ : Γ(X, 𝒱.U0)) (f₁ : Γ(X, 𝒱.U1))
    (hsup : X.basicOpen f₀ ⊔ X.basicOpen f₁ = ⊤) : X.TwoAffineOpenCover where
  U0 := X.basicOpen f₀
  U1 := X.basicOpen f₁
  isAffineOpen_U0 := 𝒱.isAffineOpen_U0.basicOpen f₀
  isAffineOpen_U1 := 𝒱.isAffineOpen_U1.basicOpen f₁
  sup_eq_top := hsup
  isAffineOpen_inf := by
    have e : X.basicOpen f₀ ⊓ X.basicOpen f₁ =
        X.basicOpen (X.presheaf.map (homOfLE (inf_le_left : 𝒱.U0 ⊓ 𝒱.U1 ≤ 𝒱.U0)).op f₀ *
          X.presheaf.map (homOfLE (inf_le_right : 𝒱.U0 ⊓ 𝒱.U1 ≤ 𝒱.U1)).op f₁) := by
      rw [Scheme.basicOpen_mul, Scheme.basicOpen_res, Scheme.basicOpen_res]
      apply le_antisymm
      · refine le_inf (le_inf (le_inf ?_ ?_) inf_le_left) (le_inf (le_inf ?_ ?_) inf_le_right)
        · exact inf_le_left.trans (X.basicOpen_le f₀)
        · exact inf_le_right.trans (X.basicOpen_le f₁)
        · exact inf_le_left.trans (X.basicOpen_le f₀)
        · exact inf_le_right.trans (X.basicOpen_le f₁)
      · exact le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)
    rw [e]
    exact 𝒱.isAffineOpen_inf.basicOpen _

@[scoped simp] theorem refinedCover_U0 (𝒱 : X.TwoAffineOpenCover) (f₀ : Γ(X, 𝒱.U0)) (f₁ : Γ(X, 𝒱.U1)) (hsup) :
    (refinedCover 𝒱 f₀ f₁ hsup).U0 = X.basicOpen f₀ := rfl
@[scoped simp] theorem refinedCover_U1 (𝒱 : X.TwoAffineOpenCover) (f₀ : Γ(X, 𝒱.U0)) (f₁ : Γ(X, 𝒱.U1)) (hsup) :
    (refinedCover 𝒱 f₀ f₁ hsup).U1 = X.basicOpen f₁ := rfl

theorem basicOpen_nonempty [IsIntegral X] {U : X.Opens} (f : Γ(X, U)) (hf : f ≠ 0) :
    ((X.basicOpen f : X.Opens) : Set X).Nonempty := by
  rw [Set.nonempty_iff_ne_empty]
  intro h
  apply hf
  rw [← basicOpen_eq_bot_iff]
  exact SetLike.ext' h

end AlgebraicGeometry.EXREF.Topo
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_basicOpen_refinement_basis_pushforward.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_basicOpen_refinement_basis_pushforward.AlgebraicGeometry.EXREF P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_basicOpen_refinement_basis_pushforward.AlgebraicGeometry.EXREF.Dict P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_basicOpen_refinement_basis_pushforward.AlgebraicGeometry.EXREF.Topo"
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_basicOpen_refinement_basis_pushforward.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_basicOpen_refinement_basis_pushforward.AlgebraicGeometry.EXREF P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_basicOpen_refinement_basis_pushforward.AlgebraicGeometry.EXREF.Dict"
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_basicOpen_refinement_basis_pushforward.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_basicOpen_refinement_basis_pushforward.AlgebraicGeometry.EXREF P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_basicOpen_refinement_basis_pushforward.AlgebraicGeometry.EXREF.Dict"

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_basicOpen_refinement_basis_pushforward.AlgebraicGeometry Opposite TopologicalSpace"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.basicOpen_res Scheme.Modules.pushforward basicOpen_eq_bot_iff Scheme.Hom Flat.SpecMap_iff IsAffineOpen.opensRange_fromSpec IsFinite Spec IsIntegral Spec.map Scheme Scheme.Hom.finrank_SpecMap_eq_finrank IsOpenImmersion LocallyOfFinitePresentation.SpecMap_iff Flat Scheme.Hom.finrank_of_isPullback IsFinite.SpecMap_iff Scheme.basicOpen_mul IsAffineOpen Scheme.Modules Scheme.Hom.app_eq_appLE LocallyOfFinitePresentation IsAffineHom IsOpenImmersion.isPullback IsIntegral.component_integral Scheme.Modules.forall_exists_basis_map_eq_of_forall_isAffineOpen"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "mem_basicOpen basicOpen_res Modules.pushforward Hom mk Γ Hom.finrank_SpecMap_eq_finrank Hom.finrank_of_isPullback basicOpen basicOpen_mul isBasis_affineOpens Modules Opens Hom.app_eq_appLE le_iff_specializes Modules.map_smul basicOpen_le Modules.forall_exists_basis_map_eq_of_forall_isAffineOpen TwoAffineOpenCover"
namespace Modules
p2m_export "AlgebraicGeometry.Scheme.Modules" "pushforward pullback presheaf Hom isSheaf map_smul exists_baseChange_sections_linearEquiv_pushforward_tensorUnit_of_affineOpen_le forall_exists_basis_map_eq_of_forall_isAffineOpen"
namespace RGlue
p2m_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"

variable {X : Scheme.{u}} (M : X.Modules)

theorem res_res {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (x : Γ(M, U)) :
    M.presheaf.map (homOfLE h₂).op (M.presheaf.map (homOfLE h₁).op x) =
      M.presheaf.map (homOfLE (h₂.trans h₁)).op x := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

theorem res_res' {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (x : Γ(X, U)) :
    X.presheaf.map (homOfLE h₂).op (X.presheaf.map (homOfLE h₁).op x) =
      X.presheaf.map (homOfLE (h₂.trans h₁)).op x := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

theorem res_sum_smul {U W : X.Opens} (h : W ≤ U) {d : ℕ} (c : Fin d → Γ(X, U)) (v : Fin d → Γ(M, U)) :
    M.presheaf.map (homOfLE h).op (∑ i, c i • v i) =
      ∑ i, X.presheaf.map (homOfLE h).op (c i) • M.presheaf.map (homOfLE h).op (v i) := by
  rw [map_sum]
  simp only [Modules.map_smul]

variable {V : X.Opens} {d : ℕ} (e : Fin d → Γ(M, V))
  (he : ∀ (W : X.Opens) (hW : W ≤ V), IsAffineOpen W →
    ∃ b : Module.Basis (Fin d) Γ(X, W) Γ(M, W), ∀ i, b i = M.presheaf.map (homOfLE hW).op (e i))

abbrev ι (W : X.Opens) : Type u := { W' : X.Opens // W' ≤ W ∧ IsAffineOpen W' }

theorem cover (W : X.Opens) : W ≤ ⨆ i : ι W, i.1 := by
  intro x hx
  obtain ⟨_, ⟨W', hW', rfl⟩, hxW', hle⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hx W.isOpen
  exact Opens.mem_iSup.mpr ⟨⟨W', hle, hW'⟩, hxW'⟩

include he in

private theorem _root_.AlgebraicGeometry.Scheme.Modules.RGlue.linearIndependent (W : X.Opens) (hW : W ≤ V) :
    ∀ c : Fin d → Γ(X, W), ∑ i, c i • M.presheaf.map (homOfLE hW).op (e i) = 0 → c = 0 := by
  intro c hc
  funext i

  refine X.sheaf.eq_of_locally_eq' (fun j : ι W => j.1) W (fun j => homOfLE j.2.1) (cover W) (c i) 0 ?_
  intro j
  rw [map_zero]
  obtain ⟨b, hb⟩ := he j.1 (j.2.1.trans hW) j.2.2
  have hc' := congrArg (M.presheaf.map (homOfLE j.2.1).op) hc
  rw [res_sum_smul, map_zero] at hc'
  simp only [res_res] at hc'

  have hli := b.linearIndependent
  rw [Fintype.linearIndependent_iff] at hli
  have := hli (fun i => X.presheaf.map (homOfLE j.2.1).op (c i)) (by
    simpa only [hb] using hc')
  exact this i

p2m_export "AlgebraicGeometry.Scheme.Modules.RGlue" "linearIndependent"
include he in

theorem exists_coords (W : X.Opens) (hW : W ≤ V) (s : Γ(M, W)) :
    ∃ c : Fin d → Γ(X, W), ∑ i, c i • M.presheaf.map (homOfLE hW).op (e i) = s := by

  have hloc : ∀ j : ι W, ∃ c : Fin d → Γ(X, j.1),
      ∑ i, c i • M.presheaf.map (homOfLE (j.2.1.trans hW)).op (e i) = M.presheaf.map (homOfLE j.2.1).op s := by
    intro j
    obtain ⟨b, hb⟩ := he j.1 (j.2.1.trans hW) j.2.2
    refine ⟨fun i => b.repr (M.presheaf.map (homOfLE j.2.1).op s) i, ?_⟩
    conv_rhs => rw [← b.sum_repr (M.presheaf.map (homOfLE j.2.1).op s)]
    simp only [hb]
  choose c hc using hloc

  have hcompat : ∀ i, TopCat.Presheaf.IsCompatible X.presheaf (fun j : ι W => j.1) (fun j => c j i) := by
    intro i j k
    have key := linearIndependent M e he (j.1 ⊓ k.1) ((inf_le_left.trans j.2.1).trans hW)
      (fun i => X.presheaf.map (Opens.infLELeft j.1 k.1).op (c j i) - X.presheaf.map (Opens.infLERight j.1 k.1).op (c k i)) ?_
    · have := congrFun key i
      exact sub_eq_zero.mp this
    · simp only [sub_smul, Finset.sum_sub_distrib]
      rw [sub_eq_zero]
      have hj := congrArg (M.presheaf.map (Opens.infLELeft j.1 k.1).op) (hc j)
      have hk := congrArg (M.presheaf.map (Opens.infLERight j.1 k.1).op) (hc k)
      rw [show (Opens.infLELeft j.1 k.1 : j.1 ⊓ k.1 ⟶ j.1) = homOfLE inf_le_left from rfl] at hj ⊢
      rw [show (Opens.infLERight j.1 k.1 : j.1 ⊓ k.1 ⟶ k.1) = homOfLE inf_le_right from rfl] at hk ⊢
      rw [res_sum_smul, res_res] at hj hk
      simp only [res_res] at hj hk
      rw [hj, hk]

  have hglue : ∀ i, ∃ ci : Γ(X, W), ∀ j : ι W, X.presheaf.map (homOfLE j.2.1).op ci = c j i := fun i =>
    (X.sheaf.existsUnique_gluing' (fun j : ι W => j.1) W (fun j => homOfLE j.2.1) (cover W)
      (fun j => c j i) (hcompat i)).exists
  choose cg hcg using hglue
  refine ⟨cg, ?_⟩

  refine TopCat.Sheaf.eq_of_locally_eq' (C := Ab) ⟨M.presheaf, M.isSheaf⟩ (fun j : ι W => j.1) W
    (fun j => homOfLE j.2.1) (cover W) _ _ ?_
  intro j
  change M.presheaf.map (homOfLE j.2.1).op _ = M.presheaf.map (homOfLE j.2.1).op s
  rw [res_sum_smul]
  simp only [res_res, hcg]
  exact hc j

include he in
private theorem _root_.AlgebraicGeometry.Scheme.Modules.RGlue.main (W : X.Opens) (hW : W ≤ V) :
    ∃ b : Module.Basis (Fin d) Γ(X, W) Γ(M, W), ∀ i, b i = M.presheaf.map (homOfLE hW).op (e i) := by
  have hli : LinearIndependent Γ(X, W) (fun i => M.presheaf.map (homOfLE hW).op (e i)) :=
    Fintype.linearIndependent_iff.mpr fun g hg i => congrFun (linearIndependent M e he W hW g hg) i
  have hsp : ⊤ ≤ Submodule.span (X.presheaf.obj (op W)) (Set.range fun i => M.presheaf.map (homOfLE hW).op (e i)) := by
    intro s _
    obtain ⟨c, hc⟩ := exists_coords M e he W hW s
    rw [← hc]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  exact ⟨Module.Basis.mk hli hsp, fun i => Module.Basis.mk_apply hli hsp i⟩

p2m_export "AlgebraicGeometry.Scheme.Modules.RGlue" "main"
end AlgebraicGeometry.Scheme.Modules.RGlue
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_basicOpen_refinement_basis_pushforward.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_basicOpen_refinement_basis_pushforward.AlgebraicGeometry.EXREF P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_basicOpen_refinement_basis_pushforward.AlgebraicGeometry.EXREF.Dict P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_basicOpen_refinement_basis_pushforward.AlgebraicGeometry.EXREF.Topo"
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_basicOpen_refinement_basis_pushforward.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_basicOpen_refinement_basis_pushforward.AlgebraicGeometry.EXREF P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_basicOpen_refinement_basis_pushforward.AlgebraicGeometry.EXREF.Dict P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_basicOpen_refinement_basis_pushforward.AlgebraicGeometry.EXREF.Topo"
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_basicOpen_refinement_basis_pushforward.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_basicOpen_refinement_basis_pushforward.AlgebraicGeometry.EXREF P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_basicOpen_refinement_basis_pushforward.AlgebraicGeometry.EXREF.Dict P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_basicOpen_refinement_basis_pushforward.AlgebraicGeometry.EXREF.Topo"
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_basicOpen_refinement_basis_pushforward.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_basicOpen_refinement_basis_pushforward.AlgebraicGeometry.EXREF P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_basicOpen_refinement_basis_pushforward.AlgebraicGeometry.EXREF.Dict P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_basicOpen_refinement_basis_pushforward.AlgebraicGeometry.EXREF.Topo"

namespace EXREF

section BaseChange

variable {A : Type u} [CommRing A] {P : Type v} [AddCommGroup P] [Module A P]

theorem exists_basis_baseChange_of_isUnit {d : ℕ} (f : A) (e : Fin d → P)
    (hind : LinearIndependent A e) (hspan : ∀ p : P, f • p ∈ Submodule.span A (Set.range e))
    (A' : Type w) [CommRing A'] [Algebra A A'] (hu : IsUnit (algebraMap A A' f)) :
    ∃ b : Module.Basis (Fin d) A' (A' ⊗[A] P), ∀ i, b i = (1 : A') ⊗ₜ[A] e i := by
  classical

  let φ : (Fin d → A) →ₗ[A] P := Fintype.linearCombination A e
  have hφ : ∀ c, φ c = ∑ i, c i • e i := fun c => by simp [φ, Fintype.linearCombination_apply]
  have hφs : ∀ i, φ (Pi.single i 1) = e i := fun i => by simp [φ]
  have hφinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    rw [hφ] at hc
    exact funext fun i => Fintype.linearIndependent_iff.mp hind c hc i
  have hφrange : ∀ p : P, f • p ∈ LinearMap.range φ := by
    intro p
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun A).mp (hspan p)
    exact ⟨c, by rw [hφ, hc]⟩

  let ι : (Fin d → A) ≃ₗ[A] LinearMap.range φ := LinearEquiv.ofInjective φ hφinj
  let μ : P →ₗ[A] LinearMap.range φ := LinearMap.codRestrict (LinearMap.range φ) (f • LinearMap.id) hφrange
  let ψ : P →ₗ[A] (Fin d → A) := ι.symm.toLinearMap ∘ₗ μ
  have hφψ : ∀ p : P, φ (ψ p) = f • p := by
    intro p
    have h1 : ((ι (ψ p) : LinearMap.range φ) : P) = (μ p : P) := by
      simp only [ψ, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, LinearEquiv.apply_symm_apply]
    have h2 : ((ι (ψ p) : LinearMap.range φ) : P) = φ (ψ p) := LinearEquiv.ofInjective_apply φ (ψ p)
    rw [← h2, h1]
    rfl
  have hψφ : ∀ c : Fin d → A, ψ (φ c) = f • c := by
    intro c
    apply hφinj
    rw [hφψ, map_smul]

  let φ' : A' ⊗[A] (Fin d → A) →ₗ[A'] A' ⊗[A] P := φ.baseChange A'
  let ψ' : A' ⊗[A] P →ₗ[A'] A' ⊗[A] (Fin d → A) := ψ.baseChange A'
  have h1 : ψ' ∘ₗ φ' = algebraMap A A' f • LinearMap.id := by
    refine TensorProduct.AlgebraTensorModule.ext fun a c => ?_
    simp only [φ', ψ', LinearMap.coe_comp, Function.comp_apply, LinearMap.baseChange_tmul, hψφ,
      LinearMap.smul_apply, LinearMap.id_coe, id_eq]
    rw [TensorProduct.tmul_smul, ← IsScalarTower.algebraMap_smul A' f (a ⊗ₜ[A] c)]
  have h2 : φ' ∘ₗ ψ' = algebraMap A A' f • LinearMap.id := by
    refine TensorProduct.AlgebraTensorModule.ext fun a p => ?_
    simp only [φ', ψ', LinearMap.coe_comp, Function.comp_apply, LinearMap.baseChange_tmul, hφψ,
      LinearMap.smul_apply, LinearMap.id_coe, id_eq]
    rw [TensorProduct.tmul_smul, ← IsScalarTower.algebraMap_smul A' f (a ⊗ₜ[A] p)]
  obtain ⟨u, hu'⟩ := hu
  let g : A' ⊗[A] P →ₗ[A'] A' ⊗[A] (Fin d → A) := ((u⁻¹ : A'ˣ) : A') • ψ'
  have hg1 : g ∘ₗ φ' = LinearMap.id := by
    rw [LinearMap.smul_comp, h1, smul_smul, ← hu', Units.inv_mul, one_smul]
  have hg2 : φ' ∘ₗ g = LinearMap.id := by
    rw [LinearMap.comp_smul, h2, smul_smul, ← hu', Units.inv_mul, one_smul]
  let E : A' ⊗[A] (Fin d → A) ≃ₗ[A'] A' ⊗[A] P := LinearEquiv.ofLinear φ' g hg2 hg1
  let b0 : Module.Basis (Fin d) A' (A' ⊗[A] (Fin d → A)) := Algebra.TensorProduct.basis A' (Pi.basisFun A (Fin d))
  refine ⟨b0.map E, fun i => ?_⟩
  rw [Module.Basis.map_apply]
  change φ' (b0 i) = _
  rw [Algebra.TensorProduct.basis_apply, Pi.basisFun_apply]
  simp only [φ', LinearMap.baseChange_tmul, hφs]

end BaseChange
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_basicOpen_refinement_basis_pushforward.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_basicOpen_refinement_basis_pushforward.AlgebraicGeometry.EXREF P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_basicOpen_refinement_basis_pushforward.AlgebraicGeometry.EXREF.Dict P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_basicOpen_refinement_basis_pushforward.AlgebraicGeometry.EXREF.Topo"

end EXREF
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_basicOpen_refinement_basis_pushforward.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_basicOpen_refinement_basis_pushforward.AlgebraicGeometry.EXREF P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_basicOpen_refinement_basis_pushforward.AlgebraicGeometry.EXREF.Dict P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_basicOpen_refinement_basis_pushforward.AlgebraicGeometry.EXREF.Topo"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.basicOpen_res Scheme.Modules.pushforward basicOpen_eq_bot_iff Scheme.Hom Flat.SpecMap_iff IsAffineOpen.opensRange_fromSpec IsFinite Spec IsIntegral Spec.map Scheme Scheme.Hom.finrank_SpecMap_eq_finrank IsOpenImmersion LocallyOfFinitePresentation.SpecMap_iff Flat Scheme.Hom.finrank_of_isPullback IsFinite.SpecMap_iff Scheme.basicOpen_mul IsAffineOpen Scheme.Modules Scheme.Hom.app_eq_appLE LocallyOfFinitePresentation IsAffineHom IsOpenImmersion.isPullback IsIntegral.component_integral Scheme.Modules.forall_exists_basis_map_eq_of_forall_isAffineOpen"
namespace EXREF
namespace Assembly
p2m_open "AlgebraicGeometry"

p2m_open "AlgebraicGeometry.Scheme.Modules P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_basicOpen_refinement_basis_pushforward.AlgebraicGeometry.Scheme.Modules"

variable {X Y : Scheme.{u}} (π : Y ⟶ X) (d : ℕ)

theorem he_basicOpen [IsAffineHom π] {U : X.Opens} (hU : IsAffineOpen U) {f : Γ(X, U)} {e : Fin d → Γ(((Scheme.Modules.pushforward π).obj (𝟙_ Y.Modules)), U)}
    (hli : LinearIndependent Γ(X, U) e)
    (hspan : ∀ p : Γ(((Scheme.Modules.pushforward π).obj (𝟙_ Y.Modules)), U), f • p ∈ Submodule.span Γ(X, U) (Set.range e)) :
    ∀ (W : X.Opens) (hW : W ≤ X.basicOpen f),
      ∃ b : Module.Basis (Fin d) Γ(X, W) Γ(((Scheme.Modules.pushforward π).obj (𝟙_ Y.Modules)), W),
        ∀ i, b i = ((Scheme.Modules.pushforward π).obj (𝟙_ Y.Modules)).presheaf.map (homOfLE hW).op
          (((Scheme.Modules.pushforward π).obj (𝟙_ Y.Modules)).presheaf.map (homOfLE (X.basicOpen_le f)).op (e i)) := by
  refine Scheme.Modules.forall_exists_basis_map_eq_of_forall_isAffineOpen ((Scheme.Modules.pushforward π).obj (𝟙_ Y.Modules)) _ ?_
  intro W hW hWaff
  have hWU : W ≤ U := hW.trans (X.basicOpen_le f)
  letI : Algebra Γ(X, U) Γ(X, W) := (X.presheaf.map (homOfLE hWU).op).hom.toAlgebra

  have hu : IsUnit (algebraMap Γ(X, U) Γ(X, W) f) := by
    have h1 := X.toRingedSpace.isUnit_res_basicOpen f
    have h2 := h1.map (X.presheaf.map (homOfLE hW).op).hom
    change IsUnit (X.presheaf.map (homOfLE hWU).op f)
    rw [← Scheme.Modules.RGlue.res_res' (h₁ := X.basicOpen_le f) (h₂ := hW)]
    exact h2
  obtain ⟨b, hb⟩ := EXREF.exists_basis_baseChange_of_isUnit f e hli hspan Γ(X, W) hu
  obtain ⟨ψ, hψ⟩ := exists_baseChange_sections_linearEquiv_pushforward_tensorUnit_of_affineOpen_le π hU hWaff hWU
  refine ⟨b.map ψ, fun i => ?_⟩
  rw [Module.Basis.map_apply, hb, hψ, Scheme.Modules.RGlue.res_res]

variable [IsFinite π] [Flat π] [LocallyOfFinitePresentation π] (hd : ∀ x : X, π.finrank x = d)

include hd in

theorem chart_step [IsIntegral X] {U : X.Opens} (hU : IsAffineOpen U) (hUne : (U : Set X).Nonempty)
    {Z : Set X} (hZ : IsClosed Z) (hfin : (Z ∩ (U : Set X)).Finite) :
    ∃ (f : Γ(X, U)) (e : Fin d → Γ(((Scheme.Modules.pushforward π).obj (𝟙_ Y.Modules)), U)), f ≠ 0 ∧ Z ∩ (U : Set X) ⊆ X.basicOpen f ∧
      LinearIndependent Γ(X, U) e ∧ ∀ p : Γ(((Scheme.Modules.pushforward π).obj (𝟙_ Y.Modules)), U), f • p ∈ Submodule.span Γ(X, U) (Set.range e) := by
  classical
  haveI : Nonempty U := by
    obtain ⟨x, hx⟩ := hUne; exact ⟨⟨x, hx⟩⟩
  haveI : IsDomain Γ(X, U) := IsIntegral.component_integral U
  haveI : Module.Finite Γ(X, U) Γ(((Scheme.Modules.pushforward π).obj (𝟙_ Y.Modules)), U) := Dict.finite_sections_pushforward_unit π hU
  obtain ⟨S, hSmax, hScov⟩ := Topo.exists_finset_isMaximal' hU hZ hfin

  obtain ⟨𝔪, h𝔪⟩ := Ideal.exists_maximal Γ(X, U)
  let S' : Finset (Ideal Γ(X, U)) := insert 𝔪 S
  have hS'max : ∀ 𝔭 ∈ S', 𝔭.IsMaximal := fun 𝔭 h𝔭 => by
    rcases Finset.mem_insert.mp h𝔭 with rfl | h
    · exact h𝔪
    · exact hSmax 𝔭 h
  obtain ⟨f, e, hfS, hli, hspan⟩ :=
    Module.exists_forall_notMem_and_linearIndependent_and_smul_mem_span_of_finrank_baseChange_eq d S' hS'max
      ⟨𝔪, Finset.mem_insert_self _ _⟩ (fun K _ _ => Dict.finrank_baseChange_sections_pushforward_unit π d hd hU K)
  refine ⟨f, e, ?_, hScov f (fun 𝔭 h𝔭 => hfS 𝔭 (Finset.mem_insert_of_mem h𝔭)), hli, hspan⟩
  rintro rfl
  exact hfS 𝔪 (Finset.mem_insert_self _ _) 𝔪.zero_mem

include hd in

theorem main [IsIntegral X]
    (hX : ∀ Z : Set X, IsClosed Z → Z ≠ Set.univ → Z.Finite)
    (𝒱 : X.TwoAffineOpenCover) (h₀ : (𝒱.U0 : Set X).Nonempty) (h₁ : (𝒱.U1 : Set X).Nonempty) :
    ∃ (f₀ : Γ(X, 𝒱.U0)) (f₁ : Γ(X, 𝒱.U1)) (𝒱' : X.TwoAffineOpenCover),
      𝒱'.U0 = X.basicOpen f₀ ∧ 𝒱'.U1 = X.basicOpen f₁ ∧
      (∃ e : Fin d → Γ(((Scheme.Modules.pushforward π).obj (𝟙_ Y.Modules)), 𝒱'.U0),
        ∀ (W : X.Opens) (hW : W ≤ 𝒱'.U0),
          ∃ b : Module.Basis (Fin d) Γ(X, W) Γ(((Scheme.Modules.pushforward π).obj (𝟙_ Y.Modules)), W),
            ∀ i, b i = ((Scheme.Modules.pushforward π).obj (𝟙_ Y.Modules)).presheaf.map (homOfLE hW).op (e i)) ∧
      (∃ e : Fin d → Γ(((Scheme.Modules.pushforward π).obj (𝟙_ Y.Modules)), 𝒱'.U1),
        ∀ (W : X.Opens) (hW : W ≤ 𝒱'.U1),
          ∃ b : Module.Basis (Fin d) Γ(X, W) Γ(((Scheme.Modules.pushforward π).obj (𝟙_ Y.Modules)), W),
            ∀ i, b i = ((Scheme.Modules.pushforward π).obj (𝟙_ Y.Modules)).presheaf.map (homOfLE hW).op (e i)) := by

  have hfin : ∀ O : X.Opens, (O : Set X).Nonempty → ((O : Set X)ᶜ).Finite := fun O hO => by
    refine hX _ O.isOpen.isClosed_compl fun h => ?_
    obtain ⟨x, hx⟩ := hO
    exact (h ▸ Set.mem_univ x : x ∈ (O : Set X)ᶜ) hx

  obtain ⟨f₁, e₁, hf₁, hcov₁, hli₁, hspan₁⟩ :=
    chart_step π d hd 𝒱.isAffineOpen_U1 h₁ 𝒱.U0.isOpen.isClosed_compl
      ((hfin 𝒱.U0 h₀).subset Set.inter_subset_left)

  have hD₁ : ((X.basicOpen f₁ : X.Opens) : Set X).Nonempty := Topo.basicOpen_nonempty f₁ hf₁
  obtain ⟨f₀, e₀, -, hcov₀, hli₀, hspan₀⟩ :=
    chart_step π d hd 𝒱.isAffineOpen_U0 h₀ (X.basicOpen f₁).isOpen.isClosed_compl
      ((hfin _ hD₁).subset Set.inter_subset_left)

  have hsup : X.basicOpen f₀ ⊔ X.basicOpen f₁ = ⊤ :=
    Topo.sup_basicOpen_eq_top 𝒱.sup_eq_top f₀ f₁ (fun x hx1 hx0 => hcov₁ ⟨hx0, hx1⟩)
      (fun x hx0 hxf => hcov₀ ⟨hxf, hx0⟩)
  refine ⟨f₀, f₁, Topo.refinedCover 𝒱 f₀ f₁ hsup, rfl, rfl, ?_, ?_⟩
  · exact ⟨fun i => ((Scheme.Modules.pushforward π).obj (𝟙_ Y.Modules)).presheaf.map (homOfLE (X.basicOpen_le f₀)).op (e₀ i),
      he_basicOpen π d 𝒱.isAffineOpen_U0 hli₀ hspan₀⟩
  · exact ⟨fun i => ((Scheme.Modules.pushforward π).obj (𝟙_ Y.Modules)).presheaf.map (homOfLE (X.basicOpen_le f₁)).op (e₁ i),
      he_basicOpen π d 𝒱.isAffineOpen_U1 hli₁ hspan₁⟩

end AlgebraicGeometry.EXREF.Assembly
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_basicOpen_refinement_basis_pushforward.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_basicOpen_refinement_basis_pushforward.AlgebraicGeometry.EXREF P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_basicOpen_refinement_basis_pushforward.AlgebraicGeometry.EXREF.Dict P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_basicOpen_refinement_basis_pushforward.AlgebraicGeometry.EXREF.Topo"
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_basicOpen_refinement_basis_pushforward.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_basicOpen_refinement_basis_pushforward.AlgebraicGeometry.EXREF P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_basicOpen_refinement_basis_pushforward.AlgebraicGeometry.EXREF.Dict P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_basicOpen_refinement_basis_pushforward.AlgebraicGeometry.EXREF.Topo"
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_basicOpen_refinement_basis_pushforward.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_basicOpen_refinement_basis_pushforward.AlgebraicGeometry.EXREF P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_basicOpen_refinement_basis_pushforward.AlgebraicGeometry.EXREF.Dict P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_basicOpen_refinement_basis_pushforward.AlgebraicGeometry.EXREF.Topo"

theorem solution
    {X Y : Scheme.{u}} (π : Y ⟶ X) [IsFinite π] [Flat π] [LocallyOfFinitePresentation π]
    (d : ℕ) (hd : ∀ x : X, π.finrank x = d)
    [IsIntegral X]

    (hX : ∀ Z : Set X, IsClosed Z → Z ≠ Set.univ → Z.Finite)
    (𝒱 : X.TwoAffineOpenCover) (h₀ : (𝒱.U0 : Set X).Nonempty) (h₁ : (𝒱.U1 : Set X).Nonempty) :
    ∃ (f₀ : Γ(X, 𝒱.U0)) (f₁ : Γ(X, 𝒱.U1)) (𝒱' : X.TwoAffineOpenCover),
      𝒱'.U0 = X.basicOpen f₀ ∧ 𝒱'.U1 = X.basicOpen f₁ ∧
      (∃ e : Fin d → Γ((Scheme.Modules.pushforward π).obj (𝟙_ Y.Modules), 𝒱'.U0),
        ∀ (W : X.Opens) (hW : W ≤ 𝒱'.U0),
          ∃ b : Module.Basis (Fin d) Γ(X, W) Γ((Scheme.Modules.pushforward π).obj (𝟙_ Y.Modules), W),
            ∀ i, b i = ((Scheme.Modules.pushforward π).obj (𝟙_ Y.Modules)).presheaf.map (homOfLE hW).op (e i)) ∧
      (∃ e : Fin d → Γ((Scheme.Modules.pushforward π).obj (𝟙_ Y.Modules), 𝒱'.U1),
        ∀ (W : X.Opens) (hW : W ≤ 𝒱'.U1),
          ∃ b : Module.Basis (Fin d) Γ(X, W) Γ((Scheme.Modules.pushforward π).obj (𝟙_ Y.Modules), W),
            ∀ i, b i = ((Scheme.Modules.pushforward π).obj (𝟙_ Y.Modules)).presheaf.map (homOfLE hW).op (e i)) :=
  AlgebraicGeometry.EXREF.Assembly.main π d hd hX 𝒱 h₀ h₁

end S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_basicOpen_refinement_basis_pushforward
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_basicOpen_refinement_basis_pushforward (solution)
