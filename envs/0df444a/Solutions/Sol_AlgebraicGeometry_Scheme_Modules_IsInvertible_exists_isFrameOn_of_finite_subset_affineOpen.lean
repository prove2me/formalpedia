-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_isFrameOn_of_finite_subset_affineOpen
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/177543c3-c37b-551f-b16d-08b102afd512

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_FiniteBySections_of_isFinite
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_of_iSup
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_nonempty_pullback_iso_unit
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_isFrameOn_of_pullback_iso_unit
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_isFrameOn_of_finite_subset_affineOpen

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_isFrameOn_of_finite_subset_affineOpen.AlgebraicGeometry"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "HasAffineProperty Scheme.Modules.pullback Scheme.Opens.range_ι Scheme.Hom IsFinite IsAffine Spec RingedSpace.isUnit_res_basicOpen Scheme IsOpenImmersion HasAffineProperty.iff_of_isAffine Proj Scheme.Modules.pullbackCongr IsOpenImmersion.isoOfRangeEq isAffineOpen_top Proj.basicOpen IsAffineOpen Scheme.Modules Scheme.Hom.preimage_iSup Scheme.Opens Proj.iSup_basicOpen_eq_top Scheme.Modules.map_smul RingedSpace Scheme.Modules.pullbackComp IsOpenImmersion.isoOfRangeEq_hom_fac Scheme.Modules.IsInvertible Scheme.Modules.pullbackUnitIso Scheme.Modules.IsFrameOn Scheme.Modules.FiniteBySections ProjSpace.irrelevant_le_span_X Scheme.Modules.FiniteBySections.of_isFinite Scheme.Modules.IsFrameOn.of_iSup Scheme.Modules.exists_isFrameOn_of_pullback_iso_unit"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "mem_basicOpen ringCatSheaf Modules.pullback Opens.range_ι Hom Γ isoSpec basicOpen Modules.pullbackCongr Modules Hom.preimage_iSup Opens le_iff_specializes Modules.map_smul basicOpen_le Modules.pullbackComp Modules.IsInvertible Modules.pullbackUnitIso Modules.IsFrameOn Modules.FiniteBySections Modules.FiniteBySections.of_isFinite Modules.IsFrameOn.of_iSup Modules.exists_isFrameOn_of_pullback_iso_unit"
namespace Modules
p2m_export "AlgebraicGeometry.Scheme.Modules" "pullback presheaf Hom pullbackCongr map_smul pullbackComp IsInvertible pullbackUnitIso IsFrameOn FiniteBySections FiniteBySections.of_isFinite IsFrameOn.of_iSup exists_isFrameOn_of_pullback_iso_unit"
namespace SemilocalOneSection
p2m_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"

open TopologicalSpace Opposite

attribute [local instance] MvPolynomial.gradedAlgebra

variable {X : Scheme.{u}} {M : X.Modules}

theorem map_smul' {U V : X.Opens} (h : V ≤ U) (r : Γ(X, U)) (m : Γ(M, U)) :
    M.presheaf.map (homOfLE h).op (r • m) = X.presheaf.map (homOfLE h).op r • M.presheaf.map (homOfLE h).op m :=
  Scheme.Modules.map_smul M _ r m

theorem isFrameOn_of_eq_unit_smul {U U' W : X.Opens} (hWU : W ≤ U) (hWU' : W ≤ U') {e : Γ(M, U)}
    (he : Scheme.Modules.IsFrameOn e W) (s : Γ(M, U')) (G : Γ(X, W)) (hG : IsUnit G)
    (hs : M.presheaf.map (homOfLE hWU').op s = G • M.presheaf.map (homOfLE hWU).op e) :
    Scheme.Modules.IsFrameOn s W := by
  intro W' hW'U' hW'W
  have hs' : M.presheaf.map (homOfLE hW'U').op s =
      X.presheaf.map (homOfLE hW'W).op G • M.presheaf.map (homOfLE (hW'W.trans hWU)).op e := by
    have := congrArg (M.presheaf.map (homOfLE hW'W).op) hs
    rw [map_smul', ← CategoryTheory.comp_apply, ← Functor.map_comp, ← CategoryTheory.comp_apply,
      ← Functor.map_comp] at this
    exact this
  have hG' : IsUnit (X.presheaf.map (homOfLE hW'W).op G) := hG.map _
  obtain ⟨u, hu⟩ := hG'
  have hb := he (hW'W.trans hWU) hW'W
  have hcomp : (fun g : Γ(X, W') => g • M.presheaf.map (homOfLE hW'U').op s) =
      (fun g : Γ(X, W') => g • M.presheaf.map (homOfLE (hW'W.trans hWU)).op e) ∘ (fun g => g * ↑u) := by
    funext g
    simp only [Function.comp_apply, hs', ← hu, smul_smul]
  rw [hcomp]
  exact hb.comp (Units.mulRight_bijective u)

theorem isUnit_add_of_mem_maximalIdeal {R : Type*} [CommRing R] [IsLocalRing R] {u m : R} (hu : IsUnit u)
    (hm : m ∈ IsLocalRing.maximalIdeal R) : IsUnit (u + m) := by
  by_contra h
  have h' : u + m ∈ IsLocalRing.maximalIdeal R := (IsLocalRing.mem_maximalIdeal _).mpr h
  have : u ∈ IsLocalRing.maximalIdeal R := by
    have := Ideal.sub_mem _ h' hm
    rwa [add_sub_cancel_right] at this
  exact (IsLocalRing.mem_maximalIdeal _).mp this hu

theorem core {A : Type u} [CommRing A] (g : X ⟶ Spec (.of A)) [IsFinite g]
    (hM : Scheme.Modules.IsInvertible M) (F : Finset X) (hFcl : ∀ x ∈ F, IsClosed ({x} : Set X)) :
    ∃ (s : Γ(M, ⊤)) (Wtot : X.Opens), (∀ x ∈ F, x ∈ Wtot) ∧ Scheme.Modules.IsFrameOn s Wtot := by
  classical
  have hfin := (HasAffineProperty.iff_of_isAffine (P := @IsFinite) (f := g)).mp inferInstance
  haveI : IsAffine X := hfin.1
  have hXtop : IsAffineOpen (⊤ : X.Opens) := isAffineOpen_top X

  obtain ⟨N, 𝔓, -⟩ := Scheme.Modules.FiniteBySections.of_isFinite g M hM
  let U : Fin (N + 1) → X.Opens := fun i =>
    𝔓.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A) (MvPolynomial.X i)
  have hUframe : ∀ i, Scheme.Modules.IsFrameOn (𝔓.σ i) (U i) := fun i => by
    intro W hW hWU; exact 𝔓.frame i W hWU
  have hUcov : ⨆ i, U i = ⊤ := by
    simp only [U, ← Scheme.Hom.preimage_iSup]
    rw [Proj.iSup_basicOpen_eq_top _ (fun j => MvPolynomial.X j) (ProjSpace.irrelevant_le_span_X A N)]
    rfl
  have hmemU : ∀ x : X, ∃ i, x ∈ U i := fun x => by
    have : x ∈ (⨆ i, U i) := by rw [hUcov]; trivial
    exact Opens.mem_iSup.mp this
  choose ix hix using hmemU

  let 𝔮 : X → PrimeSpectrum Γ(X, ⊤) := fun x => hXtop.primeIdealOf ⟨x, trivial⟩
  have hfrom : ∀ x, hXtop.fromSpec.base (𝔮 x) = x := fun x => hXtop.fromSpec_primeIdealOf ⟨x, trivial⟩

  have hincomp : ∀ x x', x ∈ F → x' ∈ F → (𝔮 x').asIdeal ≤ (𝔮 x).asIdeal → x' = x := by
    intro x x' hx hx' hle
    have hspec : (𝔮 x') ⤳ (𝔮 x) := (PrimeSpectrum.le_iff_specializes _ _).mp hle
    have hspec' : x' ⤳ x := by
      have := hspec.map hXtop.fromSpec.base.hom.continuous
      rwa [hfrom x', hfrom x] at this
    have hmem : x ∈ closure ({x'} : Set X) := hspec'.mem_closure
    rw [(hFcl x' hx').closure_eq, Set.mem_singleton_iff] at hmem
    exact hmem.symm

  have hsep : ∀ x ∈ F, ∃ a : Γ(X, ⊤), a ∉ (𝔮 x).asIdeal ∧ ∀ x' ∈ F, x' ≠ x → a ∈ (𝔮 x').asIdeal := by
    intro x hx
    have hnle : ¬ (F.erase x).inf (fun x' => (𝔮 x').asIdeal) ≤ (𝔮 x).asIdeal := by
      intro hle
      obtain ⟨x', hx', hx'le⟩ := (Ideal.IsPrime.inf_le' (𝔮 x).isPrime).mp hle
      obtain ⟨hx'x, hx'F⟩ := Finset.mem_erase.mp hx'
      exact hx'x (hincomp x x' hx hx'F hx'le)
    obtain ⟨a, ha, ha'⟩ := SetLike.not_le_iff_exists.mp hnle
    refine ⟨a, ha', fun x' hx' hne => ?_⟩
    exact (Finset.inf_le (Finset.mem_erase.mpr ⟨hne, hx'⟩) : (F.erase x).inf (fun x' => (𝔮 x').asIdeal) ≤ _) ha
  choose! a ha_self ha_other using hsep

  have hbasic : ∀ (x : X) (f : Γ(X, ⊤)), x ∈ X.basicOpen f ↔ f ∉ (𝔮 x).asIdeal := by
    intro x f
    rw [← PrimeSpectrum.mem_basicOpen, show PrimeSpectrum.basicOpen f = hXtop.fromSpec ⁻¹ᵁ X.basicOpen f from
      (hXtop.fromSpec_preimage_basicOpen f).symm]
    show x ∈ X.basicOpen f ↔ hXtop.fromSpec.base (𝔮 x) ∈ X.basicOpen f
    rw [hfrom x]

  let s : Γ(M, ⊤) := ∑ x ∈ F, a x • 𝔓.σ (ix x)
  have hsframe : ∀ x₀ ∈ F, ∃ W : X.Opens, x₀ ∈ W ∧ Scheme.Modules.IsFrameOn s W := by
    intro x₀ hx₀
    have he := hUframe (ix x₀)
    have hcoef : ∀ x, ∃! c : Γ(X, U (ix x₀)),
        c • M.presheaf.map (homOfLE (le_top : U (ix x₀) ≤ ⊤)).op (𝔓.σ (ix x₀)) =
          M.presheaf.map (homOfLE (le_top : U (ix x₀) ≤ ⊤)).op (𝔓.σ (ix x)) :=
      fun x => he.existsUnique le_top le_rfl _
    choose c hc hcuniq using hcoef
    have hc₀ : c x₀ = 1 := (hcuniq x₀ 1 (one_smul _ _)).symm ▸ rfl
    let G : Γ(X, U (ix x₀)) := ∑ x ∈ F, X.presheaf.map (homOfLE (le_top : U (ix x₀) ≤ ⊤)).op (a x) * c x
    have hsG : M.presheaf.map (homOfLE (le_top : U (ix x₀) ≤ ⊤)).op s =
        G • M.presheaf.map (homOfLE (le_top : U (ix x₀) ≤ ⊤)).op (𝔓.σ (ix x₀)) := by
      simp only [s, G, map_sum, map_smul', Finset.sum_smul, mul_smul, hc]
    have hGx₀ : IsUnit (X.presheaf.germ (U (ix x₀)) x₀ (hix x₀) G) := by
      have hsplit : G = X.presheaf.map (homOfLE (le_top : U (ix x₀) ≤ ⊤)).op (a x₀) +
          ∑ x ∈ F.erase x₀, X.presheaf.map (homOfLE (le_top : U (ix x₀) ≤ ⊤)).op (a x) * c x := by
        simp only [G]
        rw [← Finset.add_sum_erase F _ hx₀, hc₀, mul_one]
      rw [hsplit, map_add, map_sum]
      apply isUnit_add_of_mem_maximalIdeal
      · rw [X.presheaf.germ_res_apply (homOfLE _) x₀ (hix x₀)]
        exact (X.mem_basicOpen (a x₀) x₀ trivial).mp ((hbasic x₀ (a x₀)).mpr (ha_self x₀ hx₀))
      · refine Ideal.sum_mem _ fun x hx => ?_
        obtain ⟨hxx₀, hxF⟩ := Finset.mem_erase.mp hx
        rw [map_mul]
        refine Ideal.mul_mem_right _ _ ?_
        rw [X.presheaf.germ_res_apply (homOfLE _) x₀ (hix x₀), IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
        exact fun hu => ((hbasic x₀ (a x)).mp ((X.mem_basicOpen (a x) x₀ trivial).mpr hu)) (ha_other x hxF x₀ hx₀ hxx₀.symm)
    refine ⟨X.basicOpen G, (X.mem_basicOpen G x₀ (hix x₀)).mpr hGx₀, ?_⟩
    have hWU : X.basicOpen G ≤ U (ix x₀) := X.basicOpen_le G
    refine isFrameOn_of_eq_unit_smul (U := ⊤) (U' := ⊤) le_top le_top (he.mono hWU) s
      (X.presheaf.map (homOfLE hWU).op G) (RingedSpace.isUnit_res_basicOpen _ G) ?_
    have := congrArg (M.presheaf.map (homOfLE hWU).op) hsG
    rw [map_smul', ← CategoryTheory.comp_apply, ← Functor.map_comp, ← CategoryTheory.comp_apply,
      ← Functor.map_comp] at this
    exact this
  choose! Wf hWf_mem hWf_frame using hsframe
  let Wtot : X.Opens := ⨆ x : F, Wf x
  have hstot : Scheme.Modules.IsFrameOn s Wtot := Scheme.Modules.IsFrameOn.of_iSup _ fun x => hWf_frame x x.2
  exact ⟨s, Wtot, fun x hx => Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hWf_mem x hx⟩, hstot⟩

noncomputable def pb2 {X₀ X₁ X₂ : Scheme.{u}} (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂) (L : X₂.Modules) :
    (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj L) ≅ (Scheme.Modules.pullback (f ≫ g)).obj L :=
  (Scheme.Modules.pullbackComp f g).app L

theorem nonempty_iso_unit_of_iso_comp {X' Y' Y'' : Scheme.{u}} {K : X'.Modules} (f : Y' ⟶ X') (f' : Y'' ⟶ X')
    (e : Y'' ⟶ Y') [IsIso e] (hef : e ≫ f = f')
    (h : Nonempty ((Scheme.Modules.pullback f).obj K ≅ SheafOfModules.unit Y'.ringCatSheaf)) :
    Nonempty ((Scheme.Modules.pullback f').obj K ≅ SheafOfModules.unit Y''.ringCatSheaf) :=
  ⟨(Scheme.Modules.pullbackCongr hef.symm).app K ≪≫ (pb2 e f K).symm ≪≫
    (Scheme.Modules.pullback e).mapIso h.some ≪≫ Scheme.Modules.pullbackUnitIso e⟩

end AlgebraicGeometry.Scheme.Modules.SemilocalOneSection

open AlgebraicGeometry.Scheme.Modules.SemilocalOneSection in

theorem solution
    {X : Scheme.{u}} (L : X.Modules) (hL : Scheme.Modules.IsInvertible L)
    (U : X.Opens) (hU : IsAffineOpen U)
    (T : Set X) (hT : T.Finite) (hTU : T ⊆ (U : Set X)) (hTcl : ∀ t ∈ T, IsClosed ({t} : Set X)) :
    ∃ (V : X.Opens) (hVU : V ≤ U) (s : Γ(L, V)), T ⊆ (V : Set X) ∧ Scheme.Modules.IsFrameOn s V := by
  classical
  haveI : IsAffine U := hU
  let g : (U : Scheme.{u}) ⟶ Spec (.of Γ(X, U)) := hU.isoSpec.hom
  haveI : IsFinite g := inferInstance

  have hTfin : ((fun x : (U : Scheme.{u}) => (x.1 : X)) ⁻¹' T).Finite :=
    hT.preimage (Subtype.val_injective.injOn)
  let F : Finset (U : Scheme.{u}) := hTfin.toFinset
  have hF : ∀ x : (U : Scheme.{u}), x ∈ F ↔ (x.1 : X) ∈ T := fun x => by
    rw [Set.Finite.mem_toFinset]; exact Iff.rfl
  have hFcl : ∀ x ∈ F, IsClosed ({x} : Set (U : Scheme.{u})) := by
    intro x hx
    have h1 : IsClosed ((fun y : (U : Scheme.{u}) => (y.1 : X)) ⁻¹' {(x.1 : X)}) :=
      (hTcl _ ((hF x).mp hx)).preimage continuous_subtype_val
    have h2 : ((fun y : (U : Scheme.{u}) => (y.1 : X)) ⁻¹' {(x.1 : X)}) = {x} := by
      ext y
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      exact ⟨fun h => Subtype.ext h, fun h => h ▸ rfl⟩
    rwa [h2] at h1

  obtain ⟨s₀, Wtot, hFW, hstot⟩ := core g (hL.pullback U.ι) F hFcl
  obtain ⟨t⟩ := hstot.nonempty_pullback_iso_unit Wtot le_top le_rfl

  let V : X.Opens := U.ι ''ᵁ Wtot
  have hrange : Set.range ⇑(Wtot.ι ≫ U.ι).base = Set.range ⇑V.ι.base := by
    have hc : ⇑(Wtot.ι ≫ U.ι).base = ⇑U.ι.base ∘ ⇑Wtot.ι.base := rfl
    rw [hc, Set.range_comp, Scheme.Opens.range_ι, Scheme.Opens.range_ι]
    rfl
  let e := IsOpenImmersion.isoOfRangeEq _ _ hrange
  have he : e.hom ≫ V.ι = Wtot.ι ≫ U.ι := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ hrange
  obtain ⟨eV⟩ := nonempty_iso_unit_of_iso_comp (K := L) (Wtot.ι ≫ U.ι) V.ι e.inv (by rw [Iso.inv_comp_eq, he])
    ⟨(pb2 _ _ L).symm ≪≫ t⟩
  obtain ⟨s, hs⟩ := Scheme.Modules.exists_isFrameOn_of_pullback_iso_unit V eV
  refine ⟨V, U.ι_image_le Wtot, s, ?_, hs⟩
  intro x hx
  exact ⟨⟨x, hTU hx⟩, hFW _ ((hF ⟨x, hTU hx⟩).mpr hx), rfl⟩

end S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_isFrameOn_of_finite_subset_affineOpen
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_isFrameOn_of_finite_subset_affineOpen (solution)
