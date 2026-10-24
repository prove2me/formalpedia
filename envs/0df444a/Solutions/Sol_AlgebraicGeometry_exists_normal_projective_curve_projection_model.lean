-- Prove2me | solution 1 for AlgebraicGeometry.exists_normal_projective_curve_projection_model
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-23T19:13:19.029629+00:00
-- url     : https://prove2.me/submissions/ba7b6ba4-14f5-4a46-a320-45bb2094f315

import Definitions.Def_AlgebraicGeometry_ModulesGlueOfCocycle
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Mathlib
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isIntegral_image_and_isIso_stalkMap_toImage_genericPoint
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top
import Theorems.Thm_AlgebraicGeometry_exists_dense_affine_separating_function_field_parameters
import Theorems.Thm_AlgebraicGeometry_exists_isClosedImmersion_projSpace_pullback_of_isClosedImmersion
import Theorems.Thm_AlgebraicGeometry_exists_isFinite_isIntegrallyClosed_stalk_isIso_morphismRestrict_of_isIntegral
import Theorems.Thm_AlgebraicGeometry_toENat_trdeg_residueField_eq_topologicalKrullDim_closure
import Theorems.Thm_HomogeneousIdeal_exists_homogeneous_pos_mem_forall_notMem

universe u v


open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules.GlueOfCocycle

namespace PhilipponFiniteCocycle
variable {X : Scheme.{u}} {r : ℕ}

/-- A finite chart cocycle, without equating the index and scheme universes. -/
structure UnitCocycle (V : Fin r → X.Opens) where
  u : ∀ i j, Γ(X, V i ⊓ V j)
  refl : ∀ i, u i i = 1
  cocycle : ∀ i j k,
    rO (le_inf (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right) :
      V i ⊓ V j ⊓ V k ≤ V i ⊓ V j) (u i j) *
    rO (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
      V i ⊓ V j ⊓ V k ≤ V j ⊓ V k) (u j k) =
    rO (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
      V i ⊓ V j ⊓ V k ≤ V i ⊓ V k) (u i k)

variable {V : Fin r → X.Opens}

def UnitCocycle.lift (c : UnitCocycle V) :
    Scheme.Modules.UnitCocycle (fun i : ULift.{u} (Fin r) => V i.down) where
  u i j := c.u i.down j.down
  refl i := c.refl i.down
  cocycle i j k := c.cocycle i.down j.down k.down

noncomputable abbrev glueOfCocycle (c : UnitCocycle V) : X.Modules :=
  Scheme.Modules.glueOfCocycle c.lift

noncomputable abbrev glueComponent (c : UnitCocycle V) (T : X.Opens) (i : Fin r) :=
  Scheme.Modules.glueComponent c.lift T (ULift.up i)

lemma leij (T : X.Opens) (i j : Fin r) : T ⊓ (V i ⊓ V j) ≤ V i ⊓ V j := inf_le_right

noncomputable abbrev glueMk (c : UnitCocycle V) (T : X.Opens)
    (x : ∀ i, Γ(X, T ⊓ V i))
    (hx : ∀ i j,
      rO (inf_le_inf_left T inf_le_left : T ⊓ (V i ⊓ V j) ≤ T ⊓ V i) (x i) =
      rO (leij T i j) (c.u i j) *
      rO (inf_le_inf_left T inf_le_right : T ⊓ (V i ⊓ V j) ≤ T ⊓ V j) (x j)) :
    Γ(glueOfCocycle c, T) :=
  Scheme.Modules.glueMk c.lift T (fun i => x i.down) (fun i j => hx i.down j.down)

noncomputable abbrev glueFrame (c : UnitCocycle V) (i : Fin r) :=
  Scheme.Modules.glueFrame c.lift (ULift.up i)

lemma glue_ext (c : UnitCocycle V) {T : X.Opens} {p q : Γ(glueOfCocycle c, T)}
    (h : ∀ i, glueComponent c T i p = glueComponent c T i q) : p = q :=
  Scheme.Modules.glue_ext c.lift (fun i => h i.down)

lemma glueComponent_map (c : UnitCocycle V) {T T' : X.Opens} (h : T' ≤ T)
    (i : Fin r) (p : Γ(glueOfCocycle c, T)) :
    glueComponent c T' i ((glueOfCocycle c).presheaf.map (homOfLE h).op p) =
      rO (inf_le_inf_right (V i) h) (glueComponent c T i p) := rfl

lemma glueComponent_smul (c : UnitCocycle V) {T : X.Opens} (g : Γ(X, T))
    (i : Fin r) (p : Γ(glueOfCocycle c, T)) :
    glueComponent c T i (g • p) = rO inf_le_left g * glueComponent c T i p := rfl

lemma glueComponent_glueFrame (c : UnitCocycle V) (i k : Fin r) :
    glueComponent c (V i) k (glueFrame c i) =
      rO (le_of_eq (inf_comm (V i) (V k))) (c.u k i) := rfl

lemma isFrameOn_glueFrame (c : UnitCocycle V) (i : Fin r) :
    Scheme.Modules.IsFrameOn (glueFrame c i) (V i) :=
  Scheme.Modules.isFrameOn_glueFrame c.lift (ULift.up i)

end PhilipponFiniteCocycle


-- Generalizes the accepted FLT chart constructions to arbitrary universes.
-- Original accepted sources and their hashes are archived in the work directory.
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite HomogeneousLocalization
attribute [local instance] MvPolynomial.gradedAlgebra


set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_mem_isAffineOpen_isClosedImmersion_morphismRestrict_basicOpen_of_isImmersion_proj

set_option autoImplicit false


open CategoryTheory

namespace AlgebraicGeometry

namespace A1ChartFin

variable {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]

theorem Proj.exists_basicOpen_le_forall_mem_of_finset (U : (Proj 𝒜).Opens) (S : Finset (Proj 𝒜))
    (hS : ∀ x ∈ S, x ∈ U) :
    ∃ (n : ℕ) (f : A), 0 < n ∧ f ∈ 𝒜 n ∧ Proj.basicOpen 𝒜 f ≤ U ∧ ∀ x ∈ S, x ∈ Proj.basicOpen 𝒜 f := by
  classical
  set Z : Set (Proj 𝒜) := (U : Set (Proj 𝒜))ᶜ with hZdef
  have hZ : IsClosed Z := U.isOpen.isClosed_compl
  set J : HomogeneousIdeal 𝒜 := ProjectiveSpectrum.vanishingIdeal Z with hJdef
  have hZJ : ProjectiveSpectrum.zeroLocus 𝒜 (J : Set A) = Z := by
    rw [hJdef, ProjectiveSpectrum.zeroLocus_vanishingIdeal_eq_closure]
    exact hZ.closure_eq
  have havoid : ∀ p ∈ S.image (fun x : Proj 𝒜 => x.asHomogeneousIdeal),
      ¬ (J ⊓ HomogeneousIdeal.irrelevant 𝒜 ≤ p) := by
    intro p hp hle
    obtain ⟨x, hxS, rfl⟩ := Finset.mem_image.mp hp
    change (J ⊓ HomogeneousIdeal.irrelevant 𝒜).toIdeal ≤ x.asHomogeneousIdeal.toIdeal at hle
    rw [HomogeneousIdeal.toIdeal_inf, x.isPrime.inf_le] at hle
    rcases hle with hle | hle
    · have hxZ : x ∈ Z := by
        rw [← hZJ]
        exact (ProjectiveSpectrum.mem_zeroLocus 𝒜 x _).mpr hle
      exact hxZ (hS x hxS)
    · exact x.not_irrelevant_le hle
  obtain ⟨n, f, hn, hfn, hfI, hf⟩ :=
    (J ⊓ HomogeneousIdeal.irrelevant 𝒜).exists_homogeneous_pos_mem_forall_notMem inf_le_right
      (S.image fun x : Proj 𝒜 => x.asHomogeneousIdeal)
      (fun p hp => by
        obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hp
        exact x.isPrime)
      havoid
  refine ⟨n, f, hn, hfn, ?_, ?_⟩
  · intro y hy
    by_contra hyU
    have hyZ : y ∈ Z := hyU
    rw [← hZJ] at hyZ
    have hfJ : f ∈ J := (inf_le_left : J ⊓ HomogeneousIdeal.irrelevant 𝒜 ≤ J) hfI
    exact (Proj.mem_basicOpen 𝒜 f y).mp hy ((ProjectiveSpectrum.mem_zeroLocus 𝒜 y _).mp hyZ hfJ)
  · intro x hx
    rw [Proj.mem_basicOpen]
    exact hf _ (Finset.mem_image_of_mem _ hx)

end A1ChartFin

theorem A1ChartFin.isAffineOpen_ι_preimage_of_le {Y : Scheme.{u}} {U V : Y.Opens} (hV : IsAffineOpen V) (h : V ≤ U) :
    IsAffineOpen (U.ι ⁻¹ᵁ V) := by
  have himg : IsAffineOpen (U.ι ''ᵁ (U.ι ⁻¹ᵁ V)) := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_eq_right.mpr h]
    exact hV
  haveI : IsAffine (U.ι ''ᵁ U.ι ⁻¹ᵁ V) := himg
  exact IsAffine.of_isIso (U.ι.isoImage (U.ι ⁻¹ᵁ V)).hom

theorem A1ChartFin.isClosedImmersion_morphismRestrict_of_le_coborderRange {X Y : Scheme.{u}} (ι : X ⟶ Y) [IsImmersion ι]
    (W : Y.Opens) (hW : W ≤ ι.coborderRange) : IsClosedImmersion (ι ∣_ W) := by
  apply IsClosedImmersion.of_isPreimmersion
  have hsub : (Subtype.val : ↥W → ↥Y) ⁻¹' coborder (Set.range ι) = Set.univ :=
    Set.eq_univ_of_forall fun w => hW w.2
  have hcl : (Subtype.val : ↥W → ↥Y) ⁻¹' Set.range ι =
      (Subtype.val : ↥W → ↥Y) ⁻¹' closure (Set.range ι) := by
    conv_lhs => rw [← coborder_inter_closure (s := Set.range ι)]
    rw [Set.preimage_inter, hsub, Set.univ_inter]
  have key : IsClosed ((Subtype.val : ↥W → ↥Y) ⁻¹' Set.range ι) := by
    rw [hcl]; exact isClosed_closure.preimage continuous_subtype_val
  rw [morphismRestrict_base]
  erw [Set.range_restrictPreimage]
  exact key

end AlgebraicGeometry

open _root_.AlgebraicGeometry _root_.P2MW.S_AlgebraicGeometry_exists_mem_isAffineOpen_isClosedImmersion_morphismRestrict_basicOpen_of_isImmersion_proj.AlgebraicGeometry in
theorem solution
    {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]
    {X : Scheme.{u}} (ι : X ⟶ Proj 𝒜) [IsImmersion ι] (S : Finset X) :
    ∃ (d : ℕ) (F : A) (_ : F ∈ 𝒜 d), 0 < d ∧ (∀ x ∈ S, x ∈ ι ⁻¹ᵁ Proj.basicOpen 𝒜 F) ∧
      IsAffineOpen (ι ⁻¹ᵁ Proj.basicOpen 𝒜 F) ∧ IsClosedImmersion (ι ∣_ Proj.basicOpen 𝒜 F) := by
  classical
  set U := ι.coborderRange with hU
  set g := ι.liftCoborder with hgdef
  have hg : g ≫ U.ι = ι := ι.liftCoborder_ι
  obtain ⟨n, F, hn, hFn, hle, hmem⟩ := A1ChartFin.Proj.exists_basicOpen_le_forall_mem_of_finset 𝒜 U (S.image ι.base) (by
    intro y hy
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hy
    rw [← hg]
    exact (g.base x).2)
  refine ⟨n, F, hFn, hn, ?_, ?_, ?_⟩
  · intro x hx
    exact hmem _ (Finset.mem_image_of_mem _ hx)
  · have H : IsAffineOpen ((g ≫ U.ι) ⁻¹ᵁ Proj.basicOpen 𝒜 F) :=
      (A1ChartFin.isAffineOpen_ι_preimage_of_le (Proj.isAffineOpen_basicOpen 𝒜 F hFn hn) hle).preimage g
    rwa [hg] at H
  · exact A1ChartFin.isClosedImmersion_morphismRestrict_of_le_coborderRange ι _ hle

end S_AlgebraicGeometry_exists_mem_isAffineOpen_isClosedImmersion_morphismRestrict_basicOpen_of_isImmersion_proj
end P2MW


set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Proj_exists_cocycle_basicOpen_eq_inf_of_mem_of_pos

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite HomogeneousLocalization

theorem solution
    {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]
    {d : ℕ} (hd : 0 < d) {r : ℕ} (F : Fin r → A) (hF : ∀ i : Fin r, F i ∈ 𝒜 d) :
    ∃ w : ∀ i j : Fin r, Γ(Proj 𝒜, Proj.basicOpen 𝒜 (F i)),
      (∀ i : Fin r, IsAffineOpen (Proj.basicOpen 𝒜 (F i))) ∧
      (∀ i : Fin r, w i i = 1) ∧
      (∀ i j k : Fin r,
        (Proj 𝒜).presheaf.map (homOfLE (inf_le_left : Proj.basicOpen 𝒜 (F i) ⊓ Proj.basicOpen 𝒜 (F j) ≤ Proj.basicOpen 𝒜 (F i))).op (w i k) =
          (Proj 𝒜).presheaf.map (homOfLE (inf_le_left : Proj.basicOpen 𝒜 (F i) ⊓ Proj.basicOpen 𝒜 (F j) ≤ Proj.basicOpen 𝒜 (F i))).op (w i j) *
            (Proj 𝒜).presheaf.map (homOfLE (inf_le_right : Proj.basicOpen 𝒜 (F i) ⊓ Proj.basicOpen 𝒜 (F j) ≤ Proj.basicOpen 𝒜 (F j))).op (w j k)) ∧
      (∀ i j : Fin r, (Proj 𝒜).basicOpen (w i j) = Proj.basicOpen 𝒜 (F i) ⊓ Proj.basicOpen 𝒜 (F j)) := by
  classical

  have res_res : ∀ {P : Scheme.{u}} {U₁ U₂ U₃ : P.Opens} (h₁ : U₁ ≤ U₂) (h₂ : U₂ ≤ U₃) (x : Γ(P, U₃)),
      P.presheaf.map (homOfLE h₁).op (P.presheaf.map (homOfLE h₂).op x) =
        P.presheaf.map (homOfLE (h₁.trans h₂)).op x := by
    intro P U₁ U₂ U₃ h₁ h₂ x
    rw [← CommRingCat.comp_apply, ← Functor.map_comp]
    rfl

  have res_inj : ∀ {P : Scheme.{u}} {U₁ U₂ : P.Opens} (e : U₁ = U₂) (x y : Γ(P, U₂)),
      P.presheaf.map (homOfLE e.le).op x = P.presheaf.map (homOfLE e.le).op y → x = y := by
    intro P U₁ U₂ e x y h
    subst e
    have : (homOfLE (le_refl U₁)).op = 𝟙 _ := Quiver.Hom.unop_inj (Subsingleton.elim _ _)
    simpa [this] using h

  let q : ∀ i j : Fin r, Away 𝒜 (F i) := fun i j =>
    Away.mk 𝒜 (hF i) 1 (F j) (by simpa only [one_smul] using hF j)
  have hV : ∀ i : Fin r, IsAffineOpen (Proj.basicOpen 𝒜 (F i)) := fun i =>
    Proj.isAffineOpen_basicOpen 𝒜 (F i) (hF i) hd
  refine ⟨fun i j => Proj.awayToSection 𝒜 (F i) (q i j), hV, ?_, ?_, ?_⟩
  ·
    intro i
    have : q i i = 1 := by
      apply HomogeneousLocalization.val_injective
      rw [HomogeneousLocalization.val_one]
      simp only [q, Away.val_mk]
      rw [← Localization.mk_one, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
      exact ⟨1, by simp⟩
    show Proj.awayToSection 𝒜 (F i) (q i i) = 1
    rw [this, map_one]
  ·
    intro i j k
    have e : Proj.basicOpen 𝒜 (F i * F j) = Proj.basicOpen 𝒜 (F i) ⊓ Proj.basicOpen 𝒜 (F j) :=
      Proj.basicOpen_mul 𝒜 (F i) (F j)
    apply res_inj e
    simp only [map_mul, res_res]

    have h1 := congrArg (fun φ => φ.hom (q i k))
      (Proj.awayMap_awayToSection 𝒜 (f := F i) (hF j) (x := F i * F j) rfl)
    have h2 := congrArg (fun φ => φ.hom (q i j))
      (Proj.awayMap_awayToSection 𝒜 (f := F i) (hF j) (x := F i * F j) rfl)
    have h3 := congrArg (fun φ => φ.hom (q j k))
      (Proj.awayMap_awayToSection 𝒜 (f := F j) (hF i) (x := F i * F j) (mul_comm _ _))
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom] at h1 h2 h3

    rw [show (Proj 𝒜).presheaf.map (homOfLE (e.le.trans inf_le_left)).op (Proj.awayToSection 𝒜 (F i) (q i k)) = _ from h1.symm,
      show (Proj 𝒜).presheaf.map (homOfLE (e.le.trans inf_le_left)).op (Proj.awayToSection 𝒜 (F i) (q i j)) = _ from h2.symm,
      show (Proj 𝒜).presheaf.map (homOfLE (e.le.trans inf_le_right)).op (Proj.awayToSection 𝒜 (F j) (q j k)) = _ from h3.symm,
      ← map_mul]
    congr 1
    apply HomogeneousLocalization.val_injective
    simp only [q, HomogeneousLocalization.awayMap_mk, HomogeneousLocalization.val_mul, Away.val_mk, Localization.mk_mul]
    rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
    refine ⟨1, ?_⟩
    simp only [OneMemClass.coe_one, Submonoid.coe_mul, one_mul]
    ring
  ·
    intro i j

    have hfrom : (hV i).fromSpec = Spec.map (Proj.awayToSection 𝒜 (F i)) ≫ Proj.awayι 𝒜 (F i) (hF i) hd := by
      rw [← Proj.basicOpenIsoSpec_inv_ι, ← IsAffineOpen.isoSpec_inv_ι, ← Category.assoc]
      congr 1
      rw [← cancel_epi (hV i).isoSpec.hom, Iso.hom_inv_id, IsAffineOpen.isoSpec_hom, ← Category.assoc]
      show 𝟙 _ = Proj.basicOpenToSpec 𝒜 (F i) ≫ _
      rw [← Proj.basicOpenIsoSpec_hom 𝒜 (F i) (hF i) hd, Iso.hom_inv_id]

    have hpre : (hV i).fromSpec ⁻¹ᵁ Proj.basicOpen 𝒜 (F j) =
        PrimeSpectrum.basicOpen (Proj.awayToSection 𝒜 (F i) (q i j)) := by
      rw [hfrom, Scheme.Hom.comp_preimage, Proj.awayι_preimage_basicOpen 𝒜 (hF i) hd (hF j) hd]
      have hq : Away.isLocalizationElem (hF i) (hF j) = q i j ^ d := by
        apply HomogeneousLocalization.val_injective
        simp only [q, Away.isLocalizationElem, Away.val_mk, HomogeneousLocalization.val_pow, Localization.mk_pow]
        congr 1
        exact Subtype.ext (by simp [← pow_mul, pow_one])
      rw [hq]
      conv_rhs => rw [← PrimeSpectrum.basicOpen_pow _ d hd, ← map_pow]
      ext1
      rfl
    rw [← (hV i).fromSpec_image_basicOpen, ← hpre, Scheme.Hom.image_preimage_eq_opensRange_inf,
      IsAffineOpen.opensRange_fromSpec]

end S_AlgebraicGeometry_Proj_exists_cocycle_basicOpen_eq_inf_of_mem_of_pos
end P2MW


set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Hom_app_cocycle_and_basicOpen_app_eq_inf_of_basicOpen_eq_inf

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

theorem solution
    {X Z : Scheme.{u}} (f : X ⟶ Z) {r : ℕ} (V : Fin r → Z.Opens) (w : ∀ i j : Fin r, Γ(Z, V i))
    (hW1 : ∀ i, w i i = 1)
    (hW2 : ∀ i j k : Fin r,
      Z.presheaf.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (w i k) =
        Z.presheaf.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (w i j) *
          Z.presheaf.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op (w j k))
    (hW3 : ∀ i j : Fin r, Z.basicOpen (w i j) = V i ⊓ V j) :
    (∀ i : Fin r, f.app (V i) (w i i) = 1) ∧
    (∀ i j k : Fin r,
      X.presheaf.map (homOfLE (inf_le_left : f ⁻¹ᵁ V i ⊓ f ⁻¹ᵁ V j ≤ f ⁻¹ᵁ V i)).op (f.app (V i) (w i k)) =
        X.presheaf.map (homOfLE (inf_le_left : f ⁻¹ᵁ V i ⊓ f ⁻¹ᵁ V j ≤ f ⁻¹ᵁ V i)).op (f.app (V i) (w i j)) *
          X.presheaf.map (homOfLE (inf_le_right : f ⁻¹ᵁ V i ⊓ f ⁻¹ᵁ V j ≤ f ⁻¹ᵁ V j)).op (f.app (V j) (w j k))) ∧
    (∀ i j : Fin r, X.basicOpen (f.app (V i) (w i j)) = f ⁻¹ᵁ V i ⊓ f ⁻¹ᵁ V j) := by

  have nat : ∀ {U U' : Z.Opens} {W : X.Opens} (h : U ≤ U') (h' : W ≤ f ⁻¹ᵁ U') (h'' : W ≤ f ⁻¹ᵁ U)
      (x : Γ(Z, U')),
      X.presheaf.map (homOfLE h').op (f.app U' x) =
        X.presheaf.map (homOfLE h'').op (f.app U (Z.presheaf.map (homOfLE h).op x)) := by
    intro U U' W h h' h'' x
    have e := congrArg (fun φ => (X.presheaf.map (homOfLE h'').op).hom (φ.hom x)) (f.naturality (homOfLE h).op)
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at e
    have hh : (homOfLE h').op = ((Opens.map f.base).map (homOfLE h).op.unop).op ≫ (homOfLE h'').op :=
      Quiver.Hom.unop_inj (Subsingleton.elim _ _)
    rw [e]
    change _ = (X.presheaf.map ((Opens.map f.base).map (homOfLE h).op.unop).op ≫
      X.presheaf.map (homOfLE h'').op).hom (f.app U' x)
    rw [← Functor.map_comp, ← hh]
  have hpre : ∀ i j : Fin r, f ⁻¹ᵁ V i ⊓ f ⁻¹ᵁ V j ≤ f ⁻¹ᵁ (V i ⊓ V j) := fun i j x hx => hx
  refine ⟨fun i => by rw [hW1, map_one], fun i j k => ?_, fun i j => ?_⟩
  · rw [nat (inf_le_left : V i ⊓ V j ≤ V i) inf_le_left (hpre i j) (w i k),
      nat (inf_le_left : V i ⊓ V j ≤ V i) inf_le_left (hpre i j) (w i j),
      nat (inf_le_right : V i ⊓ V j ≤ V j) inf_le_right (hpre i j) (w j k), hW2, map_mul, map_mul]
  · rw [← Scheme.preimage_basicOpen, hW3]
    rfl

end S_AlgebraicGeometry_Scheme_Hom_app_cocycle_and_basicOpen_app_eq_inf_of_basicOpen_eq_inf
end P2MW



set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_exists_forall_exists_eq_and_map_eq_pow_mul_map_of_basicOpen_eq_inf

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

theorem solution
    {Z : Scheme.{u}} {r : ℕ} (V : Fin r → Z.Opens) (hV : ∀ i, IsAffineOpen (V i))
    (w : ∀ i j : Fin r, Γ(Z, V i))
    (hW1 : ∀ i, w i i = 1)
    (hW2 : ∀ i j k : Fin r,
      Z.presheaf.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (w i k) =
        Z.presheaf.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (w i j) *
          Z.presheaf.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op (w j k))
    (hW3 : ∀ i j : Fin r, Z.basicOpen (w i j) = V i ⊓ V j)
    (i₀ : Fin r) (g : Γ(Z, V i₀)) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → ∃ t : ∀ j : Fin r, Γ(Z, V j), t i₀ = g ∧
      ∀ j m : Fin r,
        Z.presheaf.map (homOfLE (inf_le_left : V j ⊓ V m ≤ V j)).op (t j) =
          Z.presheaf.map (homOfLE (inf_le_left : V j ⊓ V m ≤ V j)).op (w j m) ^ k *
            Z.presheaf.map (homOfLE (inf_le_right : V j ⊓ V m ≤ V m)).op (t m) := by
  classical

  have res_res : ∀ {A B C : Z.Opens} (h₁ : A ≤ B) (h₂ : B ≤ C) (x : Γ(Z, C)),
      Z.presheaf.map (homOfLE h₁).op (Z.presheaf.map (homOfLE h₂).op x) =
        Z.presheaf.map (homOfLE (h₁.trans h₂)).op x := by
    intro A B C h₁ h₂ x
    rw [← CommRingCat.comp_apply, ← Functor.map_comp]
    rfl

  have stepA : ∀ j : Fin r, ∃ (a : Γ(Z, V j)) (n : ℕ),
      Z.presheaf.map (homOfLE (inf_le_left : V j ⊓ V i₀ ≤ V j)).op a =
        Z.presheaf.map (homOfLE (inf_le_left : V j ⊓ V i₀ ≤ V j)).op (w j i₀) ^ n *
          Z.presheaf.map (homOfLE (inf_le_right : V j ⊓ V i₀ ≤ V i₀)).op g := by
    intro j
    letI : Algebra Γ(Z, V j) Γ(Z, V j ⊓ V i₀) :=
      (Z.presheaf.map (homOfLE (inf_le_left : V j ⊓ V i₀ ≤ V j)).op).hom.toAlgebra
    haveI : IsLocalization.Away (w j i₀) Γ(Z, V j ⊓ V i₀) :=
      (hV j).isLocalization_of_eq_basicOpen (w j i₀) (homOfLE inf_le_left) (hW3 j i₀).symm
    obtain ⟨⟨a, ⟨s, ⟨n, rfl⟩⟩⟩, h⟩ := IsLocalization.surj (Submonoid.powers (w j i₀))
      (Z.presheaf.map (homOfLE (inf_le_right : V j ⊓ V i₀ ≤ V i₀)).op g)
    refine ⟨a, n, ?_⟩
    simp only [RingHom.algebraMap_toAlgebra, map_pow] at h
    rw [← h, mul_comm]
  choose a₀ n₀ ha₀ using stepA

  let a : ∀ j : Fin r, Γ(Z, V j) := Function.update a₀ i₀ g
  let n : Fin r → ℕ := Function.update n₀ i₀ 0
  have ha : ∀ j, Z.presheaf.map (homOfLE (inf_le_left : V j ⊓ V i₀ ≤ V j)).op (a j) =
      Z.presheaf.map (homOfLE (inf_le_left : V j ⊓ V i₀ ≤ V j)).op (w j i₀) ^ n j *
        Z.presheaf.map (homOfLE (inf_le_right : V j ⊓ V i₀ ≤ V i₀)).op g := by
    intro j
    by_cases hj : j = i₀
    · subst hj
      simp only [a, n, Function.update_self, pow_zero, one_mul]
    · simp only [a, n, Function.update_of_ne hj]
      exact ha₀ j

  let k₁ : ℕ := Finset.univ.sup n
  have hn : ∀ j, n j ≤ k₁ := fun j => Finset.le_sup (f := n) (Finset.mem_univ j)
  let b : ∀ j : Fin r, Γ(Z, V j) := fun j => a j * w j i₀ ^ (k₁ - n j)
  have hb : ∀ j, Z.presheaf.map (homOfLE (inf_le_left : V j ⊓ V i₀ ≤ V j)).op (b j) =
      Z.presheaf.map (homOfLE (inf_le_left : V j ⊓ V i₀ ≤ V j)).op (w j i₀) ^ k₁ *
        Z.presheaf.map (homOfLE (inf_le_right : V j ⊓ V i₀ ≤ V i₀)).op g := by
    intro j
    simp only [b, map_mul, map_pow, ha]
    rw [mul_right_comm, ← pow_add, Nat.add_sub_cancel' (hn j)]
  have hbi₀ : b i₀ = g := by
    simp only [b, a, n, Function.update_self, hW1, one_pow, mul_one]

  have stepB : ∀ j m : Fin r, ∃ e : ℕ,
      Z.presheaf.map (homOfLE (inf_le_left : V j ⊓ V m ≤ V j)).op (w j i₀) ^ e *
        (Z.presheaf.map (homOfLE (inf_le_left : V j ⊓ V m ≤ V j)).op (b j) -
          Z.presheaf.map (homOfLE (inf_le_left : V j ⊓ V m ≤ V j)).op (w j m) ^ k₁ *
            Z.presheaf.map (homOfLE (inf_le_right : V j ⊓ V m ≤ V m)).op (b m)) = 0 := by
    intro j m
    have hjm : IsAffineOpen (V j ⊓ V m) := by rw [← hW3 j m]; exact (hV j).basicOpen (w j m)

    have hT : (V j ⊓ V m) ⊓ (V j ⊓ V i₀) =
        Z.basicOpen (Z.presheaf.map (homOfLE (inf_le_left : V j ⊓ V m ≤ V j)).op (w j i₀)) := by
      rw [Scheme.basicOpen_res, hW3]
    letI : Algebra Γ(Z, V j ⊓ V m) Γ(Z, (V j ⊓ V m) ⊓ (V j ⊓ V i₀)) :=
      (Z.presheaf.map (homOfLE (inf_le_left : (V j ⊓ V m) ⊓ (V j ⊓ V i₀) ≤ V j ⊓ V m)).op).hom.toAlgebra
    haveI : IsLocalization.Away (Z.presheaf.map (homOfLE (inf_le_left : V j ⊓ V m ≤ V j)).op (w j i₀))
        Γ(Z, (V j ⊓ V m) ⊓ (V j ⊓ V i₀)) :=
      hjm.isLocalization_of_eq_basicOpen _ (homOfLE inf_le_left) hT

    have hvan : Z.presheaf.map (homOfLE (inf_le_left : (V j ⊓ V m) ⊓ (V j ⊓ V i₀) ≤ V j ⊓ V m)).op
        (Z.presheaf.map (homOfLE (inf_le_left : V j ⊓ V m ≤ V j)).op (b j) -
          Z.presheaf.map (homOfLE (inf_le_left : V j ⊓ V m ≤ V j)).op (w j m) ^ k₁ *
            Z.presheaf.map (homOfLE (inf_le_right : V j ⊓ V m ≤ V m)).op (b m)) = 0 := by
      have e1 := congrArg (Z.presheaf.map (homOfLE
        (inf_le_right : (V j ⊓ V m) ⊓ (V j ⊓ V i₀) ≤ V j ⊓ V i₀)).op) (hb j)
      have e2 := congrArg (Z.presheaf.map (homOfLE
        (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right) :
          (V j ⊓ V m) ⊓ (V j ⊓ V i₀) ≤ V m ⊓ V i₀)).op) (hb m)
      have e3 := congrArg (Z.presheaf.map (homOfLE
        (inf_le_left : (V j ⊓ V m) ⊓ (V j ⊓ V i₀) ≤ V j ⊓ V m)).op) (hW2 j m i₀)
      simp only [map_sub, map_mul, map_pow, res_res] at e1 e2 e3 ⊢
      rw [e1, e2, e3]
      ring
    obtain ⟨⟨_, ⟨e, rfl⟩⟩, he⟩ := (IsLocalization.map_eq_zero_iff
      (Submonoid.powers (Z.presheaf.map (homOfLE (inf_le_left : V j ⊓ V m ≤ V j)).op (w j i₀)))
      Γ(Z, (V j ⊓ V m) ⊓ (V j ⊓ V i₀)) _).mp hvan
    exact ⟨e, he⟩
  choose e he using stepB

  let E : ℕ := Finset.univ.sup (fun jm : Fin r × Fin r => e jm.1 jm.2)
  have hE : ∀ j m, e j m ≤ E := fun j m =>
    Finset.le_sup (f := fun jm : Fin r × Fin r => e jm.1 jm.2) (Finset.mem_univ (j, m))
  refine ⟨k₁ + E, fun k hk => ⟨fun j => b j * w j i₀ ^ (k - k₁), ?_, ?_⟩⟩
  ·
    simp only [hbi₀, hW1, one_pow, mul_one]
  · intro j m
    obtain ⟨E', hE'⟩ : ∃ E', k = k₁ + (e j m + E') := ⟨k - k₁ - e j m, by have := hE j m; omega⟩
    have hkk : k - k₁ = e j m + E' := by omega
    have c := hW2 j m i₀
    have d := he j m
    simp only [map_mul, map_pow, hkk]
    rw [hE']
    rw [c] at d ⊢
    linear_combination ((Z.presheaf.map (homOfLE (inf_le_left : V j ⊓ V m ≤ V j)).op (w j m) *
      Z.presheaf.map (homOfLE (inf_le_right : V j ⊓ V m ≤ V m)).op (w m i₀)) ^ E') * d

end S_AlgebraicGeometry_Scheme_exists_forall_exists_eq_and_map_eq_pow_mul_map_of_basicOpen_eq_inf
end P2MW



set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Hom_isImmersion_of_forall_isAffineOpen_preimage_of_forall_surjective_app

set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

namespace QPC2


theorem isImmersion_respectsRight_isOpenImmersion :
    MorphismProperty.RespectsRight @IsImmersion @IsOpenImmersion :=
  ⟨fun i hi f hf => by haveI := hi; haveI := hf; infer_instance⟩

theorem surjective_app_of_eq {X Y : Scheme.{u}} (f : X ⟶ Y) (U V : Y.Opens) (e : V = U)
    (hs : Function.Surjective (f.app U)) : Function.Surjective (f.app V) := by
  subst e; exact hs

theorem isClosedImmersion_morphismRestrict_of_surjective {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U : Y.Opens) (hU : IsAffineOpen U) (hfU : IsAffineOpen (f ⁻¹ᵁ U))
    (hs : Function.Surjective (f.app U)) : IsClosedImmersion (f ∣_ U) := by
  haveI : IsAffine U := hU
  haveI : IsAffine (f ⁻¹ᵁ U) := hfU
  rw [HasAffineProperty.iff_of_isAffine (P := @IsClosedImmersion)]
  refine ⟨hfU, ?_⟩
  rw [morphismRestrict_appTop]
  have e : U.ι ''ᵁ ⊤ = U := by simp [Scheme.Hom.image_top_eq_opensRange]
  have h1 : Function.Surjective (f.app (U.ι ''ᵁ ⊤)) := surjective_app_of_eq f U _ e hs
  have h2 : Function.Surjective
      (X.presheaf.map (eqToHom (image_morphismRestrict_preimage f U ⊤)).op) :=
    (ConcreteCategory.bijective_of_isIso _).2
  intro y
  obtain ⟨z, rfl⟩ := h2 y
  obtain ⟨x, rfl⟩ := h1 z
  exact ⟨x, ConcreteCategory.comp_apply _ _ _⟩

theorem isImmersion_of_affine_charts {Y P : Scheme.{u}} (φ : Y ⟶ P) {J : Type*} (W : J → P.Opens)
    (hWaff : ∀ j, IsAffineOpen (W j)) (hYaff : ∀ j, IsAffineOpen (φ ⁻¹ᵁ W j))
    (hcov : ⨆ j, φ ⁻¹ᵁ W j = ⊤) (hsurj : ∀ j, Function.Surjective (φ.app (W j))) :
    IsImmersion φ := by
  haveI := isImmersion_respectsRight_isOpenImmersion
  have hrange : Set.range φ.base ⊆ ((⨆ j, W j : P.Opens) : Set P) := by
    rintro _ ⟨y, rfl⟩
    have hy : y ∈ (⨆ j, φ ⁻¹ᵁ W j : Y.Opens) := by rw [hcov]; trivial
    simp only [TopologicalSpace.Opens.mem_iSup] at hy
    obtain ⟨j, hj⟩ := hy
    simp only [TopologicalSpace.Opens.coe_iSup, Set.mem_iUnion, SetLike.mem_coe]
    exact ⟨j, hj⟩
  exact IsZariskiLocalAtTarget.of_range_subset_iSup (P := @IsImmersion) W hrange
    (fun j => by
      haveI := isClosedImmersion_morphismRestrict_of_surjective φ (W j) (hWaff j) (hYaff j) (hsurj j)
      infer_instance)

end QPC2

theorem solution
    {Y P : Scheme.{u}} (φ : Y ⟶ P) {J : Type v} (W : J → P.Opens)
    (hWaff : ∀ j, IsAffineOpen (W j)) (hYaff : ∀ j, IsAffineOpen (φ ⁻¹ᵁ W j))
    (hcov : ⨆ j, φ ⁻¹ᵁ W j = ⊤) (hsurj : ∀ j, Function.Surjective (φ.app (W j))) :
    IsImmersion φ :=
  QPC2.isImmersion_of_affine_charts φ W hWaff hYaff hcov hsurj

end S_AlgebraicGeometry_Scheme_Hom_isImmersion_of_forall_isAffineOpen_preimage_of_forall_surjective_app
end P2MW



set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_glueOfCocycle_preimage_basicOpen_eq_of_basicOpen_eq_inf

set_option autoImplicit false

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.GlueOfCocycle

attribute [local instance] MvPolynomial.gradedAlgebra

namespace GluedPres

variable {Y : Scheme.{u}} {r : ℕ} {V : Fin r → Y.Opens} (c : PhilipponFiniteCocycle.UnitCocycle V)

def Compat (x : ∀ j : Fin r, Γ(Y, V j)) : Prop :=
  ∀ i j, rO (inf_le_left : V i ⊓ V j ≤ V i) (x i) = c.u i j * rO (inf_le_right : V i ⊓ V j ≤ V j) (x j)

noncomputable def sec (x : ∀ j : Fin r, Γ(Y, V j)) (hx : Compat c x) : Γ(PhilipponFiniteCocycle.glueOfCocycle c, ⊤) :=
  PhilipponFiniteCocycle.glueMk c ⊤ (fun j => rO (inf_le_right : ⊤ ⊓ V j ≤ V j) (x j)) fun i j => by
    rw [rO_rO, rO_rO]
    have h := congrArg (rO (PhilipponFiniteCocycle.leij ⊤ i j)) (hx i j)
    rw [map_mul, rO_rO, rO_rO] at h
    exact h

theorem glueComponent_sec (x : ∀ j : Fin r, Γ(Y, V j)) (hx : Compat c x) (j : Fin r) :
    PhilipponFiniteCocycle.glueComponent c ⊤ j (sec c x hx) = rO (inf_le_right : ⊤ ⊓ V j ≤ V j) (x j) := rfl

theorem glueComponent_map_sec (x : ∀ j : Fin r, Γ(Y, V j)) (hx : Compat c x) {W : Y.Opens} (j : Fin r) :
    PhilipponFiniteCocycle.glueComponent c W j ((PhilipponFiniteCocycle.glueOfCocycle c).presheaf.map (homOfLE (le_top : W ≤ ⊤)).op (sec c x hx)) =
      rO (inf_le_right : W ⊓ V j ≤ V j) (x j) := by
  rw [PhilipponFiniteCocycle.glueComponent_map, glueComponent_sec, rO_rO]

theorem map_sec_eq_glueFrame (x : ∀ j : Fin r, Γ(Y, V j)) (hx : Compat c x) (i : Fin r)
    (hxi : ∀ j, rO (inf_le_left : V j ⊓ V i ≤ V j) (x j) = c.u j i) :
    (PhilipponFiniteCocycle.glueOfCocycle c).presheaf.map (homOfLE (le_top : V i ≤ ⊤)).op (sec c x hx) = PhilipponFiniteCocycle.glueFrame c i := by
  apply PhilipponFiniteCocycle.glue_ext
  intro j
  rw [glueComponent_map_sec, PhilipponFiniteCocycle.glueComponent_glueFrame, ← hxi j, rO_rO]

theorem bijective_smul_of_map_eq_glueFrame (s : Γ(PhilipponFiniteCocycle.glueOfCocycle c, ⊤)) (i : Fin r)
    (hs : (PhilipponFiniteCocycle.glueOfCocycle c).presheaf.map (homOfLE (le_top : V i ≤ ⊤)).op s = PhilipponFiniteCocycle.glueFrame c i)
    (W : Y.Opens) (hW : W ≤ V i) :
    Function.Bijective fun g : Γ(Y, W) => g • ((PhilipponFiniteCocycle.glueOfCocycle c).presheaf.map (homOfLE (le_top : W ≤ ⊤)).op s : Γ(PhilipponFiniteCocycle.glueOfCocycle c, W)) := by
  have key : (PhilipponFiniteCocycle.glueOfCocycle c).presheaf.map (homOfLE (le_top : W ≤ ⊤)).op s =
      (PhilipponFiniteCocycle.glueOfCocycle c).presheaf.map (homOfLE hW).op (PhilipponFiniteCocycle.glueFrame c i) := by
    rw [← hs]
    change _ = ((PhilipponFiniteCocycle.glueOfCocycle c).presheaf.map (homOfLE (le_top : V i ≤ ⊤)).op ≫
      (PhilipponFiniteCocycle.glueOfCocycle c).presheaf.map (homOfLE hW).op) s
    rw [← Functor.map_comp]; rfl
  rw [key]
  exact PhilipponFiniteCocycle.isFrameOn_glueFrame c i hW hW

theorem subsingleton_sections_bot (M : Y.Modules) : Subsingleton (M.val.obj (op (⊥ : Y.Opens))) := by
  have hbot : (⊥ : Sieve (⊥ : Y.Opens)) ∈ (Opens.grothendieckTopology ↥Y) (⊥ : Y.Opens) :=
    fun x hx => (Opens.mem_bot.1 hx).elim
  have hT : Limits.IsTerminal (M.val.presheaf.obj (op (⊥ : Y.Opens))) :=
    Sheaf.isTerminalOfBotCover ⟨M.val.presheaf, M.isSheaf⟩ (⊥ : Y.Opens) hbot
  have h0 : (𝟙 (M.val.presheaf.obj (op (⊥ : Y.Opens))) : _ ⟶ _) = 0 := hT.hom_ext _ _
  refine ⟨fun a b => ?_⟩
  have ha : a = 0 := by
    have := congrArg (fun φ => (ConcreteCategory.hom φ) a) h0
    simp at this
    exact this
  have hb : b = 0 := by
    have := congrArg (fun φ => (ConcreteCategory.hom φ) b) h0
    simp at this
    exact this
  rw [ha, hb]

theorem subsingleton_functions_bot : Subsingleton (Γ(Y, (⊥ : Y.Opens)) : Type _) := by
  have hbot : (⊥ : Sieve (⊥ : Y.Opens)) ∈ (Opens.grothendieckTopology ↥Y) (⊥ : Y.Opens) :=
    fun x hx => (Opens.mem_bot.1 hx).elim
  have hT : Limits.IsTerminal (Y.sheaf.val.obj (op (⊥ : Y.Opens))) :=
    Sheaf.isTerminalOfBotCover Y.sheaf (⊥ : Y.Opens) hbot
  let e := hT.uniqueUpToIso CommRingCat.punitIsTerminal
  refine ⟨fun a b => ?_⟩
  have h1 : ∀ x : Γ(Y, (⊥ : Y.Opens)), e.inv.hom (e.hom.hom x) = x := fun x => by
    have := congrArg (fun φ => (ConcreteCategory.hom φ) x) e.hom_inv_id
    simpa using this
  rw [← h1 a, ← h1 b, Subsingleton.elim (e.hom.hom a) (e.hom.hom b)]

theorem bijective_smul_bot (M : Y.Modules) (s : Γ(M, ⊤)) (W : Y.Opens) (hW : W ≤ ⊥) :
    Function.Bijective fun g : Γ(Y, W) => g • (M.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op s : Γ(M, W)) := by
  have hW' : W = ⊥ := le_bot_iff.1 hW
  subst hW'
  haveI : Subsingleton (Γ(M, (⊥ : Y.Opens)) : Type _) := subsingleton_sections_bot M
  haveI : Subsingleton (Γ(Y, (⊥ : Y.Opens)) : Type _) := subsingleton_functions_bot
  exact ⟨fun a b _ => Subsingleton.elim a b, fun m => ⟨0, Subsingleton.elim _ _⟩⟩

theorem isUnit_of_frames {M : Y.Modules} {W : Y.Opens} (s t : Γ(M, W))
    (hs : Function.Bijective fun g : Γ(Y, W) => g • s) (ht : Function.Bijective fun g : Γ(Y, W) => g • t)
    (f : Γ(Y, W)) (h : s = f • t) : IsUnit f := by
  obtain ⟨f', hf'⟩ := hs.2 t
  have hf'' : f' • s = t := hf'
  have h1 : (f * f') • s = (1 : Γ(Y, W)) • s := by
    rw [one_smul, mul_smul, hf'', ← h]
  exact isUnit_iff_exists_inv.2 ⟨f', hs.1 h1⟩

theorem inf_le_basicOpen_of_frame (x : ∀ j : Fin r, Γ(Y, V j)) (hx : Compat c x) (W : Y.Opens)
    (hW : ∀ W' : Y.Opens, W' ≤ W → Function.Bijective fun g : Γ(Y, W') =>
      g • ((PhilipponFiniteCocycle.glueOfCocycle c).presheaf.map (homOfLE (le_top : W' ≤ ⊤)).op (sec c x hx) : Γ(PhilipponFiniteCocycle.glueOfCocycle c, W')))
    (j : Fin r) : W ⊓ V j ≤ Y.basicOpen (x j) := by

  set W' : Y.Opens := W ⊓ V j with hW'
  let s : Γ(PhilipponFiniteCocycle.glueOfCocycle c, W') := (PhilipponFiniteCocycle.glueOfCocycle c).presheaf.map (homOfLE (le_top : W' ≤ ⊤)).op (sec c x hx)
  let t : Γ(PhilipponFiniteCocycle.glueOfCocycle c, W') := (PhilipponFiniteCocycle.glueOfCocycle c).presheaf.map (homOfLE (inf_le_right : W' ≤ V j)).op (PhilipponFiniteCocycle.glueFrame c j)
  have hs : Function.Bijective fun g : Γ(Y, W') => g • s := hW W' inf_le_left
  have ht : Function.Bijective fun g : Γ(Y, W') => g • t := PhilipponFiniteCocycle.isFrameOn_glueFrame c j (inf_le_right : W' ≤ V j) inf_le_right
  obtain ⟨f, hf⟩ := ht.2 s
  have hfu : IsUnit f := isUnit_of_frames s t hs ht f hf.symm

  have hcomp : rO (inf_le_right : W' ⊓ V j ≤ V j) (x j) = rO (inf_le_left : W' ⊓ V j ≤ W') f := by
    have h1 := congrArg (PhilipponFiniteCocycle.glueComponent c W' j) hf
    rw [PhilipponFiniteCocycle.glueComponent_smul, PhilipponFiniteCocycle.glueComponent_map, PhilipponFiniteCocycle.glueComponent_glueFrame, rO_rO,
      show rO ((inf_le_inf_right (V j) (inf_le_right : W' ≤ V j)).trans (le_of_eq (inf_comm (V j) (V j)))) (c.u j j) = 1 by
        rw [c.refl, map_one], mul_one] at h1
    rw [h1]
    exact (glueComponent_map_sec c x hx j).symm
  have hu : IsUnit (rO (inf_le_right : W' ⊓ V j ≤ V j) (x j)) := by rw [hcomp]; exact hfu.map _
  have hb := Y.basicOpen_of_isUnit hu
  rw [show rO (inf_le_right : W' ⊓ V j ≤ V j) (x j) = Y.presheaf.map (homOfLE (inf_le_right : W' ⊓ V j ≤ V j)).op (x j) from rfl,
    Scheme.basicOpen_res] at hb
  calc W ⊓ V j = W' ⊓ V j := by rw [hW', inf_assoc, inf_idem]
    _ = W' ⊓ V j ⊓ Y.basicOpen (x j) := hb.symm
    _ ≤ Y.basicOpen (x j) := inf_le_right

theorem eq_of_smul_sec_eq {x x' : ∀ j : Fin r, Γ(Y, V j)} (hx : Compat c x) (hx' : Compat c x') (i : Fin r)
    (hxi : x i = 1) {D : Y.Opens} (hD : V i ≤ D) (g : Γ(Y, D))
    (h : g • (PhilipponFiniteCocycle.glueOfCocycle c).presheaf.map (homOfLE (le_top : D ≤ ⊤)).op (sec c x hx) =
      (PhilipponFiniteCocycle.glueOfCocycle c).presheaf.map (homOfLE (le_top : D ≤ ⊤)).op (sec c x' hx')) :
    rO hD g = x' i := by

  have h2 := congrArg (PhilipponFiniteCocycle.glueComponent c D i) h
  rw [PhilipponFiniteCocycle.glueComponent_smul, glueComponent_map_sec, glueComponent_map_sec, hxi, map_one, mul_one] at h2

  have hinj := (rO_bijective_of_le_le (inf_le_right : D ⊓ V i ≤ V i) (le_inf hD le_rfl)).1
  apply hinj
  rw [rO_rO]
  exact h2

end GluedPres

open GluedPres in
theorem solution
    (B : Type u) [CommRing B] (Y : Scheme.{u}) (πY : Y ⟶ Spec (CommRingCat.of B))
    (r : ℕ) (V : Fin r → Y.Opens) (hVaff : ∀ i, IsAffineOpen (V i)) (hcov : (⨆ i, V i) = ⊤)
    (w : ∀ i j : Fin r, Γ(Y, V i)) (hw1 : ∀ i, w i i = 1)
    (hw3 : ∀ i j : Fin r, Y.basicOpen (w i j) = V i ⊓ V j)
    (k : ℕ) (hk : 0 < k) (c : PhilipponFiniteCocycle.UnitCocycle V)
    (hc : ∀ i j : Fin r, c.u i j = Y.presheaf.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (w i j) ^ k)
    (N : ℕ) (a : Fin (N + 1) → ∀ j : Fin r, Γ(Y, V j))
    (ha : ∀ (α : Fin (N + 1)) (j m : Fin r),
      Y.presheaf.map (homOfLE (inf_le_left : V j ⊓ V m ≤ V j)).op (a α j) =
        Y.presheaf.map (homOfLE (inf_le_left : V j ⊓ V m ≤ V j)).op (w j m) ^ k *
          Y.presheaf.map (homOfLE (inf_le_right : V j ⊓ V m ≤ V m)).op (a α m))
    (e : Fin r → Fin (N + 1)) (he : Function.Injective e) (hae : ∀ i j : Fin r, a (e i) j = w j i ^ k) :
    ∃ 𝔓 : (PhilipponFiniteCocycle.glueOfCocycle c).ProjPresentation πY N,
      (∀ (α : Fin (N + 1)) (j : Fin r), PhilipponFiniteCocycle.glueComponent c ⊤ j (𝔓.σ α) =
        Y.presheaf.map (homOfLE (inf_le_right : ⊤ ⊓ V j ≤ V j)).op (a α j)) ∧
      ∃ hV : ∀ i : Fin r, V i ≤ 𝔓.toProj ⁻¹ᵁ
          Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) B) (MvPolynomial.X (e i)),
        (∀ i : Fin r, 𝔓.toProj ⁻¹ᵁ
          Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) B) (MvPolynomial.X (e i)) = V i) ∧
        (∀ (i : Fin r) (α : Fin (N + 1)),
          𝔓.toProj.appLE (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) B) (MvPolynomial.X (e i)))
              (V i) (hV i)
            (Proj.awayToSection _ (MvPolynomial.X (e i)) (ProjSpace.ratio B N (e i) α)) = a α i) := by
  classical

  have hx : ∀ α : Fin (N + 1), Compat c (a α) := by
    intro α i j
    show rO _ (a α i) = c.u i j * rO _ (a α j)
    rw [hc]
    exact ha α i j
  let σ : Fin (N + 1) → Γ(PhilipponFiniteCocycle.glueOfCocycle c, ⊤) := fun α => sec c (a α) (hx α)

  have hσe : ∀ i : Fin r,
      (PhilipponFiniteCocycle.glueOfCocycle c).presheaf.map (homOfLE (le_top : V i ≤ ⊤)).op (σ (e i)) = PhilipponFiniteCocycle.glueFrame c i := by
    intro i
    refine map_sec_eq_glueFrame c (a (e i)) (hx _) i fun j => ?_
    show rO _ (a (e i) j) = c.u j i
    rw [hae, map_pow, hc]

  let U' : Fin (N + 1) → Y.Opens := fun α => if h : ∃ i, e i = α then V h.choose else ⊥
  have hU'e : ∀ i, U' (e i) = V i := by
    intro i
    have h : ∃ i', e i' = e i := ⟨i, rfl⟩
    simp only [U', dif_pos h]
    rw [he h.choose_spec]
  have hU' : iSup U' = ⊤ := by
    apply top_le_iff.1
    rw [← hcov]
    exact iSup_le fun i => (hU'e i).symm.le.trans (le_iSup U' (e i))
  have hframe : ∀ (α : Fin (N + 1)) (W : Y.Opens), W ≤ U' α →
      Function.Bijective fun g : Γ(Y, W) =>
        g • ((PhilipponFiniteCocycle.glueOfCocycle c).presheaf.map (homOfLE (le_top : W ≤ ⊤)).op (σ α) : Γ(PhilipponFiniteCocycle.glueOfCocycle c, W)) := by
    intro α W hW
    by_cases h : ∃ i, e i = α
    · obtain ⟨i, rfl⟩ := h
      rw [hU'e] at hW
      exact bijective_smul_of_map_eq_glueFrame c (σ (e i)) i (hσe i) W hW
    · have hbot : U' α = ⊥ := dif_neg h
      rw [hbot] at hW
      exact bijective_smul_bot _ _ W hW
  obtain ⟨𝔓, h𝔓σ, h𝔓U⟩ :=
    AlgebraicGeometry.Scheme.Modules.exists_projPresentation_of_iSup_eq_top πY (PhilipponFiniteCocycle.glueOfCocycle c) N σ U' hU' hframe
  have hV : ∀ i : Fin r, V i ≤ 𝔓.toProj ⁻¹ᵁ
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) B) (MvPolynomial.X (e i)) :=
    fun i => (hU'e i).symm.le.trans (h𝔓U (e i))
  refine ⟨𝔓, ?_, hV, ?_, ?_⟩
  ·
    intro α j
    rw [h𝔓σ]
    exact glueComponent_sec c (a α) (hx α) j
  ·
    intro i
    refine le_antisymm ?_ (hV i)
    intro y hy
    have hy' : y ∈ (⊤ : Y.Opens) := trivial
    rw [← hcov] at hy'
    obtain ⟨j, hj⟩ := Opens.mem_iSup.1 hy'
    have hle := inf_le_basicOpen_of_frame c (a (e i)) (hx (e i))
      (𝔓.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) B) (MvPolynomial.X (e i)))
      (fun W' hW' => by have hf := 𝔓.frame (e i) W' hW'; rw [h𝔓σ] at hf; exact hf) j
    have hyj : y ∈ Y.basicOpen (a (e i) j) := hle ⟨hy, hj⟩
    rw [hae, Y.basicOpen_pow _ hk, hw3] at hyj
    exact hyj.2
  ·
    intro i α
    have hr := 𝔓.app_ratio_smul (e i) α
    rw [h𝔓σ] at hr
    have h1 := eq_of_smul_sec_eq c (hx (e i)) (hx α) i (by rw [hae, hw1, one_pow]) (hV i) _ hr
    exact h1

end S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_glueOfCocycle_preimage_basicOpen_eq_of_basicOpen_eq_inf
end P2MW



set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_exists_isImmersion_proj_of_affineCover_cocycle_basicOpen_eq_of_locallyOfFiniteType

set_option autoImplicit false

attribute [local instance] MvPolynomial.gradedAlgebra

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open AlgebraicGeometry.Scheme.Modules.GlueOfCocycle

namespace AmpleChartsAux

theorem exists_finset_forall_surjective {B C : Type u} [CommRing B] [CommRing C] (f : B →+* C) (hf : f.FiniteType) :
    ∃ s : Finset C, ∀ (D : Type u) [CommRing D] (ψ : D →+* C) (θ : B →+* D), ψ.comp θ = f →
      (∀ x ∈ s, x ∈ Set.range ψ) → Function.Surjective ψ := by
  letI : Algebra B C := f.toAlgebra
  obtain ⟨s, hs⟩ := hf
  refine ⟨s, fun D _ ψ θ hcomp hsub => ?_⟩
  let S : Subalgebra B C :=
    { carrier := Set.range ψ
      mul_mem' := by rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩; exact ⟨a * b, map_mul ψ a b⟩
      add_mem' := by rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩; exact ⟨a + b, map_add ψ a b⟩
      algebraMap_mem' := fun r => ⟨θ r, by rw [← RingHom.comp_apply, hcomp]; rfl⟩ }
  have hle : Algebra.adjoin B (s : Set C) ≤ S := Algebra.adjoin_le hsub
  intro c
  have hc : c ∈ Algebra.adjoin B (s : Set C) := by rw [hs]; trivial
  exact hle hc

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))

noncomputable def φ (U : X.affineOpens) : CommRingCat.of R ⟶ Γ(X, U.1) :=
  (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appLE ⊤ U.1 (by simp)

lemma fromSpec_comp (U : X.affineOpens) : U.2.fromSpec ≫ f = Spec.map (φ f U) := by
  rw [φ, Spec.map_comp, ← Scheme.isoSpec_Spec_inv, ← IsAffineOpen.fromSpec_top]
  exact (IsAffineOpen.SpecMap_appLE_fromSpec f (isAffineOpen_top _) U.2 (by simp)).symm

lemma finiteType_φ [LocallyOfFiniteType f] (U : X.affineOpens) : (φ f U).hom.FiniteType := by
  have h := HasRingHomProperty.appLE (P := @LocallyOfFiniteType) f inferInstance ⟨⊤, isAffineOpen_top _⟩ U (by simp)
  rw [φ, CommRingCat.hom_comp]
  exact RingHom.FiniteType.comp h
    (RingHom.FiniteType.of_surjective _ (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv).2)

lemma SpecMap_awayToSection_comp_awayι {n : ℕ} (i : Fin (n + 1)) :
    Spec.map (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (MvPolynomial.X i)) ≫
      Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (MvPolynomial.X i) (ProjSpace.X_mem_one R n i) one_pos =
    (Proj.isAffineOpen_basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (MvPolynomial.X i)
      (ProjSpace.X_mem_one R n i) one_pos).fromSpec := by
  have hU := Proj.isAffineOpen_basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (MvPolynomial.X i)
      (ProjSpace.X_mem_one R n i) one_pos
  haveI : IsAffine (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (MvPolynomial.X i)) := hU
  rw [Proj.awayι, IsAffineOpen.fromSpec, ← Category.assoc]
  congr 1
  rw [Iso.comp_inv_eq, Iso.eq_inv_comp, Proj.basicOpenIsoSpec_hom, IsAffineOpen.isoSpec_hom, Proj.basicOpenToSpec]

end AmpleChartsAux

open AmpleChartsAux in
theorem solution
    (B : Type u) [CommRing B] (Y : Scheme.{u}) (πY : Y ⟶ Spec (CommRingCat.of B)) [LocallyOfFiniteType πY]
    (r : ℕ) (V : Fin r → Y.Opens) (hVaff : ∀ i, IsAffineOpen (V i)) (hcov : (⨆ i, V i) = ⊤)
    (w : ∀ i j : Fin r, Γ(Y, V i)) (hw1 : ∀ i, w i i = 1)
    (hw2 : ∀ i j k : Fin r,
      Y.presheaf.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (w i k) =
        Y.presheaf.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (w i j) *
          Y.presheaf.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op (w j k))
    (hw3 : ∀ i j : Fin r, Y.basicOpen (w i j) = V i ⊓ V j) :
    ∃ (qpn : ℕ) (qpι : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (qpn + 1)) B)),
      IsImmersion qpι ∧ qpι ≫ ProjSpace.π B qpn = πY := by
  classical

  let Va : Fin r → Y.affineOpens := fun i => ⟨V i, hVaff i⟩

  have hgen := fun i => exists_finset_forall_surjective (φ πY (Va i)).hom (finiteType_φ πY (Va i))
  choose s hs using hgen

  let I : Type u := Σ i : Fin r, ↥(s i)
  haveI : Fintype I := inferInstance
  have hC1 := fun x : I => P2MW.S_AlgebraicGeometry_Scheme_exists_forall_exists_eq_and_map_eq_pow_mul_map_of_basicOpen_eq_inf.solution
    V hVaff w hw1 hw2 hw3 x.1 (x.2 : Γ(Y, V x.1))
  choose k₀ hk₀ using hC1
  let k : ℕ := (Finset.univ.sup k₀) + 1
  have hk : 0 < k := Nat.succ_pos _
  have hkx : ∀ x : I, k₀ x ≤ k := fun x => (Finset.le_sup (Finset.mem_univ x)).trans (Nat.le_succ _)
  have ht := fun x : I => hk₀ x k (hkx x)
  choose t ht₁ ht₂ using ht

  let M : ℕ := Fintype.card I
  let eI : I ≃ Fin M := Fintype.equivFin I
  let N : ℕ := r + M
  let a : Fin (N + 1) → ∀ j : Fin r, Γ(Y, V j) := fun α =>
    if h : α.val < r then (fun j => w j ⟨α.val, h⟩ ^ k)
    else if h' : α.val - r < M then t (eI.symm ⟨α.val - r, h'⟩) else fun _ => 0
  let e : Fin r → Fin (N + 1) := fun i => ⟨i.val, by omega⟩
  have he : Function.Injective e := by
    intro i j h; exact Fin.ext (by simpa [e] using congrArg Fin.val h)
  have hae : ∀ i j : Fin r, a (e i) j = w j i ^ k := by
    intro i j; simp only [a, e, dif_pos i.isLt]
  have a_ext : ∀ (x : I) (j : Fin r), a ⟨r + (eI x).val, by omega⟩ j = t x j := by
    intro x j
    simp only [a]
    rw [dif_neg (by omega), dif_pos (by simp)]
    congr 1
    have : (⟨r + (eI x).val - r, by omega⟩ : Fin M) = eI x := Fin.ext (by simp)
    rw [this, Equiv.symm_apply_apply]
  have ha : ∀ (α : Fin (N + 1)) (j m : Fin r),
      Y.presheaf.map (homOfLE (inf_le_left : V j ⊓ V m ≤ V j)).op (a α j) =
        Y.presheaf.map (homOfLE (inf_le_left : V j ⊓ V m ≤ V j)).op (w j m) ^ k *
          Y.presheaf.map (homOfLE (inf_le_right : V j ⊓ V m ≤ V m)).op (a α m) := by
    intro α j m
    by_cases h : α.val < r
    · simp only [a, dif_pos h, map_pow]
      rw [hw2 j m ⟨α.val, h⟩, mul_pow]
    · by_cases h' : α.val - r < M
      · simp only [a, dif_neg h, dif_pos h']
        exact ht₂ _ j m
      · simp only [a, dif_neg h, dif_neg h', map_zero, mul_zero]

  let c : PhilipponFiniteCocycle.UnitCocycle V :=
    { u := fun i j => rO (inf_le_left : V i ⊓ V j ≤ V i) (w i j) ^ k
      refl := fun i => by simp only [hw1, map_one, one_pow]
      cocycle := fun i j l => by
        simp only [map_pow, rO_rO, ← mul_pow]
        congr 1
        have h := congrArg (rO (le_inf (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right) :
          V i ⊓ V j ⊓ V l ≤ V i ⊓ V j)) (hw2 i j l)
        rw [map_mul, rO_rO, rO_rO, rO_rO] at h
        exact h.symm }
  have hc : ∀ i j : Fin r, c.u i j = Y.presheaf.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (w i j) ^ k :=
    fun _ _ => rfl

  obtain ⟨𝔓, -, hVle, hpre, happ⟩ :=
    P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_glueOfCocycle_preimage_basicOpen_eq_of_basicOpen_eq_inf.solution
      B Y πY r V hVaff hcov w hw1 hw3 k hk c hc N a ha e he hae

  let 𝒜 := MvPolynomial.homogeneousSubmodule (Fin (N + 1)) B
  let W : Fin r → (Proj 𝒜).Opens := fun i => Proj.basicOpen 𝒜 (MvPolynomial.X (e i))
  have hWaff : ∀ i, IsAffineOpen (W i) := fun i =>
    Proj.isAffineOpen_basicOpen 𝒜 (MvPolynomial.X (e i)) (ProjSpace.X_mem_one B N (e i)) one_pos
  have hYaff : ∀ i, IsAffineOpen (𝔓.toProj ⁻¹ᵁ W i) := fun i => by rw [hpre i]; exact hVaff i
  have hcov' : (⨆ i, 𝔓.toProj ⁻¹ᵁ W i) = ⊤ := by
    have : (fun i => 𝔓.toProj ⁻¹ᵁ W i) = V := funext hpre
    rw [this]; exact hcov
  have hsurj : ∀ i, Function.Surjective (𝔓.toProj.app (W i)) := by
    intro i

    let ψ : HomogeneousLocalization.Away 𝒜 (MvPolynomial.X (e i)) →+* Γ(Y, V i) :=
      (𝔓.toProj.appLE (W i) (V i) (hVle i)).hom.comp (Proj.awayToSection 𝒜 (MvPolynomial.X (e i))).hom

    have hψB : ψ.comp (algebraMap B (HomogeneousLocalization.Away 𝒜 (MvPolynomial.X (e i)))) = (φ πY (Va i)).hom := by
      have key : CommRingCat.ofHom (algebraMap B (HomogeneousLocalization.Away 𝒜 (MvPolynomial.X (e i)))) ≫
          Proj.awayToSection 𝒜 (MvPolynomial.X (e i)) ≫ 𝔓.toProj.appLE (W i) (V i) (hVle i) = φ πY (Va i) := by
        apply Spec.map_injective
        have h' : ∀ (Z : Scheme.{u}) (g : Proj 𝒜 ⟶ Z),
            Spec.map (Proj.awayToSection 𝒜 (MvPolynomial.X (e i))) ≫
              Proj.awayι 𝒜 (MvPolynomial.X (e i)) (ProjSpace.X_mem_one B N (e i)) one_pos ≫ g = (hWaff i).fromSpec ≫ g :=
          fun Z g => by rw [← Category.assoc, SpecMap_awayToSection_comp_awayι]
        rw [Spec.map_comp, Spec.map_comp, ← fromSpec_comp, ← ProjSpace.awayι_comp_π, Category.assoc, h',
          ← Category.assoc, IsAffineOpen.SpecMap_appLE_fromSpec 𝔓.toProj (hWaff i) (hVaff i) (hVle i), Category.assoc,
          𝔓.toProj_π]
      have := congrArg CommRingCat.Hom.hom key
      simp [CommRingCat.hom_comp, RingHom.comp_assoc] at this
      exact this

    have hgen : ∀ x ∈ s i, x ∈ Set.range ψ := by
      intro x hx
      refine ⟨ProjSpace.ratio B N (e i) ⟨r + (eI ⟨i, ⟨x, hx⟩⟩).val, by omega⟩, ?_⟩
      change (𝔓.toProj.appLE (W i) (V i) (hVle i)) (Proj.awayToSection 𝒜 (MvPolynomial.X (e i)) _) = x
      rw [happ i, a_ext ⟨i, ⟨x, hx⟩⟩ i, ht₁]
    have hψ : Function.Surjective ψ := hs i _ ψ _ hψB hgen

    have h1 : Function.Surjective (𝔓.toProj.appLE (W i) (V i) (hVle i)) := Function.Surjective.of_comp hψ
    have h2 : 𝔓.toProj.appLE (W i) (V i) (hVle i) = 𝔓.toProj.app (W i) ≫ Y.presheaf.map (homOfLE (hVle i)).op := rfl
    rw [h2] at h1
    have hbij := rO_bijective_of_le_le (X := Y) (hVle i) (le_of_eq (hpre i))
    intro y
    obtain ⟨x, hx⟩ := h1 (rO (hVle i) y)
    exact ⟨x, hbij.1 hx⟩
  refine ⟨N, 𝔓.toProj, ?_, 𝔓.toProj_π⟩
  exact P2MW.S_AlgebraicGeometry_Scheme_Hom_isImmersion_of_forall_isAffineOpen_preimage_of_forall_surjective_app.solution
    𝔓.toProj W hWaff hYaff hcov' hsurj

end S_AlgebraicGeometry_Scheme_exists_isImmersion_proj_of_affineCover_cocycle_basicOpen_eq_of_locallyOfFiniteType
end P2MW



set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_isImmersion_projSpace_comp_of_isFinite_of_isImmersion_of_isNoetherianRing

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

attribute [local instance] MvPolynomial.gradedAlgebra

namespace P5FQP

theorem compactSpace_of_isImmersion_proj_of_isNoetherianRing
    {𝒪 : Type u} [CommRing 𝒪] [IsNoetherianRing 𝒪] {M : Scheme.{u}} {n : ℕ}
    (ι : M ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) 𝒪)) [IsImmersion ι] : CompactSpace M := by
  let P := Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) 𝒪)
  haveI : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian (ProjSpace.π 𝒪 n)
  haveI : CompactSpace P := QuasiCompact.compactSpace_of_compactSpace (ProjSpace.π 𝒪 n)
  haveI : IsNoetherian P := {}
  have hc : IsCompact (Set.range ι) := TopologicalSpace.NoetherianSpace.isCompact _
  rw [← Set.image_univ, ← ι.isEmbedding.isCompact_iff] at hc
  exact ⟨hc⟩

theorem exists_fin_cover {X : Scheme.{u}} [CompactSpace X] (O : X → X.Opens) (hO : ∀ x, x ∈ O x) :
    ∃ (r : ℕ) (c : Fin r → X), (⨆ i, O (c i)) = ⊤ := by
  classical
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x => (O x : Set X)) (fun x => (O x).isOpen)
    (fun x _ => Set.mem_iUnion.mpr ⟨x, hO x⟩)
  refine ⟨t.card, fun i => (t.equivFin.symm i).1, ?_⟩
  apply top_le_iff.mp
  intro y _
  obtain ⟨x, hx⟩ := Set.mem_iUnion.mp (ht (Set.mem_univ y))
  obtain ⟨hxt, hyx⟩ := Set.mem_iUnion.mp hx
  exact Opens.mem_iSup.mpr ⟨t.equivFin ⟨x, hxt⟩, by simpa using hyx⟩

end P5FQP

namespace P12FQP
open P5FQP

theorem exists_affineCover_cocycle_of_isImmersion_proj
    {𝒪 : Type u} [CommRing 𝒪] [IsNoetherianRing 𝒪] {M : Scheme.{u}} {n : ℕ}
    (ι : M ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) 𝒪)) [IsImmersion ι] :
    ∃ (r : ℕ) (U : Fin r → M.Opens) (w : ∀ i j : Fin r, Γ(M, U i)),
      (∀ i, IsAffineOpen (U i)) ∧ (⨆ i, U i) = ⊤ ∧
      (∀ i, w i i = 1) ∧
      (∀ i j k : Fin r,
        M.presheaf.map (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).op (w i k) =
          M.presheaf.map (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).op (w i j) *
            M.presheaf.map (homOfLE (inf_le_right : U i ⊓ U j ≤ U j)).op (w j k)) ∧
      (∀ i j : Fin r, M.basicOpen (w i j) = U i ⊓ U j) := by
  classical
  haveI : CompactSpace M := compactSpace_of_isImmersion_proj_of_isNoetherianRing ι
  let 𝒜 := MvPolynomial.homogeneousSubmodule (Fin (n + 1)) 𝒪

  have hA1 : ∀ x : M, ∃ (d : ℕ) (F : MvPolynomial (Fin (n + 1)) 𝒪), F ∈ 𝒜 d ∧ 0 < d ∧
      x ∈ ι ⁻¹ᵁ Proj.basicOpen 𝒜 F ∧ IsAffineOpen (ι ⁻¹ᵁ Proj.basicOpen 𝒜 F) := by
    intro x
    obtain ⟨d, F, hFd, hd, hS, haff, -⟩ :=
      P2MW.S_AlgebraicGeometry_exists_mem_isAffineOpen_isClosedImmersion_morphismRestrict_basicOpen_of_isImmersion_proj.solution 𝒜 ι {x}
    exact ⟨d, F, hFd, hd, hS x (Finset.mem_singleton_self x), haff⟩
  choose d F hFd hd hmem haff using hA1
  obtain ⟨r, c, hcov⟩ := exists_fin_cover (fun x => ι ⁻¹ᵁ Proj.basicOpen 𝒜 (F x)) hmem

  let D : ℕ := ∏ i : Fin r, d (c i)
  have hDpos : 0 < D := Finset.prod_pos fun i _ => hd (c i)
  have hdvd : ∀ i : Fin r, d (c i) ∣ D := fun i => Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  let e : Fin r → ℕ := fun i => D / d (c i)
  have he : ∀ i, e i * d (c i) = D := fun i => Nat.div_mul_cancel (hdvd i)
  have hepos : ∀ i, 0 < e i := fun i => Nat.div_pos (Nat.le_of_dvd hDpos (hdvd i)) (hd (c i))
  let G : Fin r → MvPolynomial (Fin (n + 1)) 𝒪 := fun i => F (c i) ^ e i
  have hG : ∀ i, G i ∈ 𝒜 D := by
    intro i
    have := SetLike.pow_mem_graded (e i) (hFd (c i))
    rwa [smul_eq_mul, he i] at this
  have hGF : ∀ i, Proj.basicOpen 𝒜 (G i) = Proj.basicOpen 𝒜 (F (c i)) := fun i =>
    Proj.basicOpen_pow 𝒜 _ _ (hepos i)

  obtain ⟨v, -, hv1, hv2, hv3⟩ :=
    P2MW.S_AlgebraicGeometry_Proj_exists_cocycle_basicOpen_eq_inf_of_mem_of_pos.solution 𝒜 hDpos G hG
  obtain ⟨hu1, hu2, hu3⟩ :=
    P2MW.S_AlgebraicGeometry_Scheme_Hom_app_cocycle_and_basicOpen_app_eq_inf_of_basicOpen_eq_inf.solution ι
      (fun i => Proj.basicOpen 𝒜 (G i)) v hv1 hv2 hv3
  refine ⟨r, fun i => ι ⁻¹ᵁ Proj.basicOpen 𝒜 (G i), fun i j => ι.app _ (v i j), ?_, ?_, hu1, hu2, hu3⟩
  · intro i
    show IsAffineOpen (ι ⁻¹ᵁ Proj.basicOpen 𝒜 (G i))
    rw [hGF i]
    exact haff (c i)
  · show (⨆ i, ι ⁻¹ᵁ Proj.basicOpen 𝒜 (G i)) = ⊤
    rw [show (⨆ i, ι ⁻¹ᵁ Proj.basicOpen 𝒜 (G i)) = ⨆ i, ι ⁻¹ᵁ Proj.basicOpen 𝒜 (F (c i)) from
      iSup_congr fun i => by rw [hGF i]]
    exact hcov

end P12FQP

open P12FQP in
theorem solution
    {𝒪 : Type u} [CommRing 𝒪] [IsNoetherianRing 𝒪] {Z M : Scheme.{u}} (πM : M ⟶ Spec (CommRingCat.of 𝒪)) (ζ : Z ⟶ M) [IsFinite ζ]
    (hM : ∃ (qpn : ℕ) (qpι : M ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (qpn + 1)) 𝒪)),
      IsImmersion qpι ∧ qpι ≫ ProjSpace.π 𝒪 qpn = πM) :
    ∃ (qpn : ℕ) (qpι : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (qpn + 1)) 𝒪)),
      IsImmersion qpι ∧ qpι ≫ ProjSpace.π 𝒪 qpn = ζ ≫ πM := by
  classical
  obtain ⟨n, ι, hι, hιπ⟩ := hM
  haveI : IsImmersion ι := hι

  obtain ⟨r, U, w, hUaff, hUcov, hw1, hw2, hw3⟩ := P12FQP.exists_affineCover_cocycle_of_isImmersion_proj ι
  obtain ⟨hw1', hw2', hw3'⟩ :=
    P2MW.S_AlgebraicGeometry_Scheme_Hom_app_cocycle_and_basicOpen_app_eq_inf_of_basicOpen_eq_inf.solution ζ U w hw1 hw2 hw3

  haveI : LocallyOfFiniteType ι := by
    rw [← ι.liftCoborder_ι]; infer_instance
  haveI : LocallyOfFiniteType πM := by
    rw [← hιπ]; infer_instance
  haveI : LocallyOfFiniteType (ζ ≫ πM) := inferInstance

  have hVaff : ∀ i : Fin r, IsAffineOpen (ζ ⁻¹ᵁ U i) := fun i => (hUaff i).preimage ζ
  have hVcov : (⨆ i, ζ ⁻¹ᵁ U i) = ⊤ := by
    rw [← Scheme.Hom.preimage_iSup, hUcov, Scheme.Hom.preimage_top]
  exact P2MW.S_AlgebraicGeometry_Scheme_exists_isImmersion_proj_of_affineCover_cocycle_basicOpen_eq_of_locallyOfFiniteType.solution
    𝒪 Z (ζ ≫ πM) r (fun i => ζ ⁻¹ᵁ U i) hVaff hVcov (fun i j => ζ.app (U i) (w i j)) hw1' hw2' hw3'

end S_AlgebraicGeometry_exists_isImmersion_projSpace_comp_of_isFinite_of_isImmersion_of_isNoetherianRing
end P2MW


open AlgebraicGeometry CategoryTheory TopologicalSpace
attribute [local instance] MvPolynomial.gradedAlgebra

namespace PhilipponProjectiveNormalization

lemma topological_dimension_eq_iSup_stalk (X : Scheme.{u}) :
    topologicalKrullDim X = ⨆ x : X, ringKrullDim (X.presheaf.stalk x) := by
  rw [show topologicalKrullDim X = Order.krullDim X from
    Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X))]
  simp_rw [Order.krullDim_eq_iSup_coheight, ringKrullDim_stalk_eq_coheight]

lemma topological_dimension_eq_of_surjective_of_stalk_dimension
    {X Y : Scheme.{u}} (f : Y ⟶ X) (hf : Function.Surjective f.base)
    (hd : ∀ y : Y, ringKrullDim (Y.presheaf.stalk y) =
      ringKrullDim (X.presheaf.stalk (f y))) :
    topologicalKrullDim Y = topologicalKrullDim X := by
  rw [topological_dimension_eq_iSup_stalk, topological_dimension_eq_iSup_stalk]
  simp_rw [hd]
  exact hf.iSup_comp (fun x : X => ringKrullDim (X.presheaf.stalk x))

lemma exists_closed_embedding_of_finite_over_projective
    (K : Type u) [Field K] {X Y : Scheme.{u}}
    (π : X ⟶ Spec (.of K)) [IsProper π] (ν : Y ⟶ X) [IsFinite ν]
    (n : ℕ)
    (i : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K))
    [IsClosedImmersion i] (hi : i ≫ ProjSpace.π K n = π) :
    ∃ (m : ℕ)
      (j : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) K)),
      IsClosedImmersion j ∧ j ≫ ProjSpace.π K m = ν ≫ π := by
  obtain ⟨m, j, hj, hπ⟩ :=
    P2MW.S_AlgebraicGeometry_exists_isImmersion_projSpace_comp_of_isFinite_of_isImmersion_of_isNoetherianRing.solution
      π ν ⟨n, i, inferInstance, hi⟩
  letI := hj
  haveI : IsProper (j ≫ ProjSpace.π K m) := by rw [hπ]; infer_instance
  haveI : IsProper j := IsProper.of_comp j (ProjSpace.π K m)
  exact ⟨m, j, IsClosedImmersion.of_isPreimmersion j j.isClosedMap.isClosed_range, hπ⟩

end PhilipponProjectiveNormalization


set_option autoImplicit false
open AlgebraicGeometry CategoryTheory

namespace PhilipponProjectiveNormalization

/-- An open set lifts through a morphism that is an isomorphism over its image. -/
lemma exists_open_lift_of_isIso_morphismRestrict
    {U G H : Scheme.{u}} (t : U ⟶ G) [IsOpenImmersion t] (ν : H ⟶ G)
    [IsIso (ν ∣_ t.opensRange)] :
    ∃ t' : U ⟶ H, IsOpenImmersion t' ∧ t' ≫ ν = t := by
  let t' : U ⟶ H := t.isoOpensRange.hom ≫ inv (ν ∣_ t.opensRange) ≫
    (ν ⁻¹ᵁ t.opensRange).ι
  refine ⟨t', inferInstance, ?_⟩
  dsimp only [t']
  rw [Category.assoc, Category.assoc, ← morphismRestrict_ι,
    IsIso.inv_hom_id_assoc, Scheme.Hom.isoOpensRange_hom_ι]

end PhilipponProjectiveNormalization



set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory TopologicalSpace
attribute [local instance] MvPolynomial.gradedAlgebra

namespace PhilipponProjectiveNormalization

/-- Finite projective normalization retaining a specified normal open chart. -/
theorem exists_normal_projective_finite_cover_with_open_lift
    (K : Type u) [Field K] {X U : Scheme.{u}} [IsIntegral X]
    (π : X ⟶ Spec (.of K)) [IsProper π] (n : ℕ)
    (i : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K))
    [IsClosedImmersion i] (hi : i ≫ ProjSpace.π K n = π)
    (t : U ⟶ X) [IsOpenImmersion t]
    (ht : ∀ u : U, IsIntegrallyClosed (X.presheaf.stalk (t u))) :
    ∃ (Y : Scheme.{u}) (ν : Y ⟶ X) (t' : U ⟶ Y),
      IsIntegral Y ∧ (∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)) ∧
      IsFinite ν ∧ Surjective ν ∧ topologicalKrullDim Y = topologicalKrullDim X ∧
      IsOpenImmersion t' ∧ t' ≫ ν = t ∧
      (∀ V : X.Opens, (∀ x ∈ V, IsIntegrallyClosed (X.presheaf.stalk x)) →
        IsIso (ν ∣_ V)) ∧
      ∃ (m : ℕ)
        (j : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) K)),
        IsClosedImmersion j ∧ j ≫ ProjSpace.π K m = ν ≫ π := by
  obtain ⟨Y, ν, hY, hnormal, hν, hsurj, hdim, hiso⟩ :=
    AlgebraicGeometry.exists_isFinite_isIntegrallyClosed_stalk_isIso_morphismRestrict_of_isIntegral K π
  letI := hY
  letI := hν
  have hnormalRange : ∀ x ∈ t.opensRange, IsIntegrallyClosed (X.presheaf.stalk x) := by
    intro x hx
    obtain ⟨u, rfl⟩ := hx
    exact ht u
  letI := hiso t.opensRange hnormalRange
  obtain ⟨t', ht', hfac⟩ := exists_open_lift_of_isIso_morphismRestrict t ν
  exact ⟨Y, ν, t', hY, hnormal, hν, ⟨hsurj⟩,
    topological_dimension_eq_of_surjective_of_stalk_dimension ν hsurj hdim,
    ht', hfac, hiso, exists_closed_embedding_of_finite_over_projective K π ν n i hi⟩

end PhilipponProjectiveNormalization



set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory HomogeneousLocalization
attribute [local instance] MvPolynomial.gradedAlgebra

namespace PhilipponAlterationProjection.ProjectiveAffineChart
variable (R : Type u) [CommRing R] (n : ℕ)

abbrev grading := MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R
abbrev chartRing := Away (grading R n) (MvPolynomial.X (0 : Fin (n + 1)))

noncomputable def specialize :
    MvPolynomial (Fin (n + 1)) R →+* MvPolynomial (Fin n) R :=
  MvPolynomial.eval₂Hom MvPolynomial.C (Fin.cases 1 MvPolynomial.X)

lemma specialize_X_zero : specialize R n (MvPolynomial.X (0 : Fin (n + 1))) = 1 := by
  simp [specialize]

lemma specialize_unit : IsUnit (specialize R n (MvPolynomial.X (0 : Fin (n + 1)))) :=
  isUnit_iff_exists_inv.mpr ⟨1, by rw [specialize_X_zero]; simp⟩

noncomputable def fromAway : chartRing R n →+* MvPolynomial (Fin n) R :=
  (Localization.awayLift (specialize R n) (MvPolynomial.X (0 : Fin (n + 1)))
    (specialize_unit R n)).comp
    (algebraMap (chartRing R n) (Localization.Away (MvPolynomial.X (0 : Fin (n + 1)) :
      MvPolynomial (Fin (n + 1)) R)))

lemma fromAway_coeff (r : R) :
    fromAway R n (algebraMap R (chartRing R n) r) = MvPolynomial.C r := by
  change Localization.awayLift (specialize R n) _ (specialize_unit R n)
    ((algebraMap R (chartRing R n) r).val) = _
  rw [ProjSpace.val_algebraMap]
  simp only [Localization.awayLift, IsLocalization.Away.lift_eq]
  simp [specialize]

lemma fromAway_ratio (j : Fin (n + 1)) :
    fromAway R n (ProjSpace.ratio R n 0 j) = specialize R n (MvPolynomial.X j) := by
  change Localization.awayLift (specialize R n) _ (specialize_unit R n) (ProjSpace.ratio R n 0 j).val = _
  rw [ProjSpace.ratio, Away.val_mk]
  simpa only [one_pow, mul_one] using
    Localization.awayLift_mk (specialize R n) (MvPolynomial.X (0 : Fin (n + 1)))
      (MvPolynomial.X j) 1 (by rw [specialize_X_zero]; simp) 1

noncomputable def fromAwayAlg : chartRing R n →ₐ[R] MvPolynomial (Fin n) R where
  __ := fromAway R n
  commutes' := fromAway_coeff R n

lemma fromAwayAlg_apply (x : chartRing R n) : fromAwayAlg R n x = fromAway R n x := rfl

noncomputable def toAwayAlg : MvPolynomial (Fin n) R →ₐ[R] chartRing R n :=
  MvPolynomial.aeval (fun j : Fin n => ProjSpace.ratio R n 0 j.succ)

lemma toAwayAlg_X (j : Fin n) : toAwayAlg R n (MvPolynomial.X j) = ProjSpace.ratio R n 0 j.succ :=
  MvPolynomial.aeval_X _ _

lemma from_to : (fromAwayAlg R n).comp (toAwayAlg R n) = AlgHom.id R _ := by
  apply MvPolynomial.algHom_ext
  intro j
  simp only [AlgHom.comp_apply, toAwayAlg_X, fromAwayAlg_apply, fromAway_ratio, AlgHom.id_apply]
  simp [specialize]

lemma to_from : (toAwayAlg R n).comp (fromAwayAlg R n) = AlgHom.id R _ := by
  apply AlgHom.ext_of_adjoin_eq_top (ProjSpace.adjoin_range_ratio R n 0)
  rintro _ ⟨j, rfl⟩
  simp only [AlgHom.comp_apply, fromAwayAlg_apply, fromAway_ratio, AlgHom.id_apply]
  refine Fin.cases ?_ (fun k => ?_) j
  · simp [specialize, ProjSpace.ratio_self]
  · simp [specialize, toAwayAlg]

noncomputable def equiv : chartRing R n ≃ₐ[R] MvPolynomial (Fin n) R :=
  AlgEquiv.ofAlgHom (fromAwayAlg R n) (toAwayAlg R n) (from_to R n) (to_from R n)

/-- The standard affine-space chart in projective space. -/
noncomputable def embedding : Spec (.of (MvPolynomial (Fin n) R)) ⟶ Proj (grading R n) :=
  Spec.map (CommRingCat.ofHom (equiv R n).toRingEquiv.toRingHom) ≫
    Proj.awayι (grading R n) (MvPolynomial.X (0 : Fin (n + 1)))
      (ProjSpace.X_mem_one R n 0) one_pos

instance embedding_isOpenImmersion : IsOpenImmersion (embedding R n) := by
  haveI : IsIso (CommRingCat.ofHom (equiv R n).toRingEquiv.toRingHom) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (equiv R n).bijective
  unfold embedding
  infer_instance

lemma embedding_over : embedding R n ≫ ProjSpace.π R n =
    Spec.map (CommRingCat.ofHom (MvPolynomial.C : R →+* MvPolynomial (Fin n) R)) := by
  rw [embedding, Category.assoc, ProjSpace.awayι_comp_π, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  exact (equiv R n).commutes r

end PhilipponAlterationProjection.ProjectiveAffineChart



open AlgebraicGeometry CategoryTheory
attribute [local instance] MvPolynomial.gradedAlgebra

namespace PhilipponAlterationProjection.ProjectiveAffineChart

/-- The standard affine chart, indexed by an arbitrary finite variable type. -/
noncomputable def finiteVariableEmbedding (R : Type u) [CommRing R]
    (ι : Type u) [Fintype ι] :
    Spec (.of (MvPolynomial ι R)) ⟶
      Proj (MvPolynomial.homogeneousSubmodule (Fin (Fintype.card ι + 1)) R) :=
  Spec.map (CommRingCat.ofHom
    (MvPolynomial.renameEquiv R (Fintype.equivFin ι)).symm.toRingEquiv.toRingHom) ≫
    embedding R (Fintype.card ι)

instance finiteVariableEmbedding_isOpenImmersion (R : Type u) [CommRing R]
    (ι : Type u) [Fintype ι] : IsOpenImmersion (finiteVariableEmbedding R ι) := by
  haveI : IsIso (CommRingCat.ofHom
      (MvPolynomial.renameEquiv R (Fintype.equivFin ι)).symm.toRingEquiv.toRingHom) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      (MvPolynomial.renameEquiv R (Fintype.equivFin ι)).symm.bijective
  unfold finiteVariableEmbedding
  infer_instance

lemma finiteVariableEmbedding_over (R : Type u) [CommRing R]
    (ι : Type u) [Fintype ι] :
    finiteVariableEmbedding R ι ≫ ProjSpace.π R (Fintype.card ι) =
      Spec.map (CommRingCat.ofHom (MvPolynomial.C : R →+* MvPolynomial ι R)) := by
  rw [finiteVariableEmbedding, Category.assoc, embedding_over, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  exact (MvPolynomial.renameEquiv R (Fintype.equivFin ι)).symm.commutes r

end PhilipponAlterationProjection.ProjectiveAffineChart



set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
noncomputable section
namespace PhilipponAlterationProjection

abbrev residueAlgebra {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) (x : X) : Algebra K (X.residueField x) :=
  ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop ≫
    X.presheaf.germ ⊤ x trivial ≫ X.residue x).hom.toAlgebra

lemma preimage_residue_comp {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) (x : X) :
    Spec.preimage (X.fromSpecResidueField x ≫ f) =
      (Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop ≫
        X.presheaf.germ ⊤ x trivial ≫ X.residue x := by
  apply Spec.map_injective
  rw [Spec.map_preimage]
  apply ext_of_isAffine
  simp only [Scheme.fromSpecResidueField, Scheme.Hom.comp_appTop,
    Scheme.fromSpecStalk_appTop]
  have ht : (Spec.map (Scheme.ΓSpecIso (.of K)).inv).appTop =
      (Scheme.ΓSpecIso Γ(Spec (.of K), ⊤)).inv := by
    apply (cancel_epi (Scheme.ΓSpecIso (.of K)).inv).mp
    exact (Scheme.ΓSpecIso_inv_naturality (Scheme.ΓSpecIso (.of K)).inv).symm
  simp
  simp only [Scheme.Hom.appTop] at ht ⊢
  rw [ht]

lemma residue_tower {K : Type u} [Field K] {X Y : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Spec (.of K)) (x : X) :
    letI := residueAlgebra g (f x)
    letI := residueAlgebra (f ≫ g) x
    letI := (f.residueFieldMap x).hom.toAlgebra
    IsScalarTower K (Y.residueField (f x)) (X.residueField x) := by
  letI := residueAlgebra g (f x)
  letI := residueAlgebra (f ≫ g) x
  letI := (f.residueFieldMap x).hom.toAlgebra
  apply IsScalarTower.of_algebraMap_eq'
  simp only [RingHom.algebraMap_toAlgebra]
  have h := congrArg Spec.preimage
    (congrArg (fun a => a ≫ g)
      (Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField f x))
  simp only [Category.assoc, Spec.preimage_comp, Spec.preimage_map,
    preimage_residue_comp] at h
  exact congrArg CommRingCat.Hom.hom h.symm

lemma isIso_residueFieldMap_of_isPreimmersion {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsPreimmersion f] (x : X) : IsIso (f.residueFieldMap x) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨(f.residueFieldMap x).hom.injective, ?_⟩
  intro z
  obtain ⟨a, ha⟩ := X.residue_surjective x z
  obtain ⟨b, hb⟩ := f.stalkMap_surjective x a
  refine ⟨Y.residue (f x) b, ?_⟩
  have h := congrArg (fun t : Y.presheaf.stalk (f x) ⟶ X.residueField x => t b)
    (Scheme.residue_residueFieldMap f x)
  simpa [hb, ha] using h


lemma dimension_eq_of_open_immersion {K : Type u} [Field K]
    {U W : Scheme.{u}} [IsIntegral U] [IsIntegral W]
    (f : U ⟶ W) [IsOpenImmersion f]
    (d : W ⟶ Spec (.of K)) [LocallyOfFiniteType d] :
    topologicalKrullDim U = topologicalKrullDim W := by
  let u := genericPoint U
  let L := W.residueField (f u)
  let E := U.residueField u
  letI : Algebra K L := residueAlgebra d (f u)
  letI : Algebra K E := residueAlgebra (f ≫ d) u
  letI : Algebra L E := (f.residueFieldMap u).hom.toAlgebra
  letI : IsScalarTower K L E := residue_tower f d u
  letI : IsIso (f.residueFieldMap u) := isIso_residueFieldMap_of_isPreimmersion f u
  let e : L ≃ₐ[K] E := AlgEquiv.ofBijective (IsScalarTower.toAlgHom K L E)
    (ConcreteCategory.bijective_of_isIso (f.residueFieldMap u))
  have he : Algebra.trdeg K L = Algebra.trdeg K E := e.trdeg_eq
  have hW := toENat_trdeg_residueField_eq_topologicalKrullDim_closure d (f u)
  have hU := toENat_trdeg_residueField_eq_topologicalKrullDim_closure (f ≫ d) u
  have hgen : f u = genericPoint W := genericPoint_eq_of_isOpenImmersion f
  have hclW : closure ({f u} : Set W) = Set.univ := by rw [hgen]; exact genericPoint_spec W
  have hclU : closure ({u} : Set U) = Set.univ := genericPoint_spec U
  have hdW : topologicalKrullDim W = topologicalKrullDim (closure ({f u} : Set W)) := by
    rw [hclW]
    exact (IsHomeomorph.topologicalKrullDim_eq (Homeomorph.Set.univ W)
      (Homeomorph.Set.univ W).isHomeomorph).symm
  have hdU : topologicalKrullDim U = topologicalKrullDim (closure ({u} : Set U)) := by
    rw [hclU]
    exact (IsHomeomorph.topologicalKrullDim_eq (Homeomorph.Set.univ U)
      (Homeomorph.Set.univ U).isHomeomorph).symm
  rw [hdU, hdW, ← hU, ← hW]
  change (Cardinal.toENat (Algebra.trdeg K E) : WithBot ℕ∞) =
    (Cardinal.toENat (Algebra.trdeg K L) : WithBot ℕ∞)
  rw [he]

lemma dimension_eq_card_of_function_field_basis {K : Type u} [Field K]
    {X : Scheme.{u}} [IsIntegral X]
    (π : X ⟶ Spec (.of K)) [LocallyOfFiniteType π] (S : Finset X.functionField)
    (hS : letI : Algebra K X.functionField :=
      ((Scheme.ΓSpecIso (.of K)).inv ≫ π.appTop ≫
        X.presheaf.germ ⊤ (genericPoint X) trivial).hom.toAlgebra
      IsTranscendenceBasis K ((↑) : S → X.functionField)) :
    topologicalKrullDim X = (Fintype.card S : WithBot ℕ∞) := by
  letI : Algebra K X.functionField :=
    ((Scheme.ΓSpecIso (.of K)).inv ≫ π.appTop ≫
      X.presheaf.germ ⊤ (genericPoint X) trivial).hom.toAlgebra
  let L := X.residueField (genericPoint X)
  letI : Algebra K L := residueAlgebra π (genericPoint X)
  letI : Algebra X.functionField L := (X.residue (genericPoint X)).hom.toAlgebra
  letI : IsScalarTower K X.functionField L := by
    apply IsScalarTower.of_algebraMap_eq'
    rfl
  have hbij : Function.Bijective (X.residue (genericPoint X)) :=
    ⟨(X.residue (genericPoint X)).hom.injective, X.residue_surjective _⟩
  let e : X.functionField ≃ₐ[K] L :=
    AlgEquiv.ofBijective (IsScalarTower.toAlgHom K X.functionField L) hbij
  have he : Algebra.trdeg K X.functionField = Algebra.trdeg K L := e.trdeg_eq
  have hd := toENat_trdeg_residueField_eq_topologicalKrullDim_closure π (genericPoint X)
  have hcl : closure ({genericPoint X} : Set X) = Set.univ := genericPoint_spec X
  have hdim : topologicalKrullDim X = topologicalKrullDim (closure ({genericPoint X} : Set X)) := by
    rw [hcl]
    exact (IsHomeomorph.topologicalKrullDim_eq (Homeomorph.Set.univ X)
      (Homeomorph.Set.univ X).isHomeomorph).symm
  rw [hdim, ← hd]
  change (Cardinal.toENat (Algebra.trdeg K L) : WithBot ℕ∞) = _
  rw [← he, ← hS.cardinalMk_eq_trdeg]
  simp

end PhilipponAlterationProjection



set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
attribute [local instance] MvPolynomial.gradedAlgebra

namespace PhilipponAlterationProjection

/-- The integral graph closure of a map on a dense open of a projective variety. -/
theorem exists_integral_projective_graph_closure
    (K : Type u) [Field K] {X Y : Scheme.{u}} [IsIntegral X]
    (π : X ⟶ Spec (.of K)) [IsProper π]
    (ρ : Y ⟶ Spec (.of K)) [IsProper ρ]
    (n : ℕ)
    (i : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K))
    [IsClosedImmersion i] (hi : i ≫ ProjSpace.π K n = π)
    (m : ℕ)
    (j : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) K))
    [IsClosedImmersion j] (hj : j ≫ ProjSpace.π K m = ρ)
    (U : X.Opens) (hU : Dense (U : Set X))
    (a : (U : Scheme) ⟶ Y) (ha : a ≫ ρ = U.ι ≫ π) :
    ∃ (G : Scheme.{u}) (p : G ⟶ X) (q : G ⟶ Y) (s : (U : Scheme) ⟶ G),
      IsIntegral G ∧ IsProper p ∧ Surjective p ∧ IsProper q ∧
      IsOpenImmersion s ∧ IsDominant s ∧
      (∀ u : (U : Scheme), IsIso (p.stalkMap (s u))) ∧
      s ≫ p = U.ι ∧ s ≫ q = a ∧ p ≫ π = q ≫ ρ ∧
      ∃ (d : ℕ)
        (k : G ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) K)),
        IsClosedImmersion k ∧ k ≫ ProjSpace.π K d = p ≫ π := by
  letI : Nonempty U := by
    obtain ⟨x, hx⟩ := hU.nonempty
    exact ⟨⟨x, hx⟩⟩
  letI : IsIntegral (U : Scheme) := inferInstance
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian π
  letI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace π
  letI : AlgebraicGeometry.IsNoetherian X := ⟨⟩
  letI : NoetherianSpace (U : Scheme) := U.ι.isOpenEmbedding.isInducing.noetherianSpace
  let b : (U : Scheme) ⟶ pullback π ρ := pullback.lift U.ι a ha.symm
  have hbfst : b ≫ pullback.fst π ρ = U.ι := by simp only [b, pullback.lift_fst]
  haveI : IsImmersion (b ≫ pullback.fst π ρ) := by rw [hbfst]; infer_instance
  haveI : IsImmersion b := IsImmersion.of_comp b (pullback.fst π ρ)
  haveI : QuasiCompact b := inferInstance
  obtain ⟨hG, _, _⟩ := b.isIntegral_image_and_isIso_stalkMap_toImage_genericPoint
  letI := hG
  let G := b.image
  let p : G ⟶ X := b.imageι ≫ pullback.fst π ρ
  let q : G ⟶ Y := b.imageι ≫ pullback.snd π ρ
  let s : (U : Scheme) ⟶ G := b.toImage
  have hsp : s ≫ p = U.ι := by
    simp only [s, p, ← Category.assoc, Scheme.Hom.toImage_imageι]
    exact hbfst
  have hsq : s ≫ q = a := by
    simp only [s, q, ← Category.assoc, Scheme.Hom.toImage_imageι]
    simp only [b, pullback.lift_snd]
  have hpfield : ∀ u : (U : Scheme), IsIso (p.stalkMap (s u)) := by
    intro u
    have h : IsIso ((s ≫ p).stalkMap u) := by rw [hsp]; infer_instance
    rw [Scheme.Hom.stalkMap_comp] at h
    letI : IsIso (p.stalkMap (s u) ≫ s.stalkMap u) := h
    exact IsIso.of_isIso_comp_right (p.stalkMap (s u)) (s.stalkMap u)
  have hsurj : Surjective p := by
    constructor
    have hc : IsClosed (Set.range p) := p.isClosedMap.isClosed_range
    have hsub : (U : Set X) ⊆ Set.range p := by
      intro x hx
      refine ⟨s ⟨x, hx⟩, ?_⟩
      have h := congrArg (fun f : (U : Scheme) ⟶ X => f ⟨x, hx⟩) hsp
      simpa only [Scheme.Hom.comp_apply, Scheme.Opens.ι_apply] using h
    have hall : Set.univ ⊆ Set.range p := by
      rw [← hU.closure_eq]
      exact closure_minimal hsub hc
    exact fun x => hall (Set.mem_univ x)
  obtain ⟨d, l, _, hl, hlπ⟩ :=
    AlgebraicGeometry.exists_isClosedImmersion_projSpace_pullback_of_isClosedImmersion
      π ρ n i inferInstance hi m j inferInstance hj
  letI := hl
  refine ⟨G, p, q, s, hG, inferInstance, hsurj, inferInstance,
    inferInstance, inferInstance, hpfield, hsp, hsq, ?_, d, b.imageι ≫ l, inferInstance, ?_⟩
  · simp only [p, q, Category.assoc, pullback.condition]
  · simp only [p, Category.assoc, hlπ]

end PhilipponAlterationProjection


set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory TopologicalSpace
attribute [local instance] MvPolynomial.gradedAlgebra

namespace PhilipponAlterationProjection

/-- Normal projective graph closure retaining a specified normal dense open chart. -/
theorem exists_normal_projective_graph_closure
    (K : Type u) [Field K] {X Y : Scheme.{u}} [IsIntegral X]
    (π : X ⟶ Spec (.of K)) [IsProper π]
    (ρ : Y ⟶ Spec (.of K)) [IsProper ρ]
    (n : ℕ)
    (i : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K))
    [IsClosedImmersion i] (hi : i ≫ ProjSpace.π K n = π)
    (m : ℕ)
    (j : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) K))
    [IsClosedImmersion j] (hj : j ≫ ProjSpace.π K m = ρ)
    (U : X.Opens) (hU : Dense (U : Set X))
    (hnormal : ∀ u : U, IsIntegrallyClosed (X.presheaf.stalk u.val))
    (a : (U : Scheme) ⟶ Y) (ha : a ≫ ρ = U.ι ≫ π) :
    ∃ (G : Scheme.{u}) (p : G ⟶ X) (q : G ⟶ Y) (s : (U : Scheme) ⟶ G),
      IsIntegral G ∧ (∀ z : G, IsIntegrallyClosed (G.presheaf.stalk z)) ∧
      topologicalKrullDim G = topologicalKrullDim X ∧
      IsProper p ∧ Surjective p ∧ IsProper q ∧
      IsOpenImmersion s ∧ IsDominant s ∧
      (∀ u : (U : Scheme), IsIso (p.stalkMap (s u))) ∧
      s ≫ p = U.ι ∧ s ≫ q = a ∧ p ≫ π = q ≫ ρ ∧
      ∃ (d : ℕ)
        (k : G ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) K)),
        IsClosedImmersion k ∧ k ≫ ProjSpace.π K d = p ≫ π := by
  obtain ⟨G, p, q, s, hG, hp, hsurj, hq, hs, hsdom, hpstalk, hsp, hsq, hbase,
    d, k, hk, hkbase⟩ :=
    exists_integral_projective_graph_closure K π ρ n i hi m j hj U hU a ha
  letI : Nonempty U := by
    obtain ⟨x, hx⟩ := hU.nonempty
    exact ⟨⟨x, hx⟩⟩
  letI := hG
  letI := hp
  letI := hq
  letI := hs
  letI := hk
  have hdim : topologicalKrullDim G = topologicalKrullDim X :=
    (dimension_eq_of_open_immersion s (p ≫ π)).symm.trans
      (dimension_eq_of_open_immersion U.ι π)
  have hnormalRange : ∀ u : (U : Scheme),
      IsIntegrallyClosed (G.presheaf.stalk (s u)) := by
    intro u
    have hu : p (s u) = u.val := by
      simpa only [Scheme.Hom.comp_apply, Scheme.Opens.ι_apply] using
        congrArg (fun f : (U : Scheme) ⟶ X => f u) hsp
    letI : IsIntegrallyClosed (X.presheaf.stalk (p (s u))) := by
      rw [hu]
      exact hnormal u
    letI := hpstalk u
    exact IsIntegrallyClosed.of_equiv (asIso (p.stalkMap (s u))).commRingCatIsoToRingEquiv
  obtain ⟨H, ν, s', hH, hnormalH, hν, hνsurj, hνdim, hs', hs'ν, _, l, k', hk', hk'base⟩ :=
    PhilipponProjectiveNormalization.exists_normal_projective_finite_cover_with_open_lift
      K (p ≫ π) d k hkbase s hnormalRange
  letI := hH
  letI := hν
  letI := hνsurj
  letI := hsurj
  letI := hs'
  have hsp' : s' ≫ (ν ≫ p) = U.ι := by rw [← Category.assoc, hs'ν, hsp]
  have hsq' : s' ≫ (ν ≫ q) = a := by rw [← Category.assoc, hs'ν, hsq]
  have hstalk : ∀ u : (U : Scheme), IsIso ((ν ≫ p).stalkMap (s' u)) := by
    intro u
    have h : IsIso ((s' ≫ (ν ≫ p)).stalkMap u) := by rw [hsp']; infer_instance
    rw [Scheme.Hom.stalkMap_comp] at h
    letI : IsIso ((ν ≫ p).stalkMap (s' u) ≫ s'.stalkMap u) := h
    exact IsIso.of_isIso_comp_right ((ν ≫ p).stalkMap (s' u)) (s'.stalkMap u)
  refine ⟨H, ν ≫ p, ν ≫ q, s', hH, hnormalH, hνdim.trans hdim,
    inferInstance, inferInstance, inferInstance, hs',
    ⟨s'.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace⟩,
    hstalk, hsp', hsq', ?_, l, k', hk', ?_⟩
  · rw [Category.assoc, hbase, Category.assoc]
  · simpa only [Category.assoc] using hk'base

end PhilipponAlterationProjection


set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory TopologicalSpace
attribute [local instance] MvPolynomial.gradedAlgebra

namespace PhilipponAlterationProjection

lemma projective_space_irreducible (K : Type u) [Field K] (n : ℕ) :
    IrreducibleSpace (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K)) := by
  let 𝒜 := MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K
  have hprime : (⊥ : HomogeneousIdeal 𝒜).toIdeal.IsPrime := by
    change (⊥ : Ideal (MvPolynomial (Fin (n + 1)) K)).IsPrime
    infer_instance
  have hrel : ¬ HomogeneousIdeal.irrelevant 𝒜 ≤ ⊥ := by
    intro h
    have hX : (MvPolynomial.X (0 : Fin (n + 1)) : MvPolynomial _ K) ∈
        HomogeneousIdeal.irrelevant 𝒜 :=
      HomogeneousIdeal.mem_irrelevant_of_mem _ (by decide : 0 < 1)
        (ProjSpace.X_mem_one K n 0)
    have hz : (MvPolynomial.X (0 : Fin (n + 1)) : MvPolynomial _ K) = 0 := by
      change MvPolynomial.X 0 ∈ (⊥ : Ideal (MvPolynomial (Fin (n + 1)) K))
      exact h hX
    exact MvPolynomial.X_ne_zero _ hz
  let η : ProjectiveSpectrum 𝒜 := ⟨⊥, hprime, hrel⟩
  have hη : IsGenericPoint η (Set.univ : Set (ProjectiveSpectrum 𝒜)) := by
    apply Set.eq_univ_of_forall
    intro y
    exact (ProjectiveSpectrum.le_iff_mem_closure 𝒜 η y).mp (show
      η.asHomogeneousIdeal ≤ y.asHomogeneousIdeal from bot_le)
  exact (irreducibleSpace_def _).mpr hη.isIrreducible

/-- The proper extension of a dominant affine map through an affine projective chart is surjective. -/
lemma projective_projection_surjective_of_dense_affine_chart
    (K : Type u) [Field K] (n : ℕ) (ι : Type u) {U G : Scheme.{u}}
    (f : U ⟶ Spec (.of (MvPolynomial ι K))) [IsDominant f]
    (e : Spec (.of (MvPolynomial ι K)) ⟶
      Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K))
    [IsOpenImmersion e]
    (q : G ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K))
    [IsProper q] (t : U ⟶ G) (htq : t ≫ q = f ≫ e) : Surjective q := by
  letI := projective_space_irreducible K n
  haveI : IsDominant e :=
    ⟨IsOpenMap.denseRange_of_isPreirreducibleSpace e e.isOpenEmbedding.isOpenMap⟩
  haveI : IsDominant (t ≫ q) := by rw [htq]; infer_instance
  haveI : IsDominant q := IsDominant.of_comp t q
  infer_instance

end PhilipponAlterationProjection



set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory

namespace PhilipponAlterationProjection

noncomputable def forgetParameterMap (K : Type u) [Field K] {ι κ : Type u}
    (j : κ ↪ ι) : Spec (.of (MvPolynomial ι K)) ⟶ Spec (.of (MvPolynomial κ K)) :=
  Spec.map (CommRingCat.ofHom (MvPolynomial.rename (R := K) j))

instance forgetParameterMap_dominant (K : Type u) [Field K] {ι κ : Type u}
    (j : κ ↪ ι) : IsDominant (forgetParameterMap K j) := by
  constructor
  let φ : MvPolynomial κ K →+* MvPolynomial ι K :=
    (MvPolynomial.rename (R := K) j).toRingHom
  change DenseRange (PrimeSpectrum.comap φ)
  apply (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical
    φ).mpr
  rw [(RingHom.injective_iff_ker_eq_bot φ).mp (MvPolynomial.rename_injective j j.injective)]
  exact bot_le

lemma forgetParameterMap_over (K : Type u) [Field K] {ι κ : Type u} (j : κ ↪ ι) :
    forgetParameterMap K j ≫
      Spec.map (CommRingCat.ofHom (MvPolynomial.C : K →+* MvPolynomial κ K)) =
      Spec.map (CommRingCat.ofHom (MvPolynomial.C : K →+* MvPolynomial ι K)) := by
  unfold forgetParameterMap
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact RingHom.ext (fun x => MvPolynomial.rename_C j x)

end PhilipponAlterationProjection



set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
open Algebra

namespace PhilipponAlterationProjection

/-- Removing one element of a transcendence basis leaves a one-parameter basis over the field
generated by the other elements. -/
lemma one_parameter_basis
    (K F : Type u) [Field K] [Field F] [Algebra K F]
    (S T : Finset F) (x : S)
    (hb : IsTranscendenceBasis K ((↑) : S → F))
    (hT : (T : Set F) = (S : Set F) \ {x.val}) :
    IsTranscendenceBasis (IntermediateField.adjoin K (T : Set F))
      (fun _ : Unit => x.val) := by
  classical
  let L := IntermediateField.adjoin K (T : Set F)
  have hrange : ((↑) : S → F) '' ({x}ᶜ : Set S) = (T : Set F) := by
    rw [hT]
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨z.property, ?_⟩
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff, Subtype.ext_iff] using hz
    · rintro ⟨hy, hne⟩
      refine ⟨⟨y, hy⟩, ?_, rfl⟩
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff, Subtype.ext_iff] using hne
  have hxtr : Transcendental L x.val := by
    apply IntermediateField.transcendental_adjoin_iff.mpr
    have h := hb.1.transcendental_adjoin (s := ({x}ᶜ : Set S)) (i := x) (by simp)
    rwa [hrange] at h
  have hxind : AlgebraicIndependent L (fun _ : Unit => x.val) :=
    (algebraicIndependent_unique_type_iff (ι := Unit)).mpr hxtr
  let B := Algebra.adjoin L ({x.val} : Set F)
  have hB : ∀ z : S, IsAlgebraic B z.val := by
    intro z
    have hzB : z.val ∈ B := by
      by_cases hzx : z.val = x.val
      · exact hzx ▸ Algebra.subset_adjoin (Set.mem_singleton x.val)
      · have hzT : z.val ∈ T := by
          rw [← Finset.mem_coe, hT]
          exact ⟨z.property, hzx⟩
        exact B.algebraMap_mem (⟨z.val, IntermediateField.subset_adjoin K _ hzT⟩ : L)
    exact isAlgebraic_algebraMap (⟨z.val, hzB⟩ : B)
  have hAlg : Algebra.IsAlgebraic B F := hb.isAlgebraic_iff.mpr hB
  apply hxind.isTranscendenceBasis_iff_isAlgebraic.mpr
  change Algebra.IsAlgebraic (Algebra.adjoin L (Set.range (fun _ : Unit => x.val))) F
  rw [Set.range_const]
  exact hAlg

end PhilipponAlterationProjection



set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory TopologicalSpace
attribute [local instance] MvPolynomial.gradedAlgebra

namespace PhilipponAlterationProjection

/-- A normal proper projective projection of relative transcendence dimension one. -/
theorem exists_normal_projective_curve_projection_model
    (K : Type u) [Field K] [PerfectField K] {X : Scheme.{u}} [IsIntegral X]
    (π : X ⟶ Spec (.of K)) [IsProper π] (n : ℕ)
    (i : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K))
    [IsClosedImmersion i] (hi : i ≫ ProjSpace.π K n = π)
    (hnormalX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hdim : 1 < topologicalKrullDim X) :
    letI : Algebra K X.functionField :=
      ((Scheme.ΓSpecIso (.of K)).inv ≫ π.appTop ≫
        X.presheaf.germ ⊤ (genericPoint X) trivial).hom.toAlgebra
    ∃ S : Finset X.functionField,
      IsTranscendenceBasis K ((↑) : S → X.functionField) ∧
      Module.Finite (IntermediateField.adjoin K (S : Set X.functionField)) X.functionField ∧
      Algebra.IsSeparable (IntermediateField.adjoin K (S : Set X.functionField)) X.functionField ∧
      ∃ (x : S) (T : Finset X.functionField) (j : T ↪ S),
        (T : Set X.functionField) = (S : Set X.functionField) \ {x.val} ∧
        (∀ z : T, (j z).val = z.val) ∧
        0 < Fintype.card T ∧
        topologicalKrullDim X = ((Fintype.card T + 1 : ℕ) : WithBot ℕ∞) ∧
        IsTranscendenceBasis (IntermediateField.adjoin K (T : Set X.functionField))
          (fun _ : Unit => x.val) ∧
        Algebra.trdeg (IntermediateField.adjoin K (T : Set X.functionField)) X.functionField = 1 ∧
        ∃ (U : X.Opens) (hU : IsAffineOpen U), Dense (U : Set X) ∧
          ∃ hne : Nonempty U, ∃ a : S → Γ(X, U),
            (∀ z : S, @Scheme.germToFunctionField X _ U hne (a z) = z.val) ∧
            ∃ f : (U : Scheme) ⟶ Spec (.of (MvPolynomial S K)),
              f = hU.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom
                (MvPolynomial.eval₂Hom
                  ((Scheme.ΓSpecIso (.of K)).inv ≫ π.appLE ⊤ U (by simp)).hom a)) ∧
              IsDominant f ∧
              f ≫ Spec.map (CommRingCat.ofHom (MvPolynomial.C : K →+* MvPolynomial S K)) = U.ι ≫ π ∧
              ∃ (G : Scheme.{u}) (p : G ⟶ X)
                (q : G ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (Fintype.card T + 1)) K))
                (t : (U : Scheme) ⟶ G)
                (e : Spec (.of (MvPolynomial T K)) ⟶
                  Proj (MvPolynomial.homogeneousSubmodule (Fin (Fintype.card T + 1)) K)),
                IsIntegral G ∧ (∀ g : G, IsIntegrallyClosed (G.presheaf.stalk g)) ∧
                topologicalKrullDim G = topologicalKrullDim X ∧
                IsProper p ∧ Surjective p ∧ IsProper q ∧ Surjective q ∧
                IsOpenImmersion t ∧ IsDominant t ∧
                (∀ u : (U : Scheme), IsIso (p.stalkMap (t u))) ∧
                IsOpenImmersion e ∧
                e ≫ ProjSpace.π K (Fintype.card T) =
                  Spec.map (CommRingCat.ofHom (MvPolynomial.C : K →+* MvPolynomial T K)) ∧
                t ≫ p = U.ι ∧
                t ≫ q = f ≫ Spec.map (CommRingCat.ofHom (MvPolynomial.rename (R := K) j)) ≫ e ∧
                p ≫ π = q ≫ ProjSpace.π K (Fintype.card T) ∧
                ∃ (d : ℕ)
                  (k : G ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) K)),
                  IsClosedImmersion k ∧ k ≫ ProjSpace.π K d = p ≫ π := by
  classical
  letI : Algebra K X.functionField :=
    ((Scheme.ΓSpecIso (.of K)).inv ≫ π.appTop ≫
      X.presheaf.germ ⊤ (genericPoint X) trivial).hom.toAlgebra
  obtain ⟨S, hb, hf, hsep, U, hU, hdense, hne, a, ha, f, hfeq, hdom, hover⟩ :=
    AlgebraicGeometry.exists_dense_affine_separating_function_field_parameters K π
  have hSdim := dimension_eq_card_of_function_field_basis π S hb
  have hcard : 1 < S.card := by
    rw [hSdim] at hdim
    simp only [Fintype.card_coe] at hdim
    exact_mod_cast hdim
  obtain ⟨x, hx⟩ := Finset.card_pos.mp (lt_trans Nat.zero_lt_one hcard)
  let T := S.erase x
  let j : T ↪ S :=
    { toFun := fun z => ⟨z.val, Finset.mem_of_mem_erase z.property⟩
      inj' := by
        intro z w h
        apply Subtype.ext
        exact congrArg (fun y : S => y.val) h }
  have hTcard : T.card + 1 = S.card := Finset.card_erase_add_one hx
  have hTpos : 0 < Fintype.card T := by
    simp only [Fintype.card_coe]
    omega
  have hdim' : topologicalKrullDim X = ((Fintype.card T + 1 : ℕ) : WithBot ℕ∞) := by
    simpa only [Fintype.card_coe, hTcard] using hSdim
  have hTset : (T : Set X.functionField) = (S : Set X.functionField) \ {x} :=
    Finset.coe_erase x S
  have hrel := one_parameter_basis K X.functionField S T ⟨x, hx⟩ hb hTset
  have htrdeg : Algebra.trdeg (IntermediateField.adjoin K (T : Set X.functionField))
      X.functionField = 1 := by
    simpa using hrel.lift_cardinalMk_eq_trdeg.symm
  letI := hne
  letI := hdom
  let e := ProjectiveAffineChart.finiteVariableEmbedding K T
  let f' := f ≫ forgetParameterMap K j
  let b := f' ≫ e
  have hbbase : b ≫ ProjSpace.π K (Fintype.card T) = U.ι ≫ π := by
    dsimp only [b, f', e]
    rw [Category.assoc, Category.assoc,
      ProjectiveAffineChart.finiteVariableEmbedding_over,
      forgetParameterMap_over, hover]
  obtain ⟨G, p, q, t, hG, hnormalG, hGdim, hp, hsurj, hq, ht, htdom, hpstalk,
    htp, htq, hbase, d, k, hk, hkbase⟩ :=
    exists_normal_projective_graph_closure K π (ProjSpace.π K (Fintype.card T))
      n i hi (Fintype.card T) (𝟙 _) (by simp) U hdense
      (fun u => hnormalX u.val) b hbbase
  letI := hq
  have hsq : Surjective q := projective_projection_surjective_of_dense_affine_chart
    K (Fintype.card T) T f' e q t htq
  refine ⟨S, hb, hf, hsep, ⟨x, hx⟩, T, j, hTset, ?_, hTpos, hdim', hrel, htrdeg,
    U, hU, hdense, hne, a, ha, f, hfeq, hdom, hover,
    G, p, q, t, e, hG, hnormalG, hGdim, hp, hsurj, hq, hsq, ht, htdom, hpstalk,
    inferInstance, ?_, htp, ?_, hbase, d, k, hk, hkbase⟩
  · intro z
    rfl
  · exact ProjectiveAffineChart.finiteVariableEmbedding_over K T
  · simpa only [b, f', forgetParameterMap, Category.assoc] using htq

end PhilipponAlterationProjection


theorem solution
    (K : Type u) [Field K] [PerfectField K] {X : Scheme.{u}} [IsIntegral X]
    (π : X ⟶ Spec (.of K)) [IsProper π] (n : ℕ)
    (i : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K))
    [IsClosedImmersion i] (hi : i ≫ ProjSpace.π K n = π)
    (hnormalX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (hdim : 1 < topologicalKrullDim X) :
    letI : Algebra K X.functionField :=
      ((Scheme.ΓSpecIso (.of K)).inv ≫ π.appTop ≫
        X.presheaf.germ ⊤ (genericPoint X) trivial).hom.toAlgebra
    ∃ S : Finset X.functionField,
      IsTranscendenceBasis K ((↑) : S → X.functionField) ∧
      Module.Finite (IntermediateField.adjoin K (S : Set X.functionField)) X.functionField ∧
      Algebra.IsSeparable (IntermediateField.adjoin K (S : Set X.functionField)) X.functionField ∧
      ∃ (x : S) (T : Finset X.functionField) (j : T ↪ S),
        (T : Set X.functionField) = (S : Set X.functionField) \ {x.val} ∧
        (∀ z : T, (j z).val = z.val) ∧
        0 < Fintype.card T ∧
        topologicalKrullDim X = ((Fintype.card T + 1 : ℕ) : WithBot ℕ∞) ∧
        IsTranscendenceBasis (IntermediateField.adjoin K (T : Set X.functionField))
          (fun _ : Unit => x.val) ∧
        Algebra.trdeg (IntermediateField.adjoin K (T : Set X.functionField)) X.functionField = 1 ∧
        ∃ (U : X.Opens) (hU : IsAffineOpen U), Dense (U : Set X) ∧
          ∃ hne : Nonempty U, ∃ a : S → Γ(X, U),
            (∀ z : S, @Scheme.germToFunctionField X _ U hne (a z) = z.val) ∧
            ∃ f : (U : Scheme) ⟶ Spec (.of (MvPolynomial S K)),
              f = hU.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom
                (MvPolynomial.eval₂Hom
                  ((Scheme.ΓSpecIso (.of K)).inv ≫ π.appLE ⊤ U (by simp)).hom a)) ∧
              IsDominant f ∧
              f ≫ Spec.map (CommRingCat.ofHom (MvPolynomial.C : K →+* MvPolynomial S K)) = U.ι ≫ π ∧
              ∃ (G : Scheme.{u}) (p : G ⟶ X)
                (q : G ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (Fintype.card T + 1)) K))
                (t : (U : Scheme) ⟶ G)
                (e : Spec (.of (MvPolynomial T K)) ⟶
                  Proj (MvPolynomial.homogeneousSubmodule (Fin (Fintype.card T + 1)) K)),
                IsIntegral G ∧ (∀ g : G, IsIntegrallyClosed (G.presheaf.stalk g)) ∧
                topologicalKrullDim G = topologicalKrullDim X ∧
                IsProper p ∧ Surjective p ∧ IsProper q ∧ Surjective q ∧
                IsOpenImmersion t ∧ IsDominant t ∧
                (∀ u : (U : Scheme), IsIso (p.stalkMap (t u))) ∧
                IsOpenImmersion e ∧
                e ≫ ProjSpace.π K (Fintype.card T) =
                  Spec.map (CommRingCat.ofHom (MvPolynomial.C : K →+* MvPolynomial T K)) ∧
                t ≫ p = U.ι ∧
                t ≫ q = f ≫ Spec.map (CommRingCat.ofHom (MvPolynomial.rename (R := K) j)) ≫ e ∧
                p ≫ π = q ≫ ProjSpace.π K (Fintype.card T) ∧
                ∃ (d : ℕ)
                  (k : G ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) K)),
                  IsClosedImmersion k ∧ k ≫ ProjSpace.π K d = p ≫ π := by
  exact PhilipponAlterationProjection.exists_normal_projective_curve_projection_model K π n i hi hnormalX hdim
