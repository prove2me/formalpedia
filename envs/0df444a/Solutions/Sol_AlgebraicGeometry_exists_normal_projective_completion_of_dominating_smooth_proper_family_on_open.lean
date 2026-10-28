-- Prove2me | solution 1 for AlgebraicGeometry.exists_normal_projective_completion_of_dominating_smooth_proper_family_on_open
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-25T22:43:11.28809+00:00
-- url     : https://prove2.me/submissions/98f51fd1-2e5b-4c94-8b9b-7658d923980b

import Definitions.Def_AlgebraicGeometry_ModulesGlueOfCocycle
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Mathlib
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isIntegral_image_and_isIso_stalkMap_toImage_genericPoint
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top
import Theorems.Thm_AlgebraicGeometry_Smooth_isDomain_and_isIntegrallyClosed_stalk
import Theorems.Thm_AlgebraicGeometry_exists_isClosedImmersion_projSpace_pullback_of_isClosedImmersion
import Theorems.Thm_AlgebraicGeometry_exists_isFinite_isIntegrallyClosed_stalk_isIso_morphismRestrict_of_isIntegral
import Theorems.Thm_AlgebraicGeometry_toENat_trdeg_residueField_eq_topologicalKrullDim_closure
import Theorems.Thm_HomogeneousIdeal_exists_homogeneous_pos_mem_forall_notMem

universe u v
noncomputable section

/- Finite projective normalization with a retained normal affine chart.
Reuses the accepted source for 7d122c2e-85fc-4c12-80b1-6a0ba09d0dca.
The unrelated separating-parameter theorem is omitted. -/



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
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory TopologicalSpace
attribute [local instance] MvPolynomial.gradedAlgebra


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


set_option linter.style.haveILetI false
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
namespace PhilipponDominatingIntegralOpen

/-- A dense continuous image of a noetherian space into an irreducible space
already has a dense image on an irreducible open of the source. -/
lemma exists_irreducible_open_dense_image
    {Y X : Type u} [TopologicalSpace Y] [TopologicalSpace X]
    [NoetherianSpace Y] [IrreducibleSpace X]
    (f : Y → X) (hf : Continuous f) (hd : DenseRange f) :
    ∃ U : Set Y, IsOpen U ∧ IsIrreducible U ∧ Dense (f '' U) := by
  classical
  let C := irreducibleComponents Y
  have hC : C.Finite := NoetherianSpace.finite_irreducibleComponents
  let T := (fun Z : Set Y => closure (f '' Z)) '' C
  have hT : T.Finite := hC.image _
  have hclosed : ∀ A ∈ T, IsClosed A := by
    rintro A ⟨Z, _, rfl⟩
    exact isClosed_closure
  have hcover : (Set.univ : Set X) ⊆ ⋃₀ T := by
    have hsub : Set.range f ⊆ ⋃₀ T := by
      rintro x ⟨y, rfl⟩
      apply Set.mem_sUnion.mpr
      refine ⟨closure (f '' irreducibleComponent y), ?_, ?_⟩
      · exact ⟨irreducibleComponent y, irreducibleComponent_mem_irreducibleComponents y, rfl⟩
      · exact subset_closure ⟨y, mem_irreducibleComponent, rfl⟩
    rw [← hd.closure_range]
    exact closure_minimal hsub (by
      rw [Set.sUnion_eq_biUnion]
      exact hT.isClosed_biUnion hclosed)
  obtain ⟨A, hAT, hA⟩ := isIrreducible_iff_sUnion_isClosed.mp
    (IrreducibleSpace.isIrreducible_univ X : IsIrreducible (Set.univ : Set X)) hT.toFinset
    (by simpa using hclosed) (by simpa using hcover)
  have hAT' : A ∈ T := by simpa using hAT
  obtain ⟨Z, hZ, rfl⟩ := hAT'
  have hZd : closure (f '' Z) = Set.univ := Set.eq_univ_of_univ_subset hA
  let U := (⋃₀ (C \ {Z}))ᶜ
  have hU : IsOpen U := by
    dsimp only [U]
    rw [isOpen_compl_iff, Set.sUnion_eq_biUnion]
    exact hC.sdiff.isClosed_biUnion (fun W hW => isClosed_of_mem_irreducibleComponents W hW.1)
  have hUZ : closure U = Z := closure_sUnion_irreducibleComponents_sdiff_singleton hC Z hZ
  refine ⟨U, hU, ?_, ?_⟩
  · exact isIrreducible_iff_closure.mp (hUZ.symm ▸ hZ.1)
  · rw [dense_iff_closure_eq, ← closure_image_closure hf, hUZ, hZd]

lemma exists_integral_open_dominant
    {Y X : Scheme.{u}} [IsReduced Y] [NoetherianSpace Y] [IsIntegral X]
    (f : Y ⟶ X) [IsDominant f] :
    ∃ U : Y.Opens, IsIntegral U ∧ IsDominant (U.ι ≫ f) := by
  obtain ⟨U, hU, hiU, hdU⟩ := exists_irreducible_open_dense_image f f.continuous f.denseRange
  let V : Y.Opens := ⟨U, hU⟩
  haveI : IrreducibleSpace V := Subtype.irreducibleSpace hiU
  have hV : IsIntegral V := isIntegral_of_irreducibleSpace_of_isReduced _
  refine ⟨V, hV, ⟨?_⟩⟩
  have heq : Set.range (V.ι ≫ f) = f '' U := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y.1, y.2, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, hy⟩, rfl⟩
  change Dense (Set.range (V.ι ≫ f))
  rw [heq]
  exact hdU

end PhilipponDominatingIntegralOpen

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
namespace PhilipponNormalComponents

/-- A domain stalk forces all components through the point to be the
closure of the same irreducible local spectrum. -/
lemma component_eq_closure_stalk_range
    {X : Scheme.{u}} (x : X) [IsDomain (X.presheaf.stalk x)]
    {Z : Set X} (hZ : Z ∈ irreducibleComponents X) (hx : x ∈ Z) :
    Z = closure (Set.range (X.fromSpecStalk x)) := by
  have hR : IsIrreducible (closure (Set.range (X.fromSpecStalk x))) := by
    simpa only [Set.image_univ] using
      ((IrreducibleSpace.isIrreducible_univ (Spec (X.presheaf.stalk x))).image
        (X.fromSpecStalk x) (X.fromSpecStalk x).continuous.continuousOn).closure
  have hg := hZ.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents Z hZ)
  have hm : hZ.1.genericPoint ∈ Set.range (X.fromSpecStalk x) := by
    rw [Scheme.range_fromSpecStalk]
    exact hg.specializes hx
  have hsub : Z ⊆ closure (Set.range (X.fromSpecStalk x)) := by
    rw [← hg.def]
    exact closure_mono (Set.singleton_subset_iff.mpr hm)
  exact hsub.antisymm (hZ.2 hR hsub)

lemma component_eq_of_mem
    {X : Scheme.{u}} (hX : ∀ x : X, IsDomain (X.presheaf.stalk x))
    {Z W : Set X} (hZ : Z ∈ irreducibleComponents X) (hW : W ∈ irreducibleComponents X)
    (x : X) (hxZ : x ∈ Z) (hxW : x ∈ W) : Z = W := by
  haveI := hX x
  exact (component_eq_closure_stalk_range x hZ hxZ).trans
    (component_eq_closure_stalk_range x hW hxW).symm

lemma isClopen_component
    {X : Scheme.{u}} [NoetherianSpace X]
    (hX : ∀ x : X, IsDomain (X.presheaf.stalk x))
    {Z : Set X} (hZ : Z ∈ irreducibleComponents X) : IsClopen Z := by
  classical
  have heq : Z = (⋃₀ (irreducibleComponents X \ {Z}))ᶜ := by
    ext x
    constructor
    · intro hx hother
      obtain ⟨W, hW, hxW⟩ := Set.mem_sUnion.mp hother
      have he := component_eq_of_mem hX hZ hW.1 x hx hxW
      exact hW.2 (Set.mem_singleton_iff.mpr he.symm)
    · intro hx
      obtain ⟨W, hW, hxW⟩ := Set.mem_sUnion.mp
        (show x ∈ ⋃₀ irreducibleComponents X by rw [sUnion_irreducibleComponents]; trivial)
      have he : W = Z := by
        by_contra hn
        exact hx (Set.mem_sUnion.mpr ⟨W, ⟨hW, by simpa using hn⟩, hxW⟩)
      simpa only [he] using hxW
  refine ⟨isClosed_of_mem_irreducibleComponents Z hZ, ?_⟩
  rw [heq, isOpen_compl_iff, Set.sUnion_eq_biUnion]
  exact NoetherianSpace.finite_irreducibleComponents.sdiff.isClosed_biUnion
    (fun W hW => isClosed_of_mem_irreducibleComponents W hW.1)

/-- Selecting an integral component of a locally domain noetherian scheme
preserves properness of maps out of it, because its inclusion is also closed. -/
lemma exists_integral_clopen_dominant
    {Y X : Scheme.{u}} [NoetherianSpace Y] [IsIntegral X]
    (hY : ∀ y : Y, IsDomain (Y.presheaf.stalk y)) (f : Y ⟶ X) [IsDominant f] :
    ∃ U : Y.Opens, IsIntegral U ∧ IsClosedImmersion U.ι ∧ IsDominant (U.ι ≫ f) := by
  haveI (y : Y) : IsDomain (Y.presheaf.stalk y) := hY y
  haveI : IsReduced Y := isReduced_of_isReduced_stalk Y
  obtain ⟨V, _hV, hiV, hdV⟩ :=
    PhilipponDominatingIntegralOpen.exists_irreducible_open_dense_image f f.continuous f.denseRange
  obtain ⟨Z, hZ, hVZ⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible V hiV
  have hcZ := isClopen_component hY hZ
  let U : Y.Opens := ⟨Z, hcZ.2⟩
  haveI : IrreducibleSpace U := Subtype.irreducibleSpace hZ.1
  have hiU : IsIntegral U := isIntegral_of_irreducibleSpace_of_isReduced _
  have hcU : IsClosedImmersion U.ι := IsClosedImmersion.of_isPreimmersion U.ι (by
    rw [Scheme.Opens.range_ι]
    change IsClosed Z
    exact hcZ.1)
  refine ⟨U, hiU, hcU, ⟨?_⟩⟩
  have heq : Set.range (U.ι ≫ f) = f '' Z := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y.1, y.2, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, hy⟩, rfl⟩
  change Dense (Set.range (U.ι ≫ f))
  rw [heq]
  exact hdV.mono (Set.image_mono hVZ)

end PhilipponNormalComponents

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
attribute [local instance] MvPolynomial.gradedAlgebra
namespace PhilipponTwoMapGraph

lemma surjective_of_proper_of_dominant
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] [IsDominant f] : Surjective f := by
  have he : Set.range f = Set.univ :=
    f.isClosedMap.isClosed_range.closure_eq.symm.trans f.denseRange.closure_range
  exact ⟨Set.range_eq_univ.mp he⟩

/-- The projective graph closure simultaneously retains the given map to
the original variety and the given map to its altered projective base. -/
theorem exists_integral_projective_graph
    (k : Type u) [Field k] {Y X S : Scheme.{u}} [IsIntegral Y] [CompactSpace Y]
    (n : ℕ) (j : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k))
    [IsImmersion j]
    (πX : X ⟶ Spec (.of k)) [IsProper πX]
    (mX : ℕ) (iX : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (mX + 1)) k))
    [IsClosedImmersion iX] (hiX : iX ≫ ProjSpace.π k mX = πX)
    (πS : S ⟶ Spec (.of k)) [IsProper πS]
    (mS : ℕ) (iS : S ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (mS + 1)) k))
    [IsClosedImmersion iS] (hiS : iS ≫ ProjSpace.π k mS = πS)
    (a : Y ⟶ X) [IsDominant a] (b : Y ⟶ S) [IsDominant b]
    (hab : a ≫ πX = b ≫ πS) (ha : a ≫ πX = j ≫ ProjSpace.π k n) :
    ∃ (G : Scheme.{u}) (qX : G ⟶ X) (qS : G ⟶ S) (t : Y ⟶ G),
      IsIntegral G ∧ IsProper qX ∧ Surjective qX ∧ IsProper qS ∧ Surjective qS ∧
      IsOpenImmersion t ∧ IsDominant t ∧ t ≫ qX = a ∧ t ≫ qS = b ∧
      qX ≫ πX = qS ≫ πS ∧ topologicalKrullDim G = topologicalKrullDim Y ∧
      ∃ (d : ℕ) (l : G ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) k)),
        IsClosedImmersion l ∧ l ≫ ProjSpace.π k d = qX ≫ πX := by
  let XS := pullback πX πS
  let πXS : XS ⟶ Spec (.of k) := pullback.fst πX πS ≫ πX
  haveI : IsProper πXS := inferInstance
  obtain ⟨dXS, lXS, _hdXS, hlXS, hXSbase⟩ :=
    AlgebraicGeometry.exists_isClosedImmersion_projSpace_pullback_of_isClosedImmersion
      πX πS mX iX inferInstance hiX mS iS inferInstance hiS
  haveI : IsClosedImmersion lXS := hlXS
  obtain ⟨dT, lT, _hdT, hlT, hTbase⟩ :=
    AlgebraicGeometry.exists_isClosedImmersion_projSpace_pullback_of_isClosedImmersion
      (ProjSpace.π k n) πXS n (𝟙 _) inferInstance (Category.id_comp _)
      dXS lXS inferInstance hXSbase
  haveI : IsClosedImmersion lT := hlT
  let ab : Y ⟶ XS := pullback.lift a b hab
  let γ : Y ⟶ pullback (ProjSpace.π k n) πXS := pullback.lift j ab (by
    dsimp only [πXS]
    rw [← Category.assoc, pullback.lift_fst]
    exact ha.symm)
  haveI : IsImmersion (γ ≫ pullback.fst (ProjSpace.π k n) πXS) := by
    rw [pullback.lift_fst]
    infer_instance
  haveI : IsImmersion γ := IsImmersion.of_comp γ (pullback.fst (ProjSpace.π k n) πXS)
  haveI : QuasiSeparatedSpace XS := quasiSeparatedSpace_of_quasiSeparated πXS
  haveI : QuasiSeparatedSpace (pullback (ProjSpace.π k n) πXS : Scheme.{u}) :=
    quasiSeparatedSpace_of_quasiSeparated (pullback.snd (ProjSpace.π k n) πXS)
  haveI : QuasiCompact γ := inferInstance
  obtain ⟨hG, _, _⟩ := γ.isIntegral_image_and_isIso_stalkMap_toImage_genericPoint
  haveI := hG
  let G := γ.image
  let qX : G ⟶ X := γ.imageι ≫ pullback.snd (ProjSpace.π k n) πXS ≫ pullback.fst πX πS
  let qS : G ⟶ S := γ.imageι ≫ pullback.snd (ProjSpace.π k n) πXS ≫ pullback.snd πX πS
  let t : Y ⟶ G := γ.toImage
  have htX : t ≫ qX = a := by
    simp only [t, qX, ← Category.assoc, Scheme.Hom.toImage_imageι,
      γ, pullback.lift_snd, ab, pullback.lift_fst]
  have htS : t ≫ qS = b := by
    simp only [t, qS, ← Category.assoc, Scheme.Hom.toImage_imageι,
      γ, pullback.lift_snd, ab, pullback.lift_snd]
  haveI : IsDominant (t ≫ qX) := by rw [htX]; infer_instance
  haveI : IsDominant (t ≫ qS) := by rw [htS]; infer_instance
  haveI : IsDominant qX := IsDominant.of_comp t qX
  haveI : IsDominant qS := IsDominant.of_comp t qS
  have hqX : Surjective qX := surjective_of_proper_of_dominant qX
  have hqS : Surjective qS := surjective_of_proper_of_dominant qS
  have hbase : qX ≫ πX = qS ≫ πS := by
    dsimp only [qX, qS]
    simp only [Category.assoc, pullback.condition]
  have hdG : topologicalKrullDim G = topologicalKrullDim Y :=
    (PhilipponAlterationProjection.dimension_eq_of_open_immersion t (qX ≫ πX)).symm
  refine ⟨G, qX, qS, t, hG, inferInstance, hqX, inferInstance, hqS,
    inferInstance, inferInstance, htX, htS, hbase, hdG, dT, γ.imageι ≫ lT, inferInstance, ?_⟩
  simpa only [qX, πXS, Category.assoc] using
    congrArg (fun f => γ.imageι ≫ f)
      (hTbase.trans (pullback.condition (f := ProjSpace.π k n) (g := πXS)))

end PhilipponTwoMapGraph

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
attribute [local instance] MvPolynomial.gradedAlgebra
namespace PhilipponTwoMapNormalGraph

/-- Finite normalization retains both original maps and the specified normal source open. -/
theorem exists_normal_projective_graph
    (k : Type u) [Field k] {Y X S : Scheme.{u}} [IsIntegral Y] [CompactSpace Y]
    (hnY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    (n : ℕ) (j : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k))
    [IsImmersion j]
    (πX : X ⟶ Spec (.of k)) [IsProper πX]
    (mX : ℕ) (iX : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (mX + 1)) k))
    [IsClosedImmersion iX] (hiX : iX ≫ ProjSpace.π k mX = πX)
    (πS : S ⟶ Spec (.of k)) [IsProper πS]
    (mS : ℕ) (iS : S ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (mS + 1)) k))
    [IsClosedImmersion iS] (hiS : iS ≫ ProjSpace.π k mS = πS)
    (a : Y ⟶ X) [IsDominant a] (b : Y ⟶ S) [IsDominant b]
    (hab : a ≫ πX = b ≫ πS) (ha : a ≫ πX = j ≫ ProjSpace.π k n) :
    ∃ (G : Scheme.{u}) (qX : G ⟶ X) (qS : G ⟶ S) (t : Y ⟶ G),
      IsIntegral G ∧ (∀ x : G, IsIntegrallyClosed (G.presheaf.stalk x)) ∧ IsProper qX ∧ Surjective qX ∧ IsProper qS ∧ Surjective qS ∧
      IsOpenImmersion t ∧ IsDominant t ∧ t ≫ qX = a ∧ t ≫ qS = b ∧
      qX ≫ πX = qS ≫ πS ∧ topologicalKrullDim G = topologicalKrullDim Y ∧
      ∃ (d : ℕ) (l : G ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) k)),
        IsClosedImmersion l ∧ l ≫ ProjSpace.π k d = qX ≫ πX := by
  obtain ⟨G, qX, qS, t, hG, hqX, hsqX, hqS, hsqS, ht, hdt, htX, htS,
    hbase, hdG, d, l, hl, hlbase⟩ :=
    PhilipponTwoMapGraph.exists_integral_projective_graph
      k n j πX mX iX hiX πS mS iS hiS a b hab ha
  haveI := hG
  haveI := hqX
  haveI := hqS
  haveI := hsqX
  haveI := hsqS
  haveI := ht
  haveI := hl
  have hnormalRange (y : Y) : IsIntegrallyClosed (G.presheaf.stalk (t y)) := by
    haveI := hnY y
    exact IsIntegrallyClosed.of_equiv (asIso (t.stalkMap y)).symm.commRingCatIsoToRingEquiv
  obtain ⟨N, ν, w, hN, hnN, hν, hsν, hdν, hw, hwν, _hiso, e, v, hv, hvbase⟩ :=
    PhilipponProjectiveNormalization.exists_normal_projective_finite_cover_with_open_lift
      k (qX ≫ πX) d l hlbase t hnormalRange
  haveI := hN
  haveI := hν
  haveI := hsν
  haveI := hw
  let fX : N ⟶ X := ν ≫ qX
  let fS : N ⟶ S := ν ≫ qS
  have hwX : w ≫ fX = a := by rw [← Category.assoc, hwν, htX]
  have hwS : w ≫ fS = b := by rw [← Category.assoc, hwν, htS]
  have hwdom : IsDominant w := ⟨w.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace⟩
  refine ⟨N, fX, fS, w, hN, hnN, inferInstance, inferInstance, inferInstance,
    inferInstance, hw, hwdom, hwX, hwS, ?_, hdν.trans hdG, e, v, hv, ?_⟩
  · simpa only [fX, fS, Category.assoc] using congrArg (fun f => ν ≫ f) hbase
  · simpa only [fX, Category.assoc] using hvbase

end PhilipponTwoMapNormalGraph

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
namespace PhilipponProperFamilyRetention

/-- A proper family embedded openly in an integral completion over a base
open is already the entire restriction of that completion. -/
lemma isPullback_of_proper_open_family
    {Y G U S : Scheme.{u}} [Nonempty Y] [IsIntegral G]
    (u : U ⟶ S) [IsOpenImmersion u]
    (p : Y ⟶ U) [IsProper p]
    (t : Y ⟶ G) [IsOpenImmersion t]
    (q : G ⟶ S) [IsSeparated q] (ht : t ≫ q = p ≫ u) :
    IsPullback t p q u := by
  let c : Y ⟶ pullback q u := pullback.lift t p ht
  haveI : IsOpenImmersion (c ≫ pullback.fst q u) := by
    rw [pullback.lift_fst]
    infer_instance
  haveI : IsOpenImmersion c := IsOpenImmersion.of_comp c (pullback.fst q u)
  haveI : IsProper (c ≫ pullback.snd q u) := by
    rw [pullback.lift_snd]
    infer_instance
  haveI : IsProper c := IsProper.of_comp c (pullback.snd q u)
  haveI : Nonempty (pullback q u : Scheme.{u}) := ⟨c (Classical.choice (inferInstance : Nonempty Y))⟩
  haveI : IsIntegral (pullback q u) := isIntegral_of_isOpenImmersion (pullback.fst q u)
  have hc : IsClopen (Set.range c) := ⟨c.isClosedMap.isClosed_range,
    c.isOpenEmbedding.isOpen_range⟩
  haveI : Surjective c := ⟨Set.range_eq_univ.mp (hc.eq_univ (Set.range_nonempty c))⟩
  haveI : IsIso c := (isIso_iff_isOpenImmersion_and_surjective c).mpr
    ⟨inferInstance, inferInstance⟩
  exact IsPullback.of_iso_pullback ⟨ht⟩ (asIso c)
    (pullback.lift_fst t p ht) (pullback.lift_snd t p ht)

end PhilipponProperFamilyRetention

set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 150000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
attribute [local instance] MvPolynomial.gradedAlgebra
namespace PhilipponSmoothFamilyCompletion

lemma surjective_of_smooth_proper
    {Y U : Scheme.{u}} [Nonempty Y] [IrreducibleSpace U]
    (p : Y ⟶ U) [Smooth p] [IsProper p] : Surjective p := by
  have hc : IsClopen (Set.range p) := ⟨p.isClosedMap.isClosed_range, p.isOpenMap.isOpen_range⟩
  exact ⟨Set.range_eq_univ.mp (hc.eq_univ (Set.range_nonempty p))⟩

/-- A proper smooth covering family on an open of a projective base admits
a normal projective completion retaining an actual entire proper component
of that family and both maps to the original variety and the base. -/
theorem exists_normal_projective_completion
    (k : Type u) [Field k] {Y X S U : Scheme.{u}}
    [NoetherianSpace Y] [IsIntegral X] [IsIntegral S] [IsIntegral U]
    (u : U ⟶ S) [IsOpenImmersion u] [IsDominant u]
    (p : Y ⟶ U) [Smooth p] [IsProper p]
    (πX : X ⟶ Spec (.of k)) [IsProper πX]
    (mX : ℕ) (iX : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (mX + 1)) k))
    [IsClosedImmersion iX] (hiX : iX ≫ ProjSpace.π k mX = πX)
    (πS : S ⟶ Spec (.of k)) [IsProper πS]
    (mS : ℕ) (iS : S ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (mS + 1)) k))
    [IsClosedImmersion iS] (hiS : iS ≫ ProjSpace.π k mS = πS)
    [Smooth (p ≫ u ≫ πS)]
    (n : ℕ) (j : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k))
    [IsImmersion j] (hj : j ≫ ProjSpace.π k n = p ≫ u ≫ πS)
    (a : Y ⟶ X) [IsDominant a] (ha : a ≫ πX = p ≫ u ≫ πS) :
    ∃ (V : Y.Opens) (G : Scheme.{u}) (qX : G ⟶ X) (qS : G ⟶ S)
      (t : (V : Scheme.{u}) ⟶ G),
      IsIntegral V ∧ IsClosedImmersion V.ι ∧
      Smooth (V.ι ≫ p) ∧ IsProper (V.ι ≫ p) ∧ Surjective (V.ι ≫ p) ∧
      Smooth (V.ι ≫ p ≫ u ≫ πS) ∧ IsDominant (V.ι ≫ a) ∧
      IsIntegral G ∧ (∀ x : G, IsIntegrallyClosed (G.presheaf.stalk x)) ∧
      IsProper qX ∧ Surjective qX ∧ IsProper qS ∧ Surjective qS ∧
      IsOpenImmersion t ∧ IsDominant t ∧ t ≫ qX = V.ι ≫ a ∧
      IsPullback t (V.ι ≫ p) qS u ∧ qX ≫ πX = qS ≫ πS ∧
      topologicalKrullDim G = topologicalKrullDim V ∧
      ∃ (d : ℕ) (l : G ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) k)),
        IsClosedImmersion l ∧ l ≫ ProjSpace.π k d = qX ≫ πX := by
  haveI : IsIntegrallyClosed Γ(Spec (.of k), ⊤) :=
    IsIntegrallyClosed.of_equiv (Scheme.ΓSpecIso (.of k)).symm.commRingCatIsoToRingEquiv
  have hnY := Smooth.isDomain_and_isIntegrallyClosed_stalk (p ≫ u ≫ πS)
  obtain ⟨V, hV, hcV, hdV⟩ :=
    PhilipponNormalComponents.exists_integral_clopen_dominant (fun y => (hnY y).1) a
  haveI : IsIntegral V := hV
  haveI : IsClosedImmersion V.ι := hcV
  haveI : IsDominant (V.ι ≫ a) := hdV
  haveI : NoetherianSpace (V : Scheme.{u}) :=
    V.ι.isOpenEmbedding.isEmbedding.isInducing.noetherianSpace
  have hpV : Surjective (V.ι ≫ p) := surjective_of_smooth_proper (V.ι ≫ p)
  haveI : Surjective (V.ι ≫ p) := hpV
  have hbase : (V.ι ≫ a) ≫ πX = ((V.ι ≫ p) ≫ u) ≫ πS := by
    simp only [Category.assoc, ha]
  have hjV : (V.ι ≫ a) ≫ πX = (V.ι ≫ j) ≫ ProjSpace.π k n := by
    simp only [Category.assoc, ha, hj]
  have hnV := Smooth.isDomain_and_isIntegrallyClosed_stalk (V.ι ≫ p ≫ u ≫ πS)
  obtain ⟨G, qX, qS, t, hG, hnG, hqX, hsqX, hqS, hsqS, ht, hdt, htX, htS,
    hbG, hdG, d, l, hl, hlbase⟩ :=
    PhilipponTwoMapNormalGraph.exists_normal_projective_graph
      k (fun y => (hnV y).2) n (V.ι ≫ j) πX mX iX hiX πS mS iS hiS
      (V.ι ≫ a) ((V.ι ≫ p) ≫ u) hbase hjV
  haveI := hG
  haveI := hqS
  haveI := ht
  have hpull := PhilipponProperFamilyRetention.isPullback_of_proper_open_family
    u (V.ι ≫ p) t qS htS
  exact ⟨V, G, qX, qS, t, hV, hcV, inferInstance, inferInstance, hpV,
    inferInstance, hdV, hG, hnG, hqX, hsqX, hqS, hsqS, ht, hdt, htX,
    hpull, hbG, hdG, d, l, hl, hlbase⟩

end PhilipponSmoothFamilyCompletion

theorem solution
    (k : Type u) [Field k] {Y X S U : Scheme.{u}}
    [NoetherianSpace Y] [IsIntegral X] [IsIntegral S] [IsIntegral U]
    (u : U ⟶ S) [IsOpenImmersion u] [IsDominant u]
    (p : Y ⟶ U) [Smooth p] [IsProper p]
    (πX : X ⟶ Spec (.of k)) [IsProper πX]
    (mX : ℕ) (iX : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (mX + 1)) k))
    [IsClosedImmersion iX] (hiX : iX ≫ ProjSpace.π k mX = πX)
    (πS : S ⟶ Spec (.of k)) [IsProper πS]
    (mS : ℕ) (iS : S ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (mS + 1)) k))
    [IsClosedImmersion iS] (hiS : iS ≫ ProjSpace.π k mS = πS)
    [Smooth (p ≫ u ≫ πS)]
    (n : ℕ) (j : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k))
    [IsImmersion j] (hj : j ≫ ProjSpace.π k n = p ≫ u ≫ πS)
    (a : Y ⟶ X) [IsDominant a] (ha : a ≫ πX = p ≫ u ≫ πS) :
    ∃ (V : Y.Opens) (G : Scheme.{u}) (qX : G ⟶ X) (qS : G ⟶ S)
      (t : (V : Scheme.{u}) ⟶ G),
      IsIntegral V ∧ IsClosedImmersion V.ι ∧
      Smooth (V.ι ≫ p) ∧ IsProper (V.ι ≫ p) ∧ Surjective (V.ι ≫ p) ∧
      Smooth (V.ι ≫ p ≫ u ≫ πS) ∧ IsDominant (V.ι ≫ a) ∧
      IsIntegral G ∧ (∀ x : G, IsIntegrallyClosed (G.presheaf.stalk x)) ∧
      IsProper qX ∧ Surjective qX ∧ IsProper qS ∧ Surjective qS ∧
      IsOpenImmersion t ∧ IsDominant t ∧ t ≫ qX = V.ι ≫ a ∧
      IsPullback t (V.ι ≫ p) qS u ∧ qX ≫ πX = qS ≫ πS ∧
      topologicalKrullDim G = topologicalKrullDim V ∧
      ∃ (d : ℕ) (l : G ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) k)),
        IsClosedImmersion l ∧ l ≫ ProjSpace.π k d = qX ≫ πX := by
  exact PhilipponSmoothFamilyCompletion.exists_normal_projective_completion k u p πX mX iX hiX πS mS iS hiS n j hj a ha
