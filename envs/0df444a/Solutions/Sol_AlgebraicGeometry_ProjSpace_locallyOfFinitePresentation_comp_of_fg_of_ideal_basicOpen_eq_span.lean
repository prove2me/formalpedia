-- Prove2me | solution 1 for AlgebraicGeometry.ProjSpace.locallyOfFinitePresentation_comp_of_fg_of_ideal_basicOpen_eq_span
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/4479e742-de2e-51cb-a515-f003384e72e5

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_HilbertFunctor
import Theorems.Thm_AlgebraicGeometry_ProjSpace_exists_algHom_away_apply_ratio_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_ProjSpace_locallyOfFinitePresentation_comp_of_fg_of_ideal_basicOpen_eq_span

set_option autoImplicit false
open MvPolynomial CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.HilbertFunctor
attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace K1BSOL

section ChartFP

variable (A : Type) [CommRing A] (n : ℕ) (i : Fin (n + 1))

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A

def toAway : MvPolynomial {k : Fin (n + 1) // k ≠ i} A →ₐ[A]
    HomogeneousLocalization.Away 𝒜 (MvPolynomial.X i) :=
  MvPolynomial.aeval fun k => ProjSpace.ratio A n i k.1

def bvec : Fin (n + 1) → MvPolynomial {k : Fin (n + 1) // k ≠ i} A :=
  fun k => if h : k = i then 1 else MvPolynomial.X ⟨k, h⟩

theorem bvec_self : bvec A n i i = 1 := by simp [bvec]

theorem toAway_bvec (k : Fin (n + 1)) : toAway A n i (bvec A n i k) = ProjSpace.ratio A n i k := by
  unfold bvec
  split_ifs with h
  · subst h; rw [map_one, ProjSpace.ratio_self]
  · simp [toAway]

theorem range_toAway : Function.Surjective (toAway A n i) := by
  rw [← AlgHom.range_eq_top, eq_top_iff, ← ProjSpace.adjoin_range_ratio A n i, Algebra.adjoin_le_iff]
  rintro _ ⟨k, rfl⟩
  exact ⟨bvec A n i k, toAway_bvec A n i k⟩

theorem exists_algEquiv_away :
    Nonempty (MvPolynomial {k : Fin (n + 1) // k ≠ i} A ≃ₐ[A]
      HomogeneousLocalization.Away 𝒜 (MvPolynomial.X i)) := by
  obtain ⟨ψ, hψ⟩ := AlgebraicGeometry.ProjSpace.exists_algHom_away_apply_ratio_eq A n i (bvec A n i)
    (bvec_self A n i)
  have h1 : ψ.comp (toAway A n i) = AlgHom.id A _ := by
    apply MvPolynomial.algHom_ext
    intro k
    simp only [AlgHom.comp_apply, AlgHom.id_apply, toAway, MvPolynomial.aeval_X, hψ, bvec, dif_neg k.2]
  have h2 : (toAway A n i).comp ψ = AlgHom.id A _ := by
    apply AlgHom.ext_of_adjoin_eq_top (ProjSpace.adjoin_range_ratio A n i)
    rintro _ ⟨k, rfl⟩
    simp only [AlgHom.comp_apply, AlgHom.id_apply, hψ, toAway_bvec]
  exact ⟨AlgEquiv.ofAlgHom (toAway A n i) ψ h2 h1⟩

scoped instance finitePresentation_away :
    Algebra.FinitePresentation A (HomogeneousLocalization.Away 𝒜 (MvPolynomial.X i)) := by
  obtain ⟨e⟩ := exists_algEquiv_away A n i
  exact Algebra.FinitePresentation.equiv e

theorem finitePresentation_algebraMap_away :
    (algebraMap A (HomogeneousLocalization.Away 𝒜 (MvPolynomial.X i))).FinitePresentation :=
  (RingHom.finitePresentation_algebraMap).mpr (finitePresentation_away A n i)

end ChartFP

section ChartIdeal

variable {A : Type} [CommRing A] {n : ℕ}

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A

def xpow (i : Fin (n + 1)) (d : ℕ) : ↥(homogeneousSubmodule (Fin (n + 1)) A d) :=
  ⟨MvPolynomial.X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr (MvPolynomial.isHomogeneous_X_pow i d)⟩

def frac (i : Fin (n + 1)) (d : ℕ) (F : ↥(homogeneousSubmodule (Fin (n + 1)) A d)) :
    HomogeneousLocalization.Away 𝒜 (MvPolynomial.X i) :=
  HomogeneousLocalization.mk
    { deg := d
      num := F
      den := xpow (A := A) i d
      den_mem := ⟨d, rfl⟩ }

theorem frac_zero (i : Fin (n + 1)) (d : ℕ) : frac (A := A) i d 0 = 0 := by
  apply HomogeneousLocalization.val_injective
  simp only [frac, HomogeneousLocalization.val_mk, HomogeneousLocalization.val_zero, Submodule.coe_zero]
  exact Localization.mk_zero _

theorem frac_add (i : Fin (n + 1)) (d : ℕ) (F G : ↥(homogeneousSubmodule (Fin (n + 1)) A d)) :
    frac i d (F + G) = frac i d F + frac i d G := by
  apply HomogeneousLocalization.val_injective
  simp only [frac, HomogeneousLocalization.val_mk, HomogeneousLocalization.val_add, Submodule.coe_add]
  rw [Localization.add_mk_self]

theorem frac_mul (i : Fin (n + 1)) (e d : ℕ) (G : ↥(homogeneousSubmodule (Fin (n + 1)) A e))
    (F : ↥(homogeneousSubmodule (Fin (n + 1)) A d)) :
    frac i (e + d) ⟨(G : MvPolynomial (Fin (n + 1)) A) * (F : MvPolynomial (Fin (n + 1)) A),
      SetLike.mul_mem_graded G.2 F.2⟩ = frac i e G * frac i d F := by
  apply HomogeneousLocalization.val_injective
  simp only [frac, HomogeneousLocalization.val_mk, HomogeneousLocalization.val_mul]
  rw [Localization.mk_mul]
  congr 1
  ext
  simp [xpow, pow_add]

private def _root_.K1BSOL.comp (d : ℕ) (p : MvPolynomial (Fin (n + 1)) A) : ↥(homogeneousSubmodule (Fin (n + 1)) A d) :=
  ⟨homogeneousComponent d p, homogeneousComponent_mem d p⟩

p2m_export "K1BSOL" "comp"
theorem comp_zero (d : ℕ) : comp (A := A) (n := n) d 0 = 0 := Subtype.ext (by simp [comp])

theorem comp_add (d : ℕ) (p q : MvPolynomial (Fin (n + 1)) A) : comp d (p + q) = comp d p + comp d q :=
  Subtype.ext (by simp [comp])

theorem coe_decompose (φ : MvPolynomial (Fin (n + 1)) A) (i : ℕ) :
    ((DirectSum.decompose 𝒜 φ) i : MvPolynomial (Fin (n + 1)) A) = homogeneousComponent i φ :=
  MvPolynomial.decomposition.decompose'_apply φ i

theorem homogeneousComponent_mul_of_mem_right {e : ℕ} (a : MvPolynomial (Fin (n + 1)) A)
    {g : MvPolynomial (Fin (n + 1)) A} (hg : g ∈ homogeneousSubmodule (Fin (n + 1)) A e) (d : ℕ) :
    homogeneousComponent d (a * g) = if e ≤ d then homogeneousComponent (d - e) a * g else 0 := by
  have h := DirectSum.coe_decompose_mul_of_right_mem 𝒜 (a := a) d hg
  simpa only [coe_decompose] using h

theorem comp_of_mem {e : ℕ} {F : MvPolynomial (Fin (n + 1)) A}
    (hF : F ∈ homogeneousSubmodule (Fin (n + 1)) A e) (d : ℕ) :
    comp d F = if h : d = e then ⟨F, h ▸ hF⟩ else 0 := by
  apply Subtype.ext
  simp only [comp, homogeneousComponent_of_mem hF]
  split_ifs <;> rfl

def fcHom (i : Fin (n + 1)) (d : ℕ) :
    MvPolynomial (Fin (n + 1)) A →+ HomogeneousLocalization.Away 𝒜 (MvPolynomial.X i) where
  toFun p := frac i d (comp d p)
  map_zero' := by simp only [comp_zero, frac_zero]
  map_add' p q := by simp only [comp_add, frac_add]

theorem fcHom_apply (i : Fin (n + 1)) (d : ℕ) (p : MvPolynomial (Fin (n + 1)) A) :
    fcHom (A := A) i d p = frac i d (comp d p) := rfl

theorem fcHom_mul_of_mem (i : Fin (n + 1)) (d e : ℕ) (a : MvPolynomial (Fin (n + 1)) A)
    {g : MvPolynomial (Fin (n + 1)) A} (hg : g ∈ homogeneousSubmodule (Fin (n + 1)) A e) :
    fcHom (A := A) i d (a * g) = if e ≤ d then fcHom (A := A) i (d - e) a * frac i e ⟨g, hg⟩ else 0 := by
  rcases Nat.lt_or_ge d e with hde | hed
  · rw [if_neg (not_le.mpr hde), fcHom_apply]
    have h0 : comp d (a * g) = 0 := Subtype.ext (by
      simp only [comp, homogeneousComponent_mul_of_mem_right a hg d, if_neg (not_le.mpr hde),
        Submodule.coe_zero])
    rw [h0, frac_zero]
  · obtain ⟨d', rfl⟩ := Nat.exists_eq_add_of_le' hed
    rw [if_pos hed, fcHom_apply, fcHom_apply, Nat.add_sub_cancel]
    have h1 : comp (d' + e) (a * g) =
        ⟨(comp d' a : MvPolynomial (Fin (n + 1)) A) * ((⟨g, hg⟩ : ↥(𝒜 e)) : MvPolynomial (Fin (n + 1)) A),
          SetLike.mul_mem_graded (comp d' a).2 hg⟩ := Subtype.ext (by
      simp only [comp, homogeneousComponent_mul_of_mem_right a hg (d' + e), if_pos hed,
        Nat.add_sub_cancel])
    rw [h1, frac_mul]

theorem fg_span_chart (I : Ideal (MvPolynomial (Fin (n + 1)) A))
    (hI : ∀ p ∈ I, ∀ d : ℕ, homogeneousComponent d p ∈ I) (hfg : I.FG) (i : Fin (n + 1)) :
    (Ideal.span { s | ∃ (d : ℕ) (F : MvPolynomial (Fin (n + 1)) A) (hF : F.IsHomogeneous d),
          F ∈ I ∧
          s = (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X i))
              (HomogeneousLocalization.mk
                { deg := d
                  num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩
                  den := ⟨X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr (MvPolynomial.isHomogeneous_X_pow i d)⟩
                  den_mem := ⟨d, rfl⟩ }) }).FG := by
  classical
  obtain ⟨s, hs⟩ := hfg

  set aTS := (Proj.awayToSection 𝒜 (MvPolynomial.X i)).hom with haTS

  let ι := Σ g : ↥s, Fin (g.1.totalDegree + 1)
  let w : ι → HomogeneousLocalization.Away 𝒜 (MvPolynomial.X i) := fun q => frac i q.2 (comp q.2 q.1.1)
  have hsI : ∀ g ∈ s, g ∈ I := fun g hg => hs ▸ Ideal.subset_span hg

  have key : ∀ (d : ℕ) (F : MvPolynomial (Fin (n + 1)) A), F ∈ I →
      fcHom (A := A) i d F ∈ Ideal.span (Set.range w) := by
    intro d F hF
    have hF' : F ∈ Ideal.span (Set.range (Subtype.val : ↥s → MvPolynomial (Fin (n + 1)) A)) := by
      have : Set.range (Subtype.val : ↥s → MvPolynomial (Fin (n + 1)) A) = ↑s := by
        ext x; simp
      rw [this, hs]; exact hF
    obtain ⟨c, rfl⟩ := Ideal.mem_span_range_iff_exists_fun.mp hF'
    rw [map_sum]
    refine Submodule.sum_mem _ fun g _ => ?_
    have hsplit : c g * (g : MvPolynomial (Fin (n + 1)) A) =
        ∑ e ∈ Finset.range ((g : MvPolynomial (Fin (n + 1)) A).totalDegree + 1),
          c g * homogeneousComponent e (g : MvPolynomial (Fin (n + 1)) A) := by
      conv_lhs => rw [← sum_homogeneousComponent (g : MvPolynomial (Fin (n + 1)) A)]
      rw [Finset.mul_sum]
    rw [hsplit, map_sum]
    refine Submodule.sum_mem _ fun e he => ?_
    rw [fcHom_mul_of_mem i d e (c g) (homogeneousComponent_mem e (g : MvPolynomial (Fin (n + 1)) A))]
    split_ifs with hed
    · apply Ideal.mul_mem_left
      refine Ideal.subset_span ⟨⟨g, ⟨e, Finset.mem_range.mp he⟩⟩, ?_⟩
      rfl
    · exact Submodule.zero_mem _

  have hEq : Ideal.span { s | ∃ (d : ℕ) (F : MvPolynomial (Fin (n + 1)) A) (hF : F.IsHomogeneous d),
          F ∈ I ∧
          s = (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X i))
              (HomogeneousLocalization.mk
                { deg := d
                  num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩
                  den := ⟨X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr (MvPolynomial.isHomogeneous_X_pow i d)⟩
                  den_mem := ⟨d, rfl⟩ }) } = Ideal.span (Set.range (aTS ∘ w)) := by
    apply le_antisymm
    · rw [Ideal.span_le]
      rintro _ ⟨d, F, hF, hFI, rfl⟩
      have hmem := key d F hFI
      have hcF : comp d F = ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩ := by
        rw [comp_of_mem ((MvPolynomial.mem_homogeneousSubmodule d F).mpr hF), dif_pos rfl]
      rw [fcHom_apply, hcF] at hmem
      have := Ideal.mem_map_of_mem aTS hmem
      rw [Ideal.map_span, ← Set.range_comp] at this
      exact this
    · apply Ideal.span_mono
      rintro _ ⟨⟨⟨g, hg⟩, ⟨e, he⟩⟩, rfl⟩
      exact ⟨e, homogeneousComponent e g, homogeneousComponent_isHomogeneous e g, hI g (hsI g hg) e, rfl⟩
  rw [hEq]
  exact ⟨(Finset.univ : Finset ι).image (aTS ∘ w), by rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]⟩

end ChartIdeal

end K1BSOL
p2m_reactivate "P2MW.S_AlgebraicGeometry_ProjSpace_locallyOfFinitePresentation_comp_of_fg_of_ideal_basicOpen_eq_span.K1BSOL"

open K1BSOL in

theorem solution
    (n : ℕ) (A : Type) [CommRing A] (I : Ideal (MvPolynomial (Fin (n + 1)) A))
    (hI : ∀ p ∈ I, ∀ d : ℕ, homogeneousComponent d p ∈ I) (hfg : I.FG)
    (𝓘 : (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A)).IdealSheafData)
    (h𝓘 : ∀ i : Fin (n + 1),
        𝓘.ideal ⟨Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X i),
          Proj.isAffineOpen_basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X i) (ProjSpace.X_mem_one A n i) one_pos⟩ =
        Ideal.span { s | ∃ (d : ℕ) (F : MvPolynomial (Fin (n + 1)) A) (hF : F.IsHomogeneous d),
          F ∈ I ∧
          s = (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X i))
              (HomogeneousLocalization.mk
                { deg := d
                  num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩
                  den := ⟨X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr (MvPolynomial.isHomogeneous_X_pow i d)⟩
                  den_mem := ⟨d, rfl⟩ }) }) :
    LocallyOfFinitePresentation (𝓘.subschemeι ≫ ProjSpace.π A n) := by
  classical

  have hcov : (⨆ i : Fin (n + 1),
      𝓘.subschemeι ⁻¹ᵁ (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X i))) = ⊤ := by
    rw [← Scheme.Hom.preimage_iSup,
      Proj.iSup_basicOpen_eq_top (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) _
        (ProjSpace.irrelevant_le_span_X A n)]
    simp
  rw [IsZariskiLocalAtSource.iff_of_iSup_eq_top (P := @LocallyOfFinitePresentation) _ hcov]
  intro i

  have hrange : Set.range (𝓘.subschemeCover.f ⟨Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X i),
          Proj.isAffineOpen_basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X i) (ProjSpace.X_mem_one A n i) one_pos⟩).base =
      Set.range (𝓘.subschemeι ⁻¹ᵁ
        (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X i))).ι.base := by
    rw [Scheme.Opens.range_ι]
    exact congr_arg (fun W : 𝓘.subscheme.Opens => (W : Set 𝓘.subscheme)) (𝓘.opensRange_subschemeCover_map _)
  rw [← IsOpenImmersion.isoOfRangeEq_inv_fac _ _ hrange, Category.assoc,
    MorphismProperty.cancel_left_of_respectsIso (P := @LocallyOfFinitePresentation)]

  have heq : 𝓘.subschemeCover.f ⟨Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X i),
          Proj.isAffineOpen_basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X i) (ProjSpace.X_mem_one A n i) one_pos⟩ ≫
        𝓘.subschemeι ≫ ProjSpace.π A n =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
        (𝓘.ideal ⟨Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X i),
          Proj.isAffineOpen_basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X i) (ProjSpace.X_mem_one A n i) one_pos⟩))) ≫
      (Proj.isAffineOpen_basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X i)
          (ProjSpace.X_mem_one A n i) one_pos).isoSpec.inv ≫
      (Proj.basicOpenIsoSpec (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X i)
          (ProjSpace.X_mem_one A n i) one_pos).hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap A
        (HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X i)))) := by
    rw [← ProjSpace.awayι_comp_π, ← Proj.basicOpenIsoSpec_inv_ι]
    conv_lhs => rw [← Category.assoc, Scheme.IdealSheafData.subschemeCover_map_subschemeι,
      Scheme.IdealSheafData.glueDataObjι]
    dsimp only [Scheme.IdealSheafData.glueDataObj, Scheme.IdealSheafData.subschemeCover]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [heq]
  dsimp only [Scheme.IdealSheafData.subschemeCover]

  have h1 : LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
      (𝓘.ideal ⟨Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X i),
          Proj.isAffineOpen_basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X i) (ProjSpace.X_mem_one A n i) one_pos⟩)))) := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)]
    refine RingHom.FinitePresentation.of_surjective _ Ideal.Quotient.mk_surjective ?_
    rw [CommRingCat.hom_ofHom, Ideal.mk_ker, h𝓘 i]
    exact fg_span_chart I hI hfg i
  have h2 : LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom (algebraMap A
      (HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X i))))) := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)]
    exact finitePresentation_algebraMap_away A n i
  infer_instance

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_ProjSpace_locallyOfFinitePresentation_comp_of_fg_of_ideal_basicOpen_eq_span.K1BSOL"

end S_AlgebraicGeometry_ProjSpace_locallyOfFinitePresentation_comp_of_fg_of_ideal_basicOpen_eq_span
end P2MW
export P2MW.S_AlgebraicGeometry_ProjSpace_locallyOfFinitePresentation_comp_of_fg_of_ideal_basicOpen_eq_span (solution)
