-- Prove2me | solution 1 for AlgebraicGeometry.ProjSpace.exists_ideal_fg_forall_ker_ideal_basicOpen_eq_span_of_isClosedImmersion
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/fd897100-75ee-52bf-b9ed-408b56863344

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_HilbertFunctor
import Theorems.Thm_AlgebraicGeometry_ProjSpace_exists_idealSheafData_ideal_basicOpen_eq_span
import Theorems.Thm_AlgebraicGeometry_ProjSpace_eq_ker_of_ideal_basicOpen_eq_span_of_isClosedImmersion
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_ProjSpace_exists_ideal_fg_forall_ker_ideal_basicOpen_eq_span_of_isClosedImmersion

set_option autoImplicit false
open MvPolynomial CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.HilbertFunctor
attribute [local instance] MvPolynomial.gradedAlgebra

namespace IdealFGAux

theorem exists_finite_subset_le_span {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    (N : Submodule R M) (hN : N.FG) (s : Set M) (h : N ≤ Submodule.span R s) :
    ∃ T : Set M, T ⊆ s ∧ T.Finite ∧ N ≤ Submodule.span R T := by
  classical
  obtain ⟨gens, rfl⟩ := hN
  have hg : ∀ g : ↥gens, ∃ T : Finset M, ↑T ⊆ s ∧ (g : M) ∈ Submodule.span R (T : Set M) := fun g =>
    Submodule.mem_span_finite_of_mem_span (h (Submodule.subset_span g.2))
  choose T hTS hgT using hg
  refine ⟨⋃ g : ↥gens, (T g : Set M), Set.iUnion_subset hTS, Set.finite_iUnion fun g => (T g).finite_toSet, ?_⟩
  rw [Submodule.span_le]
  intro g hg'
  exact Submodule.span_mono (Set.subset_iUnion (fun g : ↥gens => (T g : Set M)) ⟨g, hg'⟩) (hgT ⟨g, hg'⟩)

theorem exists_finite_subset_image {α β : Type*} (f : α → β) (s : Set α) (T : Set β) (hT : T.Finite)
    (h : T ⊆ f '' s) : ∃ P : Set α, P ⊆ s ∧ P.Finite ∧ T ⊆ f '' P := by
  classical
  have hc : ∀ t : ↥T, ∃ a ∈ s, f a = t := fun t => h t.2
  choose g hgS hgf using hc
  haveI := hT.to_subtype
  exact ⟨Set.range g, Set.range_subset_iff.mpr hgS, Set.finite_range g,
    fun t ht => ⟨g ⟨t, ht⟩, ⟨⟨t, ht⟩, rfl⟩, hgf ⟨t, ht⟩⟩⟩

theorem homogeneousComponent_mul_left {σ : Type} {R : Type} [CommRing R] [DecidableEq σ]
    {p : MvPolynomial σ R} {k : ℕ} (hp : p.IsHomogeneous k) (q : MvPolynomial σ R) (m : ℕ) :
    homogeneousComponent m (p * q) = if k ≤ m then p * homogeneousComponent (m - k) q else 0 := by
  classical
  ext μ
  rw [coeff_homogeneousComponent]
  have hpdeg : ∀ α : σ →₀ ℕ, coeff α p ≠ 0 → Finsupp.degree α = k := fun α hα => by
    by_contra h
    exact hα (hp.coeff_eq_zero h)
  split_ifs with hμ hk
  · rw [coeff_mul, coeff_mul]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    rw [coeff_homogeneousComponent]
    by_cases hα : coeff x.1 p = 0
    · rw [hα, zero_mul, zero_mul]
    · have h1 := hpdeg x.1 hα
      have h2 : Finsupp.degree x.2 = m - k := by
        have := congrArg Finsupp.degree hx
        rw [map_add, h1, hμ] at this
        omega
      rw [if_pos h2]
  · rw [coeff_zero, coeff_mul]
    refine Finset.sum_eq_zero fun x hx => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    by_cases hα : coeff x.1 p = 0
    · rw [hα, zero_mul]
    · exfalso
      have h1 := hpdeg x.1 hα
      have := congrArg Finsupp.degree hx
      rw [map_add, h1, hμ] at this
      omega
  · rw [coeff_mul]
    symm
    refine Finset.sum_eq_zero fun x hx => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    rw [coeff_homogeneousComponent]
    split_ifs with h2
    · by_cases hα : coeff x.1 p = 0
      · rw [hα, zero_mul]
      · exfalso
        have h1 := hpdeg x.1 hα
        have := congrArg Finsupp.degree hx
        rw [map_add, h1, h2] at this
        omega
    · rw [mul_zero]
  · rw [coeff_zero]

theorem homogeneousComponent_mem_span {σ : Type} {R : Type} [CommRing R] (s : Set (MvPolynomial σ R))
    (hs : ∀ F ∈ s, ∃ d : ℕ, F.IsHomogeneous d) (p : MvPolynomial σ R) (hp : p ∈ Ideal.span s) (d : ℕ) :
    homogeneousComponent d p ∈ Ideal.span s := by
  classical
  induction hp using Submodule.span_induction generalizing d with
  | mem x hx =>
    obtain ⟨e, he⟩ := hs x hx
    rw [homogeneousComponent_of_mem ((mem_homogeneousSubmodule e x).mpr he)]
    split_ifs
    · exact Ideal.subset_span hx
    · exact Submodule.zero_mem _
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Ideal.add_mem _ (hx d) (hy d)
  | smul a x _ hx =>

    rw [smul_eq_mul, ← sum_homogeneousComponent a, Finset.sum_mul, map_sum]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [homogeneousComponent_mul_left (homogeneousComponent_isHomogeneous k a)]
    split_ifs
    · exact Ideal.mul_mem_left _ _ (hx (d - k))
    · exact Submodule.zero_mem _

theorem ker_ideal_fg_of_finitePresentation_app {Z Y : Scheme.{0}} (ι : Z ⟶ Y) [IsClosedImmersion ι]
    (U : Y.affineOpens) (h : (ι.app U.1).hom.FinitePresentation) : (ι.ker.ideal U).FG := by
  rw [Scheme.Hom.ker_apply]
  have h2 : Function.Surjective (ι.app U.1).hom := ι.app_surjective U.1 U.2
  letI alg : Algebra Γ(Y, U.1) Γ(Z, ι ⁻¹ᵁ U.1) := (ι.app U.1).hom.toAlgebra
  haveI : Algebra.FinitePresentation Γ(Y, U.1) Γ(Z, ι ⁻¹ᵁ U.1) := h
  exact Algebra.FinitePresentation.ker_fG_of_surjective (Algebra.ofId Γ(Y, U.1) Γ(Z, ι ⁻¹ᵁ U.1)) h2

theorem finitePresentation_app_of_comp {Z Y B : Scheme.{0}} (ι : Z ⟶ Y) (π : Y ⟶ B) [IsAffine B]
    [IsClosedImmersion ι] [LocallyOfFiniteType π] [LocallyOfFinitePresentation (ι ≫ π)]
    (U : Y.affineOpens) : (ι.app U.1).hom.FinitePresentation := by
  have hV : IsAffineOpen (ι ⁻¹ᵁ U.1) := U.2.preimage ι
  have e1 : ι ⁻¹ᵁ U.1 ≤ (ι ≫ π) ⁻¹ᵁ (⊤ : B.Opens) := le_top
  have h1 : ((ι ≫ π).appLE ⊤ (ι ⁻¹ᵁ U.1) e1).hom.FinitePresentation :=
    HasRingHomProperty.appLE (P := @LocallyOfFinitePresentation) _ inferInstance ⟨⊤, isAffineOpen_top B⟩ ⟨_, hV⟩ e1
  have h3 : (π.appLE ⊤ U.1 le_top).hom.FiniteType :=
    HasRingHomProperty.appLE (P := @LocallyOfFiniteType) _ inferInstance ⟨⊤, isAffineOpen_top B⟩ U le_top
  have h2 : (ι ≫ π).appLE ⊤ (ι ⁻¹ᵁ U.1) e1 = π.appLE ⊤ U.1 le_top ≫ ι.appLE U.1 (ι ⁻¹ᵁ U.1) le_rfl := by
    rw [Scheme.Hom.appLE_comp_appLE]
  rw [h2, CommRingCat.hom_comp] at h1
  have h4 := RingHom.FinitePresentation.of_comp_finiteType _ h1 h3
  rwa [Scheme.Hom.appLE_eq_app] at h4

end IdealFGAux

open IdealFGAux in
theorem solution
    (A : Type) [CommRing A] (n : ℕ) (Z : Scheme.{0})
    (ι : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A))
    [IsClosedImmersion ι] [LocallyOfFinitePresentation (ι ≫ ProjSpace.π A n)] :
    ∃ I₀ : Ideal (MvPolynomial (Fin (n + 1)) A), I₀.FG ∧
      (∀ p ∈ I₀, ∀ d : ℕ, homogeneousComponent d p ∈ I₀) ∧
      ∀ i : Fin (n + 1),
        ι.ker.ideal ⟨Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X i),
            Proj.isAffineOpen_basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X i) (ProjSpace.X_mem_one A n i) one_pos⟩ =
          Ideal.span {a | ∃ (d : ℕ) (F : MvPolynomial (Fin (n + 1)) A) (hF : F.IsHomogeneous d), F ∈ I₀ ∧
            a = (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X i))
                  (HomogeneousLocalization.mk
                    { deg := d
                      num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩
                      den := ⟨X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr (MvPolynomial.isHomogeneous_X_pow i d)⟩
                      den_mem := ⟨d, rfl⟩ })} := by
  classical

  haveI hπ : LocallyOfFiniteType (ProjSpace.π A n) := by
    have h1 : LocallyOfFiniteType (Proj.toSpecZero (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A)) :=
      inferInstance
    have h2 : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (ProjSpace.grad0Equiv A n).toRingHom)) := by
      rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType), CommRingCat.hom_ofHom]
      exact RingHom.FiniteType.of_surjective _ (ProjSpace.grad0Equiv A n).surjective
    show LocallyOfFiniteType (Proj.toSpecZero _ ≫ Spec.map (CommRingCat.ofHom (ProjSpace.grad0Equiv A n).toRingHom))
    exact MorphismProperty.comp_mem _ _ _ h1 h2

  let U : Fin (n + 1) → (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A)).affineOpens := fun i =>
    ⟨Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X i),
      Proj.isAffineOpen_basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X i) (ProjSpace.X_mem_one A n i) one_pos⟩
  let Sig : Type := Σ d : ℕ, {F : MvPolynomial (Fin (n + 1)) A // F.IsHomogeneous d}
  let sec : ∀ i : Fin (n + 1), Sig →
      Γ(Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A), Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X i)) :=
    fun i x => (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X i))
      (HomogeneousLocalization.mk
        { deg := x.1
          num := ⟨x.2.1, (MvPolynomial.mem_homogeneousSubmodule x.1 x.2.1).mpr x.2.2⟩
          den := ⟨X i ^ x.1, (MvPolynomial.mem_homogeneousSubmodule x.1 _).mpr (MvPolynomial.isHomogeneous_X_pow i x.1)⟩
          den_mem := ⟨x.1, rfl⟩ })

  have hset : ∀ (I : Ideal (MvPolynomial (Fin (n + 1)) A)) (i : Fin (n + 1)),
      { a | ∃ (d : ℕ) (F : MvPolynomial (Fin (n + 1)) A) (hF : F.IsHomogeneous d), F ∈ I ∧
            a = (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X i))
                  (HomogeneousLocalization.mk
                    { deg := d
                      num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩
                      den := ⟨X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr (MvPolynomial.isHomogeneous_X_pow i d)⟩
                      den_mem := ⟨d, rfl⟩ }) } = sec i '' {x : Sig | x.2.1 ∈ I} := by
    intro I i
    ext a
    constructor
    · rintro ⟨d, F, hF, hFI, rfl⟩
      exact ⟨⟨d, ⟨F, hF⟩⟩, hFI, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.1, x.2.1, x.2.2, hx, rfl⟩

  let IV : Ideal (MvPolynomial (Fin (n + 1)) A) := Ideal.span
    { F : MvPolynomial (Fin (n + 1)) A | ∃ (d : ℕ) (hF : F.IsHomogeneous d), 0 ≤ d ∧
      ∀ i : Fin (n + 1),
      ι.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X i))
        ((Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X i))
          (HomogeneousLocalization.mk
            { deg := d
              num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩
              den := ⟨X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr (MvPolynomial.isHomogeneous_X_pow i d)⟩
              den_mem := ⟨d, rfl⟩ })) = 0 }
  obtain ⟨𝓘, h𝓘⟩ := AlgebraicGeometry.ProjSpace.exists_idealSheafData_ideal_basicOpen_eq_span n A IV
  have hK : 𝓘 = ι.ker :=
    AlgebraicGeometry.ProjSpace.eq_ker_of_ideal_basicOpen_eq_span_of_isClosedImmersion n A Z ι inferInstance 0 𝓘 h𝓘
  have hker : ∀ i : Fin (n + 1), ι.ker.ideal (U i) = Ideal.span (sec i '' {x : Sig | x.2.1 ∈ IV}) := by
    intro i
    rw [← hK, ← hset IV i]
    exact h𝓘 i

  have hfin : ∀ i : Fin (n + 1), ∃ P : Set Sig, P ⊆ {x : Sig | x.2.1 ∈ IV} ∧ P.Finite ∧
      ι.ker.ideal (U i) ≤ Ideal.span (sec i '' P) := by
    intro i
    have hfg : (ι.ker.ideal (U i)).FG :=
      ker_ideal_fg_of_finitePresentation_app ι (U i) (finitePresentation_app_of_comp ι (ProjSpace.π A n) (U i))
    obtain ⟨T, hTS, hTfin, hle⟩ := exists_finite_subset_le_span _ hfg _ (le_of_eq (hker i))
    obtain ⟨P, hPS, hPfin, hTP⟩ := exists_finite_subset_image (sec i) _ T hTfin hTS
    exact ⟨P, hPS, hPfin, hle.trans (Submodule.span_mono hTP)⟩
  choose P hPsub hPfin hPle using hfin

  let I₀ : Ideal (MvPolynomial (Fin (n + 1)) A) := Ideal.span ((fun x : Sig => x.2.1) '' ⋃ i, P i)
  have hI₀IV : I₀ ≤ IV := by
    rw [Ideal.span_le]
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    exact hPsub i hi
  refine ⟨I₀, ?_, ?_, ?_⟩
  ·
    exact Submodule.fg_span ((Set.finite_iUnion hPfin).image _)
  ·
    intro p hp d
    refine homogeneousComponent_mem_span _ ?_ p hp d
    rintro _ ⟨x, -, rfl⟩
    exact ⟨x.1, x.2.2⟩
  ·
    intro i
    apply le_antisymm
    · refine (hPle i).trans (Ideal.span_mono ?_)
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨x.1, x.2.1, x.2.2, Ideal.subset_span ⟨x, Set.mem_iUnion.mpr ⟨i, hx⟩, rfl⟩, rfl⟩
    · rw [Ideal.span_le]
      rintro a ⟨d, F, hF, hFI, rfl⟩
      show _ ∈ ι.ker.ideal (U i)
      rw [hker i]
      exact Ideal.subset_span ⟨⟨d, ⟨F, hF⟩⟩, hI₀IV hFI, rfl⟩

end S_AlgebraicGeometry_ProjSpace_exists_ideal_fg_forall_ker_ideal_basicOpen_eq_span_of_isClosedImmersion
end P2MW
export P2MW.S_AlgebraicGeometry_ProjSpace_exists_ideal_fg_forall_ker_ideal_basicOpen_eq_span_of_isClosedImmersion (solution)
