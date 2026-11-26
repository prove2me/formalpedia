-- Prove2me | Definitions.Def_AlgebraicGeometry_EtaleNoetherianBoundedConstantModels
-- name    : AlgebraicGeometry_EtaleNoetherianBoundedConstantModels
-- status  : Definition
-- author  : @tomasz
-- created : 2026-11-26T00:11:57.922638+00:00
-- url     : https://prove2.me/theorems/03b6dcd2-0c15-50c2-9711-eba3f6e84ec9
-- title:
--   Bounded finite constant models over Noetherian affines
-- statement:
--   Every finite étale presentation over a Noetherian affine embeds in a bounded finite constant direct image.
-- source:
--   Stacks Project, 59.73.2 (https://stacks.math.columbia.edu/tag/03SA) and 59.74.4 (https://stacks.math.columbia.edu/tag/09Z7).

import Definitions.Def_AlgebraicGeometry_EtaleFiniteConstantImageFactorization
import Mathlib
import Mathlib.Algebra.Algebra.Pi
import Mathlib.Algebra.GroupWithZero.Pi
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Integral
import Mathlib.AlgebraicGeometry.Sites.AffineEtale
import Mathlib.CategoryTheory.Limits.VanKampen
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.Topology.NoetherianSpace
import Mathlib.Topology.Sober

noncomputable section

section

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace


namespace PhilipponEtaleFinitePointLifts

universe u

/-- A nonempty open piece of the fiber over an algebraically closed
point contains a lift over the same coefficient field. -/
theorem exists_lift_in_open_of_finite {X Y : Scheme.{u}} (p : Y ⟶ X)
    [IsFinite p] {K : Type u} [Field K] [IsAlgClosed K]
    (s : Spec (.of K) ⟶ X) (U : Y.Opens)
    (hU : ∃ y ∈ U, p y = s default) :
    ∃ t : Spec (.of K) ⟶ Y, t ≫ p = s ∧ t default ∈ U := by
  let Z := pullback p s
  let b := pullback.snd p s
  let : IsFinite b := MorphismProperty.pullback_snd p s (inferInstance : IsFinite p)
  let : JacobsonSpace Z := LocallyOfFiniteType.jacobsonSpace b
  have hdense : Dense (closedPoints Z) := dense_iff_closure_eq.mpr closure_closedPoints
  obtain ⟨y, hy, hyp⟩ := hU
  let a := pullback.fst p s
  have hy' : y ∈ Set.range a := by
    change y ∈ Set.range (pullback.fst p s)
    rw [Scheme.Pullback.range_fst p s]
    exact ⟨default, hyp.symm⟩
  obtain ⟨z₀, hz₀⟩ := hy'
  obtain ⟨z, hzU, hz⟩ := hdense.inter_open_nonempty (a ⁻¹' (U : Set Y))
    (U.isOpen.preimage a.continuous) ⟨z₀, by simpa [Set.mem_preimage, hz₀] using hy⟩
  let t := pointOfClosedPoint b z hz
  refine ⟨t ≫ a, ?_, ?_⟩
  · change (t ≫ pullback.fst p s) ≫ p = _
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    exact (congrArg (· ≫ s) (pointOfClosedPoint_comp b z hz)).trans (Category.id_comp s)
  · change a (t default) ∈ U
    rw [pointOfClosedPoint_apply]
    exact hzU

/-- A point with algebraically closed coefficients lifts along a finite
surjective morphism over the same coefficient field. -/
theorem exists_lift_of_finite_surjective {X Y : Scheme.{u}} (p : Y ⟶ X)
    [IsFinite p] [Surjective p] {K : Type u} [Field K] [IsAlgClosed K]
    (s : Spec (.of K) ⟶ X) : ∃ t : Spec (.of K) ⟶ Y, t ≫ p = s := by
  obtain ⟨y, hy⟩ := p.surjective (s default)
  obtain ⟨t, ht, _⟩ := exists_lift_in_open_of_finite p s ⊤ ⟨y, trivial, hy⟩
  exact ⟨t, ht⟩

/-- A point with algebraically closed coefficients lifts along an
integral surjection over the same coefficient field. -/
theorem exists_lift_of_integral_surjective {X Y : Scheme.{u}} (p : Y ⟶ X)
    [IsIntegralHom p] [Surjective p] {K : Type u} [Field K] [IsAlgClosed K]
    (s : Spec (.of K) ⟶ X) : ∃ t : Spec (.of K) ⟶ Y, t ≫ p = s := by
  let Z := pullback p s
  let b : Z ⟶ Spec (.of K) := pullback.snd p s
  let : IsIntegralHom b := MorphismProperty.pullback_snd p s (inferInstance : IsIntegralHom p)
  let : Surjective b := MorphismProperty.pullback_snd p s (inferInstance : Surjective p)
  let : IsAffine Z := isAffine_of_isAffineHom b
  let B := Γ(Z, ⊤)
  let e : Z ≅ Spec B := Z.isoSpec
  let g : CommRingCat.of K ⟶ B := Spec.preimage (e.inv ≫ b)
  have hg : Spec.map g = e.inv ≫ b := Spec.map_preimage _
  have hInt : IsIntegralHom (Spec.map g) :=
    hg.symm ▸ inferInstanceAs (IsIntegralHom (e.inv ≫ b))
  let : Algebra K B := g.hom.toAlgebra
  let : Algebra.IsIntegral K B := ⟨IsIntegralHom.SpecMap_iff.mp hInt⟩
  obtain ⟨z, _⟩ := b.surjective default
  let : Nontrivial B := PrimeSpectrum.nonempty_iff_nontrivial.mp ⟨e.hom z⟩
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (α := B)
  let : m.IsMaximal := hm
  let : Field (B ⧸ m) := Ideal.Quotient.field m
  let a := algebraMap K (B ⧸ m)
  let e' := RingEquiv.ofBijective a IsAlgClosed.algebraMap_bijective_of_isIntegral
  let φ : B →+* K := e'.symm.toRingHom.comp (Ideal.Quotient.mk m)
  have hφ : φ.comp g.hom = RingHom.id K := by
    ext x
    exact e'.symm_apply_apply x
  let t := Spec.map (CommRingCat.ofHom φ) ≫ e.inv
  have ht : t ≫ b = 𝟙 _ := by
    change (Spec.map (CommRingCat.ofHom φ) ≫ e.inv) ≫ b = _
    rw [Category.assoc, ← hg, ← Spec.map_comp]
    have hmap : g ≫ CommRingCat.ofHom φ = 𝟙 _ :=
      CommRingCat.hom_ext hφ
    rw [hmap, Spec.map_id]
  refine ⟨t ≫ pullback.fst p s, ?_⟩
  rw [Category.assoc, pullback.condition, ← Category.assoc, ht, Category.id_comp]

end PhilipponEtaleFinitePointLifts

end

section

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace PhilipponGenericMorphismCoefficients


/-- A finitely generated base subalgebra of a fraction field is defined on
one principal open of any given affine model. The factorization uses the
actual field, not an abstractly isomorphic field. -/
lemma factor_fg_base_subalgebra
    (B E : Type u) [CommRing B] [IsDomain B] [Field E]
    [Algebra B E] [IsFractionRing B E]
    (A : Subalgebra B E) (hA : A.FG) :
    ∃ (s : B), s ≠ 0 ∧
      ∃ (γ : Localization.Away s →ₐ[B] E), Function.Injective γ ∧
        ∃ (φ : A →ₐ[B] Localization.Away s),
          γ.comp φ = A.val := by
  classical
  obtain ⟨T, hT⟩ := hA
  obtain ⟨s, hs⟩ := IsLocalization.exist_integer_multiples_of_finset
    (nonZeroDivisors B) T
  have hs0 : (s : B) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp s.property
  let γ : Localization.Away (s : B) →ₐ[B] E :=
    IsLocalization.Away.liftAlgHom (s : B)
      (f := Algebra.ofId B E)
      (isUnit_iff_ne_zero.mpr (by
        change algebraMap B E (s : B) ≠ 0
        simpa only [map_zero] using (IsFractionRing.injective B E).ne hs0))
  have hγbase (b : B) : γ (algebraMap B (Localization.Away (s : B)) b) =
      algebraMap B E b := γ.commutes b
  have hM : Submonoid.powers (s : B) ≤ nonZeroDivisors B := by
    intro b hb
    obtain ⟨n, rfl⟩ := by simpa only [Algebra.smul_def] using hb
    exact mem_nonZeroDivisors_iff_ne_zero.mpr (pow_ne_zero _ hs0)
  have hγ : Function.Injective γ := by
    apply (IsLocalization.injective_iff_map_algebraMap_eq
      (Submonoid.powers (s : B)) γ.toRingHom).mpr
    intro x y
    change algebraMap B (Localization.Away (s : B)) x = _ ↔
      γ (algebraMap B (Localization.Away (s : B)) x) =
        γ (algebraMap B (Localization.Away (s : B)) y)
    rw [hγbase, hγbase]
    exact (IsLocalization.injective _ hM).eq_iff.trans
      (IsFractionRing.injective B E).eq_iff.symm
  have hTA : A ≤ γ.range := by
    rw [← hT]
    apply Algebra.adjoin_le
    intro x hx
    obtain ⟨b, hb⟩ := hs x hx
    have hb' : algebraMap B E b = algebraMap B E s * x := by simpa only [Algebra.smul_def] using hb
    refine ⟨algebraMap B (Localization.Away (s : B)) b *
      IsLocalization.Away.invSelf (s : B), ?_⟩
    change γ (_ * _) = x
    apply mul_left_cancel₀ (show algebraMap B E s ≠ 0 by
      simpa only [map_zero] using (IsFractionRing.injective B E).ne hs0)
    rw [map_mul, hγbase, hb']
    calc
      algebraMap B E s * (algebraMap B E s * x * γ (IsLocalization.Away.invSelf (s : B))) =
          (algebraMap B E s * x) * γ (algebraMap B (Localization.Away (s : B)) s *
            IsLocalization.Away.invSelf (s : B)) := by rw [map_mul, hγbase]; ring
      _ = algebraMap B E s * x := by
        rw [IsLocalization.Away.mul_invSelf, map_one]
        simp
  let e := AlgEquiv.ofInjective γ hγ
  let φ : A →ₐ[B] Localization.Away (s : B) :=
    e.symm.toAlgHom.comp (Subalgebra.inclusion hTA)
  refine ⟨s, hs0, γ, hγ, φ, ?_⟩
  ext x
  change γ (e.symm (Subalgebra.inclusion hTA x)) = (x : E)
  have he := congrArg (fun z : γ.range => (z : E))
    (e.apply_symm_apply (Subalgebra.inclusion hTA x))
  exact (AlgEquiv.ofInjective_apply γ hγ _).symm.trans he


end PhilipponGenericMorphismCoefficients

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 900000

open scoped BigOperators TensorProduct
open Algebra.TensorProduct
open PhilipponEtaleGenericIdempotents (exists_lift_completeOrthogonalIdempotents)
open PhilipponGenericMorphismCoefficients (factor_fg_base_subalgebra)


namespace PhilipponEtaleGenericSplittingSpread

universe u v

private def coordinate {R S K I : Type u} [CommRing R] [CommRing S] [CommRing K]
    [Algebra R S] [Algebra R K] (e : K ⊗[R] S ≃ₐ[K] (I → K)) (i : I) : S →ₐ[R] K :=
  ((Pi.evalAlgHom K (fun _ : I => K) i).comp e.toAlgHom).restrictScalars R |>.comp includeRight

private theorem split_of_coordinates_lift {R S K I A : Type u} [CommRing R] [IsDomain R]
    [IsIntegrallyClosed R] [CommRing S] [Algebra R S] [Algebra.Etale R S]
    [Field K] [Algebra R K] [IsFractionRing R K] [Finite I]
    [CommRing A] [Algebra R A] (γ : A →ₐ[R] K) (hγ : Function.Injective γ)
    (e : K ⊗[R] S ≃ₐ[K] (I → K)) (d : I → S →ₐ[R] A)
    (hd : ∀ i s, γ (d i s) = coordinate e i s) :
    Nonempty (A ⊗[R] S ≃ₐ[A] (I → A)) := by
  classical
  let : Fintype I := Fintype.ofFinite I
  let f : A ⊗[R] S →ₐ[A] (I → A) := (AlgHom.pi d).liftEquiv R A S (I → A)
  let τ : A ⊗[R] S →ₐ[R] K ⊗[R] S := map γ (AlgHom.id R S)
  have hτ : Function.Injective τ :=
    Module.Flat.rTensor_preserves_injective_linearMap (M := S) γ.toLinearMap hγ
  have hcomp (x : A ⊗[R] S) (i : I) : γ (f x i) = e (τ x) i := by
    let g : (I → A) →ₐ[R] (I → K) :=
      AlgHom.pi (fun j => γ.comp (Pi.evalAlgHom R (fun _ : I => A) j))
    have h : g.comp (f.restrictScalars R) = (e.toAlgHom.restrictScalars R).comp τ := by
      apply Algebra.TensorProduct.ext'
      intro a s
      ext i
      change γ ((f (a ⊗ₜ[R] s)) i) = e (τ (a ⊗ₜ[R] s)) i
      rw [show f (a ⊗ₜ[R] s) i = a * d i s by rfl, map_mul, hd]
      change γ a * coordinate e i s = e (map γ (AlgHom.id R S) (a ⊗ₜ[R] s)) i
      rw [map_tmul, AlgHom.id_apply]
      have ht : (γ a ⊗ₜ[R] s) = algebraMap K (K ⊗[R] S) (γ a) * (1 ⊗ₜ[R] s) := by
        simp only [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self_apply,
          tmul_mul_tmul, mul_one, one_mul]
      rw [ht, map_mul, e.commutes]
      rfl
    exact congrFun (DFunLike.congr_fun h x) i
  have hInj : Function.Injective f := by
    intro x y h
    apply hτ
    apply e.injective
    funext i
    rw [← hcomp, h, hcomp]
  let e' := (Algebra.TensorProduct.comm R S K).toRingEquiv.trans e.toRingEquiv
  obtain ⟨a, _, ha⟩ := exists_lift_completeOrthogonalIdempotents (I := I) e'
  have ha' (i : I) : f (1 ⊗ₜ[R] a i) = Pi.single i 1 := by
    have h : e (1 ⊗ₜ[R] a i) = Pi.single i 1 := by
      simpa [e', Algebra.TensorProduct.comm_tmul] using ha i
    ext j
    apply hγ
    rw [hcomp]
    change e (map γ (AlgHom.id R S) (1 ⊗ₜ[R] a i)) j = _
    rw [map_tmul, map_one, AlgHom.id_apply, h]
    by_cases hij : j = i
    · subst j
      simp
    · simp [Pi.single_eq_of_ne hij]
  have hSurj : Function.Surjective f := by
    intro v
    refine ⟨∑ i, algebraMap A (A ⊗[R] S) (v i) * (1 ⊗ₜ[R] a i), ?_⟩
    rw [map_sum]
    convert Finset.univ_sum_single v using 1
    apply Finset.sum_congr rfl
    intro i _
    rw [map_mul, f.commutes, ha']
    ext j
    by_cases hij : j = i
    · subst j
      simp
    · simp [Pi.single_eq_of_ne hij]
  exact ⟨AlgEquiv.ofBijective f ⟨hInj, hSurj⟩⟩

/-- Finitely many generic splittings of affine étale algebras over a
normal domain extend to splittings on the same principal open. -/
theorem exists_away_algEquiv_finset {R K : Type u} {J : Type v} [CommRing R] [IsDomain R]
    [IsIntegrallyClosed R] [Field K] [Algebra R K] [IsFractionRing R K]
    (S I : J → Type u) [∀ j, CommRing (S j)] [∀ j, Algebra R (S j)]
    [∀ j, Algebra.Etale R (S j)] [∀ j, Finite (I j)]
    (e : ∀ j, K ⊗[R] S j ≃ₐ[K] (I j → K)) (s : Finset J) :
    ∃ r : R, r ≠ 0 ∧ ∀ j ∈ s,
      Nonempty (Localization.Away r ⊗[R] S j ≃ₐ[Localization.Away r] (I j → Localization.Away r)) := by
  classical
  let (j : J) : Fintype (I j) := Fintype.ofFinite (I j)
  choose U hU using fun j => (inferInstance : Algebra.FiniteType R (S j)).out
  let V : Finset K := s.biUnion fun j => (U j).biUnion fun x =>
    Finset.univ.image fun i => coordinate (e j) i x
  let T : Subalgebra R K := Algebra.adjoin R (V : Set K)
  have hT : T.FG := ⟨V, rfl⟩
  have hb (j : J) (hj : j ∈ s) (i : I j) : ∀ x, coordinate (e j) i x ∈ T := by
    have h : (⊤ : Subalgebra R (S j)) ≤ T.comap (coordinate (e j) i) := by
      rw [← hU j]
      apply Algebra.adjoin_le
      intro x hx
      apply Algebra.subset_adjoin
      exact Finset.mem_biUnion.mpr ⟨j, hj, Finset.mem_biUnion.mpr
        ⟨x, hx, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩⟩
    exact fun x => h (show x ∈ (⊤ : Subalgebra R (S j)) by trivial)
  obtain ⟨r, hr, γ, hγ, δ, hδ⟩ := factor_fg_base_subalgebra R K T hT
  refine ⟨r, hr, fun j hj => ?_⟩
  let d (i : I j) : S j →ₐ[R] Localization.Away r :=
    δ.comp ((coordinate (e j) i).codRestrict T (hb j hj i))
  exact split_of_coordinates_lift γ hγ (e j) d
    (fun i x => DFunLike.congr_fun hδ (⟨coordinate (e j) i x, hb j hj i x⟩ : T))

/-- A finite family of affine étale algebras over a domain splits on a
dense principal open of the normalization in one finite separable extension
of the fraction field. -/
theorem exists_simultaneous_split_on_normalization
    {R : Type u} [CommRing R] [IsDomain R] {J : Type v}
    (S : J → Type u) [∀ j, CommRing (S j)] [∀ j, Algebra R (S j)]
    [∀ j, Algebra.Etale R (S j)] (s : Finset J) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra (FractionRing R) L)
      (_ : FiniteDimensional (FractionRing R) L) (_ : Algebra.IsSeparable (FractionRing R) L)
      (_ : Algebra R L) (_ : IsScalarTower R (FractionRing R) L)
      (b : integralClosure R L), b ≠ 0 ∧
      ∀ j ∈ s, ∃ (I : Type u) (_ : Finite I), Nonempty
        (Localization.Away b ⊗[R] S j ≃ₐ[Localization.Away b] (I → Localization.Away b)) := by
  classical
  let K := FractionRing R
  obtain ⟨L, _, _, _, _, hL⟩ :=
    PhilipponFiniteEtaleSplittingField.exists_splittingField_finset K (fun j => K ⊗[R] S j) s
  let : Algebra R L := ((algebraMap K L).comp (algebraMap R K)).toAlgebra
  let : IsScalarTower R K L := IsScalarTower.of_algebraMap_eq' rfl
  let B := integralClosure R L
  let : IsFractionRing B L := integralClosure.isFractionRing_of_finite_extension K L
  let : IsIntegrallyClosed B := integralClosure.isIntegrallyClosedOfFiniteExtension K
  have hsplit (j : s) : ∃ n : ℕ, Nonempty (L ⊗[B] (B ⊗[R] S j) ≃ₐ[L] (Fin n → L)) := by
    obtain ⟨n, ⟨a⟩⟩ := (hL j j.property).nonempty_algEquiv_fun
    exact ⟨n, ⟨(cancelBaseChange R B L L (S j)).trans
      ((cancelBaseChange R K L L (S j)).symm.trans a)⟩⟩
  choose n hn using hsplit
  let I (j : s) := ULift.{u} (Fin (n j))
  let (j : s) : Finite (I j) := inferInstanceAs (Finite (ULift (Fin (n j))))
  let e (j : s) : L ⊗[B] (B ⊗[R] S j) ≃ₐ[L] (I j → L) :=
    (Classical.choice (hn j)).trans (AlgEquiv.piCongrLeft' L (fun _ : Fin (n j) => L) Equiv.ulift.symm)
  obtain ⟨b, hb, h⟩ := exists_away_algEquiv_finset (fun j : s => B ⊗[R] S j) I e Finset.univ
  refine ⟨L, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, b, hb, fun j hj => ?_⟩
  let A := Localization.Away b
  let j' : s := ⟨j, hj⟩
  obtain ⟨a⟩ := h j' (Finset.mem_univ j')
  exact ⟨I j', inferInstance, ⟨(cancelBaseChange R B A A (S j)).symm.trans a⟩⟩

end PhilipponEtaleGenericSplittingSpread

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PhilipponEtaleBaseChangeComparison (baseChange)
open PhilipponEtaleFiniteConstantColimits (finiteConstant)
open PhilipponEtaleFinitePresentations
  (chartSplits exists_trivializing_charts finiteEtalePresentations)
open PhilipponEtaleSmallSite (pullbackSheaves)
open PhilipponFreeEtaleFieldTrivialization (chart exists_affineChartIso splitBaseChangeIso)


namespace PhilipponEtaleFinitePresentationTrivialization

universe u

private abbrev Ab (X : Scheme.{u}) := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}

private abbrev specMap (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] :
    Spec (.of S) ⟶ Spec (.of R) := Spec.map (CommRingCat.ofHom (algebraMap R S))

/-- A bounded finite presentation on an affine scheme becomes finite
constant on a dense principal open of the normalization of any integral
affine base change in a suitable finite separable extension. -/
theorem exists_trivialization_on_normalization
    {X : Scheme.{u}} [IsAffine X] (R : Type u) [CommRing R] [IsDomain R]
    (i : Spec (.of R) ⟶ X) (N : ℕ) (hN : N ≠ 0) (F : Ab X)
    (hF : finiteEtalePresentations X N F) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra (FractionRing R) L)
      (_ : FiniteDimensional (FractionRing R) L) (_ : Algebra.IsSeparable (FractionRing R) L)
      (_ : Algebra R L) (_ : IsScalarTower R (FractionRing R) L)
      (b : integralClosure R L), b ≠ 0 ∧
      finiteConstant (Spec (.of (Localization.Away b))) N
        ((pullbackSheaves (specMap R (Localization.Away b) ≫ i)).obj F) := by
  classical
  obtain ⟨s, hs⟩ := exists_trivializing_charts X N hN F hF
  let U (j : s) := (Scheme.AffineEtale.Spec X).obj j.val
  have hU (j : s) : IsAffine (U j).left := inferInstanceAs (IsAffine (Spec _))
  let V (j : s) := (baseChange i).obj (U j)
  let (j : s) : IsAffine (V j).left :=
    @Scheme.Pullback.isAffine_of_isAffine_isAffine_isAffine (U j).left (Spec (.of R)) X
      (U j).hom i (hU j) inferInstance ‹IsAffine X›
  choose S hc ha he e using fun j : s => exists_affineChartIso R (V j)
  let : ∀ j, CommRing (S j) := hc
  let : ∀ j, Algebra R (S j) := ha
  let : ∀ j, Algebra.Etale R (S j) := he
  obtain ⟨L, _, _, _, _, _, _, b, hb, hsplit⟩ :=
    PhilipponEtaleGenericSplittingSpread.exists_simultaneous_split_on_normalization
      (R := R) S Finset.univ
  refine ⟨L, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, b, hb, ?_⟩
  let A := Localization.Away b
  let : IsDomain A := Localization.Away.isDomain hb
  let hA : IrreducibleSpace (PrimeSpectrum A) := PrimeSpectrum.irreducibleSpace
  let : PreconnectedSpace (Spec (.of A)) :=
    @PreirreducibleSpace.preconnectedSpace (PrimeSpectrum A) _ hA.toPreirreducibleSpace
  let : Nonempty (Spec (.of A)) := hA.toNonempty
  let f := specMap R A
  refine hs (Spec (.of A)) (f ≫ i) ?_
  intro W hW
  let j : s := ⟨W, hW⟩
  obtain ⟨I, _, ⟨a⟩⟩ := hsplit j (Finset.mem_univ j)
  let c := splitBaseChangeIso R (S j) A I a
  let d := (baseChange f).mapIso (Classical.choice (e j))
  let g := (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) f i).symm.app (U j)
  exact ⟨I, inferInstance, ⟨c ≪≫ d ≪≫ g⟩⟩

end PhilipponEtaleFinitePresentationTrivialization

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponEtaleAcyclicCohomology (globalSections globalSectionsIso globalSectionsIso_hom_app_eq_map pullbackConstantIso)
open PhilipponEtaleBaseChangeComparison (baseChange)
open PhilipponEtaleClosedCover (restriction)
open PhilipponEtaleClosedPushforward (pushforward)
open PhilipponEtaleConstantDegreeZero (continuousSheaf constantSheafIso homEquiv_constantSheafIso_apply)
open PhilipponEtaleSmallSite (pullbackAdjunction pullbackSheaves)


namespace PhilipponEtaleConstantRestriction

universe u

private abbrev terminal (X : Scheme.{u}) := Scheme.Etale.mk (𝟙 X)

private def isTerminal (X : Scheme.{u}) : IsTerminal (terminal X) :=
  IsTerminal.isTerminalOfObj (Scheme.Etale.forget X) _ Over.mkIdTerminal

variable {X Y : Scheme.{u}} (j : Y ⟶ X)
variable (M : Type u) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]

private abbrev constant (V : Scheme.{u}) :=
  (constantSheaf V.smallEtaleTopology AddCommGrpCat.{u}).obj (AddCommGrpCat.of M)

/-- The pullback unit on the constant sheaf is restriction of continuous
coefficient functions along the projection of each base-changed chart. -/
theorem unit_comp_comparison :
    (pullbackAdjunction j).unit.app (constant M X) ≫
      (pushforward j).map (((pullbackConstantIso j).app (AddCommGrpCat.of M)).hom ≫
        (constantSheafIso Y M).hom) = (constantSheafIso X M).hom ≫ restriction M j := by
  let K := AddCommGrpCat.of M
  let e := (pullbackConstantIso j).app K
  let a := pullbackAdjunction j
  let cX := constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u} (isTerminal X)
  let cY := constantSheafAdj Y.smallEtaleTopology AddCommGrpCat.{u} (isTerminal Y)
  let c := Adjunction.ofNatIsoRight (cX.comp a) (globalSectionsIso j)
  let q := e.hom ≫ (constantSheafIso Y M).hom
  let r := (constantSheafIso X M).hom ≫ restriction M j
  let G := continuousSheaf Y M
  let s := (globalSectionsIso j).hom.app G
  have he : c.homEquiv K (constant M Y) e.hom = cY.unit.app K :=
    Adjunction.homEquiv_leftAdjointUniq_hom_app c cY K
  have hq : cX.homEquiv K ((pushforward j).obj G) (a.homEquiv _ _ q) ≫ s =
      cY.homEquiv K G (constantSheafIso Y M).hom := by
    calc
      _ = c.homEquiv K G q := by
        dsimp only [c, s]
        rw [Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv]
        rfl
      _ = _ := by
        dsimp only [q]
        rw [Adjunction.homEquiv_naturality_right, he, Adjunction.homEquiv_unit]
  have hr : cX.homEquiv K ((pushforward j).obj G) r ≫ s =
      cY.homEquiv K G (constantSheafIso Y M).hom := by
    let l : terminal Y ⟶ (baseChange j).obj (terminal X) :=
      MorphismProperty.Over.homMk (pullback.lift j (𝟙 Y) ((Category.comp_id j).trans (Category.id_comp j).symm))
        (pullback.lift_snd ..) trivial
    have hs : s = G.obj.map l.op := globalSectionsIso_hom_app_eq_map j G l
    dsimp only [r]
    rw [Adjunction.homEquiv_naturality_right, hs]
    apply ConcreteCategory.hom_ext
    intro m
    change G.obj.map l.op (((restriction M j).hom.app (op (terminal X)))
      (cX.homEquiv K (continuousSheaf X M) (constantSheafIso X M).hom m)) =
        cY.homEquiv K G (constantSheafIso Y M).hom m
    rw [homEquiv_constantSheafIso_apply X M (isTerminal X),
      homEquiv_constantSheafIso_apply Y M (isTerminal Y)]
    apply ContinuousMap.ext
    intro y
    rfl
  calc
    _ = a.homEquiv (constant M X) G q := rfl
    _ = r := (cX.homEquiv K ((pushforward j).obj G)).injective ((cancel_mono s).mp (hq.trans hr.symm))

end PhilipponEtaleConstantRestriction

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 900000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponEtaleAcyclicCohomology (pullbackConstantIso)
open PhilipponEtaleClosedCover (restriction)
open PhilipponEtaleClosedPushforward (pushforward)
open PhilipponEtaleConstantDegreeZero (constantSheafIso continuousSheaf)
open PhilipponEtaleConstantRestriction (unit_comp_comparison)
open PhilipponEtaleSmallSite (pullbackAdjunction)
open scoped TensorProduct


namespace PhilipponEtaleGenericConstantImage

universe u

variable (R K : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
  [Field K] [Algebra R K] [IsFractionRing R K]

/-- The morphism from the spectrum of the fraction field to the base. -/
abbrev genericInclusion : Spec (.of K) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R K))

variable (M : Type u) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M] [Finite M]

private abbrev SpecMap (S : Type u) [CommRing S] [Algebra R S] :
    Spec (.of S) ⟶ Spec (.of R) := Spec.map (CommRingCat.ofHom (algebraMap R S))

omit [AddCommGroup M] in
private theorem bijective_restrict_affine (S : Type u) [CommRing S] [Algebra R S]
    [Algebra.Etale R S] :
    Function.Bijective (fun t : C(Spec (.of S), M) =>
      let a := pullback.fst (SpecMap R S) (genericInclusion R K)
      t.comp ⟨a, a.continuous⟩) := by
  let B := S ⊗[R] K
  let a : Spec (.of B) ⟶ Spec (.of S) := Spec.map (CommRingCat.ofHom (algebraMap S B))
  let b : Spec (.of B) ⟶ Spec (.of K) :=
    Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : K →ₐ[R] B).toRingHom)
  have h : IsPullback a b (SpecMap R S) (genericInclusion R K) :=
    isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct R S K)
  let P := pullback (SpecMap R S) (genericInclusion R K)
  let p : P ⟶ Spec (.of S) := pullback.fst (SpecMap R S) (genericInclusion R K)
  let e : Spec (.of B) ≅ P := h.isoPullback
  let f : C(Spec (.of S), M) → C(P, M) := fun t => t.comp ⟨p, p.continuous⟩
  let g : C(P, M) → C(Spec (.of B), M) := fun t => t.comp ⟨e.hom, e.hom.continuous⟩
  have hg : Function.Injective g := by
    intro s t he
    apply ContinuousMap.ext
    intro x
    obtain ⟨y, rfl⟩ := e.hom.homeomorph.surjective x
    exact congrArg (fun w : C(Spec (.of B), M) => w y) he
  have he (s : C(Spec (.of S), M)) :
      g (f s) = s.comp (PhilipponEtaleGenericConstantSections.genericMap (R := R) (K := K)) := by
    apply ContinuousMap.ext
    intro x
    exact congrArg s (congrArg (fun k : Spec (.of B) ⟶ Spec (.of S) => k x) h.isoPullback_hom_fst)
  have hSections := PhilipponEtaleGenericConstantSections.bijective_genericMap_sections
    (R := R) (S := S) (K := K) M
  change Function.Bijective f
  constructor
  · intro s t hEq
    exact hSections.injective ((he s).symm.trans ((congrArg g hEq).trans (he t)))
  · intro s
    obtain ⟨t, ht⟩ := hSections.surjective (g s)
    exact ⟨t, hg ((he t).trans ht)⟩

private theorem isIso_restriction : IsIso (restriction M (genericInclusion R K)) := by
  let X := Spec (.of R)
  let A := AddCommGrpCat.{u}
  let e := (Scheme.AffineEtale.sheafEquiv X A).inverse
  let U := sheafToPresheaf (Scheme.AffineEtale.topology X) A
  let h := restriction M (genericInclusion R K)
  suffices IsIso ((e ⋙ U).map h) from isIso_of_reflects_iso h (e ⋙ U)
  rw [NatTrans.isIso_iff_isIso_app]
  intro W
  let S := W.unop.left.unop
  let V := (Scheme.AffineEtale.Spec X).obj W.unop
  let φ : CommRingCat.of R ⟶ S := Spec.preimage V.hom
  let : Algebra R S := φ.hom.toAlgebra
  have hφ : Etale (Spec.map φ) := by unfold φ; rw [Spec.map_preimage]; exact V.prop
  let : Algebra.Etale R S := (HasRingHomProperty.Spec_iff (P := @Etale)).mp hφ
  apply (ConcreteCategory.isIso_iff_bijective _).2
  change Function.Bijective (fun t : C(Spec S, M) =>
    let a := pullback.fst V.hom (genericInclusion R K)
    t.comp ⟨a, a.continuous⟩)
  have he : SpecMap R S = V.hom := Spec.map_preimage V.hom
  rw [← he]
  exact bijective_restrict_affine R K M S

private abbrev constant (X : Scheme.{u}) :=
  (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj (AddCommGrpCat.of M)

/-- The inverse-image unit identifies a finite constant étale sheaf on
a normal affine domain with the direct image of its generic restriction. -/
theorem isIso_unit_genericInclusion :
    IsIso ((pullbackAdjunction (genericInclusion R K)).unit.app (constant M (Spec (.of R)))) := by
  let j := genericInclusion R K
  let f := (pullbackAdjunction j).unit.app (constant M (Spec (.of R)))
  let e := (pullbackConstantIso j).app (AddCommGrpCat.of M)
  let a := (pushforward j).map (e.hom ≫ (constantSheafIso (Spec (.of K)) M).hom)
  let b := (constantSheafIso (Spec (.of R)) M).hom
  let : IsIso (restriction M j) := isIso_restriction R K M
  have h : f ≫ a = b ≫ restriction M j := unit_comp_comparison j M
  have : IsIso (f ≫ a) := h ▸ (inferInstance : IsIso (b ≫ restriction M j))
  exact IsIso.of_isIso_comp_right f a

end PhilipponEtaleGenericConstantImage

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

open AlgebraicGeometry CategoryTheory
open PhilipponEtaleAcyclicCohomology (pullbackConstantIso)
open PhilipponEtaleClosedPushforward (pushforward)
open PhilipponEtaleDirectImageGerms (evalAtLift evalAtLift_naturality evalAtLift_unit)
open PhilipponEtaleGenericConstantImage (genericInclusion isIso_unit_genericInclusion)
open PhilipponEtaleSmallSite (pullbackAdjunction pullbackSheaves)
open PhilipponEtaleStalkPullback (stalkPullbackIso)


namespace PhilipponEtaleGenericConstantExtension

universe u

private abbrev Ab (X : Scheme.{u}) := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}

/-- If an adjoint coefficient map is injective on a lifted stalk, its
associated map into the direct image is injective on the base stalk. -/
theorem stalk_mono_homEquiv {X Y : Scheme.{u}} (p : Y ⟶ X) {F : Ab X} {G : Ab Y}
    (a : (pullbackSheaves p).obj F ⟶ G) {L : Type u} [Field L] [IsSepClosed L]
    (t : Spec (.of L) ⟶ Y) [Mono ((Scheme.pointSmallEtale t).sheafFiber.map a)] :
    Mono ((Scheme.pointSmallEtale (t ≫ p)).sheafFiber.map ((pullbackAdjunction p).homEquiv F G a)) := by
  let T := (Scheme.pointSmallEtale (t ≫ p)).sheafFiber (A := AddCommGrpCat.{u})
  let U := (Scheme.pointSmallEtale t).sheafFiber (A := AddCommGrpCat.{u})
  let Lp := pullbackSheaves p
  let Rp := pushforward p
  let η := (pullbackAdjunction p).unit.app F
  let e := (stalkPullbackIso p t).app F
  have hu : T.map η ≫ evalAtLift p t (Lp.obj F) = e.inv := by
    apply (cancel_mono e.hom).mp
    rw [Category.assoc, e.inv_hom_id]
    exact evalAtLift_unit p t F
  have he : T.map ((pullbackAdjunction p).homEquiv F G a) ≫ evalAtLift p t G =
      e.inv ≫ U.map a := by
    rw [Adjunction.homEquiv_unit, T.map_comp, Category.assoc]
    have hn : T.map (Rp.map a) ≫ evalAtLift p t G =
        evalAtLift p t (Lp.obj F) ≫ U.map a := evalAtLift_naturality p t a
    rw [hn, ← Category.assoc, hu]
  exact mono_of_mono_fac he

private abbrev constant (X : Scheme.{u}) (M : AddCommGrpCat.{u}) :=
  (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj M

/-- A map of finite constant sheaves on a connected scheme is an
isomorphism if it becomes one after pullback to a connected nonempty scheme. -/
theorem isIso_of_pullback_of_finiteConstant {X Y : Scheme.{u}}
    [PreconnectedSpace X] [Nonempty X] [PreconnectedSpace Y] [Nonempty Y]
    (f : Y ⟶ X) {F G : Ab X} (m : F ⟶ G) (N : ℕ)
    (hF : PhilipponEtaleFiniteConstantColimits.finiteConstant X N F)
    (hG : PhilipponEtaleFiniteConstantColimits.finiteConstant X N G)
    (hm : IsIso ((pullbackSheaves f).map m)) : IsIso m := by
  obtain ⟨A, _, ⟨eF⟩⟩ := hF
  obtain ⟨B, _, ⟨eG⟩⟩ := hG
  let C := constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}
  let D := constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u}
  let ff := PhilipponEtaleFiniteConstantColimits.constantSheafFullyFaithful X
  let gg := PhilipponEtaleFiniteConstantColimits.constantSheafFullyFaithful Y
  let P := pullbackSheaves f
  let b : A ⟶ B := ff.preimage (eF.hom ≫ m ≫ eG.inv)
  have hb : C.map b = eF.hom ≫ m ≫ eG.inv := ff.map_preimage _
  let : IsIso (P.map m) := hm
  let : IsIso (P.map (C.map b)) := by
    rw [hb, P.map_comp, P.map_comp]
    infer_instance
  let e := pullbackConstantIso f
  have hnat : P.map (C.map b) ≫ e.hom.app B = e.hom.app A ≫ D.map b := e.hom.naturality b
  let : IsIso (e.hom.app A ≫ D.map b) := hnat ▸ inferInstance
  let : IsIso (D.map b) := IsIso.of_isIso_comp_left (e.hom.app A) (D.map b)
  let : IsIso b := gg.isIso_of_isIso_map b
  have he : m = eF.inv ≫ C.map b ≫ eG.hom := by
    rw [hb]
    simp
  rw [he]
  infer_instance

/-- A finite constant generic trivialization extends to a coefficient
map on a normal affine scheme which is an isomorphism over its generic point. -/
theorem exists_extension_of_generic_trivialization
    (R K : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [Field K] [Algebra R K] [IsFractionRing R K] {X : Scheme.{u}}
    (p : Spec (.of R) ⟶ X) (F : Ab X) (M : AddCommGrpCat.{u}) [Finite M]
    (β : (pullbackSheaves (genericInclusion R K)).obj ((pullbackSheaves p).obj F) ≅
      constant (Spec (.of K)) M) :
    ∃ a : (pullbackSheaves p).obj F ⟶ constant (Spec (.of R)) M,
      IsIso ((pullbackSheaves (genericInclusion R K)).map a) := by
  let j := genericInclusion R K
  let a := pullbackAdjunction j
  let E := (pullbackSheaves p).obj F
  let C := constant (Spec (.of R)) M
  let e := β ≪≫ ((pullbackConstantIso j).app M).symm
  let η := a.unit.app C
  let : TopologicalSpace M := ⊥
  let : DiscreteTopology M := ⟨rfl⟩
  let : IsIso η := isIso_unit_genericInclusion R K M
  let b := a.homEquiv E ((pullbackSheaves j).obj C) e.hom
  let α : E ⟶ C := b ≫ inv η
  have hα : (pullbackSheaves j).map α = e.hom := by
    apply (a.homEquiv E ((pullbackSheaves j).obj C)).injective
    calc
      _ = α ≫ η := by
        simpa only [Category.comp_id, a.homEquiv_id] using
          a.homEquiv_naturality_left α (𝟙 ((pullbackSheaves j).obj C))
      _ = b := by
        change (b ≫ inv η) ≫ η = b
        rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  exact ⟨α, hα.symm ▸ (inferInstance : IsIso e.hom)⟩

/-- A generic trivialization on a normal affine model gives a coefficient
map into the constant direct image that is injective at all geometric
points of the base lifting to that generic point. -/
theorem exists_map_of_generic_trivialization
    (R K : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [Field K] [Algebra R K] [IsFractionRing R K] {X : Scheme.{u}}
    (p : Spec (.of R) ⟶ X) (F : Ab X) (M : AddCommGrpCat.{u}) [Finite M]
    (β : (pullbackSheaves (genericInclusion R K)).obj ((pullbackSheaves p).obj F) ≅
      constant (Spec (.of K)) M) :
    ∃ f : F ⟶ (pushforward p).obj (constant (Spec (.of R)) M),
      ∀ (L : Type u) [Field L] [IsSepClosed L] (t : Spec (.of L) ⟶ Spec (.of K)),
        Mono ((Scheme.pointSmallEtale ((t ≫ genericInclusion R K) ≫ p)).sheafFiber.map f) := by
  obtain ⟨α, hα⟩ := exists_extension_of_generic_trivialization R K p F M β
  let : IsIso ((pullbackSheaves (genericInclusion R K)).map α) := hα
  let j := genericInclusion R K
  let E := (pullbackSheaves p).obj F
  let C := constant (Spec (.of R)) M
  refine ⟨(pullbackAdjunction p).homEquiv F C α, fun L _ _ t => ?_⟩
  let T := (Scheme.pointSmallEtale (t ≫ j)).sheafFiber (A := AddCommGrpCat.{u})
  let U := (Scheme.pointSmallEtale t).sheafFiber (A := AddCommGrpCat.{u})
  let d := stalkPullbackIso j t
  have hn : U.map ((pullbackSheaves j).map α) ≫ d.hom.app C = d.hom.app E ≫ T.map α :=
    d.hom.naturality α
  let : IsIso (d.hom.app E ≫ T.map α) := hn ▸ inferInstance
  let : IsIso (T.map α) := IsIso.of_isIso_comp_left (d.hom.app E) (T.map α)
  exact stalk_mono_homEquiv p α (t ≫ j)

end PhilipponEtaleGenericConstantExtension

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

open AlgebraicGeometry CategoryTheory
open PhilipponEtaleAcyclicCohomology (pullbackConstantIso)
open PhilipponEtaleClosedPushforward (pushforward)
open PhilipponEtaleCohomologyAlong (pullbackComposition)
open PhilipponEtaleFiniteConstantColimits (finiteCoefficients finiteConstant)
open PhilipponEtaleGenericConstantExtension
  (exists_extension_of_generic_trivialization isIso_of_pullback_of_finiteConstant stalk_mono_homEquiv)
open PhilipponEtaleGenericConstantImage (genericInclusion)
open PhilipponEtaleSmallSite (pullbackAdjunction pullbackSheaves)
open PhilipponEtaleStalkPullback (stalkPullbackIso)


namespace PhilipponEtaleGenericChartExtension

universe u

private abbrev Ab (X : Scheme.{u}) := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}

private abbrev constant (X : Scheme.{u}) (M : AddCommGrpCat.{u}) :=
  (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj M

private theorem isIso_stalk_of_isIso_pullback {Y V : Scheme.{u}} (v : V ⟶ Y)
    {E C : Ab Y} (a : E ⟶ C) [IsIso ((pullbackSheaves v).map a)]
    {L : Type u} [Field L] [IsSepClosed L] (t : Spec (.of L) ⟶ V) :
    IsIso ((Scheme.pointSmallEtale (t ≫ v)).sheafFiber.map a) := by
  exact (NatIso.isIso_map_iff (stalkPullbackIso v t) a).mp
    (inferInstanceAs (IsIso
      ((Scheme.pointSmallEtale t).sheafFiber.map ((pullbackSheaves v).map a))))

/-- A finite constant trivialization on a connected chart through the
generic point gives a map into the constant direct image of the normal
model. Its stalk map is injective wherever the geometric point lifts to the chart. -/
theorem exists_map_of_const_on_generic_chart
    (R K : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [Field K] [Algebra R K] [IsFractionRing R K] {X V : Scheme.{u}}
    [PreconnectedSpace V] [Nonempty V]
    (p : Spec (.of R) ⟶ X) (v : V ⟶ Spec (.of R))
    (r : Spec (.of K) ⟶ V) (hr : r ≫ v = genericInclusion R K)
    (F : Ab X) (N : ℕ) (hF : finiteConstant V N ((pullbackSheaves v).obj ((pullbackSheaves p).obj F))) :
    ∃ (M : AddCommGrpCat.{u}) (_ : finiteCoefficients N M)
      (m : F ⟶ (pushforward p).obj (constant (Spec (.of R)) M)),
      ∀ (L : Type u) [Field L] [IsSepClosed L] (t : Spec (.of L) ⟶ V),
        Mono ((Scheme.pointSmallEtale ((t ≫ v) ≫ p)).sheafFiber.map m) := by
  let E := (pullbackSheaves p).obj F
  let P := pullbackSheaves v
  let Q := pullbackSheaves r
  obtain ⟨M, hM, ⟨β⟩⟩ := hF
  let : Finite M := hM.1
  let C := constant (Spec (.of R)) M
  let e := pullbackComposition v r (genericInclusion R K) hr
  let β₀ : (pullbackSheaves (genericInclusion R K)).obj E ≅ constant (Spec (.of K)) M :=
    (e.app E).symm ≪≫ Q.mapIso β.symm ≪≫ (pullbackConstantIso r).app M
  obtain ⟨α, hα⟩ := exists_extension_of_generic_trivialization R K p F M β₀
  have hQ : IsIso (Q.map (P.map α)) := (NatIso.isIso_map_iff e α).mpr hα
  have hE : finiteConstant V N (P.obj E) := ⟨M, hM, ⟨β⟩⟩
  have hC : finiteConstant V N (P.obj C) := ⟨M, hM, ⟨((pullbackConstantIso v).app M).symm⟩⟩
  let hK : IrreducibleSpace (PrimeSpectrum K) := PrimeSpectrum.irreducibleSpace
  let : PreconnectedSpace (Spec (.of K)) :=
    @PreirreducibleSpace.preconnectedSpace (PrimeSpectrum K) _ hK.toPreirreducibleSpace
  let : Nonempty (Spec (.of K)) := hK.toNonempty
  let : IsIso ((pullbackSheaves v).map α) :=
    isIso_of_pullback_of_finiteConstant r (P.map α) N hE hC hQ
  refine ⟨M, hM, (pullbackAdjunction p).homEquiv F C α, fun L _ _ t => ?_⟩
  let := isIso_stalk_of_isIso_pullback v α t
  exact stalk_mono_homEquiv p α (t ≫ v)

end PhilipponEtaleGenericChartExtension

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits


namespace PhilipponFiniteSchemeCoproduct

universe u

variable {I : Type u} {X : Scheme.{u}} {Y : I → Scheme.{u}} (p : ∀ i, Y i ⟶ X)

/-- A finite coproduct of finite morphisms to an affine scheme is finite. -/
theorem isFinite_sigmaDesc [Finite I] [IsAffine X] [∀ i, IsFinite (p i)] :
    IsFinite (Sigma.desc p) := by
  let : ∀ i, IsAffine (Y i) := fun i => isAffine_of_isAffineHom (p i)
  let R := Γ(X, ⊤)
  let S (i : I) := Γ(Y i, ⊤)
  let : ∀ i, Algebra R (S i) := fun i => (p i).appTop.hom.toAlgebra
  let : ∀ i, Module.Finite R (S i) := fun i => (p i).finite_appTop
  let a : R ⟶ CommRingCat.of (∀ i, S i) := CommRingCat.ofHom (algebraMap R (∀ i, S i))
  let e := (Sigma.mapIso fun i => (Y i).isoSpec) ≪≫ asIso (sigmaSpec S)
  let : IsFinite (Spec.map a) := (IsFinite.SpecMap_iff a).2 (RingHom.finite_algebraMap.mpr inferInstance)
  have he : Sigma.desc p = e.hom ≫ Spec.map a ≫ X.isoSpec.inv := by
    apply Sigma.hom_ext
    intro i
    simp only [e, Sigma.ι_desc, Iso.trans_hom, asIso_hom, Category.assoc, Sigma.ι_mapIso_hom_assoc]
    change p i = (Y i).isoSpec.hom ≫ Sigma.ι (fun j => Spec (S j)) i ≫
      sigmaSpec S ≫ Spec.map a ≫ X.isoSpec.inv
    rw [ι_sigmaSpec_assoc, ← Spec.map_comp_assoc]
    have h : a ≫ CommRingCat.ofHom (Pi.evalRingHom (S ·) i) = (p i).appTop := by
      apply CommRingCat.hom_ext
      ext x
      rfl
    rw [h, Scheme.isoSpec_inv_naturality, Iso.hom_inv_id_assoc]
  rw [he]
  infer_instance

/-- Local finite presentation can be checked on the coproduct inclusions. -/
theorem locallyOfFinitePresentation_sigmaDesc [∀ i, LocallyOfFinitePresentation (p i)] :
    LocallyOfFinitePresentation (Sigma.desc p) := by
  apply IsZariskiLocalAtSource.of_openCover (P := @LocallyOfFinitePresentation) (sigmaOpenCover Y)
  intro i
  change LocallyOfFinitePresentation (Sigma.ι Y i ≫ Sigma.desc p)
  rw [Sigma.ι_desc]
  infer_instance

/-- The inclusion of a component after base change of the coproduct. -/
def pullbackInclusion {T : Scheme.{u}} (f : T ⟶ X) (i : I) :
    pullback f (p i) ⟶ pullback f (Sigma.desc p) :=
  pullback.lift (pullback.fst f (p i)) (pullback.snd f (p i) ≫ Sigma.ι Y i) (by
    rw [Category.assoc, Sigma.ι_desc, pullback.condition])

@[reassoc (attr := simp)]
theorem pullbackInclusion_fst {T : Scheme.{u}} (f : T ⟶ X) (i : I) :
    pullbackInclusion p f i ≫ pullback.fst f (Sigma.desc p) = pullback.fst f (p i) :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem pullbackInclusion_snd {T : Scheme.{u}} (f : T ⟶ X) (i : I) :
    pullbackInclusion p f i ≫ pullback.snd f (Sigma.desc p) =
      pullback.snd f (p i) ≫ Sigma.ι Y i :=
  pullback.lift_snd _ _ _

/-- The pullback of a finite coproduct is the coproduct of the pullbacks. -/
def pullbackCoproductIso [Finite I] {T : Scheme.{u}} (f : T ⟶ X) :
    (∐ fun i => pullback f (p i)) ≅ pullback f (Sigma.desc p) := by
  let a := FinitaryPreExtensive.isUniversal_finiteCoproducts (coproductIsCoproduct Y)
  let h := (a.nonempty_isColimit_of_isPullback_left p (Sigma.desc p) f
    (fun i => pullback.fst f (p i)) (fun i => pullback.snd f (p i))
    (fun i => IsPullback.of_hasPullback f (p i)) (IsPullback.of_hasPullback f (Sigma.desc p))
    (Cofan.mk _ (pullbackInclusion p f)) (Iso.refl _) (by simp) (by simp) (by simp)).some
  exact (coproductIsCoproduct (fun i => pullback f (p i))).coconePointUniqueUpToIso h

@[reassoc (attr := simp)]
theorem ι_pullbackCoproductIso [Finite I] {T : Scheme.{u}} (f : T ⟶ X) (i : I) :
    Sigma.ι (fun i => pullback f (p i)) i ≫ (pullbackCoproductIso p f).hom =
      pullbackInclusion p f i := by
  unfold pullbackCoproductIso
  exact (coproductIsCoproduct (fun i => pullback f (p i))).comp_coconePointUniqueUpToIso_hom _ ⟨i⟩

end PhilipponFiniteSchemeCoproduct

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 900000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponEtaleBaseChangeComparison (baseChange)
open PhilipponEtaleBoundedFiniteModelReduction (boundedFiniteModel)
open PhilipponEtaleClosedPushforward (pushforward)
open PhilipponEtaleConstantDegreeZero (constantSheafIso continuousSheaf)
open PhilipponFiniteSchemeCoproduct


namespace PhilipponEtaleFiniteModelCoproduct

universe u

private abbrev Ab (X : Scheme.{u}) := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}

variable {I : Type u} [Finite I] {X : Scheme.{u}} {Y : I → Scheme.{u}}
  (p : ∀ i, Y i ⟶ X) (M : I → AddCommGrpCat.{u})

local instance (i : I) : TopologicalSpace (M i) := ⊥
local instance (i : I) : DiscreteTopology (M i) := ⟨rfl⟩
local instance : TopologicalSpace (∀ i, M i) := ⊥
local instance : DiscreteTopology (∀ i, M i) := ⟨rfl⟩

private abbrev atComponent (i : I) := (pushforward (p i)).obj (continuousSheaf (Y i) (M i))
private abbrev fiber {Y : Scheme.{u}} (p : Y ⟶ X) (W : X.Etale) : Scheme.{u} :=
  pullback W.hom p

private def baseHomeo (W : X.Etale) :
    (Σ i, fiber (p i) W) ≃ₜ fiber (Sigma.desc p) W :=
  (sigmaMk (fun i => fiber (p i) W)).trans (pullbackCoproductIso p W.hom).hom.homeomorph

private theorem baseHomeo_mk (W : X.Etale) (i : I) (z : fiber (p i) W) :
    baseHomeo p W ⟨i, z⟩ = pullbackInclusion p W.hom i z := by
  change (pullbackCoproductIso p W.hom).hom (sigmaMk _ ⟨i, z⟩) = _
  rw [sigmaMk_mk, ← Scheme.Hom.comp_apply, ι_pullbackCoproductIso]

private abbrev chartMap {T : Scheme.{u}} (r : T ⟶ X) {U V : X.Etale} (a : U ⟶ V) :
    fiber r U ⟶ fiber r V := ((baseChange r).map a).left

@[reassoc]
private theorem chartMap_fst {T : Scheme.{u}} (r : T ⟶ X) {U V : X.Etale} (a : U ⟶ V) :
    chartMap r a ≫ pullback.fst V.hom r = pullback.fst U.hom r ≫ a.left :=
  pullback.lift_fst _ _ _

@[reassoc]
private theorem chartMap_snd {T : Scheme.{u}} (r : T ⟶ X) {U V : X.Etale} (a : U ⟶ V) :
    chartMap r a ≫ pullback.snd V.hom r = pullback.snd U.hom r :=
  pullback.lift_snd _ _ _

omit [Finite I] in
private theorem chartMap_inclusion {U V : X.Etale} (a : U ⟶ V) (i : I) :
    pullbackInclusion p U.hom i ≫ chartMap (Sigma.desc p) a =
      chartMap (p i) a ≫ pullbackInclusion p V.hom i := by
  apply pullback.hom_ext
  · simp only [Category.assoc, chartMap_fst, pullbackInclusion_fst_assoc, pullbackInclusion_fst]
  · simp only [Category.assoc, chartMap_snd, pullbackInclusion_snd, chartMap_snd_assoc]

variable {F : Ab X} (m : ∀ i, F ⟶ atComponent p M i)

private abbrev componentSection (i : I) (W : X.Etale) (s : F.obj.obj (op W)) :
    C(fiber (p i) W, M i) := (m i).hom.app (op W) s

variable {B : AddCommGrpCat.{u}} [TopologicalSpace B] [DiscreteTopology B]
  (l : ∀ i, M i ⟶ B)

private def assembled (W : X.Etale) (s : F.obj.obj (op W)) :
    C(fiber (Sigma.desc p) W, B) := by
  let a (i : I) := componentSection p M m i W s
  let k (z : Σ i, fiber (p i) W) : B := l z.1 (a z.1 z.2)
  have hk : Continuous k := continuous_sigma fun i =>
    (continuous_of_discreteTopology (f := l i)).comp (a i).continuous
  exact ⟨k ∘ (baseHomeo p W).symm, hk.comp (baseHomeo p W).symm.continuous⟩

omit [DiscreteTopology B] in
private theorem assembled_component (W : X.Etale) (s : F.obj.obj (op W)) (i : I)
    (z : fiber (p i) W) :
    assembled p M m l W s (pullbackInclusion p W.hom i z) =
      l i (componentSection p M m i W s z) := by
  rw [← baseHomeo_mk]
  exact congrArg (fun t : Σ j, fiber (p j) W =>
    l t.1 (componentSection p M m t.1 W s t.2))
    ((baseHomeo p W).symm_apply_apply ⟨i, z⟩)

private def combined : F ⟶ (pushforward (Sigma.desc p)).obj (continuousSheaf (∐ Y) B) := by
  classical
  refine ⟨{
    app := fun W => AddCommGrpCat.ofHom {
      toFun := assembled p M m l W.unop
      map_zero' := ?_
      map_add' := fun s t => ?_ }
    naturality := ?_ }⟩
  · apply ContinuousMap.ext
    intro z
    obtain ⟨⟨i, w⟩, rfl⟩ := (baseHomeo p W.unop).surjective z
    simp only [baseHomeo_mk, assembled_component, componentSection, map_zero,
      ContinuousMap.zero_apply]
  · apply ContinuousMap.ext
    intro z
    obtain ⟨⟨i, w⟩, rfl⟩ := (baseHomeo p W.unop).surjective z
    rw [baseHomeo_mk, assembled_component]
    change l i (componentSection p M m i W.unop (s + t) w) =
      assembled p M m l W.unop s _ + assembled p M m l W.unop t _
    have hm : componentSection p M m i W.unop (s + t) =
        componentSection p M m i W.unop s + componentSection p M m i W.unop t :=
      ((m i).hom.app (op W.unop)).hom.map_add s t
    rw [assembled_component, assembled_component, hm, ContinuousMap.add_apply, map_add]
  · intro U V a
    apply ConcreteCategory.hom_ext
    intro s
    apply ContinuousMap.ext
    intro z
    obtain ⟨⟨i, w⟩, rfl⟩ := (baseHomeo p V.unop).surjective z
    rw [baseHomeo_mk]
    let b := chartMap (Sigma.desc p) a.unop
    let bᵢ := chartMap (p i) a.unop
    have h : b (pullbackInclusion p V.unop.hom i w) =
        pullbackInclusion p U.unop.hom i (bᵢ w) :=
      congrArg (fun d : fiber (p i) V.unop ⟶ fiber (Sigma.desc p) U.unop => d w)
        (chartMap_inclusion p a.unop i)
    change assembled p M m l V.unop (F.obj.map a s) (pullbackInclusion p V.unop.hom i w) =
      assembled p M m l U.unop s (b (pullbackInclusion p V.unop.hom i w))
    rw [h, assembled_component, assembled_component]
    have hm := ConcreteCategory.congr_hom ((m i).hom.naturality a) s
    exact congrArg (fun c : C(fiber (p i) V.unop, M i) => l i (c w)) hm

/-- Coefficient homomorphisms that jointly detect sections can be assembled into
a single map to the constant direct image on the coproduct. -/
private theorem mono_combined
    (h : ∀ (G : Ab X) (a b : G ⟶ F),
      (∀ i W s z, l i (componentSection p M m i W (a.hom.app (op W) s) z) =
        l i (componentSection p M m i W (b.hom.app (op W) s) z)) → a = b) :
    Mono (combined p M m l) := by
  refine ⟨fun {G} a b e => h G a b fun i W s z => ?_⟩
  have eW := ConcreteCategory.congr_hom (congrArg (fun g => g.hom.app (op W)) e) s
  have ev := congrArg (fun c : C(fiber (Sigma.desc p) W, B) =>
    c (pullbackInclusion p W.hom i z)) eW
  change assembled p M m l W (a.hom.app (op W) s) _ =
    assembled p M m l W (b.hom.app (op W) s) _ at ev
  simpa only [assembled_component] using ev

/-- A finite jointly monic family of finite constant direct images can
be replaced by a single finite constant direct image with the same bound. -/
theorem boundedFiniteModel_of_jointly_mono [IsAffine X] [∀ i, IsFinite (p i)]
    [∀ i, LocallyOfFinitePresentation (p i)] [∀ i, Finite (M i)]
    (N : ℕ) (hM : ∀ i, N • 𝟙 (M i) = 0)
    (v : ∀ i, F ⟶ (pushforward (p i)).obj
      ((constantSheaf (Y i).smallEtaleTopology AddCommGrpCat.{u}).obj (M i)))
    (hv : ∀ (G : Ab X) (a b : G ⟶ F), (∀ i, a ≫ v i = b ≫ v i) → a = b) :
    boundedFiniteModel X N F := by
  classical
  let e (i : I) := (pushforward (p i)).mapIso (constantSheafIso (Y i) (M i))
  let m (i : I) : F ⟶ atComponent p M i := v i ≫ (e i).hom
  let B := AddCommGrpCat.of (∀ i, M i)
  let l (i : I) : M i ⟶ B := AddCommGrpCat.ofHom (show M i →+ (∀ j, M j) from {
    toFun := fun x => (Pi.single i x : ∀ j, M j)
    map_zero' := Pi.single_zero i
    map_add' := fun x y => by
      change (Pi.single i (x + y) : ∀ j, M j) = Pi.single i x + Pi.single i y
      rw [Pi.single_add] })
  let k := combined p M m l
  let e' := (pushforward (Sigma.desc p)).mapIso (constantSheafIso (∐ Y) (∀ i, M i))
  have hB : N • 𝟙 B = 0 := by
    apply ConcreteCategory.hom_ext
    intro x
    funext i
    exact ConcreteCategory.congr_hom (hM i) (x i)
  let : Mono k := mono_combined p M m l fun G a b h => hv G a b fun i => (cancel_mono (e i).hom).mp (by
    rw [Category.assoc, Category.assoc]
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext W
    apply ConcreteCategory.hom_ext
    intro s
    apply ContinuousMap.ext
    intro z
    have hl (x : M i) : l i x i = x := by
      change (Pi.single i x : ∀ j, M j) i = x
      exact Pi.single_eq_same (M := fun j => M j) i x
    have hEval := congrArg (fun x : B => x i) (h i W.unop s z)
    change componentSection p M m i W.unop (a.hom.app W s) z =
      componentSection p M m i W.unop (b.hom.app W s) z
    simpa only [hl] using hEval)
  exact ⟨∐ Y, Sigma.desc p, isFinite_sigmaDesc p, locallyOfFinitePresentation_sigmaDesc p,
    B, inferInstance, hB, k ≫ e'.inv, inferInstance⟩

end PhilipponEtaleFiniteModelCoproduct

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open PhilipponEtaleBoundedFiniteModelReduction (boundedFiniteModel)
open PhilipponEtaleClosedPushforward (pushforward)
open PhilipponEtaleGeometricStalks

namespace PhilipponEtaleGenericModelDetection

universe u v

/-- A choice that works on a relative open neighborhood of the generic
point of each irreducible closed set can be made using finitely many indices. -/
theorem exists_finite_detection {X : Type u} [TopologicalSpace X] [NoetherianSpace X]
    [QuasiSober X] {I : Type v} (good : I → X → Prop)
    (h : ∀ x : X, ∃ i : I, ∃ U : Opens X, x ∈ U ∧
      ∀ y ∈ closure ({x} : Set X), y ∈ U → good i y) :
    ∃ s : Finset I, ∀ x : X, ∃ i ∈ s, good i x := by
  classical
  have hZ (Z : Closeds X) : ∃ s : Finset I, ∀ x ∈ Z, ∃ i ∈ s, good i x := by
    apply wellFounded_lt.induction Z
    clear Z
    intro Z ih
    rcases eq_or_ne Z ⊥ with rfl | hZ
    · exact ⟨∅, fun _ hx => (show False from hx).elim⟩
    by_cases hirr : IsPreirreducible (Z : Set X)
    · let he : IsIrreducible (Z : Set X) := ⟨Closeds.coe_nonempty.2 hZ, hirr⟩
      let x := he.genericPoint
      have hx : IsGenericPoint x (Z : Set X) := he.isGenericPoint_genericPoint Z.isClosed
      obtain ⟨i, U, hxU, hi⟩ := h x
      let B : Closeds X := ⟨(U : Set X)ᶜ, U.isOpen.isClosed_compl⟩
      have hsub : Z ⊓ B < Z := inf_lt_left.2 (fun hle => (hle hx.mem) hxU)
      obtain ⟨s, hs⟩ := ih (Z ⊓ B) hsub
      refine ⟨insert i s, fun y hy => ?_⟩
      by_cases hyU : y ∈ U
      · exact ⟨i, Finset.mem_insert_self _ _, hi y (hx.def.symm ▸ hy) hyU⟩
      · obtain ⟨j, hj, hgood⟩ := hs y ⟨hy, hyU⟩
        exact ⟨j, Finset.mem_insert_of_mem hj, hgood⟩
    · simp only [isPreirreducible_iff_isClosed_union_isClosed, not_forall, not_or] at hirr
      obtain ⟨Z₁, Z₂, h₁, h₂, hcover, hproper₁, hproper₂⟩ := hirr
      lift Z₁ to Closeds X using h₁
      lift Z₂ to Closeds X using h₂
      obtain ⟨s₁, hs₁⟩ := ih (Z ⊓ Z₁) (inf_lt_left.2 hproper₁)
      obtain ⟨s₂, hs₂⟩ := ih (Z ⊓ Z₂) (inf_lt_left.2 hproper₂)
      refine ⟨s₁ ∪ s₂, fun x hx => ?_⟩
      rcases hcover hx with hx₁ | hx₂
      · obtain ⟨i, hi, hix⟩ := hs₁ x ⟨hx, hx₁⟩
        exact ⟨i, Finset.mem_union_left _ hi, hix⟩
      · obtain ⟨i, hi, hix⟩ := hs₂ x ⟨hx, hx₂⟩
        exact ⟨i, Finset.mem_union_right _ hi, hix⟩
  obtain ⟨s, hs⟩ := hZ ⊤
  exact ⟨s, fun x => hs x (by trivial)⟩

private abbrev Ab (X : Scheme.{u}) := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}

/-- Data for a morphism into a bounded finite constant direct image. -/
structure FiniteConstantMap {X : Scheme.{u}} (F : Ab X) (N : ℕ) where
  Y : Scheme.{u}
  p : Y ⟶ X
  finite : IsFinite p
  presentation : LocallyOfFinitePresentation p
  M : AddCommGrpCat.{u}
  finiteGroup : Finite M
  killed : N • 𝟙 M = 0
  map : F ⟶ (pushforward p).obj ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj M)

/-- Whether the map into the finite constant direct image is injective
at the chosen algebraically closed geometric point over a scheme point. -/
def injectiveAt {X : Scheme.{u}} {F : Ab X} {N : ℕ} (b : FiniteConstantMap F N) (x : X) : Prop :=
  Function.Injective ((Scheme.pointSmallEtale (algebraicallyClosedGeometricMap x)).sheafFiber.map b.map)

/-- On a Noetherian affine scheme, finite constant maps that are injective
on relative generic neighborhoods give a single bounded finite model. -/
theorem boundedFiniteModel_of_generic_injectivity {X : Scheme.{u}} [IsAffine X] [NoetherianSpace X]
    (N : ℕ) (F : Ab X) (h : ∀ x : X, ∃ b : FiniteConstantMap F N, ∃ U : X.Opens,
      x ∈ U ∧ ∀ y ∈ closure ({x} : Set X), y ∈ U → injectiveAt b y) :
    boundedFiniteModel X N F := by
  classical
  obtain ⟨s, hs⟩ := exists_finite_detection (fun b : FiniteConstantMap F N => injectiveAt b) h
  let e := Fintype.equivFin s
  let I := ULift.{u} (Fin (Fintype.card s))
  let b (i : I) : FiniteConstantMap F N := (e.symm i.down).val
  let P := ObjectProperty.ofObj (fun x : X => Scheme.pointSmallEtale (algebraicallyClosedGeometricMap x))
  have hP : P.IsConservativeFamilyOfPoints := algebraicallyClosedGeometricPoints_conservative X
  let G (i : I) : Ab X :=
    (pushforward (b i).p).obj ((constantSheaf (b i).Y.smallEtaleTopology AddCommGrpCat.{u}).obj (b i).M)
  let v (i : I) : F ⟶ G i := (b i).map
  let m := Pi.lift v
  have hm : Mono m := by
    let : ∀ Φ : P.FullSubcategory, Mono (Φ.obj.sheafFiber.map m) := by
      intro Φ
      obtain ⟨x, hx⟩ := (ObjectProperty.ofObj_iff _ _).mp Φ.property
      rw [← hx]
      obtain ⟨c, hc, hg⟩ := hs x
      let i : I := ⟨e ⟨c, hc⟩⟩
      let T := (Scheme.pointSmallEtale (algebraicallyClosedGeometricMap x)).sheafFiber (A := AddCommGrpCat.{u})
      have hi : b i = c := congrArg Subtype.val (e.symm_apply_apply ⟨c, hc⟩)
      have hi' : injectiveAt (b i) x := by rw [hi]; exact hg
      have hMono : Mono (T.map (v i)) := (AddCommGrpCat.mono_iff_injective _).2 hi'
      have hEq : T.map m ≫ T.map (Pi.π G i) = T.map (v i) := by
        rw [← T.map_comp, Pi.lift_π]
      exact mono_of_mono_fac hEq
    exact (hP.jointlyReflectMonomorphisms AddCommGrpCat.{u}).mono m
  let : ∀ i, IsFinite (b i).p := fun i => (b i).finite
  let : ∀ i, LocallyOfFinitePresentation (b i).p := fun i => (b i).presentation
  let : ∀ i, Finite (b i).M := fun i => (b i).finiteGroup
  refine PhilipponEtaleFiniteModelCoproduct.boundedFiniteModel_of_jointly_mono
    (fun i => (b i).p) (fun i => (b i).M) N (fun i => (b i).killed) v ?_
  intro H a a' heq
  apply (cancel_mono m).mp
  apply Pi.hom_ext
  intro i
  change a ≫ (Pi.lift v) ≫ Pi.π G i = a' ≫ (Pi.lift v) ≫ Pi.π G i
  simpa only [Category.assoc, Pi.lift_π] using heq i

end PhilipponEtaleGenericModelDetection

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 160000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PhilipponEtaleCohomologyAlong (pullbackComposition)
open PhilipponEtaleFiniteConstantColimits (finiteConstant)
open PhilipponEtaleFinitePointLifts (exists_lift_of_integral_surjective)
open PhilipponEtaleFinitePresentationTrivialization (exists_trivialization_on_normalization)
open PhilipponEtaleBoundedFiniteModelReduction (boundedFiniteModel)
open PhilipponEtaleFinitePresentations (finiteEtalePresentations ind_boundedFiniteModel_of_finitePresentations)
open PhilipponEtaleGenericChartExtension (exists_map_of_const_on_generic_chart)
open PhilipponEtaleGenericConstantImage (genericInclusion)
open PhilipponEtaleGenericModelDetection (FiniteConstantMap injectiveAt boundedFiniteModel_of_generic_injectivity)
open PhilipponEtaleGeometricStalks (algebraicallyClosedGeometricMap algebraicallyClosedGeometricMap_apply)
open PhilipponEtaleIntegralModelFactorization (exists_finite_factor)
open PhilipponEtaleSmallSite (pullbackSheaves)
open PhilipponEtaleStalkPullback (exists_point_lift_of_mem_range)


namespace PhilipponEtaleFinitePresentationModel

universe u

private abbrev Ab (X : Scheme.{u}) := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}

private abbrev specMap (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] :
    Spec (.of S) ⟶ Spec (.of R) := Spec.map (CommRingCat.ofHom (algebraMap R S))

/-- The generic point of the spectrum of a domain. -/
def genericPoint (R : Type u) [CommRing R] [IsDomain R] : Spec (.of R) :=
  ⟨⊥, Ideal.isPrime_bot⟩

private theorem finite_isLocallyOfFinitePresentation (R : Type u) [CommRing R] [IsNoetherianRing R]
    {Y : Scheme.{u}} (q : Y ⟶ Spec (.of R)) [IsFinite q] : LocallyOfFinitePresentation q := by
  let : IsAffine Y := isAffine_of_isAffineHom q
  let : IsNoetherianRing (CommRingCat.of R) := inferInstanceAs (IsNoetherianRing R)
  let e := Y.isoSpec
  let g := Spec.preimage (e.inv ≫ q)
  have hg : Spec.map g = e.inv ≫ q := Spec.map_preimage _
  have hgFin : IsFinite (Spec.map g) := hg.symm ▸ inferInstanceAs (IsFinite (e.inv ≫ q))
  let : LocallyOfFinitePresentation (Spec.map g) := (LocallyOfFinitePresentation.SpecMap_iff _).mpr
    (RingHom.FinitePresentation.of_finiteType.mp ((IsFinite.SpecMap_iff _).mp hgFin).finiteType)
  have hq : e.hom ≫ Spec.map g = q := by rw [hg, e.hom_inv_id_assoc]
  exact hq ▸ inferInstanceAs (LocallyOfFinitePresentation (e.hom ≫ Spec.map g))

/-- A finite constant model detects the stalks on a relative neighborhood
of the generic point of an integral closed subscheme. -/
theorem exists_model_on_relative_open
    {X : Scheme.{u}} [IsAffine X] (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (i : Spec (.of R) ⟶ X) [IsClosedImmersion i] [LocallyOfFinitePresentation i]
    (N : ℕ) (hN : N ≠ 0) (F : Ab X) (hF : finiteEtalePresentations X N F) :
    ∃ (D : FiniteConstantMap F N) (U : X.Opens),
      i (genericPoint R) ∈ U ∧ ∀ y ∈ Set.range i, y ∈ U → injectiveAt D y := by
  classical
  obtain ⟨L, _, _, _, _, _, _, b, hb, hC⟩ := exists_trivialization_on_normalization R i N hN F hF
  let K := FractionRing R
  let B := integralClosure R L
  let A := Localization.Away b
  let p₀ := specMap R B
  let p := p₀ ≫ i
  let v := specMap B A
  let : IsIntegrallyClosed B := integralClosure.isIntegrallyClosedOfFiniteExtension K
  let : IsFractionRing B L := integralClosure.isFractionRing_of_finite_extension K L
  let : IsIntegralHom p₀ := IsIntegralHom.SpecMap_iff.mpr
    (algebraMap_isIntegral_iff.mpr (inferInstance : Algebra.IsIntegral R B))
  let : IsIntegralHom p := inferInstanceAs (IsIntegralHom (p₀ ≫ i))
  have hRL : Function.Injective (algebraMap R L) := by
    rw [IsScalarTower.algebraMap_eq R K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective R K)
  have hRB : Function.Injective (algebraMap R B) := by
    intro a a' ha
    apply hRL
    simp only [IsScalarTower.algebraMap_apply R B L, ha]
  let : FaithfulSMul R B := (faithfulSMul_iff_algebraMap_injective R B).mpr hRB
  let : Surjective p₀ := ⟨Algebra.IsIntegral.comap_surjective R B⟩
  let : IsOpenImmersion v := Scheme.isOpenImmersion_SpecMap_localizationAway (R := .of B) b
  let : IsDomain A := Localization.Away.isDomain hb
  let hA : IrreducibleSpace (PrimeSpectrum A) := PrimeSpectrum.irreducibleSpace
  let : PreconnectedSpace (Spec (.of A)) :=
    @PreirreducibleSpace.preconnectedSpace (PrimeSpectrum A) _ hA.toPreirreducibleSpace
  let : Nonempty (Spec (.of A)) := hA.toNonempty
  let φ : A →ₐ[B] L := IsLocalization.Away.liftAlgHom b (f := Algebra.ofId B L)
    (isUnit_iff_ne_zero.mpr (by
      change algebraMap B L b ≠ 0
      simpa only [map_zero] using (IsFractionRing.injective B L).ne hb))
  let r : Spec (.of L) ⟶ Spec (.of A) := Spec.map (CommRingCat.ofHom φ.toRingHom)
  have hr : r ≫ v = genericInclusion B L := by
    change Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap B A)) = Spec.map (CommRingCat.ofHom (algebraMap B L))
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    exact congrArg (fun f : B →+* L => Spec.map (CommRingCat.ofHom f)) φ.comp_algebraMap
  have hv : v ≫ p = specMap R A ≫ i := by
    change v ≫ p₀ ≫ i = _
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [← IsScalarTower.algebraMap_eq R B A]
  have hE : finiteConstant (Spec (.of A)) N ((pullbackSheaves v).obj ((pullbackSheaves p).obj F)) :=
    (finiteConstant (Spec (.of A)) N).prop_of_iso ((pullbackComposition p v _ hv).app F).symm hC
  obtain ⟨M, hM, m, hm⟩ := exists_map_of_const_on_generic_chart B L p v r hr F N hE
  let : Finite M := hM.1
  obtain ⟨Z, q, hq, m₀, a, ha⟩ := exists_finite_factor hN hF i p₀ M m
  let : IsFinite q := hq
  let : LocallyOfFinitePresentation q := finite_isLocallyOfFinitePresentation R q
  let D : FiniteConstantMap F N := ⟨Z, q ≫ i, inferInstance, inferInstance, M, hM.1, hM.2, m₀⟩
  let U : X.Opens := ⟨(p '' (Set.range v)ᶜ)ᶜ,
    (p.isClosedMap _ v.opensRange.isOpen.isClosed_compl).isOpen_compl⟩
  refine ⟨D, U, ?_, ?_⟩
  · change i (genericPoint R) ∉ p '' (Set.range v)ᶜ
    rintro ⟨z, hz, hzp⟩
    have hzy : p₀ z = genericPoint R :=
      i.isClosedEmbedding.injective (show i (p₀ z) = i (genericPoint R) from hzp)
    have hzbot : z.asIdeal = ⊥ :=
      Ideal.eq_bot_of_comap_eq_bot (R := R) (congrArg PrimeSpectrum.asIdeal hzy)
    apply hz
    change z ∈ v.opensRange
    have hv' : v.opensRange = PrimeSpectrum.basicOpen b :=
      Scheme.Hom.opensRange_localizationAway (R := .of B) b
    rw [hv']
    change b ∉ z.asIdeal
    rw [hzbot]
    exact hb
  · rintro y ⟨z, rfl⟩ hy
    obtain ⟨s, hs⟩ := exists_point_lift_of_mem_range i (algebraicallyClosedGeometricMap (i z))
      (by rw [algebraicallyClosedGeometricMap_apply]; exact ⟨z, rfl⟩)
    obtain ⟨t, ht⟩ := exists_lift_of_integral_surjective p₀ s
    have ht' : t ≫ p = algebraicallyClosedGeometricMap (i z) := by
      change t ≫ p₀ ≫ i = _
      rw [← Category.assoc, ht, hs]
    have hRange : Set.range t ⊆ Set.range v := by
      rintro _ ⟨a, rfl⟩
      by_contra ha
      change i z ∉ p '' (Set.range v)ᶜ at hy
      apply hy
      refine ⟨t a, ha, ?_⟩
      rw [← Scheme.Hom.comp_apply, ht', Subsingleton.elim a default,
        algebraicallyClosedGeometricMap_apply]
    let l := IsOpenImmersion.lift v t hRange
    have hl : (l ≫ v) ≫ p = algebraicallyClosedGeometricMap (i z) := by
      rw [IsOpenImmersion.lift_fac, ht']
    have hm' := hm _ l
    rw [hl] at hm'
    let H := (Scheme.pointSmallEtale (algebraicallyClosedGeometricMap (i z))).sheafFiber
      (A := AddCommGrpCat.{u})
    change Mono (H.map m) at hm'
    rw [← ha, H.map_comp] at hm'
    let : Mono (H.map m₀ ≫ H.map a) := hm'
    exact (AddCommGrpCat.mono_iff_injective _).mp (mono_of_mono (H.map m₀) (H.map a))

/-- Over a Noetherian affine, the stalk tests give an embedding for each
finite étale presentation. -/
theorem boundedFiniteModel_of_noetherian (A : Type u) [CommRing A] [IsNoetherianRing A]
    (N : ℕ) (hN : N ≠ 0) :
    finiteEtalePresentations (Spec (.of A)) N ≤ boundedFiniteModel (Spec (.of A)) N := by
  intro F hF
  let X := Spec (.of A)
  let : IsNoetherianRing (CommRingCat.of A) := inferInstanceAs (IsNoetherianRing A)
  apply boundedFiniteModel_of_generic_injectivity N F
  intro x
  let x₀ : PrimeSpectrum A := x
  let R := A ⧸ x₀.asIdeal
  let f := Ideal.Quotient.mk x₀.asIdeal
  let i := Spec.map (CommRingCat.ofHom f)
  let : IsClosedImmersion i := IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  let : LocallyOfFinitePresentation i :=
    (LocallyOfFinitePresentation.SpecMap_iff _).mpr (RingHom.FinitePresentation.of_finiteType.mp
      (RingHom.FiniteType.of_surjective f Ideal.Quotient.mk_surjective))
  obtain ⟨D, U, hU, hloc⟩ := exists_model_on_relative_open R i N hN F hF
  have hx : i (genericPoint R) = x := by
    apply PrimeSpectrum.ext
    change (⊥ : Ideal R).comap f = x₀.asIdeal
    rw [← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
  have hi : Set.range i = closure ({x} : Set X) := by
    change Set.range (PrimeSpectrum.comap f) = closure ({x₀} : Set (PrimeSpectrum A))
    rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective,
      Ideal.mk_ker, PrimeSpectrum.closure_singleton]
  exact ⟨D, U, hx ▸ hU, fun y hy h => hloc y (hi.symm ▸ hy) h⟩

end PhilipponEtaleFinitePresentationModel

end

end


