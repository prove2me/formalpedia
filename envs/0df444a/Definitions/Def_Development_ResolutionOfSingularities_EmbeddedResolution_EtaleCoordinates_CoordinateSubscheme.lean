-- Prove2me | Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateSubscheme
-- name    : Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_CoordinateSubscheme
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T14:27:27.284806+00:00
-- url     : https://prove2.me/theorems/6a81ebba-422c-45cd-b7da-8233b9e5d8f7
-- title:
--   Coordinate Subscheme
-- statement:
--   Definitions and structural lemmas for Coordinate Subscheme, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/CoordinateSubscheme.lean

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_ChartRing
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleChartExistence
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealSheaf
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Theorems.Thm_Derivation_liftToLocalization_algebraMap
import Theorems.Thm_Derivation_mapToLocalization_algebraMap
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_coordRingHom_X
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_coordRingHom_etale
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_ideal_eq_span_coord
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleChart_ofCoords_map
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_EtaleCoordinates_basisDerivation_apply
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_appLE_top_comp_topIso_inv
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheafIterate_ideal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheafIterate_zero
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealSheaf_ideal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Derivation.liftToLocalization_algebraMap
attribute [local simp] Derivation.mapToLocalization_algebraMap
attribute [local simp] FunctorialResolution.EmbeddedResolution.EtaleChart.coordRingHom_X
attribute [local simp] FunctorialResolution.EmbeddedResolution.EtaleChart.ofCoords_map
attribute [local simp] FunctorialResolution.EmbeddedResolution.EtaleCoordinates.basisDerivation_apply
attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheafIterate_ideal
attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheafIterate_zero
attribute [local simp] FunctorialResolution.EmbeddedResolution.derivIdealSheaf_ideal


set_option autoImplicit false
universe u
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
noncomputable section
namespace FunctorialResolution.EmbeddedResolution
theorem isAffineOpen_preimage_subschemeι {X : Scheme.{u}} (Z : X.IdealSheafData) {U : X.Opens}
    (hU : IsAffineOpen U) : IsAffineOpen (Z.subschemeι ⁻¹ᵁ U) :=
  hU.preimage Z.subschemeι
theorem card_compl_eq_sub (m : ℕ) (S : Finset (Fin m)) : Sᶜ.card = m - S.card := by
  rw [Finset.card_compl, Fintype.card_fin]
def complOrderEmb (m : ℕ) (S : Finset (Fin m)) : Fin (m - S.card) ↪o Fin m :=
  Sᶜ.orderEmbOfFin (card_compl_eq_sub m S)
theorem complOrderEmb_notMem (m : ℕ) (S : Finset (Fin m)) (i : Fin (m - S.card)) :
    complOrderEmb m S i ∉ S :=
  Finset.mem_compl.mp (Finset.orderEmbOfFin_mem Sᶜ (card_compl_eq_sub m S) i)
theorem exists_complOrderEmb_eq (m : ℕ) (S : Finset (Fin m)) {j : Fin m} (hj : j ∉ S) :
    ∃ i : Fin (m - S.card), complOrderEmb m S i = j := by
  have hmem : j ∈ (↑(Sᶜ) : Set (Fin m)) := Finset.mem_coe.mpr (Finset.mem_compl.mpr hj)
  rw [← Finset.range_orderEmbOfFin Sᶜ (card_compl_eq_sub m S)] at hmem
  obtain ⟨i, hi⟩ := hmem
  exact ⟨i, hi⟩
def mvPolynomialCoordIdeal (k : Type u) [Field k] (m : ℕ) (S : Finset (Fin m)) :
    Ideal (MvPolynomial (ULift.{u} (Fin m)) k) :=
  Ideal.span ((fun j : Fin m => MvPolynomial.X (ULift.up.{u} j)) '' (S : Set (Fin m)))
theorem mvPolynomialCoordIdeal_eq_span (k : Type u) [Field k] (m : ℕ) (S : Finset (Fin m)) :
    mvPolynomialCoordIdeal k m S =
      Ideal.span ((fun j : Fin m => MvPolynomial.X (ULift.up.{u} j)) '' (S : Set (Fin m))) :=
  rfl
theorem X_mem_mvPolynomialCoordIdeal (k : Type u) [Field k] (m : ℕ) (S : Finset (Fin m)) {j : Fin m}
    (hj : j ∈ S) :
    MvPolynomial.X (ULift.up.{u} j) ∈ mvPolynomialCoordIdeal k m S :=
  Ideal.subset_span ⟨j, Finset.mem_coe.mpr hj, rfl⟩
def renameCompl (k : Type u) [Field k] (m : ℕ) (S : Finset (Fin m)) :
    MvPolynomial (ULift.{u} (Fin (m - S.card))) k →ₐ[k] MvPolynomial (ULift.{u} (Fin m)) k :=
  MvPolynomial.aeval fun i : ULift.{u} (Fin (m - S.card)) =>
    MvPolynomial.X (ULift.up.{u} (complOrderEmb m S i.down))
@[simp] theorem renameCompl_X (k : Type u) [Field k] (m : ℕ) (S : Finset (Fin m))
    (i : Fin (m - S.card)) :
    renameCompl k m S (MvPolynomial.X (ULift.up.{u} i)) =
      MvPolynomial.X (ULift.up.{u} (complOrderEmb m S i)) :=
  MvPolynomial.aeval_X _ _
theorem renameCompl_C (k : Type u) [Field k] (m : ℕ) (S : Finset (Fin m)) (a : k) :
    renameCompl k m S (MvPolynomial.C a) = MvPolynomial.C a := by
  show MvPolynomial.aeval
      (fun i : ULift.{u} (Fin (m - S.card)) => MvPolynomial.X (ULift.up.{u} (complOrderEmb m S i.down)))
      (MvPolynomial.C a) = MvPolynomial.C a
  simp
def substZeroOnFinset (k : Type u) [Field k] (m : ℕ) (S : Finset (Fin m))
    (j : ULift.{u} (Fin m)) : MvPolynomial (ULift.{u} (Fin (m - S.card))) k :=
  if h : j.down ∈ S then 0
  else MvPolynomial.X (ULift.up.{u} (Classical.choose (exists_complOrderEmb_eq m S h)))
def setCoordsZero (k : Type u) [Field k] (m : ℕ) (S : Finset (Fin m)) :
    MvPolynomial (ULift.{u} (Fin m)) k →ₐ[k] MvPolynomial (ULift.{u} (Fin (m - S.card))) k :=
  MvPolynomial.aeval (substZeroOnFinset k m S)
theorem setCoordsZero_X_of_mem (k : Type u) [Field k] (m : ℕ) (S : Finset (Fin m)) {j : Fin m}
    (hj : j ∈ S) : setCoordsZero k m S (MvPolynomial.X (ULift.up.{u} j)) = 0 := by
  have h1 : setCoordsZero k m S (MvPolynomial.X (ULift.up.{u} j)) = substZeroOnFinset k m S (ULift.up.{u} j) :=
    MvPolynomial.aeval_X _ _
  rw [h1]
  exact dif_pos hj
theorem setCoordsZero_X_complOrderEmb (k : Type u) [Field k] (m : ℕ) (S : Finset (Fin m))
    (i : Fin (m - S.card)) :
    setCoordsZero k m S (MvPolynomial.X (ULift.up.{u} (complOrderEmb m S i))) =
      MvPolynomial.X (ULift.up.{u} i) := by
  have hnot : complOrderEmb m S i ∉ S := complOrderEmb_notMem m S i
  have h1 : setCoordsZero k m S (MvPolynomial.X (ULift.up.{u} (complOrderEmb m S i)))
      = substZeroOnFinset k m S (ULift.up.{u} (complOrderEmb m S i)) := MvPolynomial.aeval_X _ _
  have h2 : substZeroOnFinset k m S (ULift.up.{u} (complOrderEmb m S i))
      = MvPolynomial.X (ULift.up.{u} (Classical.choose (exists_complOrderEmb_eq m S hnot))) :=
    dif_neg hnot
  have h3 : Classical.choose (exists_complOrderEmb_eq m S hnot) = i :=
    (complOrderEmb m S).injective (Classical.choose_spec (exists_complOrderEmb_eq m S hnot))
  rw [h1, h2, h3]
theorem setCoordsZero_eq_zero_of_mem (k : Type u) [Field k] (m : ℕ) (S : Finset (Fin m))
    {q : MvPolynomial (ULift.{u} (Fin m)) k} (hq : q ∈ mvPolynomialCoordIdeal k m S) :
    setCoordsZero k m S q = 0 := by
  have hker : mvPolynomialCoordIdeal k m S ≤ RingHom.ker ((setCoordsZero k m S).toRingHom) := by
    rw [mvPolynomialCoordIdeal_eq_span, Ideal.span_le]
    rintro x ⟨j, hj, rfl⟩
    have hx : (setCoordsZero k m S).toRingHom (MvPolynomial.X (ULift.up.{u} j)) = 0 :=
      setCoordsZero_X_of_mem k m S (Finset.mem_coe.mp hj)
    exact RingHom.mem_ker.mpr hx
  have h : q ∈ RingHom.ker ((setCoordsZero k m S).toRingHom) := hker hq
  have h2 : (setCoordsZero k m S).toRingHom q = 0 := RingHom.mem_ker.mp h
  exact h2
open scoped TensorProduct in
theorem etale_quotientMap {P A : Type u} [CommRing P] [CommRing A] {f : P →+* A}
    (hf : f.Etale) (I : Ideal P) :
    (Ideal.quotientMap (Ideal.map f I) f Ideal.le_comap_map).Etale := by
  let instPA : Algebra P A := f.toAlgebra
  have hfA : Algebra.Etale P A := hf
  let instQuot : Algebra (P ⧸ I) (A ⧸ Ideal.map f I) :=
    (Ideal.quotientMap (Ideal.map f I) f Ideal.le_comap_map).toAlgebra
  have hqm : ∀ x : P, algebraMap (P ⧸ I) (A ⧸ Ideal.map f I) (Ideal.Quotient.mk I x)
      = Ideal.Quotient.mk (Ideal.map f I) (f x) := by
    intro x
    show Ideal.quotientMap (Ideal.map f I) f Ideal.le_comap_map (Ideal.Quotient.mk I x) = _
    rw [Ideal.quotientMap_mk]
  have hst : IsScalarTower P (P ⧸ I) (A ⧸ Ideal.map f I) := by
    refine IsScalarTower.of_algebraMap_eq fun x => ?_
    show Ideal.Quotient.mk (Ideal.map f I) (f x)
      = algebraMap (P ⧸ I) (A ⧸ Ideal.map f I) (algebraMap P (P ⧸ I) x)
    rw [Ideal.Quotient.algebraMap_eq, hqm x]
  have hcomm : ∀ x : P, (1 : P ⧸ I) ⊗ₜ[P] (f x) = (Ideal.Quotient.mk I x) ⊗ₜ[P] (1 : A) := by
    intro x
    have h1 : (Algebra.TensorProduct.includeRight : A →ₐ[P] ((P ⧸ I) ⊗[P] A)) (f x)
        = algebraMap P ((P ⧸ I) ⊗[P] A) x :=
      AlgHom.commutes (Algebra.TensorProduct.includeRight : A →ₐ[P] ((P ⧸ I) ⊗[P] A)) x
    have h2 : (Algebra.TensorProduct.includeLeft : (P ⧸ I) →ₐ[P] ((P ⧸ I) ⊗[P] A))
        (Ideal.Quotient.mk I x) = algebraMap P ((P ⧸ I) ⊗[P] A) x :=
      AlgHom.commutes (Algebra.TensorProduct.includeLeft : (P ⧸ I) →ₐ[P] ((P ⧸ I) ⊗[P] A)) x
    have h3 : (Algebra.TensorProduct.includeRight : A →ₐ[P] ((P ⧸ I) ⊗[P] A)) (f x)
        = (1 : P ⧸ I) ⊗ₜ[P] (f x) := rfl
    have h4 : (Algebra.TensorProduct.includeLeft : (P ⧸ I) →ₐ[P] ((P ⧸ I) ⊗[P] A))
        (Ideal.Quotient.mk I x) = (Ideal.Quotient.mk I x) ⊗ₜ[P] (1 : A) := rfl
    rw [← h3, ← h4, h1, h2]
  have hb : ∀ (x : P) (a : A),
      (1 : P ⧸ I) ⊗ₜ[P] (f x * a) = (Ideal.Quotient.mk I x) ⊗ₜ[P] a := by
    intro x a
    have e1 : ((1 : P ⧸ I) ⊗ₜ[P] (f x)) * ((1 : P ⧸ I) ⊗ₜ[P] a)
        = (1 : P ⧸ I) ⊗ₜ[P] (f x * a) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    have e2 : ((Ideal.Quotient.mk I x) ⊗ₜ[P] (1 : A)) * ((1 : P ⧸ I) ⊗ₜ[P] a)
        = (Ideal.Quotient.mk I x) ⊗ₜ[P] a := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [← e1, ← e2, hcomm]
  obtain ⟨φ, hφ⟩ : ∃ φ : ((P ⧸ I) ⊗[P] A) →ₐ[P ⧸ I] (A ⧸ Ideal.map f I),
      ∀ (q : P ⧸ I) (a : A), φ (q ⊗ₜ[P] a)
        = algebraMap (P ⧸ I) (A ⧸ Ideal.map f I) q * Ideal.Quotient.mk (Ideal.map f I) a :=
    ⟨Algebra.TensorProduct.lift (Algebra.ofId (P ⧸ I) (A ⧸ Ideal.map f I))
        (Ideal.Quotient.mkₐ P (Ideal.map f I)) (fun _ _ => Commute.all _ _),
      fun q a => by
        simp [Algebra.TensorProduct.lift_tmul, Algebra.ofId_apply, Ideal.Quotient.mkₐ_eq_mk]⟩
  obtain ⟨ψ, hψ⟩ : ∃ ψ : (A ⧸ Ideal.map f I) →+* ((P ⧸ I) ⊗[P] A),
      ∀ a : A, ψ (Ideal.Quotient.mk (Ideal.map f I) a) = (1 : P ⧸ I) ⊗ₜ[P] a := by
    have hzero : ∀ a ∈ Ideal.map f I,
        (Algebra.TensorProduct.includeRight : A →ₐ[P] ((P ⧸ I) ⊗[P] A)).toRingHom a = 0 := by
      have hle : Ideal.map f I ≤ RingHom.ker
          (Algebra.TensorProduct.includeRight : A →ₐ[P] ((P ⧸ I) ⊗[P] A)).toRingHom := by
        rw [Ideal.map_le_iff_le_comap]
        intro x hx
        rw [Ideal.mem_comap, RingHom.mem_ker]
        show (1 : P ⧸ I) ⊗ₜ[P] (f x) = 0
        rw [hcomm, Ideal.Quotient.eq_zero_iff_mem.mpr hx, TensorProduct.zero_tmul]
      intro a ha
      exact RingHom.mem_ker.mp (hle ha)
    exact ⟨Ideal.Quotient.lift (Ideal.map f I)
      (Algebra.TensorProduct.includeRight : A →ₐ[P] ((P ⧸ I) ⊗[P] A)).toRingHom hzero,
      fun _ => rfl⟩
  have hleft : ∀ t : ((P ⧸ I) ⊗[P] A), ψ (φ t) = t := by
    intro t
    refine TensorProduct.induction_on t ?_ ?_ ?_
    · simp
    · intro q a
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
      rw [hφ, hqm, ← map_mul (Ideal.Quotient.mk (Ideal.map f I)), hψ]
      exact hb x a
    · intro u v hu hv
      rw [map_add, map_add, hu, hv]
  have hsurj : Function.Surjective φ := by
    intro b
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
    exact ⟨(1 : P ⧸ I) ⊗ₜ[P] a, by rw [hφ, map_one, one_mul]⟩
  have e : ((P ⧸ I) ⊗[P] A) ≃ₐ[P ⧸ I] (A ⧸ Ideal.map f I) :=
    AlgEquiv.ofBijective φ ⟨Function.LeftInverse.injective hleft, hsurj⟩
  have hbc : Algebra.Etale (P ⧸ I) ((P ⧸ I) ⊗[P] A) := inferInstance
  have hfe : Algebra.FormallyEtale (P ⧸ I) ((P ⧸ I) ⊗[P] A) := hbc.formallyEtale
  have hfp : Algebra.FinitePresentation (P ⧸ I) ((P ⧸ I) ⊗[P] A) := hbc.finitePresentation
  show Algebra.Etale (P ⧸ I) (A ⧸ Ideal.map f I)
  exact ⟨Algebra.FormallyEtale.of_equiv e, hfp.equiv e⟩
theorem setCoordsZero_renameCompl (k : Type u) [Field k] (m : ℕ) (S : Finset (Fin m))
    (q : MvPolynomial (ULift.{u} (Fin (m - S.card))) k) :
    setCoordsZero k m S (renameCompl k m S q) = q := by
  have h : (setCoordsZero k m S).comp (renameCompl k m S) = AlgHom.id k _ := by
    refine MvPolynomial.algHom_ext fun i => ?_
    obtain ⟨i⟩ := i
    rw [AlgHom.comp_apply, renameCompl_X, setCoordsZero_X_complOrderEmb, AlgHom.id_apply]
  exact DFunLike.congr_fun h q
theorem quotientMk_renameCompl_setCoordsZero (k : Type u) [Field k] (m : ℕ) (S : Finset (Fin m))
    (p : MvPolynomial (ULift.{u} (Fin m)) k) :
    Ideal.Quotient.mk (mvPolynomialCoordIdeal k m S) (renameCompl k m S (setCoordsZero k m S p))
      = Ideal.Quotient.mk (mvPolynomialCoordIdeal k m S) p := by
  have h : (Ideal.Quotient.mkₐ k (mvPolynomialCoordIdeal k m S)).comp
        ((renameCompl k m S).comp (setCoordsZero k m S))
      = Ideal.Quotient.mkₐ k (mvPolynomialCoordIdeal k m S) := by
    refine MvPolynomial.algHom_ext fun j => ?_
    obtain ⟨j⟩ := j
    by_cases hj : j ∈ S
    · rw [AlgHom.comp_apply, AlgHom.comp_apply, setCoordsZero_X_of_mem k m S hj, map_zero, map_zero]
      symm
      rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
      exact X_mem_mvPolynomialCoordIdeal k m S hj
    · obtain ⟨i, rfl⟩ := exists_complOrderEmb_eq m S hj
      rw [AlgHom.comp_apply, AlgHom.comp_apply, setCoordsZero_X_complOrderEmb, renameCompl_X]
  exact DFunLike.congr_fun h p
theorem bijective_quotientMk_comp_renameCompl (k : Type u) [Field k] (m : ℕ)
    (S : Finset (Fin m)) :
    Function.Bijective
      ((Ideal.Quotient.mk (mvPolynomialCoordIdeal k m S)).comp (renameCompl k m S).toRingHom) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro q hq
    have hq' : renameCompl k m S q ∈ mvPolynomialCoordIdeal k m S :=
      (Ideal.Quotient.eq_zero_iff_mem).1 hq
    have h0 := setCoordsZero_eq_zero_of_mem k m S hq'
    rwa [setCoordsZero_renameCompl] at h0
  · intro x
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    refine ⟨setCoordsZero k m S p, ?_⟩
    show Ideal.Quotient.mk (mvPolynomialCoordIdeal k m S) (renameCompl k m S (setCoordsZero k m S p))
        = Ideal.Quotient.mk (mvPolynomialCoordIdeal k m S) p
    exact quotientMk_renameCompl_setCoordsZero k m S p
theorem etale_quotientMk_comp_renameCompl (k : Type u) [Field k] (m : ℕ) (S : Finset (Fin m))
    {A : Type u} [CommRing A] (f : MvPolynomial (ULift.{u} (Fin m)) k →+* A)
    (hf : f.Etale) (J : Ideal A) (hJ : J = Ideal.map f (mvPolynomialCoordIdeal k m S)) :
    (((Ideal.Quotient.mk J).comp f).comp (renameCompl k m S).toRingHom).Etale := by
  subst hJ
  have hcomp : ((Ideal.Quotient.mk (Ideal.map f (mvPolynomialCoordIdeal k m S))).comp f).comp
        (renameCompl k m S).toRingHom
      = (Ideal.quotientMap (Ideal.map f (mvPolynomialCoordIdeal k m S)) f Ideal.le_comap_map).comp
        ((Ideal.Quotient.mk (mvPolynomialCoordIdeal k m S)).comp (renameCompl k m S).toRingHom) :=
    RingHom.ext fun q => by
      simp only [RingHom.comp_apply, Ideal.quotientMap_mk]
  rw [hcomp]
  apply RingHom.Etale.stableUnderComposition
  · apply RingHom.Etale.of_bijective
    exact bijective_quotientMk_comp_renameCompl k m S
  · exact etale_quotientMap hf (mvPolynomialCoordIdeal k m S)
variable {X : Scheme.{u}} {k : Type u} [Field k] {p : X ⟶ Spec (CommRingCat.of k)}
  {U : X.Opens} {m : ℕ}
theorem EtaleChart.map_mvPolynomialCoordIdeal_eq_ideal (c : EtaleChart p U m) (hU : IsAffineOpen U)
    (Z : X.IdealSheafData) (S : Finset (Fin m)) (h : restrictIdeal Z U = c.coordIdeal S) :
    Ideal.map c.coordRingHom (mvPolynomialCoordIdeal k m S) = Z.ideal ⟨U, hU⟩ := by
  have hfun : (fun j : Fin m => c.coordRingHom (MvPolynomial.X (ULift.up.{u} j))) = c.coord :=
    funext fun j => c.coordRingHom_X j
  rw [c.ideal_eq_span_coord hU Z S h, mvPolynomialCoordIdeal_eq_span, Ideal.map_span]
  congr 1
  rw [Set.image_image]
  exact congrArg (fun g => g '' (S : Set (Fin m))) hfun
def EtaleChart.restrictToSubschemeCoords (c : EtaleChart p U m) (Z : X.IdealSheafData)
    (S : Finset (Fin m)) (i : ULift.{u} (Fin (m - S.card))) :
    Γ((Z.subschemeι ⁻¹ᵁ U).toScheme, ⊤) :=
  (Z.subschemeι ⁻¹ᵁ U).topIso.inv.hom
    ((Z.subschemeι.appLE U (Z.subschemeι ⁻¹ᵁ U) le_rfl).hom (c.coord (complOrderEmb m S i.down)))
theorem appTop_comp_hom_apply {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C) (x : Γ(C, ⊤)) :
    ((f ≫ g).appTop).hom x = (f.appTop).hom ((g.appTop).hom x) := rfl
theorem commRingCatIso_inv_hom_apply {A B : CommRingCat.{u}} (e : A ≅ B) (x : A) :
    e.inv.hom (e.hom.hom x) = x := by
  simp
theorem commRingCatIso_hom_inv_apply {A B : CommRingCat.{u}} (e : A ≅ B) (x : B) :
    e.hom.hom (e.inv.hom x) = x := by
  simp
theorem bijective_commRingCatIso_inv {A B : CommRingCat.{u}} (e : A ≅ B) :
    Function.Bijective e.inv.hom := by
  constructor
  · intro x y hxy
    have h := congrArg e.hom.hom hxy
    rwa [commRingCatIso_hom_inv_apply, commRingCatIso_hom_inv_apply] at h
  · intro x
    exact ⟨e.hom.hom x, commRingCatIso_inv_hom_apply e x⟩
theorem iso_hom_appTop_inv_appTop_apply {A B : Scheme.{u}} (e : A ≅ B) (x : Γ(A, ⊤)) :
    (e.hom.appTop).hom ((e.inv.appTop).hom x) = x := by
  have h1 : ((e.hom ≫ e.inv).appTop).hom x
      = ((CategoryTheory.CategoryStruct.id A : A ⟶ A).appTop).hom x := by rw [e.hom_inv_id]
  rw [appTop_comp_hom_apply] at h1
  rw [h1]
  simp
theorem affineSpaceGlobalSectionsHom_apply (K : Type u) [Field K] (n : ℕ)
    (x : MvPolynomial (ULift.{u} (Fin n)) K) :
    affineSpaceGlobalSectionsHom K n x =
      ((AffineSpace.SpecIso (ULift.{u} (Fin n)) (CommRingCat.of K)).hom.appTop).hom
        ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (ULift.{u} (Fin n)) K))).inv.hom x) :=
  rfl
theorem affineSpaceGlobalSectionsHom_X_eq_coord (K : Type u) [Field K] (n : ℕ) (i : ULift.{u} (Fin n)) :
    affineSpaceGlobalSectionsHom K n (MvPolynomial.X i) =
      AffineSpace.coord (Spec (CommRingCat.of K)) i := by
  have h := AffineSpace.SpecIso_inv_appTop_coord (CommRingCat.of K) i
  rw [affineSpaceGlobalSectionsHom_apply, ← h]
  exact iso_hom_appTop_inv_appTop_apply
    (AffineSpace.SpecIso (ULift.{u} (Fin n)) (CommRingCat.of K)) _
theorem affineSpaceGlobalSectionsHom_C (K : Type u) [Field K] (n : ℕ) (a : K) :
    affineSpaceGlobalSectionsHom K n (MvPolynomial.C a) =
      ((affineSpaceFinToSpec K n).appTop).hom
        ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom a) := by
  have hov : (AffineSpace.SpecIso (ULift.{u} (Fin n)) (CommRingCat.of K)).inv ≫
      affineSpaceFinToSpec K n =
      Spec.map (CommRingCat.ofHom
        (MvPolynomial.C : K →+* MvPolynomial (ULift.{u} (Fin n)) K)) :=
    AffineSpace.SpecIso_inv_over ..
  have hmor : (AffineSpace.SpecIso (ULift.{u} (Fin n)) (CommRingCat.of K)).hom ≫
      Spec.map (CommRingCat.ofHom
        (MvPolynomial.C : K →+* MvPolynomial (ULift.{u} (Fin n)) K))
      = affineSpaceFinToSpec K n := by
    rw [← hov, Iso.hom_inv_id_assoc]
  have h1 : ((Scheme.ΓSpecIso
        (CommRingCat.of (MvPolynomial (ULift.{u} (Fin n)) K))).inv).hom (MvPolynomial.C a)
      = ((Spec.map (CommRingCat.ofHom
          (MvPolynomial.C : K →+* MvPolynomial (ULift.{u} (Fin n)) K))).appTop).hom
        ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom a) := by
    have hnat := Scheme.ΓSpecIso_inv_naturality
      (CommRingCat.ofHom (MvPolynomial.C : K →+* MvPolynomial (ULift.{u} (Fin n)) K))
    show ((CommRingCat.ofHom (MvPolynomial.C : K →+* MvPolynomial (ULift.{u} (Fin n)) K)) ≫
      (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (ULift.{u} (Fin n)) K))).inv).hom a = _
    conv_lhs => rw [hnat]
    rfl
  rw [affineSpaceGlobalSectionsHom_apply, h1, ← appTop_comp_hom_apply, hmor]
theorem etale_specMap_of_etale {R T : CommRingCat.{u}} (φ : R ⟶ T) (hφ : φ.hom.Etale) :
    Etale (Spec.map φ) := by
  rw [AlgebraicGeometry.HasRingHomProperty.Spec_iff (P := @Etale)]
  exact hφ
theorem etale_homOfVector_of_appTop_etale {Wsch : Scheme.{u}} [IsAffine Wsch]
    {K : Type u} [Field K]
    {n : ℕ} (q : Wsch ⟶ Spec (CommRingCat.of K)) (v : ULift.{u} (Fin n) → Γ(Wsch, ⊤))
    (hv : (((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (ULift.{u} (Fin n)) K))).inv ≫
      (AffineSpace.homOfVector q v ≫
        (AffineSpace.SpecIso (ULift.{u} (Fin n)) (CommRingCat.of K)).hom).appTop).hom).Etale) :
    Etale (AffineSpace.homOfVector q v) := by
  set f := AffineSpace.homOfVector q v
  set e := AffineSpace.SpecIso (ULift.{u} (Fin n)) (CommRingCat.of K)
  set φ := (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (ULift.{u} (Fin n)) K))).inv ≫
      (f ≫ e.hom).appTop with hφ
  have hφe : φ.hom.Etale := hv
  have nat : (f ≫ e.hom) ≫
      (Spec (CommRingCat.of (MvPolynomial (ULift.{u} (Fin n)) K))).toSpecΓ
      = Wsch.toSpecΓ ≫ Spec.map (f ≫ e.hom).appTop := Scheme.toSpecΓ_naturality _
  have key : f = Wsch.toSpecΓ ≫ Spec.map φ ≫ e.inv := by
    rw [hφ, Spec.map_comp]
    calc f = ((f ≫ e.hom) ≫
        (Spec (CommRingCat.of (MvPolynomial (ULift.{u} (Fin n)) K))).toSpecΓ) ≫
          Spec.map (Scheme.ΓSpecIso
            (CommRingCat.of (MvPolynomial (ULift.{u} (Fin n)) K))).inv ≫ e.inv := by simp
      _ = (Wsch.toSpecΓ ≫ Spec.map (f ≫ e.hom).appTop) ≫
          Spec.map (Scheme.ΓSpecIso
            (CommRingCat.of (MvPolynomial (ULift.{u} (Fin n)) K))).inv ≫ e.inv := by rw [nat]
      _ = Wsch.toSpecΓ ≫ (Spec.map (f ≫ e.hom).appTop ≫
          Spec.map (Scheme.ΓSpecIso
            (CommRingCat.of (MvPolynomial (ULift.{u} (Fin n)) K))).inv) ≫ e.inv := by
            simp [Category.assoc]
  have : Etale (Spec.map φ) := etale_specMap_of_etale φ hφe
  rw [key]
  infer_instance
theorem appTop_comp_specIso_eq_affineSpaceGlobalSectionsHom {Wsch : Scheme.{u}} {K : Type u} [Field K] {n : ℕ}
    (F : Wsch ⟶ affineSpaceFin K n) (x : MvPolynomial (ULift.{u} (Fin n)) K) :
    (((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (ULift.{u} (Fin n)) K))).inv ≫
        (F ≫ (AffineSpace.SpecIso (ULift.{u} (Fin n)) (CommRingCat.of K)).hom).appTop).hom) x
      = (F.appTop).hom (affineSpaceGlobalSectionsHom K n x) := by
  rw [affineSpaceGlobalSectionsHom_apply]
  show ((F ≫ (AffineSpace.SpecIso (ULift.{u} (Fin n)) (CommRingCat.of K)).hom).appTop).hom
      ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (ULift.{u} (Fin n)) K))).inv.hom x) = _
  rw [appTop_comp_hom_apply]
theorem subschemeι_appLE_apply (Zd : X.IdealSheafData) (Uo : X.Opens)
    (hUo : IsAffineOpen Uo) (z : Γ(X, Uo)) :
    (Zd.subschemeι.appLE Uo (Zd.subschemeι ⁻¹ᵁ Uo) le_rfl).hom z
      = (Zd.subschemeObjIso ⟨Uo, hUo⟩).inv.hom
          (Ideal.Quotient.mk (Zd.ideal ⟨Uo, hUo⟩) z) := by
  have hh : Zd.subschemeι.app Uo
      = CommRingCat.ofHom (Ideal.Quotient.mk (Zd.ideal ⟨Uo, hUo⟩)) ≫
        (Zd.subschemeObjIso ⟨Uo, hUo⟩).inv :=
    Scheme.IdealSheafData.subschemeι_app Zd ⟨Uo, hUo⟩
  have h2 : Zd.subschemeι.appLE Uo (Zd.subschemeι ⁻¹ᵁ Uo) le_rfl = Zd.subschemeι.app Uo := by
    simp [Scheme.Hom.appLE]
  rw [h2]
  conv_lhs => rw [hh]
  rfl
theorem coordRingHom_apply (c : EtaleChart p U m)
    (x : MvPolynomial (ULift.{u} (Fin m)) k) :
    c.coordRingHom x = U.topIso.hom.hom (c.map.appTop.hom (affineSpaceGlobalSectionsHom k m x)) :=
  rfl
theorem subschemeι_appLE_topIso_hom_appTop_apply {Wsch Ysch : Scheme.{u}} (q : Wsch ⟶ Ysch)
    (Zd : Wsch.IdealSheafData) (Uo : Wsch.Opens) (x : Γ(Ysch, ⊤)) :
    (Zd.subschemeι ⁻¹ᵁ Uo).topIso.inv.hom
        ((Zd.subschemeι.appLE Uo (Zd.subschemeι ⁻¹ᵁ Uo) le_rfl).hom
          (Uo.topIso.hom.hom (((Uo.ι ≫ q).appTop).hom x)))
      = (((Zd.subschemeι ⁻¹ᵁ Uo).ι ≫ (Zd.subschemeι ≫ q)).appTop).hom x := by
  have htop1 : q ⁻¹ᵁ (⊤ : Ysch.Opens) = ⊤ := by simp
  have htop2 : (Zd.subschemeι ≫ q) ⁻¹ᵁ (⊤ : Ysch.Opens) = ⊤ := by simp
  have e1 : Uo ≤ q ⁻¹ᵁ (⊤ : Ysch.Opens) := le_top.trans htop1.ge
  have e2 : (Zd.subschemeι ⁻¹ᵁ Uo) ≤ (Zd.subschemeι ≫ q) ⁻¹ᵁ (⊤ : Ysch.Opens) :=
    le_top.trans htop2.ge
  have hq : (Uo.ι ≫ q).appTop = q.appLE ⊤ Uo e1 ≫ Uo.topIso.inv :=
    (appLE_top_comp_topIso_inv q Uo e1).symm
  have hq2 : (Zd.subschemeι ≫ q).appLE ⊤ (Zd.subschemeι ⁻¹ᵁ Uo) e2 ≫
        (Zd.subschemeι ⁻¹ᵁ Uo).topIso.inv
      = ((Zd.subschemeι ⁻¹ᵁ Uo).ι ≫ (Zd.subschemeι ≫ q)).appTop :=
    appLE_top_comp_topIso_inv (Zd.subschemeι ≫ q) (Zd.subschemeι ⁻¹ᵁ Uo) e2
  have key : (Uo.ι ≫ q).appTop ≫ Uo.topIso.hom ≫
        Zd.subschemeι.appLE Uo (Zd.subschemeι ⁻¹ᵁ Uo) le_rfl ≫
          (Zd.subschemeι ⁻¹ᵁ Uo).topIso.inv
      = ((Zd.subschemeι ⁻¹ᵁ Uo).ι ≫ (Zd.subschemeι ≫ q)).appTop := by
    rw [hq, ← hq2, Category.assoc, Iso.inv_hom_id_assoc, ← Category.assoc,
      Scheme.Hom.appLE_comp_appLE]
  show ((Uo.ι ≫ q).appTop ≫ Uo.topIso.hom ≫
      Zd.subschemeι.appLE Uo (Zd.subschemeι ⁻¹ᵁ Uo) le_rfl ≫
        (Zd.subschemeι ⁻¹ᵁ Uo).topIso.inv).hom x = _
  rw [key]
theorem appTop_homOfVector_restrictToSubschemeCoords_eq (c : EtaleChart p U m)
    (hU : IsAffineOpen U) (Z : X.IdealSheafData) (S : Finset (Fin m)) :
    (((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (ULift.{u} (Fin (m - S.card))) k))).inv ≫
        (AffineSpace.homOfVector ((Z.subschemeι ⁻¹ᵁ U).ι ≫ (Z.subschemeι ≫ p))
            (c.restrictToSubschemeCoords Z S) ≫
          (AffineSpace.SpecIso (ULift.{u} (Fin (m - S.card)))
            (CommRingCat.of k)).hom).appTop).hom)
      = ((((Z.subschemeι ⁻¹ᵁ U).topIso.inv.hom).comp
            ((Z.subschemeObjIso ⟨U, hU⟩).inv.hom)).comp
          (((Ideal.Quotient.mk (Z.ideal ⟨U, hU⟩)).comp c.coordRingHom).comp
            (renameCompl k m S).toRingHom)) := by
  refine MvPolynomial.ringHom_ext (fun a => ?_) (fun i => ?_)
  · have hover : AffineSpace.homOfVector ((Z.subschemeι ⁻¹ᵁ U).ι ≫ (Z.subschemeι ≫ p))
        (c.restrictToSubschemeCoords Z S) ≫ affineSpaceFinToSpec k (m - S.card)
        = (Z.subschemeι ⁻¹ᵁ U).ι ≫ (Z.subschemeι ≫ p) := AffineSpace.homOfVector_over ..
    rw [appTop_comp_specIso_eq_affineSpaceGlobalSectionsHom, affineSpaceGlobalSectionsHom_C, ← appTop_comp_hom_apply, hover]
    show _ = (Z.subschemeι ⁻¹ᵁ U).topIso.inv.hom
      ((Z.subschemeObjIso ⟨U, hU⟩).inv.hom
        (Ideal.Quotient.mk (Z.ideal ⟨U, hU⟩)
          (c.coordRingHom (renameCompl k m S (MvPolynomial.C a)))))
    rw [renameCompl_C, coordRingHom_apply, affineSpaceGlobalSectionsHom_C, ← appTop_comp_hom_apply,
      c.comp_struct, ← subschemeι_appLE_apply Z U hU, subschemeι_appLE_topIso_hom_appTop_apply]
  · obtain ⟨i⟩ := i
    rw [appTop_comp_specIso_eq_affineSpaceGlobalSectionsHom, affineSpaceGlobalSectionsHom_X_eq_coord, AffineSpace.homOfVector_appTop_coord]
    show (Z.subschemeι ⁻¹ᵁ U).topIso.inv.hom
        ((Z.subschemeι.appLE U (Z.subschemeι ⁻¹ᵁ U) le_rfl).hom (c.coord (complOrderEmb m S i)))
      = (Z.subschemeι ⁻¹ᵁ U).topIso.inv.hom
        ((Z.subschemeObjIso ⟨U, hU⟩).inv.hom
          (Ideal.Quotient.mk (Z.ideal ⟨U, hU⟩)
            (c.coordRingHom (renameCompl k m S (MvPolynomial.X (ULift.up.{u} i))))))
    rw [renameCompl_X, EtaleChart.coordRingHom_X, ← subschemeι_appLE_apply Z U hU]
theorem EtaleChart.etale_homOfVector_restrictToSubschemeCoords (c : EtaleChart p U m)
    (hU : IsAffineOpen U) (Z : X.IdealSheafData) (S : Finset (Fin m))
    (h : restrictIdeal Z U = c.coordIdeal S) :
    Etale (AffineSpace.homOfVector ((Z.subschemeι ⁻¹ᵁ U).ι ≫ (Z.subschemeι ≫ p))
      (c.restrictToSubschemeCoords Z S)) := by
  have hVa : IsAffine (Z.subschemeι ⁻¹ᵁ U).toScheme := isAffineOpen_preimage_subschemeι Z hU
  refine etale_homOfVector_of_appTop_etale _ _ ?_
  rw [appTop_homOfVector_restrictToSubschemeCoords_eq c hU Z S]
  apply RingHom.Etale.stableUnderComposition
  · exact etale_quotientMk_comp_renameCompl k m S c.coordRingHom (c.coordRingHom_etale hU) (Z.ideal ⟨U, hU⟩)
      (c.map_mvPolynomialCoordIdeal_eq_ideal hU Z S h).symm
  · apply RingHom.Etale.of_bijective
    exact (bijective_commRingCatIso_inv (Z.subschemeι ⁻¹ᵁ U).topIso).comp
      (bijective_commRingCatIso_inv (Z.subschemeObjIso ⟨U, hU⟩))
def EtaleChart.restrictToSubscheme (c : EtaleChart p U m) (hU : IsAffineOpen U)
    (Z : X.IdealSheafData) (S : Finset (Fin m)) (h : restrictIdeal Z U = c.coordIdeal S) :
    EtaleChart (Z.subschemeι ≫ p) (Z.subschemeι ⁻¹ᵁ U) (m - S.card) :=
  EtaleChart.ofCoords (Z.subschemeι ≫ p) (Z.subschemeι ⁻¹ᵁ U) (c.restrictToSubschemeCoords Z S)
    (c.etale_homOfVector_restrictToSubschemeCoords hU Z S h)
end FunctorialResolution.EmbeddedResolution


