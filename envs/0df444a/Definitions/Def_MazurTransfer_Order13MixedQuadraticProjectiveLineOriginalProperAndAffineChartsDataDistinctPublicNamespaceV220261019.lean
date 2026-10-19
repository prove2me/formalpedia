-- Prove2me | Definitions.Def_MazurTransfer_Order13MixedQuadraticProjectiveLineOriginalProperAndAffineChartsDataDistinctPublicNamespaceV220261019
-- name    : MazurTransfer_Order13MixedQuadraticProjectiveLineOriginalProperAndAffineChartsDataDistinctPublicNamespaceV220261019
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-19T04:24:39.417659+00:00
-- url     : https://prove2.me/theorems/f1f260fe-5238-4451-bf4d-4c382652f7c1
-- title:
--   Original projective line with proper structure map and both affine charts
-- statement:
--   The actual original Proj projective line, its proper structure map, both polynomial affine chart presentations, and their cover. The original complete types and whole constructor values, including private nonproof constructor helpers, are compared after explicit namespace renaming and expansion of inspected compiler proof declarations. Named downstream consumer: the original finite mixed quadratic hyperelliptic map and curve properness.
-- source:
--   MazurTheorem integral mixed quadratic hyperelliptic map, by Vasily Ilin and contributors; original projective-line adaptation retains attribution to the Tau Ceti contributors. Apache-2.0; campaign pin only.

import Mathlib
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Adapted complete degree-zero and properness helpers from the already pinned
WIP-compatible TauCeti/AlgebraicGeometry/ProjectiveLine/Basic.lean and Proper.lean.
The original field restriction is replaced by an arbitrary commutative ring.
This is an independent adaptation at the campaign Mathlib pin; the separate
Tau Ceti package and core pins are not changed.
Design boundary: the actual Proj projective line over a commutative ring,
with its structural morphism proved proper. Named downstream consumer:
constructing the finite integral order-thirteen hyperelliptic map to this
projective line, to establish properness of the actual integral curve.
This file does not assert that the curve morphism has been constructed.
-/
noncomputable section
namespace MazurTransfer.Order13MixedQuadraticProjectiveLineOriginal20261019
open CategoryTheory AlgebraicGeometry
open scoped DirectSum
universe u

abbrev homogeneousPieces (R : Type u) [CommRing R] :=
  MvPolynomial.homogeneousSubmodule (Fin 2) R

instance (R : Type u) [CommRing R] : GradedAlgebra (homogeneousPieces R) :=
  MvPolynomial.gradedAlgebra

abbrev scheme (R : Type u) [CommRing R] : Scheme.{u} := Proj (homogeneousPieces R)

def degreeZeroRingEquiv (R : Type u) [CommRing R] : R ≃+* homogeneousPieces R 0 :=
  RingEquiv.ofBijective (algebraMap R (homogeneousPieces R 0)) <| by
    constructor
    · intro r s hrs
      exact MvPolynomial.C_injective (Fin 2) R (congrArg Subtype.val hrs)
    · intro p
      have hp : (p : MvPolynomial (Fin 2) R) ∈
          (1 : Submodule R (MvPolynomial (Fin 2) R)) := by
        simpa [homogeneousPieces, MvPolynomial.homogeneousSubmodule_zero] using p.property
      obtain ⟨r, hr⟩ := Submodule.mem_one.mp hp
      refine ⟨r, Subtype.ext ?_⟩
      exact hr

instance (R : Type u) [CommRing R] :
    Algebra.FiniteType (homogeneousPieces R 0) (MvPolynomial (Fin 2) R) := by
  letI : IsScalarTower R (homogeneousPieces R 0) (MvPolynomial (Fin 2) R) :=
    IsScalarTower.of_algebraMap_eq
      (R := R) (S := homogeneousPieces R 0) (A := MvPolynomial (Fin 2) R) (fun r ↦ by rfl)
  exact Algebra.FiniteType.of_restrictScalars_finiteType
    R (homogeneousPieces R 0) (MvPolynomial (Fin 2) R)

def structureMap (R : Type u) [CommRing R] : scheme R ⟶ Spec (CommRingCat.of R) :=
  Proj.toSpecZero (homogeneousPieces R) ≫
    Spec.map (degreeZeroRingEquiv R).toCommRingCatIso.hom

theorem structureMap_isProper (R : Type u) [CommRing R] : IsProper (structureMap R) := by
  dsimp only [structureMap]
  infer_instance

theorem structureMap_locallyOfFiniteType (R : Type u) [CommRing R] :
    LocallyOfFiniteType (structureMap R) := by
  dsimp only [structureMap]
  infer_instance

end MazurTransfer.Order13MixedQuadraticProjectiveLineOriginal20261019
#print axioms MazurTransfer.Order13MixedQuadraticProjectiveLineOriginal20261019.degreeZeroRingEquiv
#print axioms MazurTransfer.Order13MixedQuadraticProjectiveLineOriginal20261019.structureMap_isProper
#print axioms MazurTransfer.Order13MixedQuadraticProjectiveLineOriginal20261019.structureMap_locallyOfFiniteType

end
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Complete selected chart presentation proofs adapted from the already pinned
WIP-compatible TauCeti/AlgebraicGeometry/ProjectiveLine/Basic.lean and Smooth.lean.
All coefficient rings are commutative rings, with no field hypothesis.
The independent campaign-pin adaptation does not change the Tau Ceti package.
Design boundary: polynomial presentations of both actual Proj affine charts
and their joint cover. Named downstream consumer: the finite integral
order-thirteen hyperelliptic map into the actual proper projective line.
-/
noncomputable section
namespace MazurTransfer.Order13MixedQuadraticProjectiveLineOriginal20261019
open CategoryTheory AlgebraicGeometry
open scoped DirectSum
universe u

@[simp]
theorem coe_degreeZeroRingEquiv_apply (R : Type u) [CommRing R] (r : R) :
    ((degreeZeroRingEquiv R r : homogeneousPieces R 0) : MvPolynomial (Fin 2) R) =
      MvPolynomial.C r := rfl

/-- The standard affine chart `D₊(X₁)` of the projective line. -/
abbrev standardAffineOpen (K : Type u) [CommRing K] : (scheme K).Opens :=
  Proj.basicOpen (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2))

/-- The affine chart `D₊(X₀)` containing the point at infinity. -/
abbrev infinityAffineOpen (K : Type u) [CommRing K] : (scheme K).Opens :=
  Proj.basicOpen (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2))

lemma X_one_mem_degree_one (K : Type u) [CommRing K] :
    MvPolynomial.X (1 : Fin 2) ∈ homogeneousPieces K 1 :=
  MvPolynomial.isHomogeneous_X K (1 : Fin 2)

lemma X_zero_mem_degree_one (K : Type u) [CommRing K] :
    MvPolynomial.X (0 : Fin 2) ∈ homogeneousPieces K 1 :=
  MvPolynomial.isHomogeneous_X K (0 : Fin 2)

private lemma zero_lt_one : 0 < (1 : ℕ) := Nat.zero_lt_succ 0

/-- The degree-zero homogeneous fraction `X₀ / X₁` on the standard affine chart. -/
@[expose] noncomputable def affineCoordinateAway (K : Type u) [CommRing K] :
    HomogeneousLocalization.Away (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2)) :=
  HomogeneousLocalization.Away.mk (homogeneousPieces K) (X_one_mem_degree_one K) 1
    (MvPolynomial.X (0 : Fin 2)) (by simpa using X_zero_mem_degree_one K)

/-- The regular function `X₀ / X₁` on the standard affine chart `D₊(X₁)`. -/
@[expose] noncomputable def affineCoordinate (K : Type u) [CommRing K] :
  Γ(scheme K, standardAffineOpen K) :=
  (Proj.basicOpenIsoAway (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2))
    (X_one_mem_degree_one K) zero_lt_one).hom (affineCoordinateAway K)

/-- The degree-zero homogeneous fraction `X₁ / X₀` on the affine chart containing
infinity. -/
@[expose] noncomputable def inverseAffineCoordinateAway (K : Type u) [CommRing K] :
    HomogeneousLocalization.Away (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2)) :=
  HomogeneousLocalization.Away.mk (homogeneousPieces K) (X_zero_mem_degree_one K) 1
    (MvPolynomial.X (1 : Fin 2)) (by simpa using X_one_mem_degree_one K)

/-- The regular function `X₁ / X₀` on the affine chart `D₊(X₀)`. -/
@[expose] noncomputable def inverseAffineCoordinate (K : Type u) [CommRing K] :
    Γ(scheme K, infinityAffineOpen K) :=
  (Proj.basicOpenIsoAway (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2))
    (X_zero_mem_degree_one K) zero_lt_one).hom (inverseAffineCoordinateAway K)



private noncomputable def t (K : Type u) [CommRing K] :
    HomogeneousLocalization.Away
      (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2)) :=
  HomogeneousLocalization.Away.mk (homogeneousPieces K) (X_one_mem_degree_one K) 1
    (MvPolynomial.X (0 : Fin 2)) (by simpa using X_zero_mem_degree_one K)

private lemma adjoin_X_over_degreeZero (K : Type u) [CommRing K] :
    Algebra.adjoin (homogeneousPieces K 0)
      (Set.range (MvPolynomial.X : Fin 2 → MvPolynomial (Fin 2) K)) = ⊤ := by
  apply top_unique
  intro p _
  have hall : ∀ p : MvPolynomial (Fin 2) K,
      p ∈ Algebra.adjoin (homogeneousPieces K 0)
        (Set.range (MvPolynomial.X : Fin 2 → MvPolynomial (Fin 2) K)) := by
    intro q
    induction q using MvPolynomial.induction_on with
    | C r =>
        have h := (Algebra.adjoin (homogeneousPieces K 0)
          (Set.range (MvPolynomial.X : Fin 2 → MvPolynomial (Fin 2) K))).algebraMap_mem
          (degreeZeroRingEquiv K r)
        simpa using h
    | add p q hp hq => exact add_mem hp hq
    | mul_X p i hp =>
        exact mul_mem hp (Algebra.subset_adjoin ⟨i, rfl⟩)
  exact hall p

private lemma adjoin_t (K : Type u) [CommRing K] :
    Algebra.adjoin (homogeneousPieces K 0) ({t K} : Set
      (HomogeneousLocalization.Away
        (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2)))) = ⊤ := by
  let hgen := HomogeneousLocalization.Away.adjoin_mk_prod_pow_eq_top
    (X_one_mem_degree_one K) (Fin 2)
    (MvPolynomial.X : Fin 2 → MvPolynomial (Fin 2) K)
    (adjoin_X_over_degreeZero K) (fun _ ↦ 1)
    (fun i ↦ MvPolynomial.isHomogeneous_X K i)
  rw [← top_le_iff, ← hgen, Algebra.adjoin_le_iff]
  rintro z ⟨a, ai, hai, hai_le, rfl⟩
  have hprod : (∏ i, MvPolynomial.X i ^ ai i) ∈ homogeneousPieces K (a • 1) := by
    rw [← hai]
    exact SetLike.prod_pow_mem_graded (homogeneousPieces K) (fun _ ↦ 1)
      MvPolynomial.X ai (fun i _ ↦ MvPolynomial.isHomogeneous_X K i)
  have h0 : ai 0 ≤ 1 := hai_le 0
  have h1 : ai 1 ≤ 1 := hai_le 1
  interval_cases h0a : ai 0 <;> interval_cases h1a : ai 1
  · have ha : a = 0 := by
      simpa [Fin.sum_univ_two, h0a, h1a] using hai.symm
    have heq : HomogeneousLocalization.Away.mk (homogeneousPieces K)
        (X_one_mem_degree_one K) a (∏ i, MvPolynomial.X i ^ ai i) hprod = 1 := by
      apply HomogeneousLocalization.val_injective
      simp [HomogeneousLocalization.Away.val_mk, ha, h0a, h1a,
        Fin.prod_univ_two]
    rw [heq]
    exact one_mem _
  · have ha : a = 1 := by
      simpa [Fin.sum_univ_two, h0a, h1a] using hai.symm
    have heq : HomogeneousLocalization.Away.mk (homogeneousPieces K)
        (X_one_mem_degree_one K) a (∏ i, MvPolynomial.X i ^ ai i) hprod = 1 := by
      apply HomogeneousLocalization.val_injective
      have hX1 : MvPolynomial.X (1 : Fin 2) ∈
          Submonoid.powers (MvPolynomial.X (1 : Fin 2)) :=
        (Submonoid.mem_powers_iff
          (MvPolynomial.X (1 : Fin 2) : MvPolynomial (Fin 2) K)
          (MvPolynomial.X (1 : Fin 2))).mpr ⟨1, by simp⟩
      rw [HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.val_one,
        Localization.mk_eq_mk']
      trans IsLocalization.mk' (Localization (Submonoid.powers (MvPolynomial.X (1 : Fin 2))))
        (MvPolynomial.X (1 : Fin 2))
        ⟨MvPolynomial.X (1 : Fin 2), hX1⟩
      · apply IsLocalization.mk'_eq_of_eq
        simp [ha, h0a, h1a, Fin.prod_univ_two]
      · exact IsLocalization.mk'_self (S :=
          Localization (Submonoid.powers (MvPolynomial.X (1 : Fin 2))))
          hX1
    rw [heq]
    exact one_mem _
  · have ha : a = 1 := by
      simpa [Fin.sum_univ_two, h0a, h1a] using hai.symm
    have heq : HomogeneousLocalization.Away.mk (homogeneousPieces K)
        (X_one_mem_degree_one K) a (∏ i, MvPolynomial.X i ^ ai i) hprod = t K := by
      apply HomogeneousLocalization.val_injective
      rw [HomogeneousLocalization.Away.val_mk, t, HomogeneousLocalization.Away.val_mk,
        Localization.mk_eq_mk']
      apply IsLocalization.mk'_eq_of_eq
      simp [ha, h0a, h1a, Fin.prod_univ_two]
    rw [heq]
    exact Algebra.subset_adjoin (Set.mem_singleton (t K))
  · have ha : a = 2 := by
      simpa [Fin.sum_univ_two, h0a, h1a] using hai.symm
    have heq : HomogeneousLocalization.Away.mk (homogeneousPieces K)
        (X_one_mem_degree_one K) a (∏ i, MvPolynomial.X i ^ ai i) hprod = t K := by
      apply HomogeneousLocalization.val_injective
      rw [HomogeneousLocalization.Away.val_mk, t, HomogeneousLocalization.Away.val_mk,
        Localization.mk_eq_mk']
      apply IsLocalization.mk'_eq_of_eq
      simp [ha, h0a, h1a, Fin.prod_univ_two]
      ring
    rw [heq]
    exact Algebra.subset_adjoin (Set.mem_singleton (t K))

private def coordinateToPolynomialHom (K : Type u) [CommRing K] :
    MvPolynomial (Fin 2) K →+* Polynomial (homogeneousPieces K 0) :=
  MvPolynomial.eval₂Hom
    ((Polynomial.C : homogeneousPieces K 0 →+*
      Polynomial (homogeneousPieces K 0)).comp (degreeZeroRingEquiv K).toRingHom)
    (fun i : Fin 2 ↦ if i = 0 then
      (Polynomial.X : Polynomial (homogeneousPieces K 0)) else 1)

private lemma coordinateToPolynomialHom_X_zero (K : Type u) [CommRing K] :
    coordinateToPolynomialHom K (MvPolynomial.X (0 : Fin 2)) = Polynomial.X := by
  simp [coordinateToPolynomialHom]

private lemma coordinateToPolynomialHom_X_one (K : Type u) [CommRing K] :
    coordinateToPolynomialHom K (MvPolynomial.X (1 : Fin 2)) = 1 := by
  simp [coordinateToPolynomialHom]

private noncomputable def awayToPolynomial (K : Type u) [CommRing K] :
    HomogeneousLocalization.Away
        (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2)) →+*
      Polynomial (homogeneousPieces K 0) :=
  (Localization.awayLift (coordinateToPolynomialHom K)
      (MvPolynomial.X (1 : Fin 2)) (by
        change IsUnit (coordinateToPolynomialHom K (MvPolynomial.X (1 : Fin 2)))
        rw [coordinateToPolynomialHom_X_one]
        exact isUnit_one)).comp
    (algebraMap
      (HomogeneousLocalization.Away
        (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2)))
      (Localization.Away (MvPolynomial.X (1 : Fin 2))))

private lemma awayToPolynomial_t (K : Type u) [CommRing K] :
    awayToPolynomial K (t K) = Polynomial.X := by
  simp only [awayToPolynomial, RingHom.comp_apply, t,
    HomogeneousLocalization.algebraMap_apply, HomogeneousLocalization.Away.val_mk]
  have hinv : coordinateToPolynomialHom K (MvPolynomial.X (1 : Fin 2)) *
      (1 : Polynomial (homogeneousPieces K 0)) = 1 := by
    rw [coordinateToPolynomialHom_X_one]
    simp
  have h := Localization.awayLift_mk
    (A := Polynomial (homogeneousPieces K 0)) (coordinateToPolynomialHom K)
    (MvPolynomial.X (1 : Fin 2)) (MvPolynomial.X (0 : Fin 2)) 1
    hinv 1
  simpa [coordinateToPolynomialHom] using h

private lemma awayToPolynomial_fromZero (K : Type u) [CommRing K]
    (r : homogeneousPieces K 0) :
    awayToPolynomial K
      (HomogeneousLocalization.fromZeroRingHom (homogeneousPieces K)
        (Submonoid.powers (MvPolynomial.X (1 : Fin 2))) r) = Polynomial.C r := by
  obtain ⟨s, rfl⟩ := (degreeZeroRingEquiv K).surjective r
  simp only [awayToPolynomial, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply,
    HomogeneousLocalization.fromZeroRingHom]
  have hinv : coordinateToPolynomialHom K (MvPolynomial.X (1 : Fin 2)) *
      (1 : Polynomial (homogeneousPieces K 0)) = 1 := by
    rw [coordinateToPolynomialHom_X_one]
    simp
  have h := Localization.awayLift_mk
    (A := Polynomial (homogeneousPieces K 0)) (coordinateToPolynomialHom K)
    (MvPolynomial.X (1 : Fin 2)) (MvPolynomial.C s) 1
    hinv 0
  convert h using 1
  · congr 1
  · simp [coordinateToPolynomialHom]

private noncomputable def awayToPolynomialAlgHom (K : Type u) [CommRing K] :
    HomogeneousLocalization.Away
        (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2)) →ₐ[homogeneousPieces K 0]
      Polynomial (homogeneousPieces K 0) :=
  { awayToPolynomial K with
    commutes' := awayToPolynomial_fromZero K }

private lemma transcendental_t (K : Type u) [CommRing K] :
    Transcendental (homogeneousPieces K 0) (t K) := by
  rw [transcendental_iff_injective]
  intro p q hpq
  have h := congrArg (awayToPolynomialAlgHom K) hpq
  have ht : (awayToPolynomialAlgHom K) (t K) = Polynomial.X :=
    awayToPolynomial_t K
  calc
    p = Polynomial.aeval Polynomial.X p := (Polynomial.aeval_X_left_apply p).symm
    _ = Polynomial.aeval ((awayToPolynomialAlgHom K) (t K)) p := by
      rw [ht]
    _ = (awayToPolynomialAlgHom K) (Polynomial.aeval (t K) p) :=
      AlgHom.congr_fun (Polynomial.aeval_algHom (awayToPolynomialAlgHom K) (t K)) p
    _ = (awayToPolynomialAlgHom K) (Polynomial.aeval (t K) q) := h
    _ = Polynomial.aeval ((awayToPolynomialAlgHom K) (t K)) q :=
      (AlgHom.congr_fun (Polynomial.aeval_algHom (awayToPolynomialAlgHom K) (t K)) q).symm
    _ = Polynomial.aeval Polynomial.X q := by rw [ht]
    _ = q := Polynomial.aeval_X_left_apply q

private noncomputable def polynomialAwayAlgEquiv (K : Type u) [CommRing K] :
    Polynomial (homogeneousPieces K 0) ≃ₐ[homogeneousPieces K 0]
      HomogeneousLocalization.Away
        (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2)) :=
  (Polynomial.algEquivOfTranscendental (homogeneousPieces K 0) (t K)
    (transcendental_t K)).trans
      ((Subalgebra.equivOfEq _ _ (adjoin_t K)).trans Subalgebra.topEquiv)

/-- The standard affine chart of the projective line is a polynomial line over the degree-zero
homogeneous coordinate ring. -/
noncomputable def standardAffinePolynomialEquiv (K : Type u) [CommRing K] :
    Polynomial (homogeneousPieces K 0) ≃+*
      Γ(scheme K, standardAffineOpen K) :=
  (polynomialAwayAlgEquiv K).toRingEquiv.trans
    (Proj.basicOpenIsoAway (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2))
      (X_one_mem_degree_one K) Nat.zero_lt_one).commRingCatIsoToRingEquiv

/-- Under the polynomial presentation of the standard chart, the polynomial variable is the
affine coordinate `X₀ / X₁`. -/
@[simp]
lemma standardAffinePolynomialEquiv_X (K : Type u) [CommRing K] :
    standardAffinePolynomialEquiv K Polynomial.X = affineCoordinate K := by
  change (Proj.basicOpenIsoAway (homogeneousPieces K) (MvPolynomial.X (1 : Fin 2))
      (X_one_mem_degree_one K) Nat.zero_lt_one).hom
        (polynomialAwayAlgEquiv K Polynomial.X) = _
  have hX : polynomialAwayAlgEquiv K Polynomial.X = t K := by
    simp [polynomialAwayAlgEquiv]
  rw [hX]
  congr 1



/-- The standard chart `D₊(X₁)` is affine. -/
lemma isAffineOpen_standardAffineOpen (K : Type u) [CommRing K] :
    IsAffineOpen (standardAffineOpen K) :=
  Proj.isAffineOpen_basicOpen (𝒜 := homogeneousPieces K)
    (f := MvPolynomial.X (1 : Fin 2))
    (f_deg := X_one_mem_degree_one K) (hm := Nat.zero_lt_one)

/-- The two standard affine charts cover the projective line. -/
lemma standardAffineOpen_sup_infinityAffineOpen_eq_top
    (K : Type u) [CommRing K] :
    standardAffineOpen K ⊔ infinityAffineOpen K = ⊤ := by
  have hcover : ⨆ i : Fin 2,
      Proj.basicOpen (homogeneousPieces K) (MvPolynomial.X i) = ⊤ :=
    Proj.iSup_basicOpen_eq_top' (homogeneousPieces K)
      (MvPolynomial.X : Fin 2 → MvPolynomial (Fin 2) K)
      (fun i ↦ ⟨1, MvPolynomial.isHomogeneous_X K i⟩)
      (adjoin_X_over_degreeZero K)
  apply top_unique
  rw [← hcover]
  apply iSup_le
  intro i
  fin_cases i
  · exact le_sup_right
  · exact le_sup_left



private noncomputable def tZero (K : Type u) [CommRing K] :
    HomogeneousLocalization.Away
      (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2)) :=
  HomogeneousLocalization.Away.mk (homogeneousPieces K) (X_zero_mem_degree_one K) 1
    (MvPolynomial.X (1 : Fin 2)) (by simpa using X_one_mem_degree_one K)

private lemma adjoin_tZero (K : Type u) [CommRing K] :
    Algebra.adjoin (homogeneousPieces K 0) ({tZero K} : Set
      (HomogeneousLocalization.Away
        (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2)))) = ⊤ := by
  let hgen := HomogeneousLocalization.Away.adjoin_mk_prod_pow_eq_top
    (X_zero_mem_degree_one K) (Fin 2)
    (MvPolynomial.X : Fin 2 → MvPolynomial (Fin 2) K)
    (adjoin_X_over_degreeZero K) (fun _ ↦ 1)
    (fun i ↦ MvPolynomial.isHomogeneous_X K i)
  rw [← top_le_iff, ← hgen, Algebra.adjoin_le_iff]
  rintro z ⟨a, ai, hai, hai_le, rfl⟩
  have hprod : (∏ i, MvPolynomial.X i ^ ai i) ∈ homogeneousPieces K (a • 1) := by
    rw [← hai]
    exact SetLike.prod_pow_mem_graded (homogeneousPieces K) (fun _ ↦ 1)
      MvPolynomial.X ai (fun i _ ↦ MvPolynomial.isHomogeneous_X K i)
  have h0 : ai 0 ≤ 1 := hai_le 0
  have h1 : ai 1 ≤ 1 := hai_le 1
  interval_cases h0a : ai 0 <;> interval_cases h1a : ai 1
  · have ha : a = 0 := by
      simpa [Fin.sum_univ_two, h0a, h1a] using hai.symm
    have heq : HomogeneousLocalization.Away.mk (homogeneousPieces K)
        (X_zero_mem_degree_one K) a (∏ i, MvPolynomial.X i ^ ai i) hprod = 1 := by
      apply HomogeneousLocalization.val_injective
      simp [HomogeneousLocalization.Away.val_mk, ha, h0a, h1a,
        Fin.prod_univ_two]
    rw [heq]
    exact one_mem _
  · have ha : a = 1 := by
      simpa [Fin.sum_univ_two, h0a, h1a] using hai.symm
    have heq : HomogeneousLocalization.Away.mk (homogeneousPieces K)
        (X_zero_mem_degree_one K) a (∏ i, MvPolynomial.X i ^ ai i) hprod = tZero K := by
      apply HomogeneousLocalization.val_injective
      rw [HomogeneousLocalization.Away.val_mk, tZero,
        HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk']
      apply IsLocalization.mk'_eq_of_eq
      simp [ha, h0a, h1a, Fin.prod_univ_two]
    rw [heq]
    exact Algebra.subset_adjoin (Set.mem_singleton (tZero K))
  · have ha : a = 1 := by
      simpa [Fin.sum_univ_two, h0a, h1a] using hai.symm
    have heq : HomogeneousLocalization.Away.mk (homogeneousPieces K)
        (X_zero_mem_degree_one K) a (∏ i, MvPolynomial.X i ^ ai i) hprod = 1 := by
      apply HomogeneousLocalization.val_injective
      have hX0 : MvPolynomial.X (0 : Fin 2) ∈
          Submonoid.powers (MvPolynomial.X (0 : Fin 2)) :=
        (Submonoid.mem_powers_iff
          (MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) K)
          (MvPolynomial.X (0 : Fin 2))).mpr ⟨1, by simp⟩
      rw [HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.val_one,
        Localization.mk_eq_mk']
      trans IsLocalization.mk' (Localization (Submonoid.powers (MvPolynomial.X (0 : Fin 2))))
        (MvPolynomial.X (0 : Fin 2)) ⟨MvPolynomial.X (0 : Fin 2), hX0⟩
      · apply IsLocalization.mk'_eq_of_eq
        simp [ha, h0a, h1a, Fin.prod_univ_two]
      · exact IsLocalization.mk'_self (S :=
          Localization (Submonoid.powers (MvPolynomial.X (0 : Fin 2)))) hX0
    rw [heq]
    exact one_mem _
  · have ha : a = 2 := by
      simpa [Fin.sum_univ_two, h0a, h1a] using hai.symm
    have heq : HomogeneousLocalization.Away.mk (homogeneousPieces K)
        (X_zero_mem_degree_one K) a (∏ i, MvPolynomial.X i ^ ai i) hprod = tZero K := by
      apply HomogeneousLocalization.val_injective
      rw [HomogeneousLocalization.Away.val_mk, tZero,
        HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk']
      apply IsLocalization.mk'_eq_of_eq
      simp [ha, h0a, h1a, Fin.prod_univ_two]
      ring
    rw [heq]
    exact Algebra.subset_adjoin (Set.mem_singleton (tZero K))

private def coordinateToPolynomialHomZero (K : Type u) [CommRing K] :
    MvPolynomial (Fin 2) K →+* Polynomial (homogeneousPieces K 0) :=
  MvPolynomial.eval₂Hom
    ((Polynomial.C : homogeneousPieces K 0 →+*
      Polynomial (homogeneousPieces K 0)).comp (degreeZeroRingEquiv K).toRingHom)
    (fun i : Fin 2 ↦ if i = 1 then
      (Polynomial.X : Polynomial (homogeneousPieces K 0)) else 1)

private lemma coordinateToPolynomialHomZero_X_zero (K : Type u) [CommRing K] :
    coordinateToPolynomialHomZero K (MvPolynomial.X (0 : Fin 2)) = 1 := by
  simp [coordinateToPolynomialHomZero]

private lemma coordinateToPolynomialHomZero_X_one (K : Type u) [CommRing K] :
    coordinateToPolynomialHomZero K (MvPolynomial.X (1 : Fin 2)) = Polynomial.X := by
  simp [coordinateToPolynomialHomZero]

private noncomputable def awayToPolynomialZero (K : Type u) [CommRing K] :
    HomogeneousLocalization.Away
        (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2)) →+*
      Polynomial (homogeneousPieces K 0) :=
  (Localization.awayLift (coordinateToPolynomialHomZero K)
      (MvPolynomial.X (0 : Fin 2)) (by
        change IsUnit (coordinateToPolynomialHomZero K (MvPolynomial.X (0 : Fin 2)))
        rw [coordinateToPolynomialHomZero_X_zero]
        exact isUnit_one)).comp
    (algebraMap
      (HomogeneousLocalization.Away
        (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2)))
      (Localization.Away (MvPolynomial.X (0 : Fin 2))))

private lemma awayToPolynomialZero_tZero (K : Type u) [CommRing K] :
    awayToPolynomialZero K (tZero K) = Polynomial.X := by
  simp only [awayToPolynomialZero, RingHom.comp_apply, tZero,
    HomogeneousLocalization.algebraMap_apply, HomogeneousLocalization.Away.val_mk]
  have hinv : coordinateToPolynomialHomZero K (MvPolynomial.X (0 : Fin 2)) *
      (1 : Polynomial (homogeneousPieces K 0)) = 1 := by
    rw [coordinateToPolynomialHomZero_X_zero]
    simp
  have h := Localization.awayLift_mk
    (A := Polynomial (homogeneousPieces K 0)) (coordinateToPolynomialHomZero K)
    (MvPolynomial.X (0 : Fin 2)) (MvPolynomial.X (1 : Fin 2)) 1 hinv 1
  simpa [coordinateToPolynomialHomZero] using h

private lemma awayToPolynomialZero_fromZero (K : Type u) [CommRing K]
    (r : homogeneousPieces K 0) :
    awayToPolynomialZero K
      (HomogeneousLocalization.fromZeroRingHom (homogeneousPieces K)
        (Submonoid.powers (MvPolynomial.X (0 : Fin 2))) r) = Polynomial.C r := by
  obtain ⟨s, rfl⟩ := (degreeZeroRingEquiv K).surjective r
  simp only [awayToPolynomialZero, RingHom.comp_apply,
    HomogeneousLocalization.algebraMap_apply, HomogeneousLocalization.fromZeroRingHom]
  have hinv : coordinateToPolynomialHomZero K (MvPolynomial.X (0 : Fin 2)) *
      (1 : Polynomial (homogeneousPieces K 0)) = 1 := by
    rw [coordinateToPolynomialHomZero_X_zero]
    simp
  have h := Localization.awayLift_mk
    (A := Polynomial (homogeneousPieces K 0)) (coordinateToPolynomialHomZero K)
    (MvPolynomial.X (0 : Fin 2)) (MvPolynomial.C s) 1 hinv 0
  convert h using 1
  · congr 1
  · simp [coordinateToPolynomialHomZero]

private noncomputable def awayToPolynomialZeroAlgHom (K : Type u) [CommRing K] :
    HomogeneousLocalization.Away
        (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2)) →ₐ[homogeneousPieces K 0]
      Polynomial (homogeneousPieces K 0) :=
  { awayToPolynomialZero K with
    commutes' := awayToPolynomialZero_fromZero K }

private lemma transcendental_tZero (K : Type u) [CommRing K] :
    Transcendental (homogeneousPieces K 0) (tZero K) := by
  rw [transcendental_iff_injective]
  intro p q hpq
  have h := congrArg (awayToPolynomialZeroAlgHom K) hpq
  have ht : (awayToPolynomialZeroAlgHom K) (tZero K) = Polynomial.X :=
    awayToPolynomialZero_tZero K
  calc
    p = Polynomial.aeval Polynomial.X p := (Polynomial.aeval_X_left_apply p).symm
    _ = Polynomial.aeval ((awayToPolynomialZeroAlgHom K) (tZero K)) p := by rw [ht]
    _ = (awayToPolynomialZeroAlgHom K) (Polynomial.aeval (tZero K) p) :=
      AlgHom.congr_fun
        (Polynomial.aeval_algHom (awayToPolynomialZeroAlgHom K) (tZero K)) p
    _ = (awayToPolynomialZeroAlgHom K) (Polynomial.aeval (tZero K) q) := h
    _ = Polynomial.aeval ((awayToPolynomialZeroAlgHom K) (tZero K)) q :=
      (AlgHom.congr_fun
        (Polynomial.aeval_algHom (awayToPolynomialZeroAlgHom K) (tZero K)) q).symm
    _ = Polynomial.aeval Polynomial.X q := by rw [ht]
    _ = q := Polynomial.aeval_X_left_apply q

private noncomputable def polynomialAwayZeroAlgEquiv (K : Type u) [CommRing K] :
    Polynomial (homogeneousPieces K 0) ≃ₐ[homogeneousPieces K 0]
      HomogeneousLocalization.Away
        (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2)) :=
  (Polynomial.algEquivOfTranscendental (homogeneousPieces K 0) (tZero K)
    (transcendental_tZero K)).trans
      ((Subalgebra.equivOfEq _ _ (adjoin_tZero K)).trans Subalgebra.topEquiv)

/-- The affine chart containing infinity is a polynomial line over the degree-zero homogeneous
coordinate ring. -/
noncomputable def infinityAffinePolynomialEquiv (K : Type u) [CommRing K] :
    Polynomial (homogeneousPieces K 0) ≃+*
      Γ(scheme K, infinityAffineOpen K) :=
  (polynomialAwayZeroAlgEquiv K).toRingEquiv.trans
    (Proj.basicOpenIsoAway (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2))
      (X_zero_mem_degree_one K) Nat.zero_lt_one).commRingCatIsoToRingEquiv

/-- Under the polynomial presentation of the chart at infinity, the polynomial variable is the
inverse affine coordinate `X₁ / X₀`. -/
@[simp]
lemma infinityAffinePolynomialEquiv_X (K : Type u) [CommRing K] :
    infinityAffinePolynomialEquiv K Polynomial.X = inverseAffineCoordinate K := by
  change (Proj.basicOpenIsoAway (homogeneousPieces K) (MvPolynomial.X (0 : Fin 2))
      (X_zero_mem_degree_one K) Nat.zero_lt_one).hom
        (polynomialAwayZeroAlgEquiv K Polynomial.X) = _
  have hX : polynomialAwayZeroAlgEquiv K Polynomial.X = tZero K := by
    simp [polynomialAwayZeroAlgEquiv]
  rw [hX]
  congr 1



/-- The chart `D₊(X₀)` containing infinity is affine. -/
lemma isAffineOpen_infinityAffineOpen (K : Type u) [CommRing K] :
    IsAffineOpen (infinityAffineOpen K) :=
  Proj.isAffineOpen_basicOpen (𝒜 := homogeneousPieces K)
    (f := MvPolynomial.X (0 : Fin 2))
    (f_deg := X_zero_mem_degree_one K) (hm := Nat.zero_lt_one)


end MazurTransfer.Order13MixedQuadraticProjectiveLineOriginal20261019
#print axioms MazurTransfer.Order13MixedQuadraticProjectiveLineOriginal20261019.standardAffinePolynomialEquiv
#print axioms MazurTransfer.Order13MixedQuadraticProjectiveLineOriginal20261019.infinityAffinePolynomialEquiv
#print axioms MazurTransfer.Order13MixedQuadraticProjectiveLineOriginal20261019.standardAffineOpen_sup_infinityAffineOpen_eq_top
#print axioms MazurTransfer.Order13MixedQuadraticProjectiveLineOriginal20261019.isAffineOpen_standardAffineOpen
#print axioms MazurTransfer.Order13MixedQuadraticProjectiveLineOriginal20261019.isAffineOpen_infinityAffineOpen

end


