-- Prove2me | Definitions.Def_MazurTransfer_Order13MixedOriginalActualFiniteMapDataAndArbitraryDegreePowersData20261019
-- name    : MazurTransfer_Order13MixedOriginalActualFiniteMapDataAndArbitraryDegreePowersData20261019
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-19T07:08:24.724799+00:00
-- url     : https://prove2.me/theorems/c2037d43-afac-42bd-98f9-98defb49bac8
-- title:
--   Actual original finite-map data and arbitrary degree powers
-- statement:
--   The original whole-curve finite-map datum of degree three, with its exact original zero section, actual global-section polynomial bases, all positive powers and arbitrarily large degree bounds. Named downstream consumer: actual dyadic Picard representability.
-- source:
--   MazurTheorem original mixed single-section parameter algebras and reciprocal recovery, by Vas and contributors; exact official Anthropic FLT quotient/base-change bridge at pin 6e837e75355538c7f80bab5b956861e86c4eacc2; Apache-2.0. Original per-file attribution retained.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the exact original global-section parameters and bases on
the actual two affine opens, their reciprocal product and basic opens,
the original whole degree-three FiniteMapData, and all its positive powers.
Named downstream consumer: actual dyadic arbitrarily large finite-map data
and compatible integral Picard representation of the same curve and section.
Original per-file headers and attribution are retained below.
-/
import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData
import Definitions.Def_MazurTransfer_Order13MixedOriginalActualSingleSectionAffineComplementsAndCoverData20261019
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: transport the actual finite parameter map to the inverse affine
chart, retaining the original inclusion and structural morphism.
Named downstream consumer: the second chart of single-section FiniteMapData for integral Picard.
-/

noncomputable section
universe u
namespace MazurTransfer.Order13MixedInverseParameterFiniteAlgebra
open CategoryTheory AlgebraicGeometry Polynomial
open Order13DyadicMixedQuadraticCharts Order13MixedQuadraticOverlapCoordinates
open Order13MixedQuadraticGluedCurve
open MazurTorsion.XOneThirteenAffineCurve
open Order13SingleSectionFiniteAlgebra (ordinaryParameterLocalization)
variable (R : Type u) [CommRing R] [IsDomain R]

def inverseFiniteAffineSchemeToBase : inverseFiniteAffineScheme R ⟶ Spec (.of R) :=
  inverseFiniteAffineMap R ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R))

def candidateToReciprocalPatch  : candidateAlgebra R →ₐ[R]
    Order13MixedInverseParameterPositiveReciprocalPatch.PatchRing R :=
  (recoveredReciprocalPatchEquiv R).symm.toAlgHom.comp
    (IsScalarTower.toAlgHom R (candidateAlgebra R) (infinityLocalization R))

theorem ordinaryParameterToFiniteAffineScheme_base :
    ordinaryParameterToFiniteAffineScheme R ≫ inverseFiniteAffineSchemeToBase R =
      ordinaryParameterCurveMap R ≫ curveToBase R := by
  rw [ordinaryParameterCurveMap_base, ordinaryParameterToFiniteAffineScheme_eq_Spec]
  unfold inverseFiniteAffineSchemeToBase inverseFiniteAffineMap
  dsimp only [inverseFiniteAffineScheme]
  rw [← Spec.map_comp, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro c
  exact (inclusion R).commutes c

theorem reciprocalToFiniteAffineScheme_base  :
    reciprocalToFiniteAffineScheme R ≫ inverseFiniteAffineSchemeToBase R =
      positiveReciprocalCurveMap R ≫ curveToBase R := by
  rw [positiveReciprocalCurveMap_base, ← reciprocalFiniteChartRingHom_Spec]
  unfold inverseFiniteAffineSchemeToBase inverseFiniteAffineMap
  dsimp only [inverseFiniteAffineScheme]
  rw [← Spec.map_comp, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro c
  exact (candidateToReciprocalPatch R).commutes c

theorem finiteModelToCurve_base  :
    finiteModelToCurve R ≫ curveToBase R = inverseFiniteAffineSchemeToBase R := by
  apply (finiteSchemeOpenCover R).hom_ext
  intro b
  cases b with
  | true =>
    change ordinaryParameterToFiniteAffineScheme R ≫ finiteModelToCurve R ≫ curveToBase R =
      ordinaryParameterToFiniteAffineScheme R ≫ inverseFiniteAffineSchemeToBase R
    rw [← Category.assoc, ordinaryParameterToFiniteAffineScheme_finiteModelToCurve,
      ordinaryParameterToFiniteAffineScheme_base]
  | false =>
    change reciprocalToFiniteAffineScheme R ≫ finiteModelToCurve R ≫ curveToBase R =
      reciprocalToFiniteAffineScheme R ≫ inverseFiniteAffineSchemeToBase R
    rw [← Category.assoc, reciprocalToFiniteAffineScheme_finiteModelToCurve,
      reciprocalToFiniteAffineScheme_base]

def inverseChartFiniteMap  :
    (inverseChartOpen R).toScheme ⟶ Spec (.of (Polynomial R)) :=
  (finiteModelInverseChartIso R).inv ≫ inverseFiniteAffineMap R

theorem inverseChartFiniteMap_isFinite  :
    IsFinite (inverseChartFiniteMap R) := by
  let := inverseFiniteAffineMap_isFinite R 
  unfold inverseChartFiniteMap
  infer_instance

theorem inverseChartFiniteMap_base  :
    inverseChartFiniteMap R ≫
      Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R)) =
    (inverseChartOpen R).ι ≫ curveToBase R := by
  change (finiteModelInverseChartIso R).inv ≫ inverseFiniteAffineSchemeToBase R = _
  rw [← finiteModelToCurve_base R, ← Category.assoc,
    finiteModelInverseChartIso_inv_comp]

end MazurTransfer.Order13MixedInverseParameterFiniteAlgebra
#print axioms MazurTransfer.Order13MixedInverseParameterFiniteAlgebra.finiteModelToCurve_base
#print axioms MazurTransfer.Order13MixedInverseParameterFiniteAlgebra.inverseChartFiniteMap_isFinite
#print axioms MazurTransfer.Order13MixedInverseParameterFiniteAlgebra.inverseChartFiniteMap_base

end

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the exact global section ring of the actual inverse single-section
chart is identified with the constructed finite coordinate algebra.
Named downstream consumer: transport its parameter and level-set basis into
single-section FiniteMapData. Compatibility with the structural R-action
and tensor quotients is a separate obligation.
-/

noncomputable section
universe u
namespace MazurTransfer.Order13MixedInverseParameterFiniteAlgebra
open CategoryTheory AlgebraicGeometry
open Order13DyadicMixedQuadraticCharts Order13MixedQuadraticOverlapCoordinates
open Order13MixedQuadraticGluedCurve

variable (R : Type u) [CommRing R] [IsDomain R]

def inverseChartSectionsRingIso  :
    Γ(curveScheme R, inverseChartOpen R) ≅ CommRingCat.of (candidateAlgebra R) :=
  (inverseChartOpen R).topIso.symm ≪≫
    Scheme.Γ.mapIso (finiteModelInverseChartIso R).op ≪≫
      Scheme.ΓSpecIso (.of (candidateAlgebra R))

def inverseChartSectionsRingEquiv  :
    Γ(curveScheme R, inverseChartOpen R) ≃+* candidateAlgebra R :=
  (inverseChartSectionsRingIso R).commRingCatIsoToRingEquiv

end MazurTransfer.Order13MixedInverseParameterFiniteAlgebra
#print axioms MazurTransfer.Order13MixedInverseParameterFiniteAlgebra.inverseChartSectionsRingEquiv

end

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the inverse global section ring comparison retains the actual
structural coefficient map from R. Named downstream consumer: the R-algebra
comparison and tensor-quotient level-set transport for FiniteMapData.
-/

noncomputable section
universe u
namespace MazurTransfer.Order13MixedInverseParameterFiniteAlgebra
open CategoryTheory AlgebraicGeometry Opposite
open Order13DyadicMixedQuadraticCharts Order13MixedQuadraticOverlapCoordinates
open Order13MixedQuadraticGluedCurve

variable (R : Type u) [CommRing R] [IsDomain R]

theorem inverseChart_coefficient_map_topIso :
    (curveToBase R).appLE ⊤ (inverseChartOpen R) (by intro x hx; exact trivial) ≫
      (inverseChartOpen R).topIso.inv =
      ((inverseChartOpen R).ι ≫ curveToBase R).appTop := by
  exact (curveToBase R).appLE_map (by intro x hx; exact trivial)
    (eqToHom (inverseChartOpen R).ι_image_top).op

theorem inverseChartSectionsRingIso_coefficients  :
    (Scheme.ΓSpecIso (.of R)).inv ≫
      (curveToBase R).appLE ⊤ (inverseChartOpen R) (by intro x hx; exact trivial) ≫
      (inverseChartSectionsRingIso R).hom =
    CommRingCat.ofHom (algebraMap R (candidateAlgebra R)) := by
  have hb : (finiteModelInverseChartIso R).hom ≫
      (inverseChartOpen R).ι ≫ curveToBase R =
      Spec.map (CommRingCat.ofHom (algebraMap R (candidateAlgebra R))) := by
    rw [← Category.assoc, finiteModelInverseChartIso_hom_ι, finiteModelToCurve_base]
    unfold inverseFiniteAffineSchemeToBase inverseFiniteAffineMap
    change Spec.map (CommRingCat.ofHom (algebraMap (Polynomial R) (candidateAlgebra R))) ≫
      Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R)) =
      Spec.map (CommRingCat.ofHom (algebraMap R (candidateAlgebra R)))
    rw [← Spec.map_comp]
    rfl
  change (Scheme.ΓSpecIso (.of R)).inv ≫
    (curveToBase R).appLE ⊤ (inverseChartOpen R) (by intro x hx; exact trivial) ≫
    (inverseChartOpen R).topIso.inv ≫
    (finiteModelInverseChartIso R).hom.appTop ≫
    (Scheme.ΓSpecIso (.of (candidateAlgebra R))).hom = _
  have H := congrArg (fun k => (Scheme.ΓSpecIso (.of R)).inv ≫ k ≫
      (finiteModelInverseChartIso R).hom.appTop ≫
      (Scheme.ΓSpecIso (.of (candidateAlgebra R))).hom)
    (inverseChart_coefficient_map_topIso R)
  calc
    _ = (Scheme.ΓSpecIso (.of R)).inv ≫
        ((inverseChartOpen R).ι ≫ curveToBase R).appTop ≫
        (finiteModelInverseChartIso R).hom.appTop ≫
        (Scheme.ΓSpecIso (.of (candidateAlgebra R))).hom := by
      simpa only [Category.assoc] using H
    _ = (Scheme.ΓSpecIso (.of R)).inv ≫
        (Spec.map (CommRingCat.ofHom (algebraMap R (candidateAlgebra R)))).appTop ≫
        (Scheme.ΓSpecIso (.of (candidateAlgebra R))).hom := by
      have H2 := congrArg (fun k => (Scheme.ΓSpecIso (.of R)).inv ≫ k ≫
        (Scheme.ΓSpecIso (.of (candidateAlgebra R))).hom)
        (congrArg Scheme.Hom.appTop hb)
      dsimp only [inverseFiniteAffineScheme] at H2 ⊢
      simp only [Scheme.Hom.comp_appTop, Category.assoc] at H2
      convert H2 using 1
      exact congrArg (fun k => (Scheme.ΓSpecIso (.of R)).inv ≫ k ≫
        (finiteModelInverseChartIso R).hom.appTop ≫
        (Scheme.ΓSpecIso (.of (candidateAlgebra R))).hom)
        (Scheme.Hom.comp_appTop (inverseChartOpen R).ι (curveToBase R))
    _ = _ := by simp

def inverseChartSectionsAlgEquiv  :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom (curveToBase R) (inverseChartOpen R)
    Γ(curveScheme R, inverseChartOpen R) ≃ₐ[R] candidateAlgebra R := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom (curveToBase R) (inverseChartOpen R)
  refine { (inverseChartSectionsRingEquiv R) with commutes' := ?_ }
  intro r
  exact congrArg (fun f : CommRingCat.of R ⟶ CommRingCat.of (candidateAlgebra R) => f.hom r)
    (inverseChartSectionsRingIso_coefficients R)

def inverseChartParameter  :
    Γ(curveScheme R, inverseChartOpen R) :=
  (inverseChartSectionsRingEquiv R).symm (sElement R)

end MazurTransfer.Order13MixedInverseParameterFiniteAlgebra
#print axioms MazurTransfer.Order13MixedInverseParameterFiniteAlgebra.inverseChartSectionsRingIso_coefficients
#print axioms MazurTransfer.Order13MixedInverseParameterFiniteAlgebra.inverseChartSectionsAlgEquiv

end

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: transport the actual rank-three polynomial basis to the
actual inverse-chart ring using the original structural R-algebra action.
Named downstream consumer: the evaluated tensor-quotient level-set basis in
single-section FiniteMapData. The inverse chart is actual; whole FiniteMapData is a separate obligation.
-/

noncomputable section
universe u
namespace MazurTransfer.Order13MixedInverseParameterFiniteAlgebra
open AlgebraicGeometry Polynomial Module
open Order13DyadicMixedQuadraticCharts Order13MixedQuadraticOverlapCoordinates
open Order13MixedQuadraticGluedCurve

variable (R : Type u) [CommRing R] [IsDomain R]

def inverseChartPolynomialAlgEquiv  :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom (curveToBase R) (inverseChartOpen R)
    letI : Algebra (Polynomial R) Γ(curveScheme R, inverseChartOpen R) :=
      (aeval (inverseChartParameter R)).toRingHom.toAlgebra
    Γ(curveScheme R, inverseChartOpen R) ≃ₐ[Polynomial R] candidateAlgebra R := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom (curveToBase R) (inverseChartOpen R)
  letI : Algebra (Polynomial R) Γ(curveScheme R, inverseChartOpen R) :=
    (aeval (inverseChartParameter R)).toRingHom.toAlgebra
  let E := inverseChartSectionsAlgEquiv R
  refine { E.toRingEquiv with commutes' := ?_ }
  intro P
  change E (aeval (inverseChartParameter R) P) =
    algebraMap (Polynomial R) (candidateAlgebra R) P
  rw [← aeval_algHom_apply E]
  have hf : E (inverseChartParameter R) = sElement R :=
    (inverseChartSectionsRingEquiv R).apply_symm_apply _
  rw [hf]
  exact (eval_unique (IsScalarTower.toAlgHom R (Polynomial R) (candidateAlgebra R)) P).symm

def inverseChartPolynomialBasis  :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom (curveToBase R) (inverseChartOpen R)
    letI : Algebra (Polynomial R) Γ(curveScheme R, inverseChartOpen R) :=
      (aeval (inverseChartParameter R)).toRingHom.toAlgebra
    Basis (Fin 3) (Polynomial R) Γ(curveScheme R, inverseChartOpen R) := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom (curveToBase R) (inverseChartOpen R)
  letI : Algebra (Polynomial R) Γ(curveScheme R, inverseChartOpen R) :=
    (aeval (inverseChartParameter R)).toRingHom.toAlgebra
  exact (candidateBasis R).map
    (inverseChartPolynomialAlgEquiv R).symm.toLinearEquiv

theorem inverseChartPolynomialFinrank  :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom (curveToBase R) (inverseChartOpen R)
    letI : Algebra (Polynomial R) Γ(curveScheme R, inverseChartOpen R) :=
      (aeval (inverseChartParameter R)).toRingHom.toAlgebra
    Module.finrank (Polynomial R) Γ(curveScheme R, inverseChartOpen R) = 3 := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom (curveToBase R) (inverseChartOpen R)
  letI : Algebra (Polynomial R) Γ(curveScheme R, inverseChartOpen R) :=
    (aeval (inverseChartParameter R)).toRingHom.toAlgebra
  simpa using Module.finrank_eq_card_basis (inverseChartPolynomialBasis R)

end MazurTransfer.Order13MixedInverseParameterFiniteAlgebra
#print axioms MazurTransfer.Order13MixedInverseParameterFiniteAlgebra.inverseChartPolynomialBasis
#print axioms MazurTransfer.Order13MixedInverseParameterFiniteAlgebra.inverseChartPolynomialFinrank

end

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Reuses the complete checked official Anthropic FLT levelSetEquiv at pin
6e837e75355538c7f80bab5b956861e86c4eacc2, with original attribution retained.
Design boundary: the actual complement parameter is finite and its evaluated
tensor quotients are free of rank three for the actual structural R-action.
Named downstream consumer: finite_f and levelSet_free in single-section
FiniteMapData. Whole FiniteMapData and large degrees remain separate obligations.
-/

noncomputable section
universe u
namespace MazurTransfer.Order13MixedInverseParameterFiniteAlgebra
open AlgebraicGeometry Polynomial Module
open scoped TensorProduct
open Order13DyadicMixedQuadraticCharts Order13MixedQuadraticOverlapCoordinates
open Order13MixedQuadraticGluedCurve

variable (R : Type u) [CommRing R] [IsDomain R]

theorem inverseChart_parameter_finite  :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom (curveToBase R) (inverseChartOpen R)
    (aeval (inverseChartParameter R) : Polynomial R →ₐ[R]
      Γ(curveScheme R, inverseChartOpen R)).toRingHom.Finite := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom (curveToBase R) (inverseChartOpen R)
  letI : Algebra (Polynomial R) Γ(curveScheme R, inverseChartOpen R) :=
    (aeval (inverseChartParameter R)).toRingHom.toAlgebra
  exact Module.Finite.of_basis (inverseChartPolynomialBasis R)

variable (S : Type u) [CommRing S] [Algebra R S]

def inverseChartLevelSetBasis  (s : S) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom (curveToBase R) (inverseChartOpen R)
    Basis (Fin 3) S (S ⊗[R] Γ(curveScheme R, inverseChartOpen R) ⧸
      Ideal.span {(1 : S) ⊗ₜ[R] inverseChartParameter R -
        s ⊗ₜ[R] (1 : Γ(curveScheme R, inverseChartOpen R))}) := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom (curveToBase R) (inverseChartOpen R)
  letI : Algebra (Polynomial R) Γ(curveScheme R, inverseChartOpen R) :=
    (aeval (inverseChartParameter R)).toRingHom.toAlgebra
  letI : IsScalarTower R (Polynomial R) Γ(curveScheme R, inverseChartOpen R) :=
    IsScalarTower.of_algebraMap_eq fun r => by
      change algebraMap R Γ(curveScheme R, inverseChartOpen R) r =
        aeval (inverseChartParameter R) (C r)
      rw [aeval_C]
  letI : Algebra (Polynomial R) S := (aeval s).toRingHom.toAlgebra
  letI : IsScalarTower R (Polynomial R) S := IsScalarTower.of_algebraMap_eq fun r => by
    change algebraMap R S r = aeval s (C r)
    rw [aeval_C]
  let e := P2MW.S_Algebra_levelSet_finite_free_finrank_of_flat_polynomial.U4b.levelSetEquiv
    R Γ(curveScheme R, inverseChartOpen R) S (inverseChartParameter R) s
      (by change aeval (inverseChartParameter R) X = _; exact aeval_X _)
      (by change aeval s X = s; exact aeval_X s)
  exact ((inverseChartPolynomialBasis R).baseChange S).map e.symm.toLinearEquiv

theorem inverseChartLevelSet_finite_free_finrank 
    [Nontrivial S] (s : S) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom (curveToBase R) (inverseChartOpen R)
    let Q := S ⊗[R] Γ(curveScheme R, inverseChartOpen R) ⧸
      Ideal.span {(1 : S) ⊗ₜ[R] inverseChartParameter R -
        s ⊗ₜ[R] (1 : Γ(curveScheme R, inverseChartOpen R))}
    Module.Finite S Q ∧ Module.Free S Q ∧ Module.finrank S Q = 3 := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom (curveToBase R) (inverseChartOpen R)
  let b := inverseChartLevelSetBasis R S s
  exact ⟨Module.Finite.of_basis b, Module.Free.of_basis b, by
    simpa using Module.finrank_eq_card_basis b⟩

end MazurTransfer.Order13MixedInverseParameterFiniteAlgebra
#print axioms MazurTransfer.Order13MixedInverseParameterFiniteAlgebra.inverseChart_parameter_finite
#print axioms MazurTransfer.Order13MixedInverseParameterFiniteAlgebra.inverseChartLevelSet_finite_free_finrank

end

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: transport the actual finite parameter map to the affine
complement, retaining the original inclusion and structural morphism.
Named downstream consumer: single-section FiniteMapData for integral Picard.
-/

noncomputable section
universe u
namespace MazurTransfer.Order13MixedSingleSectionFiniteAlgebra
open CategoryTheory AlgebraicGeometry Polynomial
open Order13DyadicMixedQuadraticCharts Order13MixedQuadraticGluedCurve
open Order13MixedActualPositiveInfinityComplement
variable (R : Type u) [CommRing R] [IsDomain R]

theorem reciprocalToFiniteAffineScheme_base  :
    reciprocalToFiniteAffineScheme R ≫ finiteAffineSchemeToBase R =
      reciprocalPatchChartMap R ≫ curveToBase R := by
  rw [reciprocalPatchChartMap, Category.assoc, reciprocalChartMap_curveToBase]
  unfold reciprocalToFiniteAffineScheme reciprocalFiniteChartIso candidateInfinityChartMap
    finiteAffineSchemeToBase finiteAffineMap reciprocalPatchInclusion reciprocalToBase
  change (Spec.map (CommRingCat.ofHom (recoveredReciprocalPatchEquiv R).symm.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap (candidateAlgebra R) (infinityLocalization R)))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap (Polynomial R) (candidateAlgebra R))) ≫
        Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R)) = _
  simp only [← Spec.map_comp]
  have hrhs := (Spec.map_comp
    (CommRingCat.ofHom (algebraMap R (reciprocalCoordinateRing R)))
    (CommRingCat.ofHom (algebraMap (reciprocalCoordinateRing R)
      (Order13MixedSingleSectionReciprocalPatch.PatchRing R)))).symm
  apply Eq.trans ?_ hrhs.symm
  change Spec.map _ = Spec.map _
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  change candidateToReciprocalPatch R (algebraMap R (candidateAlgebra R) r) =
    algebraMap R (Order13MixedSingleSectionReciprocalPatch.PatchRing R) r
  exact (candidateToReciprocalPatch R).commutes r

theorem finiteModelToCurve_base  :
    finiteModelToCurve R ≫ curveToBase R = finiteAffineSchemeToBase R := by
  apply (finiteSchemeOpenCover R).hom_ext
  intro b
  cases b with
  | true =>
    change ordinaryToFiniteAffineScheme R ≫ finiteModelToCurve R ≫ curveToBase R =
      ordinaryToFiniteAffineScheme R ≫ finiteAffineSchemeToBase R
    rw [← Category.assoc, ordinaryToFiniteAffineScheme_finiteModelToCurve,
      ordinaryChartMap_curveToBase, ordinaryToFiniteAffineScheme_base]
  | false =>
    change reciprocalToFiniteAffineScheme R ≫ finiteModelToCurve R ≫ curveToBase R =
      reciprocalToFiniteAffineScheme R ≫ finiteAffineSchemeToBase R
    rw [← Category.assoc, reciprocalToFiniteAffineScheme_finiteModelToCurve,
      reciprocalToFiniteAffineScheme_base]

def sectionComplementFiniteMap  :
    (sectionComplementOpen R).toScheme ⟶ Spec (.of (Polynomial R)) :=
  (finiteModelSectionComplementIso R).inv ≫ finiteAffineMap R

theorem sectionComplementFiniteMap_isFinite  :
    IsFinite (sectionComplementFiniteMap R) := by
  let := finiteAffineMap_isFinite R 
  unfold sectionComplementFiniteMap
  infer_instance

theorem sectionComplementFiniteMap_base  :
    sectionComplementFiniteMap R ≫
      Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R)) =
    (sectionComplementOpen R).ι ≫ curveToBase R := by
  change (finiteModelSectionComplementIso R).inv ≫ finiteAffineSchemeToBase R = _
  rw [← finiteModelToCurve_base R, ← Category.assoc,
    finiteModelSectionComplementIso_inv_comp]

end MazurTransfer.Order13MixedSingleSectionFiniteAlgebra
#print axioms MazurTransfer.Order13MixedSingleSectionFiniteAlgebra.finiteModelToCurve_base
#print axioms MazurTransfer.Order13MixedSingleSectionFiniteAlgebra.sectionComplementFiniteMap_isFinite
#print axioms MazurTransfer.Order13MixedSingleSectionFiniteAlgebra.sectionComplementFiniteMap_base

end

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the exact global section ring of the actual single-section
complement is identified with the constructed finite coordinate algebra.
Named downstream consumer: transport its parameter and level-set basis into
single-section FiniteMapData. Compatibility with the structural R-action
and tensor quotients is a separate obligation.
-/

noncomputable section
universe u
namespace MazurTransfer.Order13MixedSingleSectionFiniteAlgebra
open CategoryTheory AlgebraicGeometry
open Order13DyadicMixedQuadraticCharts Order13MixedQuadraticGluedCurve
open Order13MixedActualPositiveInfinityComplement
variable (R : Type u) [CommRing R] [IsDomain R]

def sectionComplementSectionsRingIso  :
    Γ(curveScheme R, sectionComplementOpen R) ≅ CommRingCat.of (candidateAlgebra R) :=
  (sectionComplementOpen R).topIso.symm ≪≫
    Scheme.Γ.mapIso (finiteModelSectionComplementIso R).op ≪≫
      Scheme.ΓSpecIso (.of (candidateAlgebra R))

def sectionComplementSectionsRingEquiv  :
    Γ(curveScheme R, sectionComplementOpen R) ≃+* candidateAlgebra R :=
  (sectionComplementSectionsRingIso R).commRingCatIsoToRingEquiv

end MazurTransfer.Order13MixedSingleSectionFiniteAlgebra
#print axioms MazurTransfer.Order13MixedSingleSectionFiniteAlgebra.sectionComplementSectionsRingEquiv

end

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the global section ring comparison retains the actual
structural coefficient map from R. Named downstream consumer: the R-algebra
comparison and tensor-quotient level-set transport for FiniteMapData.
-/

noncomputable section
universe u
namespace MazurTransfer.Order13MixedSingleSectionFiniteAlgebra
open CategoryTheory AlgebraicGeometry Opposite
open Order13DyadicMixedQuadraticCharts Order13MixedQuadraticGluedCurve
open Order13MixedActualPositiveInfinityComplement
variable (R : Type u) [CommRing R] [IsDomain R]

theorem sectionComplement_coefficient_map_topIso :
    (curveToBase R).appLE ⊤ (sectionComplementOpen R) (by intro x hx; exact trivial) ≫
      (sectionComplementOpen R).topIso.inv =
      ((sectionComplementOpen R).ι ≫ curveToBase R).appTop := by
  exact (curveToBase R).appLE_map (by intro x hx; exact trivial)
    (eqToHom (sectionComplementOpen R).ι_image_top).op

theorem sectionComplementSectionsRingIso_coefficients  :
    (Scheme.ΓSpecIso (.of R)).inv ≫
      (curveToBase R).appLE ⊤ (sectionComplementOpen R) (by intro x hx; exact trivial) ≫
      (sectionComplementSectionsRingIso R).hom =
    CommRingCat.ofHom (algebraMap R (candidateAlgebra R)) := by
  have hb : (finiteModelSectionComplementIso R).hom ≫
      (sectionComplementOpen R).ι ≫ curveToBase R =
      Spec.map (CommRingCat.ofHom (algebraMap R (candidateAlgebra R))) := by
    rw [← Category.assoc, finiteModelSectionComplementIso_hom_ι, finiteModelToCurve_base]
    unfold finiteAffineSchemeToBase finiteAffineMap
    change Spec.map (CommRingCat.ofHom (algebraMap (Polynomial R) (candidateAlgebra R))) ≫
      Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R)) =
      Spec.map (CommRingCat.ofHom (algebraMap R (candidateAlgebra R)))
    rw [← Spec.map_comp]
    rfl
  change (Scheme.ΓSpecIso (.of R)).inv ≫
    (curveToBase R).appLE ⊤ (sectionComplementOpen R) (by intro x hx; exact trivial) ≫
    (sectionComplementOpen R).topIso.inv ≫
    (finiteModelSectionComplementIso R).hom.appTop ≫
    (Scheme.ΓSpecIso (.of (candidateAlgebra R))).hom = _
  have H := congrArg (fun k => (Scheme.ΓSpecIso (.of R)).inv ≫ k ≫
      (finiteModelSectionComplementIso R).hom.appTop ≫
      (Scheme.ΓSpecIso (.of (candidateAlgebra R))).hom)
    (sectionComplement_coefficient_map_topIso R)
  calc
    _ = (Scheme.ΓSpecIso (.of R)).inv ≫
        ((sectionComplementOpen R).ι ≫ curveToBase R).appTop ≫
        (finiteModelSectionComplementIso R).hom.appTop ≫
        (Scheme.ΓSpecIso (.of (candidateAlgebra R))).hom := by
      simpa only [Category.assoc] using H
    _ = (Scheme.ΓSpecIso (.of R)).inv ≫
        (Spec.map (CommRingCat.ofHom (algebraMap R (candidateAlgebra R)))).appTop ≫
        (Scheme.ΓSpecIso (.of (candidateAlgebra R))).hom := by
      have H2 := congrArg (fun k => (Scheme.ΓSpecIso (.of R)).inv ≫ k ≫
        (Scheme.ΓSpecIso (.of (candidateAlgebra R))).hom)
        (congrArg Scheme.Hom.appTop hb)
      dsimp only [finiteAffineScheme] at H2 ⊢
      simp only [Scheme.Hom.comp_appTop, Category.assoc] at H2
      convert H2 using 1
      exact congrArg (fun k => (Scheme.ΓSpecIso (.of R)).inv ≫ k ≫
        (finiteModelSectionComplementIso R).hom.appTop ≫
        (Scheme.ΓSpecIso (.of (candidateAlgebra R))).hom)
        (Scheme.Hom.comp_appTop (sectionComplementOpen R).ι (curveToBase R))
    _ = _ := by simp

def sectionComplementSectionsAlgEquiv  :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom (curveToBase R) (sectionComplementOpen R)
    Γ(curveScheme R, sectionComplementOpen R) ≃ₐ[R] candidateAlgebra R := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom (curveToBase R) (sectionComplementOpen R)
  refine { (sectionComplementSectionsRingEquiv R) with commutes' := ?_ }
  intro r
  exact congrArg (fun f : CommRingCat.of R ⟶ CommRingCat.of (candidateAlgebra R) => f.hom r)
    (sectionComplementSectionsRingIso_coefficients R)

def sectionComplementParameter  :
    Γ(curveScheme R, sectionComplementOpen R) :=
  (sectionComplementSectionsRingEquiv R).symm (parameterElement R)

end MazurTransfer.Order13MixedSingleSectionFiniteAlgebra
#print axioms MazurTransfer.Order13MixedSingleSectionFiniteAlgebra.sectionComplementSectionsRingIso_coefficients
#print axioms MazurTransfer.Order13MixedSingleSectionFiniteAlgebra.sectionComplementSectionsAlgEquiv

end

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: transport the actual rank-three polynomial basis to the
actual section-complement ring using the original structural R-algebra action.
Named downstream consumer: the evaluated tensor-quotient level-set basis in
single-section FiniteMapData. No second chart or whole FiniteMapData is asserted.
-/

noncomputable section
universe u
namespace MazurTransfer.Order13MixedSingleSectionFiniteAlgebra
open AlgebraicGeometry Polynomial Module
open Order13DyadicMixedQuadraticCharts Order13MixedQuadraticGluedCurve
open Order13MixedActualPositiveInfinityComplement
variable (R : Type u) [CommRing R] [IsDomain R]

def sectionComplementPolynomialAlgEquiv  :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom (curveToBase R) (sectionComplementOpen R)
    letI : Algebra (Polynomial R) Γ(curveScheme R, sectionComplementOpen R) :=
      (aeval (sectionComplementParameter R)).toRingHom.toAlgebra
    Γ(curveScheme R, sectionComplementOpen R) ≃ₐ[Polynomial R] candidateAlgebra R := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom (curveToBase R) (sectionComplementOpen R)
  letI : Algebra (Polynomial R) Γ(curveScheme R, sectionComplementOpen R) :=
    (aeval (sectionComplementParameter R)).toRingHom.toAlgebra
  let E := sectionComplementSectionsAlgEquiv R
  refine { E.toRingEquiv with commutes' := ?_ }
  intro P
  change E (aeval (sectionComplementParameter R) P) =
    algebraMap (Polynomial R) (candidateAlgebra R) P
  rw [← aeval_algHom_apply E]
  have hf : E (sectionComplementParameter R) = parameterElement R :=
    (sectionComplementSectionsRingEquiv R).apply_symm_apply _
  rw [hf]
  exact (eval_unique (IsScalarTower.toAlgHom R (Polynomial R) (candidateAlgebra R)) P).symm

def sectionComplementPolynomialBasis  :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom (curveToBase R) (sectionComplementOpen R)
    letI : Algebra (Polynomial R) Γ(curveScheme R, sectionComplementOpen R) :=
      (aeval (sectionComplementParameter R)).toRingHom.toAlgebra
    Basis (Fin 3) (Polynomial R) Γ(curveScheme R, sectionComplementOpen R) := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom (curveToBase R) (sectionComplementOpen R)
  letI : Algebra (Polynomial R) Γ(curveScheme R, sectionComplementOpen R) :=
    (aeval (sectionComplementParameter R)).toRingHom.toAlgebra
  exact (candidateBasis R ).map
    (sectionComplementPolynomialAlgEquiv R).symm.toLinearEquiv

theorem sectionComplementPolynomialFinrank  :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom (curveToBase R) (sectionComplementOpen R)
    letI : Algebra (Polynomial R) Γ(curveScheme R, sectionComplementOpen R) :=
      (aeval (sectionComplementParameter R)).toRingHom.toAlgebra
    Module.finrank (Polynomial R) Γ(curveScheme R, sectionComplementOpen R) = 3 := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom (curveToBase R) (sectionComplementOpen R)
  letI : Algebra (Polynomial R) Γ(curveScheme R, sectionComplementOpen R) :=
    (aeval (sectionComplementParameter R)).toRingHom.toAlgebra
  simpa using Module.finrank_eq_card_basis (sectionComplementPolynomialBasis R)

end MazurTransfer.Order13MixedSingleSectionFiniteAlgebra
#print axioms MazurTransfer.Order13MixedSingleSectionFiniteAlgebra.sectionComplementPolynomialBasis
#print axioms MazurTransfer.Order13MixedSingleSectionFiniteAlgebra.sectionComplementPolynomialFinrank

end

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Reuses the complete checked official Anthropic FLT levelSetEquiv at pin
6e837e75355538c7f80bab5b956861e86c4eacc2, with original attribution retained.
Design boundary: the actual complement parameter is finite and its evaluated
tensor quotients are free of rank three for the actual structural R-action.
Named downstream consumer: finite_f and levelSet_free in single-section
FiniteMapData. The second chart and large degrees remain separate obligations.
-/

noncomputable section
universe u
namespace MazurTransfer.Order13MixedSingleSectionFiniteAlgebra
open AlgebraicGeometry Polynomial Module
open scoped TensorProduct
open Order13DyadicMixedQuadraticCharts Order13MixedQuadraticGluedCurve
open Order13MixedActualPositiveInfinityComplement
variable (R : Type u) [CommRing R] [IsDomain R]

theorem sectionComplement_parameter_finite  :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom (curveToBase R) (sectionComplementOpen R)
    (aeval (sectionComplementParameter R) : Polynomial R →ₐ[R]
      Γ(curveScheme R, sectionComplementOpen R)).toRingHom.Finite := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom (curveToBase R) (sectionComplementOpen R)
  letI : Algebra (Polynomial R) Γ(curveScheme R, sectionComplementOpen R) :=
    (aeval (sectionComplementParameter R)).toRingHom.toAlgebra
  exact Module.Finite.of_basis (sectionComplementPolynomialBasis R)

variable (S : Type u) [CommRing S] [Algebra R S]

def sectionComplementLevelSetBasis  (s : S) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom (curveToBase R) (sectionComplementOpen R)
    Basis (Fin 3) S (S ⊗[R] Γ(curveScheme R, sectionComplementOpen R) ⧸
      Ideal.span {(1 : S) ⊗ₜ[R] sectionComplementParameter R -
        s ⊗ₜ[R] (1 : Γ(curveScheme R, sectionComplementOpen R))}) := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom (curveToBase R) (sectionComplementOpen R)
  letI : Algebra (Polynomial R) Γ(curveScheme R, sectionComplementOpen R) :=
    (aeval (sectionComplementParameter R)).toRingHom.toAlgebra
  letI : IsScalarTower R (Polynomial R) Γ(curveScheme R, sectionComplementOpen R) :=
    IsScalarTower.of_algebraMap_eq fun r => by
      change algebraMap R Γ(curveScheme R, sectionComplementOpen R) r =
        aeval (sectionComplementParameter R) (C r)
      rw [aeval_C]
  letI : Algebra (Polynomial R) S := (aeval s).toRingHom.toAlgebra
  letI : IsScalarTower R (Polynomial R) S := IsScalarTower.of_algebraMap_eq fun r => by
    change algebraMap R S r = aeval s (C r)
    rw [aeval_C]
  let e := P2MW.S_Algebra_levelSet_finite_free_finrank_of_flat_polynomial.U4b.levelSetEquiv
    R Γ(curveScheme R, sectionComplementOpen R) S (sectionComplementParameter R) s
      (by change aeval (sectionComplementParameter R) X = _; exact aeval_X _)
      (by change aeval s X = s; exact aeval_X s)
  exact ((sectionComplementPolynomialBasis R).baseChange S).map e.symm.toLinearEquiv

theorem sectionComplementLevelSet_finite_free_finrank 
    [Nontrivial S] (s : S) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom (curveToBase R) (sectionComplementOpen R)
    let Q := S ⊗[R] Γ(curveScheme R, sectionComplementOpen R) ⧸
      Ideal.span {(1 : S) ⊗ₜ[R] sectionComplementParameter R -
        s ⊗ₜ[R] (1 : Γ(curveScheme R, sectionComplementOpen R))}
    Module.Finite S Q ∧ Module.Free S Q ∧ Module.finrank S Q = 3 := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom (curveToBase R) (sectionComplementOpen R)
  let b := sectionComplementLevelSetBasis R S s
  exact ⟨Module.Finite.of_basis b, Module.Free.of_basis b, by
    simpa using Module.finrank_eq_card_basis b⟩

end MazurTransfer.Order13MixedSingleSectionFiniteAlgebra
#print axioms MazurTransfer.Order13MixedSingleSectionFiniteAlgebra.sectionComplement_parameter_finite
#print axioms MazurTransfer.Order13MixedSingleSectionFiniteAlgebra.sectionComplementLevelSet_finite_free_finrank

end

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the two actual curve parameters cut out exactly the
intersection of the two actual affine opens.
Named downstream consumer: the two basic-open fields of whole single-section
FiniteMapData. The reciprocal product field is separate.
-/

noncomputable section
universe u
namespace MazurTransfer.Order13MixedSingleSectionActualParameterBasicOpens
open CategoryTheory AlgebraicGeometry
open Order13DyadicMixedQuadraticCharts Order13MixedQuadraticOverlapCoordinates
open Order13MixedQuadraticGluedCurve
open Order13MixedActualPositiveInfinityComplement
open Order13MixedInverseParameterFiniteAlgebra
variable (R : Type u) [CommRing R] [IsDomain R]

theorem first_parameter_basicOpen  :
    (curveScheme R).basicOpen (Order13MixedSingleSectionFiniteAlgebra.sectionComplementParameter R) =
      (ordinaryParameterCurveMap R).opensRange := by
  let := Order13MixedSingleSectionFiniteAlgebra.finiteModelToCurve_isOpenImmersion R
  let := Order13MixedSingleSectionFiniteAlgebra.ordinaryToFiniteAffineScheme_isOpenImmersion R
    
  let : IsOpenImmersion (Order13MixedSingleSectionFiniteAlgebra.ordinaryParameterChartMap R) :=
    IsOpenImmersion.of_isLocalization (Order13MixedSingleSectionPolynomialIdentities.t R)
  have hr : (Order13MixedSingleSectionFiniteAlgebra.ordinaryParameterChartMap R ≫
      Order13MixedSingleSectionFiniteAlgebra.ordinaryToFiniteAffineScheme R).opensRange =
      PrimeSpectrum.basicOpen (Order13MixedSingleSectionFiniteAlgebra.parameterElement R) := by
    apply SetLike.ext'
    exact Order13MixedSingleSectionFiniteAlgebra.ordinaryParameterChartMap_composite_range R
  have hc : (Order13MixedSingleSectionFiniteAlgebra.ordinaryParameterChartMap R ≫
      Order13MixedSingleSectionFiniteAlgebra.ordinaryToFiniteAffineScheme R) ≫
      Order13MixedSingleSectionFiniteAlgebra.finiteModelToCurve R = ordinaryParameterCurveMap R := by
    rw [Category.assoc, Order13MixedSingleSectionFiniteAlgebra.ordinaryToFiniteAffineScheme_finiteModelToCurve]
    rfl
  refine (MixedOriginalFiniteMapAffineBasicOpenTransport20261019.basicOpen_transport
    (sectionComplementOpen R)
    (Order13MixedSingleSectionFiniteAlgebra.finiteModelSectionComplementIso R)
    (Order13MixedSingleSectionFiniteAlgebra.parameterElement R)).trans ?_
  apply SetLike.ext'
  change Set.image ((Order13MixedSingleSectionFiniteAlgebra.finiteModelSectionComplementIso R).hom ≫
    (sectionComplementOpen R).ι)
    (PrimeSpectrum.basicOpen (Order13MixedSingleSectionFiniteAlgebra.parameterElement R) :
      Set (PrimeSpectrum (Order13MixedSingleSectionFiniteAlgebra.candidateAlgebra R))) =
    Set.range (ordinaryParameterCurveMap R)
  have hD := congrArg (fun W : (Order13MixedSingleSectionFiniteAlgebra.finiteAffineScheme R).Opens =>
    (W : Set (Order13MixedSingleSectionFiniteAlgebra.finiteAffineScheme R))) hr
  rw [Order13MixedSingleSectionFiniteAlgebra.finiteModelSectionComplementIso_hom_ι]
  refine (congrArg (Set.image (Order13MixedSingleSectionFiniteAlgebra.finiteModelToCurve R)) hD.symm).trans ?_
  change Set.image (Order13MixedSingleSectionFiniteAlgebra.finiteModelToCurve R)
    (Set.range (Order13MixedSingleSectionFiniteAlgebra.ordinaryParameterChartMap R ≫
      Order13MixedSingleSectionFiniteAlgebra.ordinaryToFiniteAffineScheme R)) = _
  rw [← Set.range_comp]
  change Set.range ((Order13MixedSingleSectionFiniteAlgebra.ordinaryParameterChartMap R ≫
    Order13MixedSingleSectionFiniteAlgebra.ordinaryToFiniteAffineScheme R) ≫
    Order13MixedSingleSectionFiniteAlgebra.finiteModelToCurve R) = _
  rw [hc]

theorem inverse_parameter_basicOpen  :
    (curveScheme R).basicOpen (inverseChartParameter R) =
      (ordinaryParameterCurveMap R).opensRange := by
  let := finiteModelToCurve_isOpenImmersion R
  let := ordinaryParameterToFiniteAffineScheme_isOpenImmersion R
  have hr : (ordinaryParameterToFiniteAffineScheme R).opensRange = PrimeSpectrum.basicOpen (sElement R) := by
    apply SetLike.ext'
    exact ordinaryParameterToFiniteAffineScheme_range R
  refine (MixedOriginalFiniteMapAffineBasicOpenTransport20261019.basicOpen_transport
    (inverseChartOpen R) (finiteModelInverseChartIso R) (sElement R)).trans ?_
  apply SetLike.ext'
  change Set.image ((finiteModelInverseChartIso R).hom ≫ (inverseChartOpen R).ι)
    (PrimeSpectrum.basicOpen (sElement R) : Set (PrimeSpectrum (candidateAlgebra R))) = Set.range (ordinaryParameterCurveMap R)
  have hD := congrArg (fun W : (inverseFiniteAffineScheme R).Opens => (W : Set (inverseFiniteAffineScheme R))) hr
  rw [finiteModelInverseChartIso_hom_ι]
  refine (congrArg (Set.image (finiteModelToCurve R)) hD.symm).trans ?_
  change Set.image (finiteModelToCurve R)
    (Set.range (ordinaryParameterToFiniteAffineScheme R)) = _
  rw [← Set.range_comp]
  change Set.range (ordinaryParameterToFiniteAffineScheme R ≫ finiteModelToCurve R) = _
  rw [ordinaryParameterToFiniteAffineScheme_finiteModelToCurve]

theorem actual_overlap_basicOpen_f  :
    sectionComplementOpen R ⊓ inverseChartOpen R =
      (curveScheme R).basicOpen (Order13MixedSingleSectionFiniteAlgebra.sectionComplementParameter R) := by
  rw [actual_chart_intersection_opensRange R, first_parameter_basicOpen R]

theorem actual_overlap_basicOpen_g  :
    sectionComplementOpen R ⊓ inverseChartOpen R =
      (curveScheme R).basicOpen (inverseChartParameter R) := by
  rw [actual_chart_intersection_opensRange R, inverse_parameter_basicOpen R]

end MazurTransfer.Order13MixedSingleSectionActualParameterBasicOpens
#print axioms MazurTransfer.Order13MixedSingleSectionActualParameterBasicOpens.actual_overlap_basicOpen_f
#print axioms MazurTransfer.Order13MixedSingleSectionActualParameterBasicOpens.actual_overlap_basicOpen_g

end

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the restrictions of the actual two curve parameters
multiply to one on their actual intersection.
Named downstream consumer: res_f_mul_res_g in original FLT FiniteMapData.
-/

noncomputable section
universe u
namespace MazurTransfer.Order13MixedSingleSectionActualParameterReciprocity
open CategoryTheory AlgebraicGeometry
open scoped MazurTransfer.Order13MixedSingleSectionFiniteAlgebra
open Order13DyadicMixedQuadraticCharts Order13MixedQuadraticOverlapCoordinates
open Order13MixedQuadraticGluedCurve
open Order13MixedActualPositiveInfinityComplement
open Order13MixedInverseParameterFiniteAlgebra
open MixedOriginalFiniteMapAffineRestrictionTransport20261019
variable (R : Type u) [CommRing R] [IsDomain R]

abbrev Ω := Order13MixedInverseParameterPolynomialIdentities.ordinaryParameterLocalization R

theorem actual_parameter_product  :
    ((curveScheme R).presheaf.map (homOfLE (inf_le_left :
      sectionComplementOpen R ⊓ inverseChartOpen R ≤ sectionComplementOpen R)).op)
      (Order13MixedSingleSectionFiniteAlgebra.sectionComplementParameter R) *
    ((curveScheme R).presheaf.map (homOfLE (inf_le_right :
      sectionComplementOpen R ⊓ inverseChartOpen R ≤ inverseChartOpen R)).op)
      (inverseChartParameter R) = 1 := by
  let j := ordinaryParameterCurveMap R
  let U := sectionComplementOpen R
  let V := inverseChartOpen R
  let W := U ⊓ V
  have hW : ⊤ ≤ j ⁻¹ᵁ W := by
    intro p hp
    change ordinaryParameterCurveMap R p ∈ sectionComplementOpen R ⊓ inverseChartOpen R
    rw [actual_chart_intersection_opensRange R]
    exact ⟨p,rfl⟩
  have hU : ⊤ ≤ j ⁻¹ᵁ U := fun p hp => (hW hp).1
  have hV : ⊤ ≤ j ⁻¹ᵁ V := fun p hp => (hW hp).2
  let φ : Order13MixedSingleSectionFiniteAlgebra.candidateAlgebra R →+* Ω R :=
    (algebraMap (ordinaryCoordinateRing R) (Ω R)).comp
      (Order13MixedSingleSectionFiniteAlgebra.inclusion R).toRingHom
  have hfScheme : Spec.map (CommRingCat.ofHom φ) ≫
      (Order13MixedSingleSectionFiniteAlgebra.finiteModelSectionComplementIso R).hom ≫ U.ι = j := by
    refine (congrArg (fun k => Spec.map (CommRingCat.ofHom φ) ≫ k)
      (Order13MixedSingleSectionFiniteAlgebra.finiteModelSectionComplementIso_hom_ι R)).trans ?_
    have hc := Order13MixedSingleSectionFiniteAlgebra.ordinaryToFiniteAffineScheme_finiteModelToCurve R
    change Spec.map (CommRingCat.ofHom φ) ≫
      Order13MixedSingleSectionFiniteAlgebra.finiteModelToCurve R = _
    have hφ : Spec.map (CommRingCat.ofHom φ) =
        Order13MixedSingleSectionFiniteAlgebra.ordinaryParameterChartMap R ≫
        Order13MixedSingleSectionFiniteAlgebra.ordinaryToFiniteAffineScheme R := by
      change Spec.map (CommRingCat.ofHom φ) =
        Spec.map (CommRingCat.ofHom (algebraMap (ordinaryCoordinateRing R) (Ω R))) ≫
        Spec.map (CommRingCat.ofHom (Order13MixedSingleSectionFiniteAlgebra.inclusion R).toRingHom)
      rw [← Spec.map_comp]
      rfl
    rw [hφ]
    change (Order13MixedSingleSectionFiniteAlgebra.ordinaryParameterChartMap R ≫
      Order13MixedSingleSectionFiniteAlgebra.ordinaryToFiniteAffineScheme R) ≫
      Order13MixedSingleSectionFiniteAlgebra.finiteModelToCurve R = j
    rw [Category.assoc, hc]
    rfl
  have hgScheme : Spec.map (CommRingCat.ofHom (inclusion R).toRingHom) ≫
      (finiteModelInverseChartIso R).hom ≫ V.ι = j := by
    refine (congrArg (fun k => Spec.map (CommRingCat.ofHom (inclusion R).toRingHom) ≫ k)
      (finiteModelInverseChartIso_hom_ι R)).trans ?_
    exact (congrArg (fun k => k ≫ finiteModelToCurve R)
      (ordinaryParameterToFiniteAffineScheme_eq_Spec R).symm).trans
      (ordinaryParameterToFiniteAffineScheme_finiteModelToCurve R)
  have hf := transportedSection_pullback U
    (Order13MixedSingleSectionFiniteAlgebra.finiteModelSectionComplementIso R)
    φ (Order13MixedSingleSectionFiniteAlgebra.parameterElement R)
    (show ⊤ ≤ (Spec.map (CommRingCat.ofHom φ) ≫
      (Order13MixedSingleSectionFiniteAlgebra.finiteModelSectionComplementIso R).hom ≫ U.ι) ⁻¹ᵁ U by
      simpa only [hfScheme] using hU)
  change (Scheme.ΓSpecIso (.of (Ω R))).hom
    ((Spec.map (CommRingCat.ofHom φ) ≫
      (Order13MixedSingleSectionFiniteAlgebra.finiteModelSectionComplementIso R).hom ≫ U.ι).appLE U ⊤ _
      (Order13MixedSingleSectionFiniteAlgebra.sectionComplementParameter R)) =
      algebraMap (ordinaryCoordinateRing R) (Ω R)
        (Order13MixedSingleSectionFiniteAlgebra.parameterElement R : ordinaryCoordinateRing R) at hf
  simp only [hfScheme, Order13MixedSingleSectionFiniteAlgebra.parameterElement_coe] at hf
  have hg := transportedSection_pullback V (finiteModelInverseChartIso R)
    (inclusion R).toRingHom (sElement R)
    (show ⊤ ≤ (Spec.map (CommRingCat.ofHom (inclusion R).toRingHom) ≫
      (finiteModelInverseChartIso R).hom ≫ V.ι) ⁻¹ᵁ V by
      simpa only [hgScheme] using hV)
  change (Scheme.ΓSpecIso (.of (Ω R))).hom
    ((Spec.map (CommRingCat.ofHom (inclusion R).toRingHom) ≫
      (finiteModelInverseChartIso R).hom ≫ V.ι).appLE V ⊤ _
      (inverseChartParameter R)) = inclusion R (sElement R) at hg
  simp only [hgScheme, inclusion_sElement] at hg
  have hImage : j ''ᵁ ⊤ = W := by
    exact j.image_top_eq_opensRange.trans (actual_chart_intersection_opensRange R).symm
  apply appLE_injective_of_image_top W j hImage hW
  apply (Scheme.ΓSpecIso (.of (Ω R))).commRingCatIsoToRingEquiv.injective
  have hresU := j.map_appLE hW (homOfLE (inf_le_left : W ≤ U)).op
  have hresV := j.map_appLE hW (homOfLE (inf_le_right : W ≤ V)).op
  simp only [map_mul, map_one]
  rw [← CommRingCat.comp_apply, hresU, ← CommRingCat.comp_apply, hresV]
  change (Scheme.ΓSpecIso (.of (Ω R))).hom
      ((j.appLE U ⊤ hU) (Order13MixedSingleSectionFiniteAlgebra.sectionComplementParameter R)) *
    (Scheme.ΓSpecIso (.of (Ω R))).hom ((j.appLE V ⊤ hV) (inverseChartParameter R)) = 1
  rw [hf, hg]
  exact IsLocalization.Away.mul_invSelf (Order13MixedSingleSectionPolynomialIdentities.t R)

end MazurTransfer.Order13MixedSingleSectionActualParameterReciprocity
#print axioms MazurTransfer.Order13MixedSingleSectionActualParameterReciprocity.actual_parameter_product

end

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: original FLT FiniteMapData for the actual whole order-13
curve over any integral coefficient ring, including the dyadic base, of degree three.
Named downstream consumer: construction of arbitrarily large degree data
and the integral Picard-family chart-section obligations. No such further
obligation is assumed or claimed here.
-/

noncomputable section
universe u
namespace MazurTransfer.Order13MixedSingleSectionActualFiniteMapData
open CategoryTheory AlgebraicGeometry
open Order13DyadicMixedQuadraticCharts Order13MixedQuadraticOverlapCoordinates
open Order13MixedQuadraticGluedCurve
open Order13MixedActualPositiveInfinityComplement
open Order13MixedInverseParameterFiniteAlgebra
open Order13MixedSingleSectionTwoActualAffineCharts
open Order13MixedSingleSectionActualParameterBasicOpens
variable (R : Type u) [CommRing R] [IsDomain R]

def positiveInfinitySection : NeronModelInfra.SchemeHomOver
    (𝟙 (Spec (.of R))) (curveToBase R) :=
  ⟨Order13MixedQuadraticInfinitySections.infinitySectionZero R,
    Order13MixedQuadraticInfinitySections.infinitySectionZero_comp R⟩

def actualFiniteMapData  :
    SmoothProperCurve.FiniteMapData (curveToBase R)
      (positiveInfinitySection R) where
  U := sectionComplementOpen R
  V := inverseChartOpen R
  f := Order13MixedSingleSectionFiniteAlgebra.sectionComplementParameter R
  g := inverseChartParameter R
  m := 3
  isAffineOpen_U := actual_first_chart_isAffineOpen R
  isAffineOpen_V := actual_inverse_chart_isAffineOpen R
  sup_eq_top := actual_two_affine_open_cover R
  mem_U_iff := mem_sectionComplementOpen_iff R
  inf_eq_basicOpen := actual_overlap_basicOpen_f R
  inf_eq_basicOpen_g := actual_overlap_basicOpen_g R
  res_f_mul_res_g := Order13MixedSingleSectionActualParameterReciprocity.actual_parameter_product R
  finite_f := Order13MixedSingleSectionFiniteAlgebra.sectionComplement_parameter_finite R
  finite_g := inverseChart_parameter_finite R
  levelSet_free S _ _ _ s :=
    Order13MixedSingleSectionFiniteAlgebra.sectionComplementLevelSet_finite_free_finrank R S s

@[simp] theorem actualFiniteMapData_degree  :
    (actualFiniteMapData R).m = 3 := rfl

@[simp] theorem actualFiniteMapData_first_chart  :
    (actualFiniteMapData R).U = sectionComplementOpen R := rfl

@[simp] theorem actualFiniteMapData_inverse_chart  :
    (actualFiniteMapData R).V = inverseChartOpen R := rfl

end MazurTransfer.Order13MixedSingleSectionActualFiniteMapData
#print axioms MazurTransfer.Order13MixedSingleSectionActualFiniteMapData.actualFiniteMapData

end

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the polynomial ring with coefficient parameter acting by
X^n is the literal monic root algebra of Y^n-T.
Named downstream consumer: the power-substitution finite free basis used to
raise the degree of actual order-13 FiniteMapData.
-/

noncomputable section
universe u
namespace MazurTransfer.MixedOriginalFiniteMapPolynomialPowerSubstitutionPresentation20261019
open Polynomial
variable (R : Type u) [CommRing R] (n : ℕ)

def Source (_n : ℕ) : Type u := Polynomial R
instance sourceCommRing : CommRing (Source R n) := inferInstanceAs (CommRing (Polynomial R))
instance sourceBaseAlgebra : Algebra R (Source R n) := inferInstanceAs (Algebra R (Polynomial R))

def sourceX : Source R n := (X : Polynomial R)
def powerMap : Source R n →+* Polynomial R := (aeval ((X : Polynomial R)^n)).toRingHom
scoped instance powerAlgebra : Algebra (Source R n) (Polynomial R) := (powerMap R n).toAlgebra

def relation : Polynomial (Source R n) := X^n - C (sourceX R n)
abbrev RootRing := AdjoinRoot (relation R n)

theorem relation_eval : (relation R n).eval₂ (powerMap R n) (X : Polynomial R) = 0 := by
  rw [relation, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C]
  change X^n - aeval ((X : Polynomial R)^n) X = 0
  rw [aeval_X, sub_self]

def forward : RootRing R n →+* Polynomial R :=
  AdjoinRoot.lift (powerMap R n) X (relation_eval R n)
def backward : Polynomial R →+* RootRing R n :=
  eval₂RingHom ((AdjoinRoot.of (relation R n)).comp (C : R →+* Source R n))
    (AdjoinRoot.root (relation R n))

theorem root_power : AdjoinRoot.root (relation R n)^n =
    AdjoinRoot.of (relation R n) (sourceX R n) := by
  have h := AdjoinRoot.eval₂_root (relation R n)
  change eval₂ (AdjoinRoot.of (relation R n)) (AdjoinRoot.root (relation R n))
    (X^n - C (sourceX R n)) = 0 at h
  rw [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C] at h
  exact sub_eq_zero.mp h

theorem backward_powerMap : (backward R n).comp (powerMap R n) =
    AdjoinRoot.of (relation R n) := by
  apply Polynomial.ringHom_ext
  · intro r
    change backward R n (aeval ((X : Polynomial R)^n) (C r)) =
      AdjoinRoot.of (relation R n) (C r)
    rw [aeval_C]
    change eval₂ _ _ (C r) = _
    rw [eval₂_C]
    rfl
  · change backward R n (aeval ((X : Polynomial R)^n) X) = AdjoinRoot.of (relation R n) X
    rw [aeval_X, map_pow]
    simpa only [backward, coe_eval₂RingHom, eval₂_X, sourceX] using root_power R n

theorem forward_backward : (forward R n).comp (backward R n) = RingHom.id _ := by
  apply Polynomial.ringHom_ext
  · intro r
    change forward R n (backward R n (C r)) = C r
    rw [backward, coe_eval₂RingHom, eval₂_C]
    change forward R n (AdjoinRoot.of (relation R n) (C r)) = C r
    exact (AdjoinRoot.lift_of (relation_eval R n) (x := (C r : Source R n))).trans
      (aeval_C ((X : Polynomial R)^n) r)
  · simp [forward, backward]

theorem backward_forward : (backward R n).comp (forward R n) = RingHom.id _ := by
  have h : ((backward R n).comp (forward R n)).comp (AdjoinRoot.mk (relation R n)) =
      AdjoinRoot.mk (relation R n) := by
    apply Polynomial.ringHom_ext
    · intro p
      change backward R n (forward R n (AdjoinRoot.of (relation R n) p)) =
        AdjoinRoot.of (relation R n) p
      simpa only [forward, AdjoinRoot.lift_of, RingHom.comp_apply] using
        RingHom.congr_fun (backward_powerMap R n) p
    · simp [forward, backward, AdjoinRoot.mk_X]
  apply RingHom.ext
  intro x
  induction x using AdjoinRoot.induction_on with
  | ih p => exact RingHom.congr_fun h p

def presentationEquiv : RootRing R n ≃ₐ[Source R n] Polynomial R where
  toFun := forward R n
  invFun := backward R n
  left_inv x := RingHom.congr_fun (backward_forward R n) x
  right_inv x := RingHom.congr_fun (forward_backward R n) x
  map_add' := (forward R n).map_add
  map_mul' := (forward R n).map_mul
  commutes' p := by
    change forward R n (AdjoinRoot.of (relation R n) p) = powerMap R n p
    simp [forward]

end MazurTransfer.MixedOriginalFiniteMapPolynomialPowerSubstitutionPresentation20261019
#print axioms MazurTransfer.MixedOriginalFiniteMapPolynomialPowerSubstitutionPresentation20261019.presentationEquiv

end

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: a monic presentation gives the polynomial power-substitution
basis, and scalar towers raise any existing polynomial basis by a factor n.
Named downstream consumers: both actual order-13 parameter powers and their
level-set bases in arbitrarily large whole-curve FiniteMapData.
-/

noncomputable section
universe u v
namespace MazurTransfer.MixedOriginalFiniteMapPolynomialPowerSubstitutionBasis20261019
open Polynomial Module
open MixedOriginalFiniteMapPolynomialPowerSubstitutionPresentation20261019
variable (R : Type u) [CommRing R] [Nontrivial R] (n : ℕ)

def powerBasis (hn : n ≠ 0) : Basis (Fin n) (Source R n) (Polynomial R) := by
  letI : Nontrivial (Source R n) := inferInstanceAs (Nontrivial (Polynomial R))
  have hd : (relation R n).natDegree = n := natDegree_X_pow_sub_C
  let b := (AdjoinRoot.powerBasis' (monic_X_pow_sub_C (sourceX R n) hn)).basis
  exact (b.map (presentationEquiv R n).toLinearEquiv).reindex (finCongr hd)

variable {A : Type u} [CommRing A] [Algebra R A] {ι : Type v}

def raisedBasis (f : A)
    (b : letI : Algebra (Polynomial R) A := (aeval f).toRingHom.toAlgebra
      Basis ι (Polynomial R) A) (hn : n ≠ 0) :
    letI : Algebra (Polynomial R) A := (aeval (f^n)).toRingHom.toAlgebra
    Basis (Fin n × ι) (Polynomial R) A := by
  letI : Algebra (Polynomial R) A := (aeval f).toRingHom.toAlgebra
  letI : Algebra (Source R n) A := ((aeval f).toRingHom.comp (powerMap R n)).toAlgebra
  letI : IsScalarTower (Source R n) (Polynomial R) A :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let bp : Basis (Fin n × ι) (Source R n) A := (powerBasis R n hn).smulTower b
  letI : Algebra (Polynomial R) A := (aeval (f^n)).toRingHom.toAlgebra
  let e : Source R n ≃+* Polynomial R := RingEquiv.refl (Polynomial R)
  refine bp.mapCoeffs e ?_
  intro c x
  change aeval (f^n) c * x = aeval f (powerMap R n c) * x
  change aeval (f^n) c * x = aeval f (c.comp ((X : Polynomial R)^n)) * x
  let p : Polynomial R := c
  change aeval (f^n) p * x = aeval f (p.comp ((X : Polynomial R)^n)) * x
  rw [aeval_comp, map_pow, aeval_X]

end MazurTransfer.MixedOriginalFiniteMapPolynomialPowerSubstitutionBasis20261019
#print axioms MazurTransfer.MixedOriginalFiniteMapPolynomialPowerSubstitutionBasis20261019.raisedBasis

end

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Reuses the complete official Anthropic FLT levelSetEquiv at pin
6e837e75355538c7f80bab5b956861e86c4eacc2, retaining its upstream attribution.
Design boundary: powers of a parameter with a finite polynomial basis
have finite maps and finite free evaluated tensor quotients of rank n*d.
Named downstream consumer: arbitrarily large actual order-13 FiniteMapData.
-/

noncomputable section
universe u
namespace MazurTransfer.MixedOriginalFiniteMapPolynomialBasisPowerLevelSets20261019
open Polynomial Module
open scoped TensorProduct
variable (R : Type u) [CommRing R] [Nontrivial R]
variable (A : Type u) [CommRing A] [Algebra R A]
variable (d n : ℕ) (f : A)
variable (b : letI : Algebra (Polynomial R) A := (aeval f).toRingHom.toAlgebra
    Basis (Fin d) (Polynomial R) A)

include b

theorem parameter_power_finite (hn : n ≠ 0) :
    (aeval (f^n) : Polynomial R →ₐ[R] A).toRingHom.Finite := by
  letI : Algebra (Polynomial R) A := (aeval (f^n)).toRingHom.toAlgebra
  exact Module.Finite.of_basis
    (MixedOriginalFiniteMapPolynomialPowerSubstitutionBasis20261019.raisedBasis R n f b hn)

variable (S : Type u) [CommRing S] [Algebra R S]

def powerLevelSetBasis (hn : n ≠ 0) (s : S) :
    Basis (Fin n × Fin d) S (S ⊗[R] A ⧸
      Ideal.span {(1 : S) ⊗ₜ[R] (f^n) - s ⊗ₜ[R] (1 : A)}) := by
  letI : Algebra (Polynomial R) A := (aeval (f^n)).toRingHom.toAlgebra
  letI : IsScalarTower R (Polynomial R) A := IsScalarTower.of_algebraMap_eq fun r => by
    change algebraMap R A r = aeval (f^n) (C r)
    rw [aeval_C]
  letI : Algebra (Polynomial R) S := (aeval s).toRingHom.toAlgebra
  letI : IsScalarTower R (Polynomial R) S := IsScalarTower.of_algebraMap_eq fun r => by
    change algebraMap R S r = aeval s (C r)
    rw [aeval_C]
  let e := P2MW.S_Algebra_levelSet_finite_free_finrank_of_flat_polynomial.U4b.levelSetEquiv
    R A S (f^n) s (by change aeval (f^n) X = _; exact aeval_X _)
      (by change aeval s X = s; exact aeval_X s)
  exact ((MixedOriginalFiniteMapPolynomialPowerSubstitutionBasis20261019.raisedBasis R n f b hn).baseChange S).map e.symm.toLinearEquiv

theorem powerLevelSet_finite_free_finrank (hn : n ≠ 0) [Nontrivial S] (s : S) :
    let Q := S ⊗[R] A ⧸ Ideal.span {(1 : S) ⊗ₜ[R] (f^n) - s ⊗ₜ[R] (1 : A)}
    Module.Finite S Q ∧ Module.Free S Q ∧ Module.finrank S Q = n*d := by
  let B := powerLevelSetBasis R A d n f b S hn s
  exact ⟨Module.Finite.of_basis B, Module.Free.of_basis B, by
    simpa using Module.finrank_eq_card_basis B⟩

end MazurTransfer.MixedOriginalFiniteMapPolynomialBasisPowerLevelSets20261019
#print axioms MazurTransfer.MixedOriginalFiniteMapPolynomialBasisPowerLevelSets20261019.powerLevelSet_finite_free_finrank

end

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: powers of the actual reciprocal curve parameters construct
original FLT FiniteMapData of degree 3*n and hence arbitrarily large degree.
Named downstream consumer: the finite-map-data input of integral Picard
representation and base-change compatibility for the actual order-13 curve.
The six chart-section conditions remain a separate obligation.
-/

noncomputable section
universe u
namespace MazurTransfer.Order13MixedSingleSectionArbitrarilyLargeFiniteMapData
open CategoryTheory AlgebraicGeometry Polynomial
open Order13DyadicMixedQuadraticCharts Order13MixedQuadraticOverlapCoordinates
open Order13MixedQuadraticGluedCurve
open Order13MixedActualPositiveInfinityComplement
open Order13MixedInverseParameterFiniteAlgebra
open Order13MixedSingleSectionActualFiniteMapData
variable (R : Type u) [CommRing R] [IsDomain R]

def actualPowerFiniteMapData  (n : ℕ) (hn : n ≠ 0) :
    SmoothProperCurve.FiniteMapData (curveToBase R)
      (positiveInfinitySection R) := by
  let F := actualFiniteMapData R
  refine { F with
    f := F.f^n
    g := F.g^n
    m := n*3
    inf_eq_basicOpen := F.inf_eq_basicOpen.trans
      ((curveScheme R).basicOpen_pow F.f (Nat.pos_of_ne_zero hn)).symm
    inf_eq_basicOpen_g := F.inf_eq_basicOpen_g.trans
      ((curveScheme R).basicOpen_pow F.g (Nat.pos_of_ne_zero hn)).symm
    res_f_mul_res_g := ?_
    finite_f := ?_
    finite_g := ?_
    levelSet_free := ?_ }
  · rw [map_pow, map_pow, ← mul_pow, F.res_f_mul_res_g, one_pow]
  · letI := Scheme.TwoAffineOpenCover.algebraOfHom (curveToBase R) (sectionComplementOpen R)
    exact MixedOriginalFiniteMapPolynomialBasisPowerLevelSets20261019.parameter_power_finite R
      Γ(curveScheme R, sectionComplementOpen R) 3 n
      (Order13MixedSingleSectionFiniteAlgebra.sectionComplementParameter R)
      (Order13MixedSingleSectionFiniteAlgebra.sectionComplementPolynomialBasis R) hn
  · letI := Scheme.TwoAffineOpenCover.algebraOfHom (curveToBase R) (inverseChartOpen R)
    exact MixedOriginalFiniteMapPolynomialBasisPowerLevelSets20261019.parameter_power_finite R
      Γ(curveScheme R, inverseChartOpen R) 3 n (inverseChartParameter R)
      (inverseChartPolynomialBasis R) hn
  · intro S _ _ _ s
    letI := Scheme.TwoAffineOpenCover.algebraOfHom (curveToBase R) (sectionComplementOpen R)
    exact MixedOriginalFiniteMapPolynomialBasisPowerLevelSets20261019.powerLevelSet_finite_free_finrank R
      Γ(curveScheme R, sectionComplementOpen R) 3 n
      (Order13MixedSingleSectionFiniteAlgebra.sectionComplementParameter R)
      (Order13MixedSingleSectionFiniteAlgebra.sectionComplementPolynomialBasis R) S hn s

@[simp] theorem actualPowerFiniteMapData_degree 
    (n : ℕ) (hn : n ≠ 0) : (actualPowerFiniteMapData R n hn).m = n*3 := rfl

theorem exists_actual_finiteMapData_degree_ge  (m₀ : ℕ) :
    ∃ F : SmoothProperCurve.FiniteMapData (curveToBase R)
      (positiveInfinitySection R), m₀ ≤ F.m := by
  refine ⟨actualPowerFiniteMapData R (m₀+1) (by omega), ?_⟩
  change m₀ ≤ (m₀+1)*3
  omega

end MazurTransfer.Order13MixedSingleSectionArbitrarilyLargeFiniteMapData
#print axioms MazurTransfer.Order13MixedSingleSectionArbitrarilyLargeFiniteMapData.exists_actual_finiteMapData_degree_ge

end


