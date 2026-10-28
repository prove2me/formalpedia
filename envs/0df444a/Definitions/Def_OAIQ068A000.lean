-- Prove2me | Definitions.Def_OAIQ068A000
-- name    : OAIQ068A000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T07:37:50.238024+00:00
-- url     : https://prove2.me/theorems/154557dc-c348-44c4-b414-201e38fffc8e
-- title:
--   Definitions bundle OAIQ068A000 of the split of OpenAI, The irrationality exponent of pi is 2 (result family 017)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PiExponent.main`, carved from OpenAI's openai/math development (OpenAI, *The irrationality exponent of pi is 2 (result family 017)*, OpenAI Math Release, September 24, 2026, result family 17, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 111 declarations of OpenAI's Lean: 55 definitions, 4 inductive types or structures, 1 instance and 51 theorems. The definitions and types are `OAI.PiExponent.AdditiveKernelTransport.kernelEquiv`, `OAI.PiExponent.AdmissibleBlowupGeometry.Index`, `OAI.PiExponent.AdmissibleBlowupGeometry.exponents`, `OAI.PiExponent.AdmissibleBlowupGeometry.scale`, `OAI.PiExponent.AdmissibleParameters`, `OAI.PiExponent.AdmissibleParameters.curveDegreeWeights`, `OAI.PiExponent.AdmissibleParameters.curveJetWeights`, `OAI.PiExponent.AdmissibleParameters.rationalWeight`, `OAI.PiExponent.GeometrySupport.ProjectiveLaurentVertex.ChartExponent`, `OAI.PiExponent.Parameters`, `OAI.PiExponent.ProjectiveO1.coordinateOpen`, `OAI.PiExponent.ProjectiveO1.coordinateRatio`, `OAI.PiExponent.ProjectiveO1.projectiveSpace`, `OAI.PiExponent.WeightedCompactification.affineChartConstant`, `OAI.PiExponent.WeightedCompactification.affineChartCoordinate`, `OAI.PiExponent.WeightedCompactification.affineChartMap`, `OAI.PiExponent.WeightedCompactification.ambientGrade`, `OAI.PiExponent.WeightedCompactification.chartEvaluation`, `OAI.PiExponent.WeightedCompactification.constantChart`, `OAI.PiExponent.WeightedCompactification.constantChartEquiv`, `OAI.PiExponent.WeightedCompactification.constantProjectiveChartIso`, `OAI.PiExponent.WeightedCompactification.gradedImageMap`, `OAI.PiExponent.WeightedCompactification.gradedMonomialMapInt`, `OAI.PiExponent.WeightedCompactification.homogeneousMonomialMap`, `OAI.PiExponent.WeightedCompactification.imageConstant`, `OAI.PiExponent.WeightedCompactification.imageCoordinate`, `OAI.PiExponent.WeightedCompactification.imageEvaluation`, `OAI.PiExponent.WeightedCompactification.imageGrade`, `OAI.PiExponent.WeightedCompactification.monomialImage`, `OAI.PiExponent.WeightedCompactification.projectiveMonomialMap`, `OAI.PiExponent.WeightedGeometryScale.Scale`, `OAI.PiExponent.WeightedGeometryScale.Scale.Index`, `OAI.PiExponent.WeightedGeometryScale.Scale.constantIndex`, `OAI.PiExponent.WeightedGeometryScale.Scale.coordinateIndex`, `OAI.PiExponent.WeightedGeometryScale.Scale.exponents`, `OAI.PiExponent.WeightedGeometryScale.Scale.pureIndex`, `OAI.PiExponent.WeightedGeometryScale.chooseScale`, `OAI.PiExponent.WeightedGeometryScale.monomials`, `OAI.PiExponent.dimensionK`, `OAI.PiExponent.dimensionV` and 19 more.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `PiExponent_Ampleness_AdmissibleBlowupGeometry`, `PiExponent_Approximation_AddEquivSignedSum`, `PiExponent_Approximation_AdditiveKernelTransport`, `PiExponent_Approximation_AdmissibleParameters`, `PiExponent_Approximation_Parameters`, `PiExponent_Approximation_WeightSeparation`, `PiExponent_Approximation_WeightedCompactification`, `PiExponent_Approximation_WeightedCompactificationGeometry`, `PiExponent_Approximation_WeightedCompactificationImmersion`, `PiExponent_Approximation_WeightedGeometryScale`, `PiExponent_Cohomology_ProjectiveLaurentVertex`, `PiExponent_Geometry_AdmissibleCurveWeights`, `PiExponent_Geometry_LineBundleTensor`, `PiExponent_Geometry_ProjectiveCharts`, `PiExponent_Geometry_ProjectiveCoordinates`, `PiExponent_Geometry_ProjectiveRatioCocycle`, `PiExponent_LocalAlgebra_Dimension`, `PiExponent_Polynomials_GradedSubring`, `PiExponent_Polynomials_SimplexCounting`, `PiExponent_Polynomials_SimplexRationalWeights`, `PiExponent_Polynomials_SurjectiveGradedMap`, `PiExponent_Polynomials_WeightedMonomialImage`, `PiExponent_Polynomials_WeightedMonomialMap`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ068A012`, `OAIQ068A013`, `OAIQ068A014`, `OAIQ068A015`, `OAIQ068A016` and `OAIQ068A017`; the statements `OAI_PiExponent_exists_admissible_parameters` and `OAI.PiExponent.exists_admissible_parameters_q68`; the proofs of `OAI_PiExponent_exists_admissible_parameters` and `OAI.PiExponent.exists_admissible_parameters_q68`.
-- source:
--   OpenAI, The irrationality exponent of pi is 2 (result family 017), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 17; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory at commit 1581d4c

import Mathlib
import Lean.Elab.Tactic.Omega

section
-- module Solutions.OAIQ068_PI.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
/-- Mathlib d13f23b's `MvPolynomial.monomial_mul_monomial`; ours is `MvPolynomial.monomial_mul`. -/
theorem _root_.MvPolynomial.monomial_mul_monomial {σ R : Type*} [CommSemiring R] {s s' : σ →₀ ℕ}
    {a b : R} : MvPolynomial.monomial s a * MvPolynomial.monomial s' b =
      MvPolynomial.monomial (s + s') (a * b) := MvPolynomial.monomial_mul
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_LineBundleTensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponentSeshadri

namespace Geometry
open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry

variable (X : Scheme)

structure LineBundle where
  sheaf : X.Modules
  locallyRankOne : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
    Nonempty (sheaf.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf)

def moduleTensor (M N : X.Modules) : X.Modules :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj
    (PresheafOfModules.Monoidal.tensorObj (R := X.presheaf) M.val N.val)

def structureSheaf : X.Modules := SheafOfModules.unit X.ringCatSheaf

end Geometry

open CategoryTheory
open CategoryTheory.Category CategoryTheory.Functor
universe v u v₁ v₂ u₁ u₂

end PiExponentSeshadri

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_ProjectiveCharts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponentSeshadri.Projective

section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MvPolynomial HomogeneousLocalization
attribute [local instance] Classical.propDecidable

lemma homogeneous_eval₂_scale {R S σ : Type*} [CommRing R] [CommRing S]
    {p : MvPolynomial σ R} {n : ℕ} (hp : p.IsHomogeneous n)
    (f : R →+* S) (u : σ → S) (a : S) :
    eval₂ f (fun j => a * u j) p = a ^ n * eval₂ f u p := by
  classical
  rw [p.as_sum]
  simp only [eval₂_sum, eval₂_monomial, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  simp only [mul_pow, Finsupp.prod, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rw [← hp.degree_eq_sum_deg_support hd]
  ring

variable {R σ : Type*} [CommRing R] (i : σ)
attribute [local instance] MvPolynomial.gradedAlgebra

abbrev PolyGrade (R σ : Type*) [CommRing R] := MvPolynomial.homogeneousSubmodule σ R
lemma poly_X_mem : X (R := R) i ∈ PolyGrade R σ 1 := isHomogeneous_X R i

abbrev PolyChart := HomogeneousLocalization.Away (PolyGrade R σ) (X i)
abbrev ChartVariables := {j : σ // j ≠ i}

def chartConstants : R →+* PolyChart (R := R) i :=
  (HomogeneousLocalization.fromZeroRingHom _ _).comp
    { toFun := fun r => ⟨C r, isHomogeneous_C _ _⟩
      map_one' := Subtype.ext C_1
      map_mul' := fun _ _ => Subtype.ext C_mul
      map_zero' := Subtype.ext C_0
      map_add' := fun _ _ => Subtype.ext C_add }

def chartCoordinate (j : σ) : PolyChart (R := R) i :=
  Away.mk _ (poly_X_mem (R := R) i) 1 (X j) (by simpa using poly_X_mem (R := R) j)

def dehomogenize : MvPolynomial σ R →+* MvPolynomial (ChartVariables i) R :=
  eval₂Hom C (fun j => if h : j = i then 1 else X ⟨j, h⟩)

@[simp] lemma dehomogenize_X_self : dehomogenize (R := R) i (X i) = 1 := by
  classical
  simp [dehomogenize]

def chartToPoly : PolyChart (R := R) i →+* MvPolynomial (ChartVariables i) R :=
  (Localization.awayLift (dehomogenize i) (X i) (by simp)).comp (algebraMap _ _)

@[simp] lemma chartToPoly_mk (n : ℕ) (p : MvPolynomial σ R)
    (hp : p ∈ PolyGrade R σ (n • 1)) :
    chartToPoly i (Away.mk _ (poly_X_mem (R := R) i) n p hp) = dehomogenize i p := by
  have h := Localization.awayLift_mk (dehomogenize (R := R) i) (X i) p 1
    (by simp) n
  simpa only [chartToPoly, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply,
    Away.val_mk, one_pow, mul_one] using h

@[simp] lemma chartToPoly_constants (r : R) :
    chartToPoly i (chartConstants i r) = C r := by
  exact (chartToPoly_mk i 0 (C r) (by simp)).trans
    (by simp [dehomogenize])

@[simp] lemma chartToPoly_coordinate (j : σ) :
    chartToPoly (R := R) i (chartCoordinate i j) =
      if h : j = i then 1 else X ⟨j, h⟩ := by
  rw [chartCoordinate, chartToPoly_mk]
  simp [dehomogenize]

end

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open MvPolynomial
attribute [local instance] Classical.propDecidable
attribute [local instance] MvPolynomial.gradedAlgebra

end PiExponentSeshadri.Projective

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_ProjectiveCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

universe u

namespace PiExponentSeshadri.Projective

section
open AlgebraicGeometry CategoryTheory HomogeneousLocalization
variable {A R σ : Type u} [CommRing A] [CommRing R] [SetLike σ A]
  [AddSubgroupClass σ A] {𝒜 : ℕ → σ} [GradedRing 𝒜]
  (f : A →+* R)

def evalAway (s : A) (hs : IsUnit (f s)) : Away 𝒜 s →+* R :=
  (IsLocalization.Away.lift s hs : Localization.Away s →+* R).comp
    (algebraMap (Away 𝒜 s) (Localization.Away s))

lemma evalAway_val (s : A) (hs : IsUnit (f s)) (x : Away 𝒜 s) :
    evalAway f s hs x = IsLocalization.Away.lift s hs x.val := rfl

lemma evalAway_mk_clear {s : A} {d : ℕ} (hs : s ∈ 𝒜 d) (hu : IsUnit (f s))
    (n : ℕ) (a : A) (ha : a ∈ 𝒜 (n • d)) :
    evalAway f s hu (Away.mk 𝒜 hs n a ha) * f s ^ n = f a := by
  rw [evalAway_val, Away.val_mk, Localization.mk_eq_mk']
  have H := IsLocalization.mk'_spec (Localization.Away s) a
    (⟨s ^ n, ⟨n, rfl⟩⟩ : Submonoid.powers s)
  apply_fun (IsLocalization.Away.lift s hu : Localization.Away s →+* R) at H
  simpa only [map_mul, IsLocalization.Away.lift_eq, map_pow] using H

end

open AlgebraicGeometry CategoryTheory TopologicalSpace

end PiExponentSeshadri.Projective

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_ProjectiveLaurentVertex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponent.GeometrySupport.ProjectiveLaurentVertex

section

attribute [local instance] Classical.propDecidable
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

abbrev ChartExponent (i : ι) := {j : ι // j ≠ i} →₀ ℕ

end

attribute [local instance] Classical.propDecidable
open scoped BigOperators
end PiExponent.GeometrySupport.ProjectiveLaurentVertex

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_ProjectiveRatioCocycle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponent.ProjectiveO1

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MvPolynomial
open HomogeneousLocalization PiExponentSeshadri.Projective

variable {R σ : Type} [CommRing R]

attribute [local instance] MvPolynomial.gradedAlgebra

abbrev projectiveSpace (R σ : Type) [CommRing R] := Proj (PolyGrade R σ)
abbrev coordinateOpen (i : σ) : (projectiveSpace R σ).Opens :=
  Proj.basicOpen (PolyGrade R σ) (X i)

def coordinateRatio (i j : σ) (W : (projectiveSpace R σ).Opens)
    (hi : W ≤ coordinateOpen i) : Γ(projectiveSpace R σ, W) :=
  ⟨fun x => HomogeneousLocalization.mk
    ⟨1, ⟨X j, poly_X_mem j⟩, ⟨X i, poly_X_mem i⟩, hi x.2⟩,
   fun x => ⟨W, x.2, 𝟙 _, 1, ⟨X j, poly_X_mem j⟩, ⟨X i, poly_X_mem i⟩,
     (fun y => hi y.2), (fun _ => rfl)⟩⟩

theorem coordinateRatio_restrict (i j : σ) {V W : (projectiveSpace R σ).Opens}
    (h : V ≤ W) (hi : W ≤ coordinateOpen i) :
    (projectiveSpace R σ).presheaf.map (homOfLE h).op (coordinateRatio i j W hi) =
      coordinateRatio i j V (h.trans hi) := by
  apply Subtype.ext
  funext x
  rfl

theorem coordinateRatio_mul (i j k : σ) (W : (projectiveSpace R σ).Opens)
    (hi : W ≤ coordinateOpen i) (hj : W ≤ coordinateOpen j) :
    coordinateRatio i j W hi * coordinateRatio j k W hj = coordinateRatio i k W hi := by
  apply Subtype.ext
  funext x
  let : x.1.asHomogeneousIdeal.toIdeal.IsPrime := x.1.isPrime
  apply HomogeneousLocalization.val_injective
  change ((HomogeneousLocalization.mk ⟨1, ⟨X j, poly_X_mem j⟩, ⟨X i, poly_X_mem i⟩, hi x.2⟩ :
      HomogeneousLocalization.AtPrime (PolyGrade R σ) x.1.asHomogeneousIdeal.toIdeal) *
    (HomogeneousLocalization.mk ⟨1, ⟨X k, poly_X_mem k⟩, ⟨X j, poly_X_mem j⟩, hj x.2⟩ :
      HomogeneousLocalization.AtPrime (PolyGrade R σ) x.1.asHomogeneousIdeal.toIdeal)).val =
    (HomogeneousLocalization.mk ⟨1, ⟨X k, poly_X_mem k⟩, ⟨X i, poly_X_mem i⟩, hi x.2⟩ :
      HomogeneousLocalization.AtPrime (PolyGrade R σ) x.1.asHomogeneousIdeal.toIdeal).val
  rw [HomogeneousLocalization.val_mul, HomogeneousLocalization.val_mk, HomogeneousLocalization.val_mk, HomogeneousLocalization.val_mk]
  change Localization.mk (X j) (⟨X i, hi x.2⟩ : x.1.asHomogeneousIdeal.toIdeal.primeCompl) *
    Localization.mk (X k) (⟨X j, hj x.2⟩ : x.1.asHomogeneousIdeal.toIdeal.primeCompl) =
    Localization.mk (X k) (⟨X i, hi x.2⟩ : x.1.asHomogeneousIdeal.toIdeal.primeCompl)
  rw [Localization.mk_mul, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [OneMemClass.coe_one, one_mul, Submonoid.coe_mul]
  ring

end PiExponent.ProjectiveO1

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Polynomials_GradedSubring
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponent

open DirectSum

variable {A : Type*} [CommRing A]
  (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜]
  (S : Subring A)

def subringGrade (n : ℕ) : Submodule ℤ S :=
  (𝒜 n).comap S.subtype.toAddMonoidHom.toIntLinearMap

theorem subringGrade_independent : iSupIndep (subringGrade 𝒜 S) := by
  have h := (DirectSum.Decomposition.isInternal 𝒜).submodule_iSupIndep
  intro i
  rw [disjoint_iff_inf_le]
  intro x hx
  apply Subtype.ext
  apply (disjoint_iff_inf_le.mp (h i))
  refine ⟨hx.1, ?_⟩
  have hle : (⨆ j, ⨆ (_ : j ≠ i), subringGrade 𝒜 S j) ≤
      (⨆ j, ⨆ (_ : j ≠ i), 𝒜 j).comap S.subtype.toAddMonoidHom.toIntLinearMap := by
    refine iSup_le fun j => iSup_le fun hj => ?_
    exact Submodule.comap_mono (le_iSup_of_le j (le_iSup_of_le hj le_rfl))
  exact hle hx.2

theorem subringGrade_spans
    (hS : ∀ n x, x ∈ S → (decompose 𝒜 x n : A) ∈ S) :
    (⨆ n, subringGrade 𝒜 S n) = ⊤ := by
  classical
  apply top_unique
  intro x _
  let c : ℕ → S := fun n => ⟨decompose 𝒜 x.1 n, hS n x.1 x.2⟩
  have he : x = ∑ n ∈ (decompose 𝒜 x.1).support, c n := by
    apply Subtype.ext
    change x.1 = S.subtype (∑ n ∈ (decompose 𝒜 x.1).support, c n)
    rw [map_sum]
    exact (sum_support_decompose 𝒜 x.1).symm
  rw [he]
  apply Submodule.sum_mem
  intro n hn
  exact (le_iSup (subringGrade 𝒜 S) n) (show c n ∈ subringGrade 𝒜 S n from
    (decompose 𝒜 x.1 n).2)

@[instance_reducible]
def subringGradedAlgebra
    (hS : ∀ n x, x ∈ S → (decompose 𝒜 x n : A) ∈ S) :
    GradedAlgebra (subringGrade 𝒜 S) where
  one_mem := show (1 : A) ∈ 𝒜 0 from SetLike.one_mem_graded 𝒜
  mul_mem := by
    intro i j x y hx hy
    change (x.1 * y.1) ∈ 𝒜 (i + j)
    exact SetLike.mul_mem_graded hx hy
  toDecomposition :=
    (DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
      (subringGrade_independent 𝒜 S) (subringGrade_spans 𝒜 S hS)).chooseDecomposition

end PiExponent

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Polynomials_WeightedMonomialMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponent.WeightedCompactification

open MvPolynomial

variable {R ι σ : Type*} [CommRing R]

attribute [local instance] MvPolynomial.gradedAlgebra

def homogeneousMonomialMap (a : σ → ι →₀ ℕ) :
    MvPolynomial σ R →+* MvPolynomial Unit (MvPolynomial ι R) :=
  eval₂Hom (C.comp C) (fun s => X () * C (monomial (a s) 1))

@[simp]
theorem homogeneousMonomialMap_X (a : σ → ι →₀ ℕ) (s : σ) :
    homogeneousMonomialMap (R := R) a (X s) = X () * C (monomial (a s) 1) := by
  simp [homogeneousMonomialMap]

theorem homogeneousMonomialMap_homogeneous (a : σ → ι →₀ ℕ)
    {p : MvPolynomial σ R} {n : ℕ} (hp : p.IsHomogeneous n) :
    (homogeneousMonomialMap a p).IsHomogeneous n := by
  have h : (homogeneousMonomialMap a p).IsHomogeneous (1 * n) :=
    hp.eval₂ (C.comp C) (fun s => X () * C (monomial (a s) 1))
      (fun r => isHomogeneous_C _ _) (fun s => by
        simpa only [mul_comm] using isHomogeneous_C_mul_X (monomial (a s) (1 : R)) ())
  rw [Nat.one_mul] at h
  exact h

end PiExponent.WeightedCompactification

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Polynomials_WeightedMonomialImage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponent.WeightedCompactification

open MvPolynomial DirectSum

variable {R ι σ : Type*} [CommRing R]

attribute [local instance] MvPolynomial.gradedAlgebra

abbrev monomialImage (a : σ → ι →₀ ℕ) := (homogeneousMonomialMap (R := R) a).range

abbrev ambientGrade (R ι : Type*) [CommRing R] (n : ℕ) :=
  (homogeneousSubmodule Unit (MvPolynomial ι R) n).restrictScalars ℤ

def gradedMonomialMapInt (a : σ → ι →₀ ℕ) :
    homogeneousSubmodule σ R →+*ᵍ ambientGrade R ι where
  __ := homogeneousMonomialMap a
  map_mem := homogeneousMonomialMap_homogeneous a

theorem monomialImage_homogeneous (a : σ → ι →₀ ℕ) (n : ℕ)
    (p : MvPolynomial Unit (MvPolynomial ι R)) (hp : p ∈ monomialImage a) :
    (decompose (ambientGrade R ι) p n : MvPolynomial Unit (MvPolynomial ι R)) ∈
      monomialImage a := by
  obtain ⟨q, rfl⟩ := hp
  refine ⟨decompose (homogeneousSubmodule σ R) q n, ?_⟩
  exact (gradedMonomialMapInt a).map_directSumDecompose

abbrev imageGrade (a : σ → ι →₀ ℕ) := subringGrade (ambientGrade R ι) (monomialImage a)

instance imageGradedAlgebra (a : σ → ι →₀ ℕ) : GradedAlgebra (imageGrade (R := R) a) :=
  subringGradedAlgebra _ _ (monomialImage_homogeneous a)

def gradedImageMap (a : σ → ι →₀ ℕ) :
    homogeneousSubmodule σ R →+*ᵍ imageGrade (R := R) a where
  __ := (homogeneousMonomialMap a).rangeRestrict
  map_mem := homogeneousMonomialMap_homogeneous a

theorem gradedImageMap_surjective (a : σ → ι →₀ ℕ) :
    Function.Surjective (gradedImageMap (R := R) a) :=
  (homogeneousMonomialMap a).rangeRestrict_surjective

abbrev imageCoordinate (a : σ → ι →₀ ℕ) (s : σ) : monomialImage (R := R) a :=
  ⟨homogeneousMonomialMap a (X s), ⟨X s, rfl⟩⟩

theorem imageCoordinate_mem (a : σ → ι →₀ ℕ) (s : σ) :
    imageCoordinate (R := R) a s ∈ imageGrade a 1 :=
  homogeneousMonomialMap_homogeneous a (isHomogeneous_X R s)

def imageEvaluation (a : σ → ι →₀ ℕ) : monomialImage (R := R) a →+* MvPolynomial ι R :=
  (eval₂Hom (RingHom.id _) (fun _ : Unit => 1)).comp (monomialImage a).subtype

@[simp]
theorem imageEvaluation_coordinate (a : σ → ι →₀ ℕ) (s : σ) :
    imageEvaluation (R := R) a (imageCoordinate a s) = monomial (a s) 1 := by
  simp [imageEvaluation, imageCoordinate, homogeneousMonomialMap]

theorem unit_homogeneous_formula {p : MvPolynomial Unit R} {n : ℕ}
    (hp : p.IsHomogeneous n) :
    p = X () ^ n * C (eval (fun _ : Unit => 1) p) := by
  have he : eval₂Hom C (fun _ : Unit => X () * (1 : MvPolynomial Unit R)) =
      RingHom.id (MvPolynomial Unit R) := by
    apply MvPolynomial.ringHom_ext
    · intro r; simp
    · intro u; cases u; simp
  have hc : (C : R →+* MvPolynomial Unit R).comp (eval₂Hom (RingHom.id _) (fun _ : Unit => 1)) =
      eval₂Hom C (fun _ : Unit => (1 : MvPolynomial Unit R)) := by
    apply MvPolynomial.ringHom_ext <;> intro r <;> simp
  have h := PiExponentSeshadri.Projective.homogeneous_eval₂_scale hp C
    (fun _ : Unit => (1 : MvPolynomial Unit R)) (X ())
  change (eval₂Hom C (fun _ : Unit => X () * (1 : MvPolynomial Unit R))) p =
    X () ^ n * (eval₂Hom C (fun _ : Unit => (1 : MvPolynomial Unit R))) p at h
  rw [he, ← hc] at h
  exact h

theorem imageEvaluation_homogeneous_eq_zero (a : σ → ι →₀ ℕ)
    {p : monomialImage (R := R) a} {n : ℕ} (hp : p ∈ imageGrade a n)
    (he : imageEvaluation a p = 0) : p = 0 := by
  apply Subtype.ext
  have h := unit_homogeneous_formula hp
  change eval (fun _ : Unit => 1) p.1 = 0 at he
  change p.1 = X () ^ n * C (eval (fun _ : Unit => 1) p.1) at h
  rw [he, map_zero, mul_zero] at h
  exact h

end PiExponent.WeightedCompactification

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_WeightedCompactification
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponent.WeightedCompactification

open MvPolynomial HomogeneousLocalization
open PiExponentSeshadri.Projective
open AlgebraicGeometry CategoryTheory

variable {R ι σ : Type*} [CommRing R]

abbrev constantChart (a : σ → ι →₀ ℕ) (z : σ) :=
  HomogeneousLocalization.Away (imageGrade (R := R) a) (imageCoordinate a z)

def chartEvaluation (a : σ → ι →₀ ℕ) (z : σ) (hz : a z = 0) :
    constantChart (R := R) a z →+* MvPolynomial ι R :=
  evalAway (imageEvaluation a) (imageCoordinate a z)
    (by simp [hz])

@[simp]
theorem chartEvaluation_mk (a : σ → ι →₀ ℕ) (z : σ) (hz : a z = 0)
    (n : ℕ) (p : monomialImage (R := R) a) (hp : p ∈ imageGrade a (n • 1)) :
    chartEvaluation a z hz (Away.mk _ (imageCoordinate_mem a z) n p hp) =
      imageEvaluation a p := by
  have h := evalAway_mk_clear (imageEvaluation a) (imageCoordinate_mem a z)
    (show IsUnit (imageEvaluation a (imageCoordinate a z)) by simp [hz]) n p hp
  simpa [chartEvaluation, hz] using h

theorem chartEvaluation_injective (a : σ → ι →₀ ℕ) (z : σ) (hz : a z = 0) :
    Function.Injective (chartEvaluation (R := R) a z hz) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨n, p, hp, rfl⟩ := Away.mk_surjective _ (imageCoordinate_mem a z) x
  rw [chartEvaluation_mk] at hx
  have hpzero := imageEvaluation_homogeneous_eq_zero a hp hx
  subst p
  apply HomogeneousLocalization.val_injective
  simp [Away.val_mk, HomogeneousLocalization.val_zero, Localization.mk_zero]

def affineChartCoordinate (a : σ → ι →₀ ℕ) (z s : σ) : constantChart (R := R) a z :=
  Away.mk _ (imageCoordinate_mem a z) 1 (imageCoordinate a s)
    (by simpa using imageCoordinate_mem (R := R) a s)

@[simp]
theorem chartEvaluation_coordinate (a : σ → ι →₀ ℕ) (z s : σ) (hz : a z = 0) :
    chartEvaluation (R := R) a z hz (affineChartCoordinate a z s) =
      monomial (a s) 1 := by
  rw [affineChartCoordinate, chartEvaluation_mk, imageEvaluation_coordinate]

def imageConstant (a : σ → ι →₀ ℕ) (r : R) : monomialImage (R := R) a :=
  ⟨homogeneousMonomialMap a (C r), ⟨C r, rfl⟩⟩

theorem imageConstant_mem (a : σ → ι →₀ ℕ) (r : R) :
    imageConstant a r ∈ imageGrade a 0 :=
  homogeneousMonomialMap_homogeneous a (isHomogeneous_C σ r)

def affineChartConstant (a : σ → ι →₀ ℕ) (z : σ) (r : R) : constantChart (R := R) a z :=
  Away.mk _ (imageCoordinate_mem a z) 0 (imageConstant a r)
    (show imageConstant a r ∈ imageGrade a (0 • 1) from imageConstant_mem a r)

@[simp]
theorem chartEvaluation_constant (a : σ → ι →₀ ℕ) (z : σ) (hz : a z = 0) (r : R) :
    chartEvaluation a z hz (affineChartConstant a z r) = C r := by
  rw [affineChartConstant, chartEvaluation_mk]
  simp [imageEvaluation, imageConstant, homogeneousMonomialMap]

theorem chartEvaluation_surjective (a : σ → ι →₀ ℕ) (z : σ) (hz : a z = 0)
    (coordinate : ι → σ) (hcoordinate : ∀ i, a (coordinate i) = Finsupp.single i 1) :
    Function.Surjective (chartEvaluation (R := R) a z hz) := by
  intro p
  induction p using MvPolynomial.induction_on with
  | C r => exact ⟨affineChartConstant a z r, chartEvaluation_constant a z hz r⟩
  | add p q hp hq =>
    obtain ⟨x, rfl⟩ := hp
    obtain ⟨y, rfl⟩ := hq
    exact ⟨x + y, map_add _ _ _⟩
  | mul_X p i hp =>
    obtain ⟨x, rfl⟩ := hp
    refine ⟨x * affineChartCoordinate a z (coordinate i), ?_⟩
    rw [map_mul, chartEvaluation_coordinate, hcoordinate]
    rfl

def constantChartEquiv (a : σ → ι →₀ ℕ) (z : σ) (hz : a z = 0)
    (coordinate : ι → σ) (hcoordinate : ∀ i, a (coordinate i) = Finsupp.single i 1) :
    constantChart (R := R) a z ≃+* MvPolynomial ι R :=
  RingEquiv.ofBijective (chartEvaluation a z hz)
    ⟨chartEvaluation_injective a z hz, chartEvaluation_surjective a z hz coordinate hcoordinate⟩

def constantProjectiveChartIso (a : σ → ι →₀ ℕ) (z : σ) (hz : a z = 0)
    (coordinate : ι → σ) (hcoordinate : ∀ i, a (coordinate i) = Finsupp.single i 1) :
    (Proj.basicOpen (imageGrade (R := R) a) (imageCoordinate a z)).toScheme ≅
      Spec (CommRingCat.of (MvPolynomial ι R)) := by
  let e : CommRingCat.of (constantChart (R := R) a z) ≅
      CommRingCat.of (MvPolynomial ι R) :=
    (constantChartEquiv (R := R) a z hz coordinate hcoordinate).toCommRingCatIso
  exact Proj.basicOpenIsoSpec _ _ (imageCoordinate_mem a z) (by decide) ≪≫
    Scheme.Spec.mapIso e.symm.op

end PiExponent.WeightedCompactification

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Polynomials_SurjectiveGradedMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponent

open DirectSum HomogeneousLocalization
open scoped HomogeneousIdeal

variable {A B S T : Type*} [CommRing A] [CommRing B]
  [SetLike S A] [AddSubgroupClass S A] [SetLike T B] [AddSubgroupClass T B]
  {𝒜 : ℕ → S} {ℬ : ℕ → T} [GradedRing 𝒜] [GradedRing ℬ]

theorem gradedMap_homogeneous_lift (f : 𝒜 →+*ᵍ ℬ) (hf : Function.Surjective f)
    {n : ℕ} {y : B} (hy : y ∈ ℬ n) : ∃ x, x ∈ 𝒜 n ∧ f x = y := by
  obtain ⟨x, hx⟩ := hf y
  refine ⟨decompose 𝒜 x n, (decompose 𝒜 x n).2, ?_⟩
  rw [f.map_directSumDecompose, hx]
  exact decompose_of_mem_same ℬ hy

theorem gradedMap_irrelevant_le_map (f : 𝒜 →+*ᵍ ℬ) (hf : Function.Surjective f) :
    ℬ₊ ≤ 𝒜₊.map f := by
  rw [HomogeneousIdeal.irrelevant_le]
  intro n hn y hy
  obtain ⟨x, hx, rfl⟩ := gradedMap_homogeneous_lift f hf hy
  exact Ideal.mem_map_of_mem f (HomogeneousIdeal.mem_irrelevant_of_mem 𝒜 hn hx)

end PiExponent

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_WeightedCompactificationImmersion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponent.WeightedCompactification

open MvPolynomial HomogeneousLocalization
open PiExponentSeshadri.Projective
open AlgebraicGeometry CategoryTheory
open scoped HomogeneousIdeal

universe u
variable {R ι σ : Type u} [CommRing R]

attribute [local instance] MvPolynomial.gradedAlgebra

abbrev projectiveMonomialMap (a : σ → ι →₀ ℕ) :
    Proj (imageGrade (R := R) a) ⟶ Proj (homogeneousSubmodule σ R) :=
  Proj.map (gradedImageMap a) (gradedMap_irrelevant_le_map _ (gradedImageMap_surjective a))

@[simp]
theorem projectiveMonomialMap_preimage (a : σ → ι →₀ ℕ) (s : σ) :
    projectiveMonomialMap (R := R) a ⁻¹ᵁ Proj.basicOpen (homogeneousSubmodule σ R) (X s) =
      Proj.basicOpen (imageGrade a) (imageCoordinate a s) := rfl


end PiExponent.WeightedCompactification

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Polynomials_SimplexCounting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace PiExponent

open Filter Topology

noncomputable def realWeightedSimplex {d : ℕ} (w : Fin d → ℝ) (H : ℝ) :
    Finset (Fin d → ℕ) := by
  classical
  exact (Fintype.piFinset (fun i => Finset.range (⌊H / w i⌋₊ + 1))).filter
    (fun a => ∑ i, w i * (a i : ℝ) ≤ H)

theorem mem_realWeightedSimplex {d : ℕ} {w : Fin d → ℝ}
    (hw : ∀ i, 0 < w i) {H : ℝ} {a : Fin d → ℕ} :
    a ∈ realWeightedSimplex w H ↔ ∑ i, w i * (a i : ℝ) ≤ H := by
  classical
  constructor
  · exact fun h => (Finset.mem_filter.mp h).2
  · intro h
    refine Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr ?_, h⟩
    intro i
    apply Finset.mem_range.mpr
    apply Nat.lt_succ_of_le
    apply Nat.le_floor
    apply (le_div_iff₀ (hw i)).mpr
    rw [mul_comm]
    exact (Finset.single_le_sum (f := fun j => w j * (a j : ℝ))
      (fun j _ => mul_nonneg (hw j).le (Nat.cast_nonneg _)) (Finset.mem_univ i)).trans h

end PiExponent

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Polynomials_SimplexRationalWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace PiExponent

theorem positive_rational_weights_common_denominator {d : ℕ}
    (ρ : Fin d → ℚ) (hρ : ∀ i, 0 < ρ i) :
    ∃ D : ℕ, 0 < D ∧ ∃ w : Fin d → ℕ,
      (∀ i, 0 < w i) ∧ ∀ i, (ρ i : ℝ) = (w i : ℝ) / (D : ℝ) := by
  classical
  let D : ℕ := ∏ i, (ρ i).den
  have hD : 0 < D := Finset.prod_pos (fun i _ => (ρ i).den_pos)
  have hd : ∀ i, (ρ i).den ∣ D :=
    fun i => Finset.dvd_prod_of_mem (fun j => (ρ j).den) (Finset.mem_univ i)
  choose k hk using hd
  have hkpos : ∀ i, 0 < k i := by
    intro i
    by_contra h
    have hkzero : k i = 0 := by omega
    have := hk i
    rw [hkzero, mul_zero] at this
    omega
  let w : Fin d → ℕ := fun i => (ρ i).num.toNat * k i
  refine ⟨D, hD, w, ?_, ?_⟩
  · intro i
    have hn : 0 < (ρ i).num := Rat.num_pos.mpr (hρ i)
    exact Nat.mul_pos (by omega) (hkpos i)
  · intro i
    have hnum : (((ρ i).num.toNat : ℕ) : ℝ) = ((ρ i).num : ℝ) := by
      exact_mod_cast (Int.toNat_of_nonneg (Rat.num_pos.mpr (hρ i)).le)
    have hcastD : (D : ℝ) = ((ρ i).den : ℝ) * (k i : ℝ) := by
      exact_mod_cast hk i
    have hkne : (k i : ℝ) ≠ 0 := by exact_mod_cast (hkpos i).ne'
    have hdenne : ((ρ i).den : ℝ) ≠ 0 := by exact_mod_cast (ρ i).den_ne_zero
    rw [Rat.cast_def, hcastD]
    change ((ρ i).num : ℝ) / ((ρ i).den : ℝ) =
      (((ρ i).num.toNat * k i : ℕ) : ℝ) / (((ρ i).den : ℝ) * (k i : ℝ))
    rw [Nat.cast_mul, hnum]
    field_simp

end PiExponent

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_WeightedGeometryScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace PiExponent.WeightedGeometryScale

theorem exists_power_scale {n : ℕ} (w : Fin n → ℚ) (hw : ∀ i, 0 < w i) :
    ∃ R : ℕ, 0 < R ∧ ∃ e : Fin n → ℕ,
      (∀ i, 0 < e i) ∧ ∀ i, w i * (e i : ℚ) = R := by
  obtain ⟨R,hR,e,he,heq⟩ := positive_rational_weights_common_denominator
    (fun i => (w i)⁻¹) (fun i => inv_pos.mpr (hw i))
  refine ⟨R,hR,e,he,fun i => ?_⟩
  have hi : (w i)⁻¹ = (e i : ℚ) / (R : ℚ) := by
    apply Rat.cast_injective (α := ℝ)
    simpa only [Rat.cast_inv, Rat.cast_div, Rat.cast_natCast] using heq i
  have hR' : (R : ℚ) ≠ 0 := by exact_mod_cast hR.ne'
  have hwi : w i ≠ 0 := (hw i).ne'
  have hi' := (eq_div_iff hR').mp hi
  rw [← hi']
  field_simp

theorem exists_common_scale {n : ℕ} (w v : Fin n → ℚ)
    (hw : ∀ i, 0 < w i) (hv : ∀ i, 0 < v i) :
    ∃ R : ℕ, 0 < R ∧ ∃ e t : Fin n → ℕ,
      (∀ i, 0 < e i) ∧ (∀ i, 0 < t i) ∧
      (∀ i, w i * (e i : ℚ) = R) ∧
      (∀ i, v i * (t i : ℚ) = R) := by
  obtain ⟨A,hA,e,he,heq⟩ := exists_power_scale w hw
  obtain ⟨B,hB,t,ht,htq⟩ := exists_power_scale v hv
  refine ⟨A*B,Nat.mul_pos hA hB,fun i => e i * B,fun i => t i * A,
    fun i => Nat.mul_pos (he i) hB,fun i => Nat.mul_pos (ht i) hA,?_,?_⟩
  · intro i
    push_cast
    rw [← mul_assoc, heq]
  · intro i
    push_cast
    rw [← mul_assoc, htq, mul_comm]

def monomials {n : ℕ} (w : Fin n → ℚ) (R : ℚ) : Finset (Fin n →₀ ℕ) :=
  (realWeightedSimplex (fun i => (w i : ℝ)) (R : ℝ)).image Finsupp.equivFunOnFinite.symm

@[simp] theorem mem_monomials {n : ℕ} (w : Fin n → ℚ) (hw : ∀ i, 0 < w i)
    (R : ℚ) (a : Fin n →₀ ℕ) :
    a ∈ monomials w R ↔ (∑ i, w i * (a i : ℚ)) ≤ R := by
  classical
  rw [monomials, Finset.mem_image]
  constructor
  · rintro ⟨b,hb,rfl⟩
    have h := (mem_realWeightedSimplex (fun i => by exact_mod_cast hw i)).mp hb
    exact_mod_cast h
  · intro ha
    refine ⟨fun i => a i,?_,Finsupp.equivFunOnFinite_symm_coe a⟩
    apply (mem_realWeightedSimplex (fun i => by exact_mod_cast hw i)).mpr
    exact_mod_cast ha

theorem zero_mem_monomials {n : ℕ} (w : Fin n → ℚ) (hw : ∀ i, 0 < w i)
    (R : ℚ) (hR : 0 ≤ R) : (0 : Fin n →₀ ℕ) ∈ monomials w R := by
  rw [mem_monomials w hw]
  simpa using hR

theorem pure_mem_monomials {n : ℕ} (w : Fin n → ℚ) (hw : ∀ i, 0 < w i)
    (R : ℚ) (e : Fin n → ℕ) (he : ∀ i, w i * (e i : ℚ) = R) (i : Fin n) :
    Finsupp.single i (e i) ∈ monomials w R := by
  classical
  rw [mem_monomials w hw]
  simpa [Finsupp.single_apply] using (he i).le

theorem coordinate_mem_monomials {n : ℕ} (w : Fin n → ℚ) (hw : ∀ i, 0 < w i)
    (R : ℚ) (e : Fin n → ℕ) (hepos : ∀ i, 0 < e i)
    (he : ∀ i, w i * (e i : ℚ) = R) (i : Fin n) :
    Finsupp.single i 1 ∈ monomials w R := by
  classical
  rw [mem_monomials w hw]
  have hi : (1 : ℚ) ≤ e i := by exact_mod_cast hepos i
  have h := mul_le_mul_of_nonneg_left hi (hw i).le
  simpa [Finsupp.single_apply, he] using h

structure Scale {n : ℕ} (w v : Fin n → ℚ) where
  radius : ℕ
  radius_pos : 0 < radius
  degreePowers : Fin n → ℕ
  jetPowers : Fin n → ℕ
  degreePowers_pos : ∀ i, 0 < degreePowers i
  jetPowers_pos : ∀ i, 0 < jetPowers i
  degreePowers_eq : ∀ i, w i * (degreePowers i : ℚ) = radius
  jetPowers_eq : ∀ i, v i * (jetPowers i : ℚ) = radius

def chooseScale {n : ℕ} (w v : Fin n → ℚ)
    (hw : ∀ i, 0 < w i) (hv : ∀ i, 0 < v i) : Scale w v := by
  apply Classical.choice
  obtain ⟨R,hR,e,t,he,ht,heq,htq⟩ := exists_common_scale w v hw hv
  exact ⟨⟨R,hR,e,t,he,ht,heq,htq⟩⟩

namespace Scale
variable {n : ℕ} {w v : Fin n → ℚ} (s : Scale w v)

abbrev Index := ↥(monomials w s.radius)

def exponents (i : s.Index) : Fin n →₀ ℕ := i.val

def constantIndex (hw : ∀ i, 0 < w i) : s.Index :=
  ⟨0,zero_mem_monomials w hw s.radius (by exact_mod_cast s.radius_pos.le)⟩

def coordinateIndex (hw : ∀ i, 0 < w i) (i : Fin n) : s.Index :=
  ⟨Finsupp.single i 1,coordinate_mem_monomials w hw s.radius s.degreePowers
    s.degreePowers_pos s.degreePowers_eq i⟩

def pureIndex (hw : ∀ i, 0 < w i) (i : Fin n) : s.Index :=
  ⟨Finsupp.single i (s.degreePowers i),pure_mem_monomials w hw s.radius
    s.degreePowers s.degreePowers_eq i⟩

@[simp] theorem exponents_constant (hw : ∀ i, 0 < w i) :
    s.exponents (s.constantIndex hw) = 0 := rfl

@[simp] theorem exponents_coordinate (hw : ∀ i, 0 < w i) (i : Fin n) :
    s.exponents (s.coordinateIndex hw i) = Finsupp.single i 1 := rfl

@[simp] theorem exponents_pure (hw : ∀ i, 0 < w i) (i : Fin n) :
    s.exponents (s.pureIndex hw i) = Finsupp.single i (s.degreePowers i) := rfl

end Scale

end PiExponent.WeightedGeometryScale

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_Parameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent

structure Parameters (ν : ℝ) where
  theta : ℚ
  A : ℚ
  B : ℚ
  C : ℚ
  eta : ℝ
  theta_pos : 0 < (theta : ℝ)
  theta_lt_A : (theta : ℝ) < A
  A_lt_B : (A : ℝ) < B
  B_lt_one : (B : ℝ) < 1
  approximation_gap : 1 - (theta : ℝ) < ν * ((A : ℝ) - theta)
  one_lt_C : 1 < (C : ℝ)
  B_lt_inv_C : (B : ℝ) < 1 / C
  B_lt_C_theta : (B : ℝ) < (C : ℝ) * theta
  C_theta_lt_one : (C : ℝ) * theta < 1
  eta_pos : 0 < eta
  eta_lt_one : eta < 1
  gap_pos : 0 < ν * ((A : ℝ) * (1 - eta) - theta) - (1 - theta)

end PiExponent

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_WeightSeparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentApprox

noncomputable section

def weightSeparationFactor (m : ℕ) (C w0 v0 theta : ℝ) : ℝ :=
  C * (max 1 (max v0 (1 / theta) / min w0 1)) ^ (m + 1)

def SeparatedWeightGrowth (m : ℕ) (D : ℝ) (x : ℕ → ℝ) : Prop :=
  ∀ i, 0 < i → i ≤ m → D * (∏ j ∈ Finset.range i, x j) < x i

end
end PiExponentApprox

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_Dimension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Filter
open scoped Topology

namespace PiExponent

def dimensionK (C : ℝ) (m : ℕ) : ℕ := ⌊C ^ m⌋₊

def dimensionW (B : ℝ) (m : ℕ) : ℝ := (B ^ m)⁻¹

def dimensionV (theta B C : ℝ) (m : ℕ) : ℝ :=
  2 * (dimensionK C m : ℝ) * theta ^ m * dimensionW B m

end PiExponent

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_AdmissibleParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent

noncomputable def interpolationSeparationConstant (m : ℕ) (sigma : ℚ) : ℝ :=
  2 * ((m : ℝ) + 2) ^ (m + 2) *
    (1 + ((m : ℝ) + 2) / (sigma : ℝ)) ^ (m + 2)

noncomputable def weightErrorCoefficient (nu theta : ℝ) (K : ℕ) : ℝ :=
  theta + Real.log 4 + Real.log (2 * (K : ℝ)) + nu + Real.log (200 * (K : ℝ))

structure AdmissibleParameters (nu Lambda c : ℝ) where
  base : Parameters nu
  epsilon : ℝ
  F0 : ℝ
  m : ℕ
  K : ℕ
  w0 : ℚ
  v0 : ℚ
  sigma : ℚ
  p : ℕ → ℤ
  q : ℕ → ℕ
  x : ℕ → ℝ
  wstar : ℝ
  epsilon_pos : 0 < epsilon
  epsilon_lt_gap : epsilon <
    nu * ((base.A : ℝ) * (1 - base.eta) - base.theta) - (1 - base.theta)
  epsilon_le_half : epsilon ≤ 1 / 2
  F0_pos : 0 < F0
  F0_large : 2 / (base.theta : ℝ) < F0
  initial_margin : nu / F0 < epsilon / 3
  m_pos : 1 ≤ m
  K_eq : K = dimensionK (base.C : ℝ) m
  K_pos : 1 ≤ K
  w0_eq : (w0 : ℝ) = dimensionW (base.B : ℝ) m
  v0_eq : (v0 : ℝ) = dimensionV (base.theta : ℝ) base.B base.C m
  w0_pos : 0 < (w0 : ℝ)
  v0_pos : 0 < (v0 : ℝ)
  volume_eq : (K : ℝ) * ((w0 : ℝ) / v0) * (base.theta : ℝ) ^ m = 1 / 2
  volume_lt_one : (K : ℝ) * (base.theta : ℝ) ^ m < 1
  dimension_margin :
    (Lambda * F0 * (m : ℝ) + 2 * Real.log 2) / (v0 : ℝ) +
      100 * (K : ℝ) / (w0 : ℝ) < epsilon / 3
  collision_margin : 2 < c *
    (base.eta ^ 2 * (K : ℝ) * (base.theta : ℝ) ^ m /
      (((m : ℝ) + 1) * (v0 : ℝ) * (base.A : ℝ) ^ m))
  sigma_pos : 0 < (sigma : ℝ)
  sigma_volume : (1 + 3 * (sigma : ℝ)) ^ (m + 1) *
    ((K : ℝ) * ((w0 : ℝ) / v0) * (base.theta : ℝ) ^ m) < 1
  sigma_centers : (1 + 3 * (sigma : ℝ)) ^ m *
    ((K : ℝ) * (base.theta : ℝ) ^ m) < 1
  sigma_theta : (1 + (sigma : ℝ)) * (base.theta : ℝ) < 1
  x_zero : x 0 = 1
  x_log : ∀ n, x (n + 1) = (Nat.ceil (Real.log (q n)) : ℝ)
  approximations : ∀ n, 2 ≤ q n ∧ p n ≠ 0 ∧
    |Real.pi - (p n : ℝ) / q n| ≤ (q n : ℝ) ^ (-nu)
  x_one_le : ∀ i, 1 ≤ x i
  weight_growth : PiExponentApprox.SeparatedWeightGrowth m
    (PiExponentApprox.weightSeparationFactor m (interpolationSeparationConstant m sigma)
      w0 v0 base.theta) x
  wstar_pos : 0 < wstar
  wstar_lower : ∀ i : Fin m, wstar ≤ x (i.val + 1)
  wstar_attained : ∃ i : Fin m, wstar = x (i.val + 1)
  weight_margin : Lambda * (∑ i : Fin m, 1 / x (i.val + 1)) +
    weightErrorCoefficient nu base.theta K / wstar < epsilon / 3

namespace AdmissibleParameters

variable {nu Lambda c : ℝ} (d : AdmissibleParameters nu Lambda c)

noncomputable def rationalWeight : ℕ → ℚ
  | 0 => 1
  | n + 1 => (Nat.ceil (Real.log (d.q n)) : ℚ)

theorem cast_rationalWeight (i : ℕ) : (d.rationalWeight i : ℝ) = d.x i := by
  cases i with
  | zero => simpa [rationalWeight] using d.x_zero.symm
  | succ n => simpa [rationalWeight] using (d.x_log n).symm

theorem rationalWeight_pos (i : ℕ) : 0 < d.rationalWeight i := by
  have h : (0 : ℝ) < (d.rationalWeight i : ℝ) := by
    rw [d.cast_rationalWeight]
    exact zero_lt_one.trans_le (d.x_one_le i)
  exact_mod_cast h

end AdmissibleParameters

end PiExponent

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_AdmissibleCurveWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.AdmissibleParameters
noncomputable section
open scoped BigOperators
variable {nu Lambda c : ℝ} (d : AdmissibleParameters nu Lambda c)

def curveDegreeWeights : Fin (d.m + 1) → ℚ :=
  Fin.cases d.w0 (fun i => d.rationalWeight (i.val + 1))

def curveJetWeights : Fin (d.m + 1) → ℚ :=
  Fin.cases d.v0 (fun i => d.rationalWeight (i.val + 1) / d.base.theta)

@[simp] lemma curveDegreeWeights_zero : d.curveDegreeWeights 0 = d.w0 := rfl
@[simp] lemma curveDegreeWeights_succ (i : Fin d.m) :
    d.curveDegreeWeights i.succ = d.rationalWeight (i.val + 1) := rfl
@[simp] lemma curveJetWeights_zero : d.curveJetWeights 0 = d.v0 := rfl
@[simp] lemma curveJetWeights_succ (i : Fin d.m) :
    d.curveJetWeights i.succ = d.rationalWeight (i.val + 1) / d.base.theta := rfl

lemma curveDegreeWeights_pos (i : Fin (d.m + 1)) : 0 < d.curveDegreeWeights i := by
  refine Fin.cases ?_ (fun i => ?_) i
  · exact_mod_cast d.w0_pos
  · simpa only [curveDegreeWeights_succ] using d.rationalWeight_pos (i.val + 1)

lemma curveJetWeights_pos (i : Fin (d.m + 1)) : 0 < d.curveJetWeights i := by
  refine Fin.cases ?_ (fun i => ?_) i
  · exact_mod_cast d.v0_pos
  · exact div_pos (d.rationalWeight_pos _) (by exact_mod_cast d.base.theta_pos)

end
end PiExponent.AdmissibleParameters

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_WeightedCompactificationGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponent.WeightedCompactification

open MvPolynomial AlgebraicGeometry CategoryTheory Topology

universe u
variable {R ι σ : Type u} [CommRing R]

def affineChartMap (a : σ → ι →₀ ℕ) (z : σ) (hz : a z = 0)
    (coordinate : ι → σ) (hcoordinate : ∀ i, a (coordinate i) = Finsupp.single i 1) :
    Spec (CommRingCat.of (MvPolynomial ι R)) ⟶ Proj (imageGrade (R := R) a) :=
  (constantProjectiveChartIso (R := R) a z hz coordinate hcoordinate).inv ≫
    (Proj.basicOpen (imageGrade a) (imageCoordinate a z)).ι

end PiExponent.WeightedCompactification

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_AdmissibleBlowupGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.AdmissibleBlowupGeometry
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry
open WeightedGeometryScale
variable {ν Λ D : ℝ} (d : AdmissibleParameters ν Λ D)

def scale : Scale d.curveDegreeWeights d.curveJetWeights :=
  chooseScale d.curveDegreeWeights d.curveJetWeights
    d.curveDegreeWeights_pos d.curveJetWeights_pos

abbrev Index := (scale d).Index
abbrev exponents : Index d → Fin (d.m+1) →₀ ℕ := (scale d).exponents

end PiExponent.AdmissibleBlowupGeometry

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_AddEquivSignedSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.AddEquivSignedSum
open scoped BigOperators

theorem map_signed_sum {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (E : A ≃+ B) (q : ℕ) (f : Fin (q+2) → A) :
    E (∑ k, (-1 : ℤ)^k.val • f k) = ∑ k, (-1 : ℤ)^k.val • E (f k) := by
  simp only [map_sum, map_zsmul]

theorem map_signed_sum_eq {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (E : A ≃+ B) (q : ℕ) (f : Fin (q+2) → A) (g : Fin (q+2) → B)
    (h : ∀ k, E (f k) = g k) :
    E (∑ k, (-1 : ℤ)^k.val • f k) = ∑ k, (-1 : ℤ)^k.val • g k := by
  rw [map_signed_sum]
  exact Finset.sum_congr rfl (fun k _ => congrArg (fun z => (-1 : ℤ)^k.val • z) (h k))

end PiExponent.AddEquivSignedSum

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_AdditiveKernelTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.AdditiveKernelTransport

variable {A A' B B' : Type*}
  [AddCommGroup A] [AddCommGroup A'] [AddCommGroup B] [AddCommGroup B']

def kernelEquiv (e : A ≃+ B) (e' : A' ≃+ B')
    (d : A →+ A') (D : B →+ B') (h : ∀ x, e' (d x) = D (e x)) :
    d.ker ≃+ D.ker where
  toFun c := ⟨e c.val, by
    change D (e c.val) = 0
    rw [← h, c.property, map_zero]⟩
  invFun c := ⟨e.symm c.val, by
    change d (e.symm c.val) = 0
    apply e'.injective
    rw [h, e.apply_symm_apply, map_zero]
    exact c.property⟩
  left_inv c := Subtype.ext (e.symm_apply_apply c.val)
  right_inv c := Subtype.ext (e.apply_symm_apply c.val)
  map_add' c b := Subtype.ext (map_add e c.val b.val)

end PiExponent.AdditiveKernelTransport

end OAI
end


