-- Prove2me | Definitions.Def_OAIQ032L003
-- name    : OAIQ032L003
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T19:45:21.764981+00:00
-- url     : https://prove2.me/theorems/8672224d-d67b-43c4-bca8-149834d9bda5
-- title:
--   Definitions bundle OAIQ032L003 of the split of OpenAI, Lech's multiplicity conjecture (result family 194)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Lech.dutta_domain`, carved from OpenAI's openai/math development (OpenAI, *Lech's multiplicity conjecture (result family 194)*, OpenAI Math Release, September 23, 2026, result family 194, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 207 declarations of OpenAI's Lean: 94 definitions, 1 inductive type or structure, 2 instances and 110 theorems. The definitions and types are `OAI.Lech.ComplexExtension.NatDouble`, `OAI.Lech.ComplexExtension.mapExtendIso`, `OAI.Lech.ComplexExtension.mapExtendXIso`, `OAI.Lech.ComplexLift.factor`, `OAI.Lech.ComplexLift.lift`, `OAI.Lech.Conductor.linearMap`, `OAI.Lech.DoubleCech.puncture`, `OAI.Lech.DoubleCech.switch`, `OAI.Lech.DoubleCech.term`, `OAI.Lech.EventuallyPolynomial`, `OAI.Lech.FactorNormalization.denominator`, `OAI.Lech.FactorNormalization.roots`, `OAI.Lech.FilteredCech.divide`, `OAI.Lech.FilteredCech.tensorBic`, `OAI.Lech.FilteredCech.term`, `OAI.Lech.FilteredFraction.augmentationEquiv`, `OAI.Lech.FilteredFraction.divide`, `OAI.Lech.FilteredFraction.fraction`, `OAI.Lech.FilteredFraction.inverseFactor`, `OAI.Lech.FilteredFraction.piece`, `OAI.Lech.FilteredFraction.restrict`, `OAI.Lech.GradedChart.denominator`, `OAI.Lech.GradedChart.restrict`, `OAI.Lech.GradedChart.term`, `OAI.Lech.Grading.beforeQuotient`, `OAI.Lech.Grading.imageDecompose`, `OAI.Lech.Grading.imageDecomposition`, `OAI.Lech.Grading.imagePiece`, `OAI.Lech.Grading.pieceMap`, `OAI.Lech.Grading.polynomialMap`, `OAI.Lech.Homogeneous.awayMap`, `OAI.Lech.Homogeneous.fraction`, `OAI.Lech.Homogeneous.gradedMap`, `OAI.Lech.Homogeneous.kernelFraction`, `OAI.Lech.IdealGraded.Ring`, `OAI.Lech.IdealGraded.coefficient`, `OAI.Lech.IdealGraded.component`, `OAI.Lech.IdealGraded.generator`, `OAI.Lech.IdealGraded.monomial`, `OAI.Lech.IdealGraded.quotientR` and 55 more.
--
--   **Sources.** They come from these modules of lean/OAI/RingTheory/Multiplicity, in whole or in part: `Multiplicity_BicomplexImageLift`, `Multiplicity_FilteredCechAugmentationRing`, `Multiplicity_FilteredCechAugmented`, `Multiplicity_FilteredFractionReesDenominator`, `Multiplicity_GradedChartCochains`, `Multiplicity_IdealGradedRing`, `Multiplicity_LechBoundedEquiv`, `Multiplicity_LechCokernelComp`, `Multiplicity_LechConnectingIso`, `Multiplicity_LechPiIso`, `Multiplicity_NativeDescentCanonicalAlg`, `Multiplicity_PerfectDomainStagesTensorTo`, `Multiplicity_PowerSeriesFinDimension`, `Multiplicity_PrimitiveChartFaithfullyFlat`, `Multiplicity_ProductSourceCoverFaceSlice`, `Multiplicity_RestrictedPolynomialImageCechComparisonHomology`, `Multiplicity_RootBundleChartsDenominator`, `Multiplicity_RootCoactionT`, `Multiplicity_SeparableOrderNormalizedLength`, `Multiplicity_SignedCechBicRow`, `Multiplicity_StandardFactorChartsL`, `Multiplicity_TensorTotalHomologyProperty`, `Multiplicity_TotalGhostRowHom`, `Multiplicity_TwistedLocalizationPieceMap`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ032L011`, `OAIQ032L012`, `OAIQ032L013`, `OAIQ032L014`, `OAIQ032L015`, `OAIQ032L016`, `OAIQ032L017` and `OAIQ032L018`; the statement `OAI_Lech_complex_estimate_basis`; the proof of `OAI.Lech.LinearNormalization.exists_linear_normalization`.
-- source:
--   OpenAI, Lech's multiplicity conjecture (result family 194), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 194; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Lechs-multiplicity-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/RingTheory/Multiplicity at commit adc7f12

import Mathlib

section
-- module Solutions.OAIQ032_LECH.Multiplicity_LechBoundedEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory


namespace Lech.Grading
open DirectSum
variable {R M N ι : Type*} [Ring R] [AddCommGroup M] [AddCommGroup N]
  [Module R M] [Module R N] [DecidableEq ι]
variable (G : ι → Submodule R M) [Decomposition G]
variable (f : M →ₗ[R] N)

def imagePiece (i : ι) : Submodule R N := (G i).map f

def pieceMap (i : ι) : G i →ₗ[R] imagePiece G f i :=
  (f.comp (G i).subtype).codRestrict _ (fun x => Submodule.mem_map_of_mem x.property)

omit [DecidableEq ι] [Decomposition G] in
@[simp] lemma pieceMap_coe (i : ι) (x : G i) :
    (pieceMap G f i x : N) = f (x : M) := rfl

def beforeQuotient : M →ₗ[R] ⨁ i, imagePiece G f i :=
  (DirectSum.lmap (pieceMap G f)).comp (decomposeLinearEquiv G).toLinearMap

@[simp] lemma beforeQuotient_piece (i : ι) (x : G i) :
    beforeQuotient G f x = DirectSum.lof R ι (fun i => ↥(imagePiece G f i)) i (pieceMap G f i x) := by
  simp [beforeQuotient]

lemma kernel_le_beforeQuotient (hf : f.ker.IsHomogeneous G) :
    f.ker ≤ (beforeQuotient G f).ker := by
  intro x hx
  apply DFinsupp.ext
  intro i
  apply Subtype.ext
  change f (decompose G x i : M) = 0
  exact hf i hx

noncomputable def imageDecompose (hs : Function.Surjective f)
    (hf : f.ker.IsHomogeneous G) : N →ₗ[R] ⨁ i, imagePiece G f i :=
  ((f.ker).liftQ (beforeQuotient G f) (kernel_le_beforeQuotient G f hf)).comp
    (f.quotKerEquivOfSurjective hs).symm.toLinearMap

@[simp] lemma imageDecompose_map (hs : Function.Surjective f)
    (hf : f.ker.IsHomogeneous G) (x : M) :
    imageDecompose G f hs hf (f x) = beforeQuotient G f x := by
  simp only [imageDecompose, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearMap.quotKerEquivOfSurjective_symm_apply, Submodule.liftQ_apply]

lemma recompose_beforeQuotient :
    (DirectSum.coeLinearMap (imagePiece G f)).comp (beforeQuotient G f) = f := by
  apply DirectSum.decompose_lhom_ext G
  intro i
  ext x
  simp [beforeQuotient_piece]

@[instance_reducible]
noncomputable def imageDecomposition (hs : Function.Surjective f)
    (hf : f.ker.IsHomogeneous G) : Decomposition (imagePiece G f) :=
  Decomposition.ofLinearMap (imagePiece G f) (imageDecompose G f hs hf)
    (by
      ext y
      obtain ⟨x, rfl⟩ := hs y
      simpa only [LinearMap.comp_apply, LinearMap.id_apply, imageDecompose_map] using
        DFunLike.congr_fun (recompose_beforeQuotient G f) x)
    (by
      apply DirectSum.linearMap_ext
      intro i
      apply LinearMap.ext
      intro x
      obtain ⟨a, ha, he⟩ := x.property
      have hx : x = pieceMap G f i ⟨a, ha⟩ := Subtype.ext he.symm
      rw [hx]
      simp only [LinearMap.comp_apply, DirectSum.coeLinearMap_lof,
        LinearMap.id_apply, pieceMap_coe, imageDecompose_map]
      exact beforeQuotient_piece G f i ⟨a, ha⟩)


end Lech.Grading


namespace Lech.IdealGraded
open Polynomial DirectSum
open scoped Classical
variable {R : Type*} [CommRing R] (I : Ideal R)

def monomial (i : ℕ) : ↥(I ^ i) →ₗ[R] reesAlgebra I :=
  ((Polynomial.monomial i).comp (I ^ i).subtype).codRestrict (reesAlgebra I).toSubmodule
    (fun x => reesAlgebra.monomial_mem.mpr x.property)

@[simp] lemma monomial_coe (i : ℕ) (x : ↥(I ^ i)) :
    (monomial I i x : R[X]) = Polynomial.monomial i (x : R) := rfl

def coefficient (i : ℕ) : reesAlgebra I →ₗ[R] ↥(I ^ i) :=
  ((Polynomial.lcoeff R i).comp (reesAlgebra I).val.toLinearMap).codRestrict _
    (fun p => p.property i)

@[simp] lemma coefficient_coe (i : ℕ) (p : reesAlgebra I) :
    (coefficient I i p : R) = (p : R[X]).coeff i := rfl

@[simp] lemma coefficient_monomial (i : ℕ) (x : ↥(I ^ i)) :
    coefficient I i (monomial I i x) = x := by
  apply Subtype.ext
  change (Polynomial.monomial i (x : R)).coeff i = (x : R)
  simp

abbrev reesGrade (i : ℕ) : Submodule R (reesAlgebra I) := (monomial I i).range

def component (i : ℕ) : reesAlgebra I →ₗ[R] reesGrade I i :=
  (monomial I i).rangeRestrict.comp (coefficient I i)

@[simp] lemma component_coe (i : ℕ) (p : reesAlgebra I) :
    ((component I i p : reesAlgebra I) : R[X]) = Polynomial.monomial i ((p : R[X]).coeff i) := rfl

noncomputable def reesDecompose : reesAlgebra I →ₗ[R] ⨁ i, reesGrade I i where
  toFun p :=
    { toFun := fun i => component I i p
      support' := by
        classical
        exact Trunc.mk ⟨(p : R[X]).support.val, fun i => by
          by_cases hi : i ∈ (p : R[X]).support
          · exact Or.inl hi
          · apply Or.inr
            apply Subtype.ext
            apply Subtype.ext
            simp [component_coe, Polynomial.notMem_support_iff.mp hi]⟩ }
  map_add' p q := by apply DFinsupp.ext; intro i; exact (component I i).map_add p q
  map_smul' a p := by apply DFinsupp.ext; intro i; exact (component I i).map_smul a p

@[simp] lemma reesDecompose_apply (p : reesAlgebra I) (i : ℕ) :
    reesDecompose I p i = component I i p := rfl

lemma reesDecompose_monomial (i : ℕ) (x : ↥(I ^ i)) :
    reesDecompose I (monomial I i x) =
      DirectSum.lof R ℕ (fun i => ↥(reesGrade I i)) i ((monomial I i).rangeRestrict x) := by
  rw [DirectSum.lof_eq_of]
  apply DFinsupp.ext
  intro j
  apply Subtype.ext
  apply Subtype.ext
  by_cases hij : i = j
  · subst j
    simp [component_coe]
  · simp [component_coe, Polynomial.coeff_monomial, hij,
      DirectSum.of_eq_of_ne _ _ _ (Ne.symm hij)]


def shifted : Ideal (reesAlgebra I) where
  carrier := {p | ∀ i, (p : R[X]).coeff i ∈ I ^ (i + 1)}
  zero_mem' i := by simp
  add_mem' hp hq i := by simpa using (I ^ (i + 1)).add_mem (hp i) (hq i)
  smul_mem' p q hq i := by
    change ((p : R[X]) * (q : R[X])).coeff i ∈ _
    rw [Polynomial.coeff_mul]
    apply Ideal.sum_mem
    rintro ⟨j, k⟩ hjk
    have hi : j + k = i := Finset.HasAntidiagonal.mem_antidiagonal.mp hjk
    have hh := Ideal.mul_mem_mul (p.property j) (hq k)
    rw [← pow_add] at hh
    simpa only [← hi, Nat.add_assoc] using hh

end Lech.IdealGraded
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_IdealGradedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
namespace Lech.IdealGraded
open Polynomial DirectSum
variable {R : Type*} [CommRing R] (I : Ideal R)

abbrev Ring := reesAlgebra I ⧸ shifted I

lemma scalar_mem_shifted {r : R} (hr : r ∈ I) :
    algebraMap R (reesAlgebra I) r ∈ shifted I := by
  intro i
  change (Polynomial.C r).coeff i ∈ I ^ (i + 1)
  by_cases hi : i = 0
  · subst i; simpa using hr
  · simp [Polynomial.coeff_C, hi]

noncomputable instance gradedAlgebra : Algebra (R ⧸ I) (Ring I) :=
  Ideal.Quotient.algebraQuotientOfLEComap (fun _ hr => scalar_mem_shifted I hr)

abbrev quotientR : reesAlgebra I →ₗ[R] Ring I := (shifted I).mkQ.restrictScalars R

end Lech.IdealGraded


namespace Lech.Grading
open SetLike MvPolynomial
variable {S B ι : Type*} [CommRing S] [CommRing B] [Algebra S B]
  (G : ℕ → Submodule S B) [GradedAlgebra G] (x : ι → B)

lemma aeval_mem (hx : ∀ i, x i ∈ G 1) {n : ℕ}
    {p : MvPolynomial ι S} (hp : p ∈ homogeneousSubmodule ι S n) :
    aeval x p ∈ G n := by
  classical
  rw [p.as_sum]
  rw [map_sum]
  apply Submodule.sum_mem
  intro d hd
  rw [aeval_monomial, ← Algebra.smul_def]
  apply Submodule.smul_mem
  have hn : d.degree = n := by
    rw [Finsupp.degree_eq_weight_one]
    exact hp (MvPolynomial.mem_support_iff.mp hd)
  rw [← hn]
  change (∏ i ∈ d.support, x i ^ d i) ∈ G (∑ i ∈ d.support, d i)
  simpa only [nsmul_eq_mul, Nat.cast_id, mul_one] using
    (SetLike.prod_pow_mem_graded G (fun _ : ι => 1) x d
      (F := d.support) (fun i _ => hx i))

attribute [local instance] MvPolynomial.gradedAlgebra
 
def polynomialMap (hx : ∀ i, x i ∈ G 1) : homogeneousSubmodule ι S →+*ᵍ G where
  toRingHom := (aeval x).toRingHom
  map_mem := aeval_mem G x hx

end Lech.Grading


namespace Lech.IdealGraded
open Polynomial DirectSum
variable {R : Type*} [CommRing R] (I : Ideal R)

variable {ι : Type*} (z : ι → R) (hz : Ideal.span (Set.range z) = I)
def generator (j : ι) : Ring I :=
  Ideal.Quotient.mk (shifted I) (monomial I 1 ⟨z j, by
    rw [pow_one, ← hz]; exact Ideal.subset_span (Set.mem_range_self j)⟩)
attribute [local instance] MvPolynomial.gradedAlgebra

end Lech.IdealGraded


namespace Lech.Homogeneous

section
open HomogeneousLocalization SetLike Graded
universe u
variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B]
  (G : ℕ → Submodule R A) (H : ℕ → Submodule R B)
  [GradedAlgebra G] [GradedAlgebra H]


instance module (U : Submonoid A) : Module R (HomogeneousLocalization G U) :=
  Function.Injective.module R (algebraMap (HomogeneousLocalization G U) (Localization U)).toAddMonoidHom
    (val_injective U) (val_smul U)

 
def fraction {f : A} {d : ℕ} (hf : f ∈ G d) (n : ℕ) :
    G (n*d) →ₗ[R] Away G f where
  toFun a := Away.mk G hf n a (by simpa only [nsmul_eq_mul, Nat.cast_id] using a.2)
  map_add' a b := by
    apply val_injective (Submonoid.powers f)
    simp only [Away.val_mk,val_add,Submodule.coe_add]
    exact (Localization.add_mk_self _ _ _).symm
  map_smul' c a := by
    apply val_injective (Submonoid.powers f)
    simp only [Away.val_mk,val_smul,Submodule.coe_smul,RingHom.id_apply]
    exact (Localization.smul_mk _ _ _).symm

variable (g : G →+*ᵍ H) (hg : ∀ (r : R) (a : A), g (r • a) = r • g a)

def gradedMap (j : ℕ) : G j →ₗ[R] H j where
  toFun a := ⟨g a,map_mem g a.2⟩
  map_add' a b := by ext; exact map_add g _ _
  map_smul' r a := by ext; exact hg r a

def awayMap (f : A) : Away G f →ₗ[R] Away H (g f) where
  toFun := Away.map g f
  map_add' := map_add _
  map_smul' r a := by
    obtain ⟨a,rfl⟩ := HomogeneousLocalization.mk_surjective a
    change HomogeneousLocalization.map g _ (HomogeneousLocalization.mk (r • a)) = _
    simp only [HomogeneousLocalization.map_mk]
    congr 1
    ext
    · rfl
    · exact hg r a.num
    · rfl

@[simp] lemma awayMap_fraction {f : A} {d : ℕ} (hf : f ∈ G d) (n : ℕ)
    (a : G (n*d)) :
    awayMap G H g hg f (fraction G hf n a) =
      fraction H (map_mem g hf) n (gradedMap G H g hg (n*d) a) := by
  exact Away.map_mk g f hf n a (by simpa only [nsmul_eq_mul, Nat.cast_id] using a.2)

lemma gradedMap_surjective (hs : Function.Surjective g) (j : ℕ) :
    Function.Surjective (gradedMap G H g hg j) := by
  intro b
  obtain ⟨a,ha⟩ := hs b
  refine ⟨DirectSum.decompose G a j,?_⟩
  apply Subtype.ext
  change g (DirectSum.decompose G a j) = (b : B)
  rw [g.map_directSumDecompose,ha]
  exact DirectSum.decompose_of_mem_same H b.2

lemma awayMap_surjective {f : A} {d : ℕ} (hf : f ∈ G d)
    (hs : Function.Surjective g) : Function.Surjective (awayMap G H g hg f) := by
  intro x
  obtain ⟨n,b,hb,rfl⟩ := Away.mk_surjective H (map_mem g hf) x
  obtain ⟨a,ha⟩ := gradedMap_surjective G H g hg hs (n*d)
    ⟨b,by simpa only [nsmul_eq_mul,Nat.cast_id] using hb⟩
  refine ⟨fraction G hf n a,?_⟩
  rw [awayMap_fraction,ha]
  rfl


end


open HomogeneousLocalization SetLike Graded
open CategoryTheory CategoryTheory.Limits
universe u
variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B]
  (G : ℕ → Submodule R A) (H : ℕ → Submodule R B)
  [GradedAlgebra G] [GradedAlgebra H]
  (g : G →+*ᵍ H) (hg : ∀ (r : R) (a : A), g (r • a) = r • g a)
  {f : A} {d : ℕ} (hf : f ∈ G d)


def kernelFraction (n : ℕ) :
    LinearMap.ker (gradedMap G H g hg (n*d)) →ₗ[R]
      LinearMap.ker (awayMap G H g hg f) :=
  ((fraction G hf n).comp (LinearMap.ker (gradedMap G H g hg (n*d))).subtype).codRestrict _ (by
    intro a
    change awayMap G H g hg f (fraction G hf n a) = 0
    rw [awayMap_fraction]
    have ha : gradedMap G H g hg (n*d) a = 0 := a.2
    rw [ha,map_zero])

end Lech.Homogeneous


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_LechPiIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
attribute [local instance] Classical.propDecidable
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian


namespace Lech.TwistedLocalization

section

section
open SetLike Graded
universe u
variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B]
  (G : ℕ → Submodule R A) [GradedAlgebra G]
  {f : A} {d : ℕ} (hf : f ∈ G d)

 
def fraction (t n : ℕ) : G (n*d+t) →ₗ[R] Localization.Away f where
  toFun a := Localization.mk (a : A) (⟨f^n, n, rfl⟩ : Submonoid.powers f)
  map_add' a b := by
    exact (Localization.add_mk_self _ _ _).symm
  map_smul' r a := by
    exact (Localization.smul_mk _ _ _).symm


def piece (t : ℕ) : Submodule R (Localization.Away f) :=
  ⨆ n : ℕ, LinearMap.range (fraction G (f := f) (d := d) t n)

omit [GradedAlgebra G] in
lemma fraction_mem (t n : ℕ) (a : G (n*d+t)) :
    fraction G (f := f) t n a ∈ piece G (f := f) (d := d) t :=
  Submodule.mem_iSup_of_mem n ⟨a,rfl⟩

include hf

lemma raise_fraction (t n k : ℕ) (a : G (n*d+t)) :
    ∃ b : G ((k+n)*d+t), fraction G (f := f) t (k+n) b =
      fraction G (f := f) t n a := by
  have hb : f^k*(a : A) ∈ G ((k+n)*d+t) := by
    rw [add_mul, add_assoc]
    exact mul_mem_graded (by simpa only [nsmul_eq_mul, Nat.cast_id] using
      (pow_mem_graded k hf)) a.property
  refine ⟨⟨f^k*(a : A),hb⟩,?_⟩
  dsimp [fraction]
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [Submonoid.coe_one, one_mul, pow_add]
  ring

lemma range_mono (t : ℕ) : Monotone (fun n : ℕ =>
    LinearMap.range (fraction G (f := f) (d := d) t n)) := by
  intro n m hnm x hx
  obtain ⟨a,rfl⟩ := hx
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le' hnm
  exact raise_fraction G hf t n k a


lemma exists_fraction (t : ℕ) (x : piece G (f := f) (d := d) t) :
    ∃ (n : ℕ) (a : G (n*d+t)), fraction G (f := f) t n a = (x : Localization.Away f) := by
  have hx := x.property
  change (x : Localization.Away f) ∈ (⨆ n, LinearMap.range (fraction G (f := f) (d := d) t n)) at hx
  rw [Submodule.mem_iSup_of_directed _ (range_mono G hf t).directed_le] at hx
  exact hx

omit hf
variable (H : ℕ → Submodule R B) [GradedAlgebra H]
  (g : G →+*ᵍ H) (hg : ∀ (r : R) (a : A), g (r • a) = r • g a)

 
def algHom : A →ₐ[R] B where
  toFun := g
  map_zero' := map_zero g
  map_one' := map_one g
  map_add' := map_add g
  map_mul' := map_mul g
  commutes' r := by
    simpa only [Algebra.smul_def, mul_one, map_one] using hg r (1 : A)

def gradedMap (j : ℕ) : G j →ₗ[R] H j where
  toFun a := ⟨g a,map_mem g a.property⟩
  map_add' a b := Subtype.ext (map_add g (a : A) (b : A))
  map_smul' r a := Subtype.ext (hg r a)

def ambientMap : Localization.Away f →ₐ[R] Localization.Away (g f) := by
  letI : IsLocalization.Away ((algHom G H g hg) f) (Localization.Away (g f)) :=
    inferInstanceAs (IsLocalization.Away (g f) (Localization.Away (g f)))
  exact IsLocalization.Away.mapₐ _ _ (algHom G H g hg) f

omit [GradedAlgebra G] [GradedAlgebra H] in
lemma ambientMap_fraction (t n : ℕ) (a : G (n*d+t)) :
    ambientMap G H g hg (fraction G (f := f) t n a) =
      fraction H (f := g f) t n (gradedMap G H g hg (n*d+t) a) := by
  simp only [ambientMap, IsLocalization.Away.mapₐ_apply, IsLocalization.Away.map,
    fraction, LinearMap.coe_mk, AddHom.coe_mk, Localization.mk_eq_mk',
    IsLocalization.map_mk']
  simp only [gradedMap, LinearMap.coe_mk, AddHom.coe_mk, algHom,
    RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, map_pow]

include hf
omit [GradedAlgebra H] in
lemma ambientMap_mem (t : ℕ) (x : piece G (f := f) (d := d) t) :
    ambientMap G H g hg (x : Localization.Away f) ∈ piece H (f := g f) (d := d) t := by
  obtain ⟨n,a,ha⟩ := exists_fraction G hf t x
  rw [← ha, ambientMap_fraction]
  exact fraction_mem H t n _

def pieceMap (t : ℕ) : piece G (f := f) (d := d) t →ₗ[R]
    piece H (f := g f) (d := d) t :=
  ((ambientMap G H g hg).toLinearMap.comp (piece G (f := f) (d := d) t).subtype).codRestrict
    _ (ambientMap_mem G hf H g hg t)

def pieceFraction (t n : ℕ) : G (n*d+t) →ₗ[R] piece G (f := f) (d := d) t :=
  (fraction G (f := f) t n).codRestrict _ (fraction_mem G t n)

omit [GradedAlgebra H] in
@[simp] lemma pieceMap_fraction (t n : ℕ) (a : G (n*d+t)) :
    pieceMap G hf H g hg t (pieceFraction G (f := f) t n a) =
      pieceFraction H (f := g f) t n (gradedMap G H g hg (n*d+t) a) := by
  apply Subtype.ext
  exact ambientMap_fraction G H g hg t n a


def kernelFraction (t n : ℕ) :
    LinearMap.ker (gradedMap G H g hg (n*d+t)) →ₗ[R]
      LinearMap.ker (pieceMap G hf H g hg t) :=
  ((pieceFraction G (f := f) t n).comp
    (LinearMap.ker (gradedMap G H g hg (n*d+t))).subtype).codRestrict _ (by
      intro a
      change pieceMap G hf H g hg t (pieceFraction G (f := f) t n a) = 0
      rw [pieceMap_fraction]
      have ha : gradedMap G H g hg (n*d+t) a = 0 := a.property
      rw [ha,map_zero])

open CategoryTheory CategoryTheory.Limits
local instance kernelAdd (t : ℕ) : AddCommGroup (LinearMap.ker (pieceMap G hf H g hg t)) :=
  Submodule.addCommGroup (R := R) (M := piece G (f := f) (d := d) t)
    (LinearMap.ker (pieceMap G hf H g hg t))
local instance kernelModule (t : ℕ) : Module R (LinearMap.ker (pieceMap G hf H g hg t)) :=
  Submodule.module (R := R) (M := piece G (f := f) (d := d) t)
    (LinearMap.ker (pieceMap G hf H g hg t))
attribute [local irreducible] pieceMap gradedMap kernelFraction

end


open SetLike Graded
universe u
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]


def ambientRestriction (f q : A) : Localization.Away f →ₐ[R] Localization.Away (f*q) :=
  IsLocalization.Away.liftAlgHom f (f := Algebra.algHom R A (Localization.Away (f*q)))
    (IsLocalization.Away.isUnit_of_dvd (f*q) (dvd_mul_right f q))

@[simp] lemma ambientRestriction_algebraMap (f q a : A) :
    ambientRestriction (R := R) f q (algebraMap A (Localization.Away f) a) =
      algebraMap A (Localization.Away (f*q)) a := by
  exact IsLocalization.Away.lift_eq f
    (IsLocalization.Away.isUnit_of_dvd (S := Localization.Away (f*q))
      (f*q) (dvd_mul_right f q)) a

lemma ambientRestriction_mk (f q a : A) (n : ℕ) :
    ambientRestriction (R := R) f q
      (Localization.mk a (⟨f^n,n,rfl⟩ : Submonoid.powers f)) =
    Localization.mk (a*q^n) (⟨(f*q)^n,n,rfl⟩ : Submonoid.powers (f*q)) := by
  simp only [Localization.mk_eq_mk']
  apply IsLocalization.eq_mk'_iff_mul_eq.mpr
  change ambientRestriction (R := R) f q (IsLocalization.mk' _ a _) *
    algebraMap A (Localization.Away (f*q)) ((f*q)^n) = _
  rw [mul_pow,map_mul,←mul_assoc,
    ←ambientRestriction_algebraMap (R := R) f q (f^n),←map_mul,
    IsLocalization.mk'_spec,ambientRestriction_algebraMap,map_mul]

variable (G : ℕ → Submodule R A) [GradedAlgebra G]
  {f q : A} {d e : ℕ} (hf : f ∈ G d) (hq : q ∈ G e)

include hq in
lemma restriction_fraction (t n : ℕ) (a : G (n*d+t)) :
    ∃ b : G (n*(d+e)+t),
      ambientRestriction (R := R) f q (fraction G (f := f) t n a) =
        fraction G (f := f*q) t n b := by
  have hb : (a : A)*q^n ∈ G (n*(d+e)+t) := by
    have heq : n*d+t+n*e = n*(d+e)+t := by ring
    simpa only [nsmul_eq_mul,Nat.cast_id,heq] using
      mul_mem_graded a.property (pow_mem_graded n hq)
  exact ⟨⟨(a : A)*q^n,hb⟩,ambientRestriction_mk f q a n⟩

include hf hq in
lemma ambientRestriction_mem (t : ℕ) (x : piece G (f := f) (d := d) t) :
    ambientRestriction (R := R) f q (x : Localization.Away f) ∈
      piece G (f := f*q) (d := d+e) t := by
  obtain ⟨n,a,ha⟩ := exists_fraction G hf t x
  obtain ⟨b,hb⟩ := restriction_fraction G hq t n a
  rw [←ha,hb]
  exact fraction_mem G t n b


end


open SetLike Graded
universe u
variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B]

 
def ambientTo {f q : A} (h : f ∣ q) : Localization.Away f →ₐ[R] Localization.Away q :=
  IsLocalization.Away.liftAlgHom f (f := Algebra.algHom R A (Localization.Away q))
    (IsLocalization.Away.isUnit_of_dvd q h)

@[simp] lemma ambientTo_algebraMap {f q : A} (h : f ∣ q) (a : A) :
    ambientTo (R := R) h (algebraMap A (Localization.Away f) a) =
      algebraMap A (Localization.Away q) a :=
  IsLocalization.Away.lift_eq f (IsLocalization.Away.isUnit_of_dvd q h) a

lemma ambientTo_comp {f q r : A} (hfq : f ∣ q) (hqr : q ∣ r) :
    (ambientTo (R := R) hqr).comp (ambientTo hfq) = ambientTo (hfq.trans hqr) := by
  apply IsLocalization.algHom_ext (Submonoid.powers f)
  ext a
  change ambientTo hqr (ambientTo hfq (algebraMap A _ a)) =
    ambientTo (hfq.trans hqr) (algebraMap A _ a)
  simp only [ambientTo_algebraMap]

lemma ambientTo_self (f : A) : ambientTo (R := R) (dvd_refl f) = AlgHom.id R _ := by
  apply IsLocalization.algHom_ext (Submonoid.powers f)
  ext a
  change ambientTo (dvd_refl f) (algebraMap A _ a) = algebraMap A _ a
  exact ambientTo_algebraMap _ a

lemma ambientTo_mk {f q c : A} (hfc : f*c=q) (a : A) (n : ℕ) :
    ambientTo (R := R) (show f ∣ q from ⟨c,hfc.symm⟩)
      (Localization.mk a (⟨f^n,n,rfl⟩ : Submonoid.powers f)) =
    Localization.mk (a*c^n) (⟨q^n,n,rfl⟩ : Submonoid.powers q) := by
  subst q
  exact ambientRestriction_mk f c a n

variable (G : ℕ → Submodule R A) [GradedAlgebra G]
  {f q c : A} {d e k : ℕ} (hf : f ∈ G d) (hc : c ∈ G k)
  (hfc : f*c=q) (hdeg : d+k=e)

include hf hc hdeg in
lemma ambientTo_mem (t : ℕ) (x : piece G (f := f) (d := d) t) :
    ambientTo (R := R) (show f ∣ q from ⟨c,hfc.symm⟩) x ∈
      piece G (f := q) (d := e) t := by
  subst q; subst e
  exact ambientRestriction_mem G hf hc t x

 
def pieceTo (t : ℕ) : piece G (f := f) (d := d) t →ₗ[R]
    piece G (f := q) (d := e) t :=
  ((ambientTo (R := R) (show f ∣ q from ⟨c,hfc.symm⟩)).toLinearMap.comp
    (piece G (f := f) (d := d) t).subtype).codRestrict _
      (ambientTo_mem G hf hc hfc hdeg t)

@[simp] lemma pieceTo_val (t : ℕ) (x : piece G (f := f) (d := d) t) :
    (pieceTo G hf hc hfc hdeg t x : Localization.Away q) =
      ambientTo (R := R) (show f ∣ q from ⟨c,hfc.symm⟩) x := rfl

end Lech.TwistedLocalization

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_TwistedLocalizationPieceMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
attribute [local instance] Classical.propDecidable
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian


namespace Lech.GradedChart
open SetLike Graded
universe u
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  (G : ℕ → Submodule R A) [GradedAlgebra G]
  {h : ℕ} (y : Fin h → A) (hy : ∀ i, y i ∈ G 1)

 
def denominator (s : Finset (Fin h)) : A := ∏ i ∈ s, y i

include hy in
lemma denominator_mem (s : Finset (Fin h)) : denominator y s ∈ G s.card := by
  simpa only [Finset.sum_const,nsmul_eq_mul,mul_one,Nat.cast_id,denominator] using
    (prod_mem_graded G (fun _ : Fin h => 1) y (F := s) (fun i _ => hy i))

lemma denominator_mul_sdiff {s v : Finset (Fin h)} (hsv : s ⊆ v) :
    denominator y s * denominator y (v\s) = denominator y v := by
  classical
  unfold denominator
  rw [mul_comm]
  exact Finset.prod_sdiff hsv

lemma denominator_dvd {s v : Finset (Fin h)} (hsv : s ⊆ v) :
    denominator y s ∣ denominator y v := ⟨_,(denominator_mul_sdiff y hsv).symm⟩

abbrev term (s : Finset (Fin h)) (t : ℕ) :=
  TwistedLocalization.piece G (f := denominator y s) (d := s.card) t

 
def restrict {s v : Finset (Fin h)} (hsv : s ⊆ v) (t : ℕ) :
    term G y s t →ₗ[R] term G y v t :=
  TwistedLocalization.pieceTo G (denominator_mem G y hy s)
    (denominator_mem G y hy (v\s)) (denominator_mul_sdiff y hsv)
    (by rw [Nat.add_comm,Finset.card_sdiff_add_card_eq_card hsv]) t

@[simp] lemma restrict_val {s v : Finset (Fin h)} (hsv : s ⊆ v) (t : ℕ)
    (x : term G y s t) : (restrict G y hy hsv t x : Localization.Away (denominator y v)) =
      TwistedLocalization.ambientTo (R := R) (denominator_dvd y hsv) x := rfl

end Lech.GradedChart


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_GradedChartCochains
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
attribute [local instance] Classical.propDecidable
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian


namespace Lech.ImageCech
open SetLike Graded
universe u
variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B]
  (G : ℕ → Submodule R A) [GradedAlgebra G]
  (H : ℕ → Submodule R B) [GradedAlgebra H]
  (g : G →+*ᵍ H) (hg : ∀ (r : R) (a : A), g (r • a) = r • g a)
  {h : ℕ} (y : Fin h → A) (hy : ∀ i, y i ∈ G 1)


abbrev term (s : Finset (Fin h)) (t : ℕ) :=
  TwistedLocalization.piece H (f := g (GradedChart.denominator y s)) (d := s.card) t

def mapTerm (s : Finset (Fin h)) (t : ℕ) :
    GradedChart.term G y s t →ₗ[R] term G H g y s t :=
  TwistedLocalization.pieceMap G (GradedChart.denominator_mem G y hy s) H g hg t

end Lech.ImageCech


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_RestrictedPolynomialImageCechComparisonHomology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
attribute [local instance] Classical.propDecidable
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian


namespace Lech.LocalizationCech
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  {h : ℕ} (y : Fin h → A)
abbrev ambient (s : Finset (Fin h)) := Localization.Away (GradedChart.denominator y s)
variable (F : (s : Finset (Fin h)) → Submodule R (ambient y s))
  (hF : ∀ {s v : Finset (Fin h)} (hsv : s ⊆ v) (x : F s),
    TwistedLocalization.ambientTo (R := R) (GradedChart.denominator_dvd y hsv) x ∈ F v)

 
def restrict {s v : Finset (Fin h)} (hsv : s ⊆ v) : F s →ₗ[R] F v :=
  ((TwistedLocalization.ambientTo (R := R) (GradedChart.denominator_dvd y hsv)).toLinearMap.comp
    (F s).subtype).codRestrict _ (hF hsv)

lemma restrict_comp {s v w : Finset (Fin h)} (hsv : s ⊆ v) (hvw : v ⊆ w) (x : F s) :
    restrict y F hF hvw (restrict y F hF hsv x) = restrict y F hF (hsv.trans hvw) x := by
  apply Subtype.ext
  exact AlgHom.congr_fun (TwistedLocalization.ambientTo_comp (GradedChart.denominator_dvd y hsv) (GradedChart.denominator_dvd y hvw)) x.val

end Lech.LocalizationCech


namespace Lech.FilteredFraction

section
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) (w : R) (d : ℕ)

 
def fraction (t n : ℕ) : ↥(I^(n*d+t)) →ₗ[R] Localization.Away w where
  toFun a := Localization.mk (a : R) (⟨w^n,n,rfl⟩ : Submonoid.powers w)
  map_add' _ _ := (Localization.add_mk_self _ _ _).symm
  map_smul' _ _ := (Localization.smul_mk _ _ _).symm

 
def piece (t : ℕ) : Submodule R (Localization.Away w) :=
  ⨆ n : ℕ, LinearMap.range (fraction I w d t n)

lemma fraction_mem (t n : ℕ) (a : ↥(I^(n*d+t))) :
    fraction I w d t n a ∈ piece I w d t :=
  Submodule.mem_iSup_of_mem n ⟨a,rfl⟩

variable (hw : w ∈ I^d)
include hw
lemma raise_fraction (t n k : ℕ) (a : ↥(I^(n*d+t))) :
    ∃ b : ↥(I^((k+n)*d+t)), fraction I w d t (k+n) b = fraction I w d t n a := by
  have hp : w^k ∈ I^(k*d) := by
    simpa only [pow_mul,mul_comm k d] using Ideal.pow_mem_pow hw k
  have hb : w^k*(a:R) ∈ I^((k+n)*d+t) := by
    rw [add_mul,add_assoc,pow_add]
    exact Ideal.mul_mem_mul hp a.property
  refine ⟨⟨w^k*(a:R),hb⟩,?_⟩
  dsimp [fraction]
  rw [Localization.mk_eq_mk_iff,Localization.r_iff_exists]
  refine ⟨1,?_⟩
  simp only [Submonoid.coe_one,one_mul,pow_add]
  ring

lemma range_mono (t : ℕ) : Monotone (fun n : ℕ => LinearMap.range (fraction I w d t n)) := by
  intro n m hnm x hx
  obtain ⟨a,rfl⟩ := hx
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le' hnm
  exact raise_fraction I w d hw t n k a

lemma exists_fraction (t : ℕ) (x : piece I w d t) :
    ∃ (n : ℕ) (a : ↥(I^(n*d+t))), fraction I w d t n a=(x:Localization.Away w) := by
  have hx := x.property
  change x.val ∈ (⨆ n, LinearMap.range (fraction I w d t n)) at hx
  rw [Submodule.mem_iSup_of_directed _ (range_mono I w d hw t).directed_le] at hx
  exact hx
omit hw

lemma antitone : Antitone (piece I w d) := by
  intro s t hst
  apply iSup_le
  intro n
  rintro _ ⟨a,rfl⟩
  exact fraction_mem I w d s n ⟨a.val,Ideal.pow_le_pow_right (by omega) a.property⟩


end


open Lech.IdealGraded SetLike Graded
universe u
variable {R : Type u} [CommRing R] (I : Ideal R)
  {w v c : R} {d e k : ℕ} (hw : w ∈ I^d) (hc : c ∈ I^k)
  (hwc : w*c=v) (hdeg : d+k=e)

include hc hdeg in
lemma restriction_fraction (t n : ℕ) (a : ↥(I^(n*d+t))) :
    ∃ b : ↥(I^(n*e+t)),
      TwistedLocalization.ambientTo (R := R) (show w ∣ v from ⟨c,hwc.symm⟩)
        (fraction I w d t n a) = fraction I v e t n b := by
  have hp : c^n ∈ I^(n*k) := by
    simpa only [pow_mul,mul_comm n k] using Ideal.pow_mem_pow hc n
  have hb : (a:R)*c^n ∈ I^(n*e+t) := by
    have heq : n*d+t+n*k=n*e+t := by rw [←hdeg]; ring
    rw [←heq,pow_add]
    exact Ideal.mul_mem_mul a.property hp
  exact ⟨⟨(a:R)*c^n,hb⟩,TwistedLocalization.ambientTo_mk hwc a n⟩

include hw hc hdeg in
lemma restriction_mem (t : ℕ) (x : piece I w d t) :
    TwistedLocalization.ambientTo (R := R) (show w ∣ v from ⟨c,hwc.symm⟩) x ∈
      piece I v e t := by
  obtain ⟨n,a,ha⟩ := exists_fraction I w d hw t x
  obtain ⟨b,hb⟩ := restriction_fraction I hc hwc hdeg t n a
  rw [←ha,hb]
  exact fraction_mem I v e t n b

 
def restrict (t : ℕ) : piece I w d t →ₗ[R] piece I v e t :=
  ((TwistedLocalization.ambientTo (R := R) (show w ∣ v from ⟨c,hwc.symm⟩)).toLinearMap.comp
    (piece I w d t).subtype).codRestrict _ (restriction_mem I hw hc hwc hdeg t)

@[simp] lemma restrict_val (t : ℕ) (x : piece I w d t) :
    (restrict I hw hc hwc hdeg t x).val =
      TwistedLocalization.ambientTo (R := R) (show w ∣ v from ⟨c,hwc.symm⟩) x := rfl


end Lech.FilteredFraction

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_FilteredFractionReesDenominator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
attribute [local instance] Classical.propDecidable
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian


namespace Lech.FilteredCech
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {h : ℕ}
  (z : Fin h → R) (hz : ∀ i, z i ∈ I)

include hz in
lemma denominator_mem (s : Finset (Fin h)) : GradedChart.denominator z s ∈ I^s.card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [GradedChart.denominator]
  | @insert i s hi ih =>
    simp only [GradedChart.denominator,Finset.prod_insert hi,Finset.card_insert_of_notMem hi]
    rw [pow_succ']
    exact Ideal.mul_mem_mul (hz i) ih

 
abbrev term (t : ℕ) (s : Finset (Fin h)) :
    Submodule R (LocalizationCech.ambient z s) :=
  FilteredFraction.piece I (GradedChart.denominator z s) s.card t

include hz in
lemma restriction_mem (t : ℕ) {s v : Finset (Fin h)} (hsv : s ⊆ v) (x : term I z t s) :
    TwistedLocalization.ambientTo (R := R) (GradedChart.denominator_dvd z hsv) x ∈ term I z t v :=
  FilteredFraction.restriction_mem I (denominator_mem I z hz s)
    (denominator_mem I z hz (v\s)) (GradedChart.denominator_mul_sdiff z hsv)
    (by rw [Nat.add_comm,Finset.card_sdiff_add_card_eq_card hsv]) t x


end Lech.FilteredCech


namespace Lech.SourceGraded
open Lech.IdealGraded SetLike Graded
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {h : ℕ}
  (z : Fin h → R) (hz : Ideal.span (Set.range z)=I)

include hz in
lemma coordinate_mem (i : Fin h) : z i ∈ I := by
  rw [←hz]
  exact Ideal.subset_span (Set.mem_range_self i)

attribute [local irreducible] TwistedLocalization.piece


end Lech.SourceGraded


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_LechCokernelComp
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject


namespace Lech.FilteredFraction
universe u
variable {R : Type u} [CommRing R] (I : Ideal R)

lemma fraction_one_zero (t n : ℕ) (a : ↥(I^(n*0+t))) :
    fraction I (1:R) 0 t n a=algebraMap R (Localization.Away (1:R)) a := by
  change Localization.mk (a:R) (⟨(1:R)^n,n,rfl⟩ : Submonoid.powers (1:R))=_
  have he : (⟨(1:R)^n,n,rfl⟩ : Submonoid.powers (1:R))=1 := Subtype.ext (one_pow n)
  rw [he,Localization.mk_eq_mk',IsLocalization.mk'_one]

 

noncomputable def augmentationEquiv (t : ℕ) : ↥(I^t) ≃ₗ[R] piece I (1:R) 0 t :=
  LinearEquiv.ofBijective
    (show ↥(I^t) →ₗ[R] piece I (1:R) 0 t from
    { toFun := fun a => ⟨algebraMap R _ a,by
        simpa only [fraction_one_zero] using fraction_mem I (1:R) 0 t 0 ⟨a.val,by simp⟩⟩
      map_add' := fun _ _ => Subtype.ext (map_add _ _ _)
      map_smul' := fun _ _ => Subtype.ext ((Algebra.linearMap R (Localization.Away (1:R))).map_smul _ _) })
    ⟨by
      intro a b hab
      apply Subtype.ext
      exact (IsLocalization.atOne R (Localization.Away (1:R))).injective (congrArg Subtype.val hab),by
      intro x
      obtain ⟨n,a,ha⟩ := exists_fraction I (1:R) 0 (by simp) t x
      exact ⟨⟨a.val,by simpa using a.property⟩,Subtype.ext ((fraction_one_zero I t n a).symm.trans ha)⟩⟩

@[simp] lemma augmentationEquiv_val (t : ℕ) (a : ↥(I^t)) :
    (augmentationEquiv I t a).val=algebraMap R (Localization.Away (1:R)) a := rfl

end Lech.FilteredFraction


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_ProductSourceCoverFaceSlice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
attribute [local instance] Classical.propDecidable
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian
open scoped BigOperators
open scoped Classical


namespace Lech.DoubleCech
open Set CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped BigOperators
universe u
variable (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M]
variable {ι κ : Type} [Fintype ι] [LinearOrder ι] [Fintype κ] [LinearOrder κ]
variable (F : Finset ι → Finset κ → Submodule R M)
  (h₁ : ∀ t,Monotone (fun s => F s t)) (h₂ : ∀ s,Monotone (F s))
abbrev term (p q : ℕ) := ∀ s : powersetCard ι p,∀ t : powersetCard κ q,F s.val t.val

omit [LinearOrder ι] [Fintype κ] [LinearOrder κ] in
lemma term_zero_horizontal (p q : ℕ) (hp : Fintype.card ι<p) :
    Subsingleton (term R M F p q) := by
  refine ⟨fun f g => funext fun s => ?_⟩
  have hh := Finset.card_le_univ s.val
  have hs : s.val.card=p := s.property
  omega
end Lech.DoubleCech


namespace Lech.ComplexExtension
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u v u' v'
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  {D : Type u'} [Category.{v'} D] [Preadditive D] [HasZeroObject D]
variable (F : C ⥤ D) [F.Additive] (K : CochainComplex C ℕ)
lemma negative_zero (n : ℕ) : IsZero ((K.extend ComplexShape.embeddingUpNat).X (Int.negSucc n)) := by
  apply K.isZero_extend_X
  intro m hm
  change (m:ℤ)=Int.negSucc n at hm
  omega
 

def mapExtendXIso (i : ℤ) :
    ((F.mapHomologicalComplex (.up ℤ)).obj (K.extend ComplexShape.embeddingUpNat)).X i ≅
      (((F.mapHomologicalComplex (.up ℕ)).obj K).extend ComplexShape.embeddingUpNat).X i :=
  match i with
  | .ofNat n => F.mapIso (K.extendXIso ComplexShape.embeddingUpNat (i := n) rfl) ≪≫
      (((F.mapHomologicalComplex (.up ℕ)).obj K).extendXIso ComplexShape.embeddingUpNat (i := n) rfl).symm
  | .negSucc n => (F.map_isZero (negative_zero K n)).isoZero ≪≫
      (negative_zero ((F.mapHomologicalComplex (.up ℕ)).obj K) n).isoZero.symm

omit [Preadditive C] [HasZeroObject C] [Preadditive D] [HasZeroObject D] [F.Additive] in
lemma map_conjugation_square {X₁ X₂ Y₁ Y₂ : C} {Z₁ Z₂ : D}
    (e₁ : X₁ ≅ X₂) (e₂ : Y₁ ≅ Y₂) (g₁ : Z₁ ≅ F.obj X₂) (g₂ : Z₂ ≅ F.obj Y₂)
    (f : X₂ ⟶ Y₂) :
    (F.mapIso e₁ ≪≫ g₁.symm).hom ≫ (g₁.hom ≫ F.map f ≫ g₂.inv) =
      F.map (e₁.hom ≫ f ≫ e₂.inv) ≫ (F.mapIso e₂ ≪≫ g₂.symm).hom := by
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.map_comp,
    Category.assoc, Iso.inv_hom_id_assoc]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id, Category.comp_id]

lemma mapExtendXIso_comm (i j : ℤ) :
    (mapExtendXIso F K i).hom ≫ (((F.mapHomologicalComplex (.up ℕ)).obj K).extend
      ComplexShape.embeddingUpNat).d i j =
    ((F.mapHomologicalComplex (.up ℤ)).obj (K.extend ComplexShape.embeddingUpNat)).d i j ≫
      (mapExtendXIso F K j).hom := by
  cases i with
  | negSucc n => exact (F.map_isZero (negative_zero K n)).eq_of_src _ _
  | ofNat n =>
    cases j with
    | negSucc m => exact (negative_zero ((F.mapHomologicalComplex (.up ℕ)).obj K) m).eq_of_tgt _ _
    | ofNat m =>
      dsimp only [mapExtendXIso,Iso.trans_hom,Iso.symm_hom,Functor.mapIso_hom]
      erw [extend_d_eq _ ComplexShape.embeddingUpNat (i := n) (j := m)
        (show ComplexShape.embeddingUpNat.f n=(n:ℤ) from rfl)
        (show ComplexShape.embeddingUpNat.f m=(m:ℤ) from rfl)]
      change _ = F.map ((K.extend ComplexShape.embeddingUpNat).d (n:ℤ) (m:ℤ)) ≫ _
      erw [extend_d_eq _ ComplexShape.embeddingUpNat (i := n) (j := m)
        (show ComplexShape.embeddingUpNat.f n=(n:ℤ) from rfl)
        (show ComplexShape.embeddingUpNat.f m=(m:ℤ) from rfl)]
      exact map_conjugation_square F
        (K.extendXIso ComplexShape.embeddingUpNat (i := n) rfl)
        (K.extendXIso ComplexShape.embeddingUpNat (i := m) rfl)
        (((F.mapHomologicalComplex (.up ℕ)).obj K).extendXIso
          ComplexShape.embeddingUpNat (i := n) rfl)
        (((F.mapHomologicalComplex (.up ℕ)).obj K).extendXIso
          ComplexShape.embeddingUpNat (i := m) rfl)
        (K.d n m)
def mapExtendIso :
    (F.mapHomologicalComplex (.up ℤ)).obj (K.extend ComplexShape.embeddingUpNat) ≅
      ((F.mapHomologicalComplex (.up ℕ)).obj K).extend ComplexShape.embeddingUpNat :=
  Hom.isoOfComponents (mapExtendXIso F K) (fun i j _ => mapExtendXIso_comm F K i j)
end Lech.ComplexExtension


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_LechConnectingIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
attribute [local instance] Classical.propDecidable
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian
open scoped BigOperators
open scoped Classical


namespace Lech.ComplexExtension
open CategoryTheory CategoryTheory.Limits HomologicalComplex HomologicalComplex₂
universe u
variable {R : Type u} [CommRing R]
abbrev NatDouble := CochainComplex (CochainComplex (ModuleCat.{u} R) ℕ) ℕ
variable (K : NatDouble (R := R))

lemma extended_acyclic (L : CochainComplex (ModuleCat.{u} R) ℕ) (hL : L.Acyclic) :
    (L.extend ComplexShape.embeddingUpNat).Acyclic := by
  intro i
  by_cases hi : 0 ≤ i
  · obtain ⟨n,rfl⟩ := Int.eq_ofNat_of_zero_le hi
    exact (L.extend_exactAt_iff ComplexShape.embeddingUpNat (j := n) rfl).mpr (hL n)
  · apply L.extend_exactAt
    intro n hn
    change (n:ℤ)=i at hn
    omega
end Lech.ComplexExtension


namespace Lech.DoubleCech

section
open Set CategoryTheory CategoryTheory.Limits HomologicalComplex HomologicalComplex₂
universe u
variable (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M]
variable {ι κ : Type} [Fintype ι] [LinearOrder ι] [Fintype κ] [LinearOrder κ]
variable (F : Finset ι → Finset κ → Submodule R M)
  (h₁ : ∀ t,Monotone (fun s => F s t)) (h₂ : ∀ s,Monotone (F s))
def switch (p q : ℕ) : term R M F p q ≃ₗ[R] term R M (fun t s => F s t) q p where
  toFun x t s := x s t
  invFun x s t := x t s
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end


open Set CategoryTheory CategoryTheory.Limits HomologicalComplex HomologicalComplex₂
universe u
end Lech.DoubleCech


namespace Lech.DoubleCech
open Set CategoryTheory CategoryTheory.Limits HomologicalComplex HomologicalComplex₂
universe u
variable (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M]
variable {ι κ : Type} [Fintype ι] [LinearOrder ι] [Fintype κ] [LinearOrder κ]
variable (F : Finset ι → Finset κ → Submodule R M)
  (h₁ : ∀ t,Monotone (fun s => F s t)) (h₂ : ∀ s,Monotone (F s))
 

def puncture (s : Finset ι) (t : Finset κ) : Submodule R M :=
  if s=∅ ∧ t=∅ then ⊥ else F s t
omit [Fintype ι] [Fintype κ] in
lemma puncture_row (s : Finset ι) (hs : s.Nonempty) : puncture R M F s=F s := by
  funext t
  simp only [puncture,hs.ne_empty,false_and,ite_false]
omit [Fintype ι] [Fintype κ] in
lemma puncture_column (t : Finset κ) (ht : t.Nonempty) :
    (fun s => puncture R M F s t)=(fun s => F s t) := by
  funext s
  simp only [puncture,ht.ne_empty,and_false,ite_false]


end Lech.DoubleCech

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_TensorTotalHomologyProperty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option backward.isDefEq.respectTransparency false
namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject


namespace Lech.TensorTotal
open CategoryTheory CategoryTheory.Limits HomologicalComplex MonoidalCategory
universe u
variable {R : Type u} [CommRing R]
variable (F : CochainComplex (ModuleCat.{u} R) ℤ) (Q : ModuleCat.{u} R)

abbrev singleZero := (single (ModuleCat.{u} R) (.up ℤ) 0).obj Q
abbrev tensorSingle := mapBifunctor F (singleZero Q) (curriedTensor (ModuleCat.{u} R)) (.up ℤ)
abbrev termTensor := ((curriedTensor (ModuleCat.{u} R)).flip.obj Q).mapHomologicalComplex (.up ℤ)

def intoTensorSingle (i : ℤ) : ((termTensor Q).obj F).X i ⟶ (tensorSingle F Q).X i :=
  (F.X i ◁ (singleObjXSelf (.up ℤ) 0 Q).inv) ≫
    ιMapBifunctor F (singleZero Q) (curriedTensor (ModuleCat.{u} R)) (.up ℤ) i 0 i (by simp)

def outOfTensorSingle (i : ℤ) : (tensorSingle F Q).X i ⟶ ((termTensor Q).obj F).X i :=
  mapBifunctorDesc (fun p q hpq => if hq : q=0 then
    have hp : p=i := by change p+q=i at hpq; omega
    (F.X p ◁ (singleObjXIsoOfEq (.up ℤ) 0 Q q hq).hom) ≫ (F.XIsoOfEq hp).hom ▷ Q
    else 0)

lemma into_out (i : ℤ) : intoTensorSingle F Q i ≫ outOfTensorSingle F Q i = 𝟙 _ := by
  simp only [intoTensorSingle,outOfTensorSingle,Category.assoc,ι_mapBifunctorDesc,
    dite_true,XIsoOfEq_rfl,Iso.refl_hom,id_whiskerRight,Category.comp_id]
  rw [←whiskerLeft_comp]
  simp only [singleObjXSelf,Iso.inv_hom_id,whiskerLeft_id]
  rfl

lemma out_into (i : ℤ) : outOfTensorSingle F Q i ≫ intoTensorSingle F Q i = 𝟙 _ := by
  apply mapBifunctor.hom_ext
  intro p q hpq
  by_cases hq : q=0
  · subst q
    have hp : p=i := by change p+0=i at hpq; omega
    subst p
    simp only [outOfTensorSingle,ι_mapBifunctorDesc_assoc,
      dite_true,XIsoOfEq_rfl,Iso.refl_hom,id_whiskerRight,Category.comp_id]
    dsimp only [intoTensorSingle]
    rw [←whiskerLeft_comp_assoc]
    simp only [singleObjXSelf,Iso.hom_inv_id,whiskerLeft_id,Category.id_comp]
  · have hzero := (curriedTensor (ModuleCat.{u} R)).obj (F.X p) |>.map_isZero
        (isZero_single_obj_X (.up ℤ) 0 Q q hq)
    exact hzero.eq_of_src _ _

def tensorSingleXIso (i : ℤ) : ((termTensor Q).obj F).X i ≅ (tensorSingle F Q).X i where
  hom := intoTensorSingle F Q i
  inv := outOfTensorSingle F Q i
  hom_inv_id := into_out F Q i
  inv_hom_id := out_into F Q i

lemma tensorSingle_d₂ (p q j : ℤ) :
    mapBifunctor.d₂ F (singleZero Q) (curriedTensor (ModuleCat.{u} R)) (.up ℤ) p q j = 0 := by
  by_cases h : p+(q+1)=j
  · rw [mapBifunctor.d₂_eq _ _ _ _ _ (show (ComplexShape.up ℤ).Rel q (q+1) from rfl) _ h]
    simp
  · rw [mapBifunctor.d₂_eq_zero' _ _ _ _ _ (show (ComplexShape.up ℤ).Rel q (q+1) from rfl) _ h]

lemma intoTensorSingle_comm (i j : ℤ) (hij : (ComplexShape.up ℤ).Rel i j) :
    intoTensorSingle F Q i ≫ (tensorSingle F Q).d i j =
      ((termTensor Q).obj F).d i j ≫ intoTensorSingle F Q j := by
  simp only [intoTensorSingle,Category.assoc,mapBifunctor.d_eq,Preadditive.comp_add,
    mapBifunctor.ι_D₁,mapBifunctor.ι_D₂,tensorSingle_d₂,comp_zero,add_zero]
  rw [mapBifunctor.d₁_eq _ _ _ _ hij _ _ (by simp)]
  dsimp
  simp [←whisker_exchange_assoc]

 

def tensorSingleIso : (termTensor Q).obj F ≅ tensorSingle F Q :=
  Hom.isoOfComponents (tensorSingleXIso F Q) (fun _ _ hij => intoTensorSingle_comm F Q _ _ hij)

def termTensorMap {Q' : ModuleCat.{u} R} (f : Q ⟶ Q') :
    (termTensor Q).obj F ⟶ (termTensor Q').obj F :=
  ((curriedTensor (ModuleCat.{u} R)).flip.map f).mapHomologicalComplex (.up ℤ) |>.app F

@[reassoc] lemma tensorSingleIso_naturality {Q' : ModuleCat.{u} R} (f : Q ⟶ Q') :
    termTensorMap F Q f ≫ (tensorSingleIso F Q').hom =
      (tensorSingleIso F Q).hom ≫ mapBifunctorMap (𝟙 F)
        ((single (ModuleCat.{u} R) (.up ℤ) 0).map f) (curriedTensor (ModuleCat.{u} R)) (.up ℤ) := by
  apply Hom.ext
  funext i
  change (F.X i ◁ f) ≫ intoTensorSingle F Q' i = intoTensorSingle F Q i ≫ _
  simp only [intoTensorSingle,Category.assoc,ι_mapBifunctorMap,HomologicalComplex.id_f,
    single_map_f_self]
  dsimp
  simp only [id_whiskerRight, Category.id_comp, ←whiskerLeft_comp_assoc, Iso.inv_hom_id_assoc]

end Lech.TensorTotal


namespace Lech
open CategoryTheory CategoryTheory.Limits
universe u
variable {R : Type u} [CommRing R]

 
noncomputable def idealCokernelIso (J : Ideal R) :
    cokernel (ModuleCat.ofHom J.subtype) ≅ ModuleCat.of R (R ⧸ J) := by
  refine ModuleCat.cokernelIsoRangeQuotient _ ≪≫ ?_
  change ModuleCat.of R (R ⧸ LinearMap.range J.subtype) ≅ _
  exact (Submodule.quotEquivOfEq _ _ (Submodule.range_subtype _)).toModuleIso

@[reassoc (attr := simp)]
lemma idealCokernelIso_π (J : Ideal R) :
    cokernel.π (ModuleCat.ofHom J.subtype) ≫ (idealCokernelIso J).hom = ModuleCat.ofHom J.mkQ := by
  unfold idealCokernelIso
  simp only [Iso.trans_hom]
  rw [← Category.assoc,ModuleCat.cokernel_π_cokernelIsoRangeQuotient_hom]
  ext
  rfl
end Lech
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_FilteredCechAugmentationRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option backward.isDefEq.respectTransparency false
namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject

namespace Lech.FilteredFraction
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {w z c : R} {d k : ℕ}
  (hw : w ∈ I^d) (hc : c ∈ I^k) (hwc : z*c=w) (hdk : k+1=d)

 
def inverseFactor (m : ℕ) : Localization.Away w :=
  Localization.mk (c^m) (⟨w^m,m,rfl⟩ : Submonoid.powers w)

include hwc in
lemma inverseFactor_mul (m : ℕ) :
    algebraMap R (Localization.Away w) (z^m) * inverseFactor (w := w) (c := c) m=1 := by
  rw [←Localization.mk_one_eq_algebraMap]
  dsimp only [inverseFactor]
  rw [Localization.mk_mul,one_mul,←mul_pow,hwc]
  exact Localization.mk_self (⟨w^m,m,rfl⟩ : Submonoid.powers w)

include hc hdk in
lemma inverseFactor_fraction (t m n : ℕ) (a : ↥(I^(n*d+(t+m)))) :
    ∃ b : ↥(I^((n+m)*d+t)),
      inverseFactor (w := w) (c := c) m * fraction I w d (t+m) n a = fraction I w d t (n+m) b := by
  have hc' : c^m ∈ I^(m*k) := by
    simpa only [pow_mul,mul_comm m k] using Ideal.pow_mem_pow hc m
  have heq : m*k+(n*d+(t+m))=(n+m)*d+t := by rw [←hdk]; ring
  have hb : c^m*(a:R) ∈ I^((n+m)*d+t) := by
    rw [←heq,pow_add]
    exact Ideal.mul_mem_mul hc' a.property
  refine ⟨⟨c^m*(a:R),hb⟩,?_⟩
  change Localization.mk (c^m) (⟨w^m,m,rfl⟩ : Submonoid.powers w) * Localization.mk (a:R) (⟨w^n,n,rfl⟩ : Submonoid.powers w) = Localization.mk (c^m*(a:R)) (⟨w^(n+m),n+m,rfl⟩ : Submonoid.powers w)
  rw [Localization.mk_mul,Localization.mk_eq_mk_iff,Localization.r_iff_exists]
  refine ⟨1,?_⟩
  simp only [Submonoid.coe_one,one_mul,Submonoid.coe_mul,pow_add]
  ring

include hw hc hdk in
lemma inverseFactor_mem (t m : ℕ) (x : piece I w d (t+m)) :
    inverseFactor (w := w) (c := c) m * x.val ∈ piece I w d t := by
  obtain ⟨n,a,ha⟩ := exists_fraction I w d hw (t+m) x
  rw [←ha]
  obtain ⟨b,hb⟩ := inverseFactor_fraction I hc hdk t m n a
  rw [hb]
  exact fraction_mem I w d t (n+m) b

 

def divide (t m : ℕ) : piece I w d (t+m) →ₗ[R] piece I w d t where
  toFun x := ⟨inverseFactor (w := w) (c := c) m * x.val,inverseFactor_mem I hw hc hdk t m x⟩
  map_add' _x _y := Subtype.ext (mul_add _ _ _)
  map_smul' _r _x := Subtype.ext (mul_smul_comm _ _ _)

include hwc in
lemma smul_divide (t m : ℕ) (x : piece I w d (t+m)) :
    z^m • divide I hw hc hdk t m x = Submodule.inclusion (antitone I w d (Nat.le_add_right t m)) x := by
  apply Subtype.ext
  change z^m • (inverseFactor (w := w) (c := c) m * x.val)=x.val
  rw [Algebra.smul_def,←mul_assoc,inverseFactor_mul hwc,one_mul]
end Lech.FilteredFraction


namespace Lech.FilteredCech
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {h : ℕ}
  (z : Fin h → R) (hz : ∀ i, z i ∈ I)

 
def divide {s : Finset (Fin h)} (i : Fin h) (hi : i∈s) (t m : ℕ) :
    term I z (t+m) s →ₗ[R] term I z t s := by
  classical
  exact FilteredFraction.divide I (denominator_mem I z hz s)
    (denominator_mem I z hz (s.erase i)) (Finset.card_erase_add_one hi) t m

lemma smul_divide {s : Finset (Fin h)} (i : Fin h) (hi : i∈s) (t m : ℕ)
    (x : term I z (t+m) s) :
    z i ^ m • divide I z hz i hi t m x =
      Submodule.inclusion (FilteredFraction.antitone I _ _ (Nat.le_add_right t m)) x := by
  classical
  apply FilteredFraction.smul_divide
  exact Finset.mul_prod_erase s z hi
end Lech.FilteredCech
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_FilteredCechAugmented
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option backward.isDefEq.respectTransparency false
namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject

lemma component_iso_square_p0 {C : Type*} [Category C]
    {X Y A B D E : C} (eA : A ≅ B) (eD : D ≅ E)
    (a : X ⟶ A) (b : Y ⟶ D) (h : X ⟶ Y) (f : B ⟶ E) (g : A ⟶ D)
    (hg : g = eA.hom ≫ f ≫ eD.inv) (ha : h ≫ b = a ≫ g) :
    (a ≫ eA.hom) ≫ f = h ≫ (b ≫ eD.hom) := by
  rw [← Category.assoc h b, ha, Category.assoc, hg]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]


namespace Lech.TensorTotal
open CategoryTheory CategoryTheory.Limits HomologicalComplex MonoidalCategory
universe u
variable {R : Type u} [CommRing R]
variable (F : CochainComplex (ModuleCat.{u} R) ℤ)
  {Q Q' : ModuleCat.{u} R} (a : R) (d inc : Q ⟶ Q')

lemma scalar_tensor_division (hd : a • d=inc) :
    (termTensor Q).map (a • 𝟙 F) ≫ termTensorMap F Q d = termTensorMap F Q inc := by
  apply Hom.ext
  funext i
  apply ModuleCat.hom_ext
  apply TensorProduct.ext
  ext x y
  change (a • x) ⊗ₜ[R] d y = x ⊗ₜ[R] inc y
  rw [TensorProduct.smul_tmul]
  have hdy := congrArg (fun f : Q ⟶ Q' => f y) hd
  change a • d y=inc y at hdy
  rw [hdy]

 
def tensorDivisionHomotopy (hd : a • d=inc) (H : Homotopy (a • 𝟙 F) 0) :
    Homotopy (termTensorMap F Q inc) 0 := by
  have HH := (((curriedTensor (ModuleCat.{u} R)).flip.obj Q).mapHomotopy H).compRight
    (termTensorMap F Q d)
  rw [scalar_tensor_division F a d inc hd,Functor.map_zero,zero_comp] at HH
  exact HH
end Lech.TensorTotal


namespace Lech.TensorPi
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive MonoidalCategory
universe u
variable {R : Type u} [CommRing R] {J : Type} [Fintype J]
  {A B C : ModuleCat.{u} R} {Q Q' Q'' : J → ModuleCat.{u} R}
open scoped TensorProduct
local instance instDecidableEq_solutions : DecidableEq J := Classical.decEq J

abbrev modulePi (Q : J → ModuleCat.{u} R) : ModuleCat.{u} R := ModuleCat.of R (∀ j, Q j)

 

def map (f : ∀ j, A ⊗ Q j ⟶ B ⊗ Q' j) : A ⊗ modulePi Q ⟶ B ⊗ modulePi Q' :=
  ModuleCat.ofHom ((TensorProduct.piRight R R B (fun j => Q' j)).symm.toLinearMap.comp
    ((LinearMap.pi (fun j => (f j).hom.comp (LinearMap.proj j))).comp
      (TensorProduct.piRight R R A (fun j => Q j)).toLinearMap))

@[simp] lemma map_apply (f : ∀ j, A ⊗ Q j ⟶ B ⊗ Q' j)
    (x : A ⊗[R] (∀ j, Q j)) (j : J) :
    TensorProduct.piRight R R B (fun j => Q' j) (map f x) j =
      f j (TensorProduct.piRight R R A (fun j => Q j) x j) := by
  change (TensorProduct.piRight R R B _)
    ((TensorProduct.piRight R R B _).symm _) j = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

lemma ext {f g : A ⊗ modulePi Q ⟶ B ⊗ modulePi Q'}
    (h : ∀ x j, TensorProduct.piRight R R B (fun j => Q' j) (f x) j =
      TensorProduct.piRight R R B (fun j => Q' j) (g x) j) : f=g := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply (TensorProduct.piRight R R B (fun j => Q' j)).injective
  funext j
  exact h x j

lemma map_comp (f : ∀ j, A ⊗ Q j ⟶ B ⊗ Q' j) (g : ∀ j, B ⊗ Q' j ⟶ C ⊗ Q'' j) :
    map (fun j => f j ≫ g j) = map f ≫ map g := by
  apply ext
  intro x j
  simp

lemma map_add (f g : ∀ j, A ⊗ Q j ⟶ B ⊗ Q' j) :
    map (fun j => f j+g j)=map f+map g := by
  apply ext
  intro x j
  change TensorProduct.piRight R R B _ (map (fun j => f j+g j) x) j =
    TensorProduct.piRight R R B _ (map f x + map g x) j
  simp only [LinearEquiv.map_add,Pi.add_apply,map_apply]
  rfl

lemma map_zero : map (fun j : J => (0 : A ⊗ Q j ⟶ B ⊗ Q' j))=0 := by
  apply ext
  intro x j
  simp

 
def piMap (g : ∀ j, Q j ⟶ Q' j) : modulePi Q ⟶ modulePi Q' :=
  ModuleCat.ofHom (LinearMap.pi (fun j => (g j).hom.comp (LinearMap.proj j)))

omit [Fintype J] in
lemma piMap_id : piMap (fun j => 𝟙 (Q j))=𝟙 (modulePi Q) := rfl
end Lech.TensorPi


namespace Lech.TensorTotal
open CategoryTheory CategoryTheory.Limits HomologicalComplex MonoidalCategory
universe u
variable {R : Type u} [CommRing R]
variable (F : CochainComplex (ModuleCat.{u} R) ℤ)

lemma termTensorMap_comp {Q Q' Q'' : ModuleCat.{u} R} (a : Q ⟶ Q') (b : Q' ⟶ Q'') :
    termTensorMap F Q (a≫b)=termTensorMap F Q a ≫ termTensorMap F Q' b := by
  apply Hom.ext
  funext p
  exact whiskerLeft_comp (F.X p) a b

lemma termTensorMap_zero {Q Q' : ModuleCat.{u} R} : termTensorMap F Q (0 : Q ⟶ Q')=0 := by
  apply Hom.ext
  funext p
  exact Functor.map_zero ((curriedTensor (ModuleCat.{u} R)).obj (F.X p)) Q Q'

 

def coefficientHomotopyOfIso {Q Q' A A' : ModuleCat.{u} R}
    (e : Q ≅ A) (e' : Q' ≅ A') (f : Q ⟶ Q') (g : A ⟶ A')
    (hf : e.hom ≫ g=f≫e'.hom) (H : Homotopy (termTensorMap F A g) 0) :
    Homotopy (termTensorMap F Q f) 0 := by
  have HH := (H.compLeft (termTensorMap F Q e.hom)).compRight
    (termTensorMap F A' e'.inv)
  rw [←termTensorMap_comp,←termTensorMap_comp,hf,Category.assoc,Iso.hom_inv_id,
    Category.comp_id,comp_zero,zero_comp] at HH
  exact HH
end Lech.TensorTotal


namespace Lech.TotalGhost
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive HomologicalComplex
open HomologicalComplex₂
universe u
variable {R : Type u} [CommRing R]
abbrev Bic := HomologicalComplex₂ (ModuleCat.{u} R) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
variable {K L M : Bic (R := R)}

 

structure RowHomotopy (f : K ⟶ L) where
  h : ∀ p q : ℤ, (K.X p).X q ⟶ (L.X (p-1)).X q
  equation : ∀ p q : ℤ, (f.f p).f q =
    (K.d p (p+1)).f q ≫ h (p+1) q ≫ (L.XXIsoOfEq _ _ _ (by omega) rfl).hom +
      h p q ≫ (L.d (p-1) p).f q

 
def homotopyTerm {f : K ⟶ L} (h : RowHomotopy f) (i j : ℤ)
    (hij : (ComplexShape.up ℤ).Rel j i) : (K.total (ComplexShape.up ℤ)).X i ⟶ (L.total (ComplexShape.up ℤ)).X j :=
  K.totalDesc (fun p q hpq => h.h p q ≫ L.ιTotal (ComplexShape.up ℤ) (p-1) q j (by
    change p+q=i at hpq
    change j+1=i at hij
    change p-1+q=j
    omega))

@[reassoc (attr := simp)] lemma ι_homotopyTerm {f : K ⟶ L} (h : RowHomotopy f)
    (p q i j : ℤ) (hpq : p+q=i) (hij : (ComplexShape.up ℤ).Rel j i) :
    K.ιTotal (ComplexShape.up ℤ) p q i hpq ≫ homotopyTerm h i j hij =
      h.h p q ≫ L.ιTotal (ComplexShape.up ℤ) (p-1) q j (by change j+1=i at hij; change p-1+q=j; omega) := by
  apply ι_totalDesc

end Lech.TotalGhost
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_PrimitiveChartFaithfullyFlat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
attribute [local instance] Classical.propDecidable
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian
open scoped BigOperators
open scoped Classical


namespace Lech.RootTransitions
open Polynomial
universe u
variable {B : Type u} [CommRing B]

lemma linear_shift (t u r : B) (d : Bˣ) (hd : (d:B)=1+(t-u)*r) :
    C (-r)*(C u*Polynomial.X+1)+C (1+t*r)*Polynomial.X=
      C (d:B)*(Polynomial.X-C (r*(↑d⁻¹:B))) := by
  have hc : (d:B)*(r*(↑d⁻¹:B))=r := by
    rw [mul_left_comm,d.mul_inv,mul_one]
  rw [mul_sub,← C_mul,hc,hd]
  simp only [map_neg,map_add,map_sub,map_mul,map_one]
  ring

end Lech.RootTransitions


namespace Lech.RootGluing
open Polynomial
universe u
variable {B : Type u} [CommRing B]

lemma map_inverse {C : Type u} [CommRing C] (φ : B →+* C) (x : B) (hx : IsUnit x) :
    φ (Ring.inverse x)=Ring.inverse (φ x) := by
  obtain ⟨v,rfl⟩ := hx
  rw [Ring.inverse_unit]
  change (((Units.map φ.toMonoidHom v)⁻¹ : Cˣ) : C)=Ring.inverse (↑(Units.map φ.toMonoidHom v))
  exact (Ring.inverse_unit _).symm

lemma denominator_comp (a b x : B) (d : Bˣ) (hd : (d:B)=1+a*x) :
    1+b*(x*(↑d⁻¹:B))=(1+(a+b)*x)*(↑d⁻¹:B) := by
  calc
    1+b*(x*(↑d⁻¹:B))=((d:B)+b*x)*(↑d⁻¹:B) := by rw [add_mul,d.mul_inv]; ring
    _ = (1+(a+b)*x)*(↑d⁻¹:B) := by rw [hd]; ring

end Lech.RootGluing
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_RootBundleChartsDenominator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
attribute [local instance] Classical.propDecidable
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian
open scoped BigOperators
open scoped Classical


namespace Lech.RootTransport
open Polynomial Lech.RootGluing
universe u
variable {B C : Type u} [CommRing B] [CommRing C] [Algebra B C]
variable (f : B[X])
  (n : ℕ)
  (hn : f.natDegree≤n)
  (t : B)
  (v : Bˣ)
  (hv : f.eval t=(v:B))
  (u : C)
  (w : Cˣ)
  (rs : Fin n → C)

include hv in
lemma mapped_eval : (f.map (algebraMap B C)).eval (algebraMap B C t)=
    (Units.map (algebraMap B C).toMonoidHom v:Cˣ) := by
  rw [Polynomial.eval_map,eval₂_at_apply,hv]
  rfl

end Lech.RootTransport

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_RootCoactionT
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
attribute [local instance] Classical.propDecidable
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian
open scoped BigOperators
open scoped Classical
namespace Lech.RootCoaction

section


lemma unit_zpow_cancel {R : Type*} [CommRing R] (a b : Rˣ) (z : ℤ) :
    a^z*(b*a⁻¹)^z=b^z := by
  rw [mul_zpow,inv_zpow,mul_left_comm,mul_inv_cancel,mul_one]

open Polynomial Lech.RootGluing
open scoped TensorProduct
universe u

end


open Polynomial Lech.RootGluing
open scoped TensorProduct
universe u
end Lech.RootCoaction


namespace Lech.NativeDescent
open scoped TensorProduct
open TensorProduct
universe u v w
variable {A : Type u} {B : Type v} {M : Type w}
  [CommRing A] [CommRing B] [Algebra A B]
  [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]

 
def inclusion : M →ₗ[A] B ⊗[A] M := TensorProduct.mk A B M 1
 
def evaluation : B ⊗[A] M →ₗ[B] M := (LinearMap.id : M →ₗ[A] M).liftBaseChange B

variable (l : M →ₗ[B] B ⊗[A] M)
 
def invariants : Submodule A M := LinearMap.eqLocus (l.restrictScalars A) inclusion

lemma invariant_eq (x : invariants l) : l (x:M)=(1:B) ⊗ₜ[A] (x:M) := x.property

 
def baseMap : B ⊗[A] invariants l →ₗ[B] M := (invariants l).subtype.liftBaseChange B

def baseInclusion : B ⊗[A] invariants l →ₗ[B] B ⊗[A] M :=
  AlgebraTensorModule.lTensor B B (invariants l).subtype

lemma evaluation_baseInclusion : (evaluation (A := A) (B := B) (M := M)).comp (baseInclusion l)=baseMap l := by
  ext x
  simp [evaluation,baseInclusion,baseMap]

lemma coaction_baseMap : l.comp (baseMap l)=baseInclusion l := by
  ext x
  change l ((1:B) • (x:M))=(1:B) ⊗ₜ[A] (x:M)
  simpa only [one_smul] using invariant_eq l x

variable [Module.Flat A B]
variable (hε : (evaluation (A := A) (B := B) (M := M)).comp l=LinearMap.id)
variable (hδ : (AlgebraTensorModule.lTensor B B inclusion).comp l=
  (AlgebraTensorModule.lTensor B B (l.restrictScalars A)).comp l)

 
def coactionToEqualizer : M →ₗ[B]
    LinearMap.eqLocus (AlgebraTensorModule.lTensor B B (l.restrictScalars A))
      (AlgebraTensorModule.lTensor B B inclusion) :=
  l.codRestrict _ (fun x => (LinearMap.congr_fun hδ x).symm)

def inverse : M →ₗ[B] B ⊗[A] invariants l :=
  (LinearMap.tensorEqLocusEquiv B B (l.restrictScalars A) inclusion).symm.toLinearMap.comp
    (coactionToEqualizer l hδ)

lemma baseInclusion_inverse : (baseInclusion l).comp (inverse l hδ)=l := by
  ext x
  change (LinearMap.lTensor B (invariants l).subtype)
    ((LinearMap.tensorEqLocusEquiv B B (l.restrictScalars A) inclusion).symm
      (coactionToEqualizer l hδ x))=l x
  exact LinearMap.lTensor_eqLocus_subtype_tensoreqLocusEquiv_symm B B
    (l.restrictScalars A) inclusion (coactionToEqualizer l hδ x)


def tensorEquiv : B ⊗[A] invariants l ≃ₗ[B] M :=
  LinearEquiv.ofLinearMap (baseMap l) (inverse l hδ)
    (by
      rw [← evaluation_baseInclusion,LinearMap.comp_assoc,baseInclusion_inverse,hε])
    (by
      apply LinearMap.ext
      intro x
      apply Module.Flat.lTensor_preserves_injective_linearMap
        (invariants l).subtype (invariants l).injective_subtype
      change baseInclusion l ((inverse l hδ) (baseMap l x))=baseInclusion l x
      rw [← LinearMap.comp_apply,baseInclusion_inverse,← LinearMap.comp_apply,coaction_baseMap])
end Lech.NativeDescent


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_StandardFactorChartsL
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
attribute [local instance] Classical.propDecidable
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian
open scoped BigOperators
open scoped Classical


namespace Lech.FactorNormalization

section
open Polynomial
universe u
variable {A : Type u} [CommRing A]
variable (f : A[X]) (n : ℕ) (hn : f.natDegree≤n) (t : A) (v w : Aˣ)
  (hv : f.eval t=(v:A)) (a b : Fin n → A)
  (hf : f.homogenize n=MvPolynomial.C (w:A)*∏ i,
    (MvPolynomial.C (a i)*MvPolynomial.X 0+MvPolynomial.C (b i)*MvPolynomial.X 1))

include hn hv hf in
lemma evaluation_product : (v:A)=(w:A)*∏ i,(t*a i+b i) := by
  have h := congrArg (MvPolynomial.aeval ![t,1]) hf
  rw [Polynomial.aeval_homogenize_of_eq_one hn _ rfl] at h
  simpa [mul_comm] using hv.symm.trans h

include hn hv hf in
lemma factor_value_unit (i : Fin n) : IsUnit (t*a i+b i) := by
  have h : IsUnit (∏ i,(t*a i+b i)) := by
    apply isUnit_of_mul_isUnit_right (x := (w:A))
    rw [← evaluation_product f n hn t v w hv a b hf]
    exact v.isUnit
  exact isUnit_of_dvd_unit (Finset.dvd_prod_of_mem (fun i => t*a i+b i) (Finset.mem_univ i)) h


def denominator (i : Fin n) : Aˣ :=
  (factor_value_unit f n hn t v w hv a b hf i).unit

lemma denominator_val (i : Fin n) :
    (denominator f n hn t v w hv a b hf i:A)=t*a i+b i :=
  (factor_value_unit f n hn t v w hv a b hf i).unit_spec

def roots (i : Fin n) : A := -a i*(denominator f n hn t v w hv a b hf i)⁻¹

lemma unit_product : w*∏ i,denominator f n hn t v w hv a b hf i=v := by
  apply Units.ext
  simpa only [Units.val_mul,Units.coe_prod,denominator_val] using
    (evaluation_product f n hn t v w hv a b hf).symm

lemma transform_factor (i : Fin n) :
    C (a i)*(C t*Polynomial.X+1)+C (b i)*Polynomial.X=
      C (denominator f n hn t v w hv a b hf i:A)*
        (Polynomial.X-C (roots f n hn t v w hv a b hf i)) := by
  let μ := denominator f n hn t v w hv a b hf i
  have hμ : (μ:A)=t*a i+b i := denominator_val f n hn t v w hv a b hf i
  have hroot : (μ:A)*roots f n hn t v w hv a b hf i= -a i := by
    change (μ:A)*(-a i*↑μ⁻¹)= -a i
    rw [mul_left_comm,Units.mul_inv,mul_one]
  rw [mul_sub,← C_mul,hroot,C_neg,sub_neg_eq_add,hμ,C_add,C_mul]
  ring

end


universe u
variable {R : Type u} [CommRing R]

 
lemma change_denominator (a b s t : R) (μ ν : Rˣ)
    (hμ : (μ:R)=s*a+b) (hν : (ν:R)=t*a+b) :
    1+(s-t)*(-a*(μ⁻¹:Rˣ))=((ν*μ⁻¹:Rˣ):R) := by
  simp only [Units.val_mul]
  calc
    _ = ((μ:R)-(s-t)*a)*(μ⁻¹:Rˣ) := by
      calc
        _ = (μ:R)*(μ⁻¹:Rˣ) - ((s-t)*a)*(μ⁻¹:Rˣ) := by rw [Units.mul_inv];ring
        _ = _ := (sub_mul _ _ _).symm
    _ = _ := by rw [hμ,hν];ring


open Polynomial
end Lech.FactorNormalization


namespace Lech.FFTensorMaps
open scoped TensorProduct
universe u v w w' z
variable {R : Type u} (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
  [Module.FaithfullyFlat R S]
variable {M : Type w} {N : Type w'} [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]

lemma bijective_baseChange_iff (f : M →ₗ[R] N) : Function.Bijective (f.baseChange S) ↔ Function.Bijective f := by
  rw [LinearMap.baseChange_eq_ltensor]
  exact and_congr (Module.FaithfullyFlat.lTensor_injective_iff_injective R S f)
    (Module.FaithfullyFlat.lTensor_surjective_iff_surjective R S f)

variable {Q : Type z} [AddCommGroup Q] [Module S Q]
lemma bijective (f : M →ₗ[R] N) (e : S ⊗[R] M ≃ₗ[S] Q) (e' : S ⊗[R] N ≃ₗ[S] Q)
    (h : e'.toLinearMap.comp (f.baseChange S)=e.toLinearMap) : Function.Bijective f := by
  apply (bijective_baseChange_iff S f).mp
  have he (x) : e' ((f.baseChange S) x)=e x := LinearMap.congr_fun h x
  constructor
  · intro x y hxy
    apply e.injective
    rw [← he x,← he y,hxy]
  · intro y
    obtain ⟨x,hx⟩ := e.surjective (e' y)
    exact ⟨x,e'.injective ((he x).trans hx)⟩
end Lech.FFTensorMaps


namespace Lech.NativeDescent
open scoped TensorProduct
open TensorProduct
universe u v w
variable {A : Type u} (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
  (N : Type w) [AddCommGroup N] [Module A N]

 
def canonical : B ⊗[A] N →ₗ[B] B ⊗[A] (B ⊗[A] N) :=
  AlgebraTensorModule.lTensor B B (TensorProduct.mk A B N 1)

lemma canonical_counit :
    (evaluation (A := A) (B := B) (M := B ⊗[A] N)).comp (canonical (A := A) B N)=LinearMap.id := by
  ext x
  simp [evaluation,canonical]

lemma canonical_coassoc :
    (AlgebraTensorModule.lTensor B B inclusion).comp (canonical (A := A) B N)=
      (AlgebraTensorModule.lTensor B B ((canonical (A := A) B N).restrictScalars A)).comp (canonical (A := A) B N) := by
  ext x
  simp [inclusion,canonical]

 
def canonicalUnit : N →ₗ[A] invariants (canonical (A := A) B N) :=
  (TensorProduct.mk A B N 1).codRestrict _ (fun x => by
    change canonical (A := A) B N (1 ⊗ₜ[A] x)=(1:B) ⊗ₜ[A] (1 ⊗ₜ[A] x)
    rfl)

lemma canonical_compat [Module.Flat A B] :
    (tensorEquiv (canonical (A := A) B N) (canonical_counit (A := A) B N) (canonical_coassoc (A := A) B N)).toLinearMap.comp
      ((canonicalUnit (A := A) B N).baseChange B)=LinearMap.id := by
  ext x
  change (1:B) • ((1:B) ⊗ₜ[A] x)=(1:B) ⊗ₜ[A] x
  rw [one_smul]

lemma canonicalUnit_bijective [Module.FaithfullyFlat A B] :
    Function.Bijective (canonicalUnit (A := A) B N) := by
  apply (FFTensorMaps.bijective_baseChange_iff (R := A) (M := N)
    (N := invariants (A := A) (canonical (A := A) B N)) B
    (canonicalUnit (A := A) B N)).mp
  have h := canonical_compat (A := A) B N
  let he := tensorEquiv (canonical (A := A) B N)
    (canonical_counit (A := A) B N) (canonical_coassoc (A := A) B N)
  have hf : (canonicalUnit (A := A) B N).baseChange B=he.symm.toLinearMap := by
    apply LinearMap.ext
    intro x
    apply he.injective
    change he ((canonicalUnit (A := A) B N).baseChange B x)=he (he.symm x)
    rw [he.apply_symm_apply]
    exact LinearMap.congr_fun h x
  rw [hf]
  exact he.symm.bijective

end Lech.NativeDescent

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_NativeDescentCanonicalAlg
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option synthInstance.maxHeartbeats 200000
namespace OAI

section
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
attribute [local instance] Classical.propDecidable
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian
open scoped BigOperators
open scoped Classical
namespace Lech.NativeDescent
open scoped TensorProduct
universe u v w
variable {A : Type u} (B : Type v) (T : Type w)
  [CommRing A] [CommRing B] [CommRing T] [Algebra A B] [Algebra A T]

 
def canonicalAlg : B ⊗[A] T →ₐ[B] B ⊗[A] (B ⊗[A] T) :=
  Algebra.TensorProduct.lift (Algebra.ofId _ _)
    (Algebra.TensorProduct.includeRight.comp (Algebra.TensorProduct.includeRight : T →ₐ[A] B ⊗[A] T))
    (fun _ _ => Commute.all _ _)

lemma canonicalAlg_linear : (canonicalAlg (A := A) B T).toLinearMap=canonical (A := A) B T := by
  ext t
  simp [canonicalAlg,canonical]

def canonicalAlgebra : Subalgebra A (B ⊗[A] T) :=
  AlgHom.equalizer ((canonicalAlg (A := A) B T).restrictScalars A) Algebra.TensorProduct.includeRight

lemma canonicalAlgebra_module : (canonicalAlgebra (A := A) B T).toSubmodule=invariants (canonical (A := A) B T) := by
  ext x
  change (canonicalAlg (A := A) B T x=(1:B) ⊗ₜ[A] x) ↔
    (canonical (A := A) B T x=(1:B) ⊗ₜ[A] x)
  rw [← canonicalAlg_linear]
  rfl

 
def canonicalAlgUnit : T →ₐ[A] canonicalAlgebra (A := A) B T where
  toFun t := ⟨1 ⊗ₜ[A] t,by
    change canonicalAlg (A := A) B T (1 ⊗ₜ[A] t)=(1:B) ⊗ₜ[A] ((1:B) ⊗ₜ[A] t)
    simp [canonicalAlg]⟩
  map_zero' := Subtype.ext (map_zero (Algebra.TensorProduct.includeRight : T →ₐ[A] B ⊗[A] T))
  map_one' := Subtype.ext (map_one (Algebra.TensorProduct.includeRight : T →ₐ[A] B ⊗[A] T))
  map_add' x y := Subtype.ext (map_add (Algebra.TensorProduct.includeRight : T →ₐ[A] B ⊗[A] T) x y)
  map_mul' x y := Subtype.ext (map_mul (Algebra.TensorProduct.includeRight : T →ₐ[A] B ⊗[A] T) x y)
  commutes' a := Subtype.ext ((Algebra.TensorProduct.includeRight : T →ₐ[A] B ⊗[A] T).commutes a)

lemma canonicalAlgUnit_bijective [Module.FaithfullyFlat A B] :
    Function.Bijective (canonicalAlgUnit (A := A) B T) := by
  let e : canonicalAlgebra (A := A) B T ≃ₗ[A] invariants (canonical (A := A) B T) :=
    LinearEquiv.ofEq _ _ (canonicalAlgebra_module (A := A) B T)
  have he : e.toLinearMap.comp (canonicalAlgUnit (A := A) B T).toLinearMap=canonicalUnit (A := A) B T := by
    ext t
    rfl
  have hb : Function.Bijective (e.toLinearMap.comp (canonicalAlgUnit (A := A) B T).toLinearMap) := by
    rw [he]
    exact canonicalUnit_bijective B T
  refine ⟨fun x y h => hb.injective (congrArg e h),?_⟩
  intro y
  obtain ⟨x,hx⟩ := hb.surjective (e y)
  exact ⟨x,e.injective hx⟩

 
def canonicalAlgEquiv [Module.FaithfullyFlat A B] : T ≃ₐ[A] canonicalAlgebra (A := A) B T :=
  AlgEquiv.ofBijective (canonicalAlgUnit (A := A) B T) (canonicalAlgUnit_bijective B T)
end Lech.NativeDescent


end
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_TotalGhostRowHom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
namespace Lech.TotalGhost
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive HomologicalComplex
open HomologicalComplex₂
universe u
variable {R : Type u} [CommRing R]
variable {K L : Bic (R := R)} {f : K ⟶ L}

lemma row_hom_transport (q r s t : ℤ) (hst : s=t)
    (H : Homotopy (((HomologicalComplex₂.flipFunctor _ _ _).map f).f q) 0) :
    H.hom r s ≫ (L.XXIsoOfEq _ _ _ hst rfl).hom = H.hom r t := by
  subst t
  simp only [XXIsoOfEq_rfl,Iso.refl_hom]
  exact Category.comp_id _

 

def RowHomotopy.ofRows
    (H : ∀ q, Homotopy (((HomologicalComplex₂.flipFunctor _ _ _).map f).f q) 0) : RowHomotopy f where
  h p q := (H q).hom p (p-1)
  equation p q := by
    have hh := (H q).comm p
    rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel p (p+1) from rfl),
      prevD_eq _ (show (ComplexShape.up ℤ).Rel (p-1) p by change p-1+1=p; omega),
      zero_f,add_zero] at hh
    exact hh.trans (congrArg (fun t : (K.X (p+1)).X q ⟶ (L.X p).X q =>
      (K.d p (p+1)).f q ≫ t +
      (show (K.X p).X q ⟶ (L.X (p-1)).X q from (H q).hom p (p-1)) ≫ (L.d (p-1) p).f q)
        (row_hom_transport q (p+1) (p+1-1) p (by omega) (H q)).symm)
end Lech.TotalGhost


namespace Lech.FilteredCech
open CategoryTheory CategoryTheory.Limits HomologicalComplex MonoidalCategory
open Lech.TensorTotal
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {h : ℕ}
  (z : Fin h → R) (hz : ∀ i, z i ∈ I)
variable (F : CochainComplex (ModuleCat.{u} R) ℤ)

def tensorBic : CochainComplex (ModuleCat.{u} R) ℤ ⥤ TotalGhost.Bic (R := R) :=
  ((curriedTensor (ModuleCat.{u} R)).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj F

end Lech.FilteredCech

open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra

open CategoryTheory CategoryTheory.Limits CochainComplex
open scoped ModuleCat.Algebra
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_SignedCechBicRow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
open CategoryTheory CategoryTheory.Limits CochainComplex
open scoped ModuleCat.Algebra
open CategoryTheory CategoryTheory.Limits CochainComplex CochainComplex.HomComplex
open CochainComplex CochainComplex.HomComplex
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped BigOperators


namespace Lech.ComplexLift
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u v w
variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  {ι : Type w} {c : ComplexShape ι}
  {K L : HomologicalComplex C c}

 

def lift (f : K ⟶ L) (a : L ⟶ L) [∀ i, Mono (f.f i)]
    (r : ∀ i, L.X i ⟶ K.X i) (hr : ∀ i, r i ≫ f.f i=a.f i) : L ⟶ K where
  f := r
  comm' i j _ := by
    apply (cancel_mono (f.f j)).mp
    rw [Category.assoc,←f.comm i j,←Category.assoc,hr,a.comm,Category.assoc,hr]

@[reassoc] lemma lift_comp (f : K ⟶ L) (a : L ⟶ L) [∀ i, Mono (f.f i)]
    (r : ∀ i, L.X i ⟶ K.X i) (hr : ∀ i, r i ≫ f.f i=a.f i) :
    lift f a r hr ≫ f=a := by
  apply Hom.ext
  funext i
  exact hr i
end Lech.ComplexLift


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_BicomplexImageLift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Lech.ComplexLift
open CategoryTheory CategoryTheory.Limits HomologicalComplex
variable {C : Type*} [Category C] [HasZeroMorphisms C]
  {ι : Type*} {c : ComplexShape ι} {K L M : HomologicalComplex C c}
def factor (f : K ⟶ L) (g : M ⟶ L) [∀ i, Mono (f.f i)]
    (r : ∀ i,M.X i ⟶ K.X i) (hr : ∀ i,r i ≫ f.f i=g.f i) : M ⟶ K where
  f := r
  comm' i j _ := by
    apply (cancel_mono (f.f j)).mp
    rw [Category.assoc,←f.comm i j,←Category.assoc,hr,g.comm,Category.assoc,hr]
lemma factor_comp (f : K ⟶ L) (g : M ⟶ L) [∀ i, Mono (f.f i)]
    (r : ∀ i,M.X i ⟶ K.X i) (hr : ∀ i,r i ≫ f.f i=g.f i) : factor f g r hr ≫ f=g := by
  apply Hom.ext
  funext i
  exact hr i
end Lech.ComplexLift

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_PerfectDomainStagesTensorTo
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MvPowerSeries
open scoped Classical
open scoped TensorProduct
open IsLocalRing
open MvPowerSeries IsLocalRing
open scoped ENNReal
open scoped ENNReal TensorProduct Classical DirectSum
open TensorProduct
open scoped TensorProduct nonZeroDivisors


namespace Lech.Conductor
variable {R C : Type*} [CommRing R] [CommRing C] [Algebra R C]
  (B : Subalgebra R C) (g : R) (hg : ∀ c : C, g • c ∈ B)

 
def linearMap : C →ₗ[B] B where
  toFun c := ⟨g • c,hg c⟩
  map_add' x y := Subtype.ext (smul_add g x y)
  map_smul' b c := by
    apply Subtype.ext
    change g • ((b : C)*c) = (b : C)*(g • c)
    exact (mul_smul_comm g (b : C) c).symm

end Lech.Conductor


end
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_SeparableOrderNormalizedLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MvPowerSeries
open scoped Classical
open scoped TensorProduct
open IsLocalRing
open MvPowerSeries IsLocalRing
open scoped ENNReal
open scoped ENNReal TensorProduct Classical DirectSum
open TensorProduct
open scoped TensorProduct nonZeroDivisors
open scoped nonZeroDivisors
open scoped BigOperators
open scoped nonZeroDivisors TensorProduct
open scoped Classical Pointwise
open CategoryTheory CategoryTheory.Limits
open CochainComplex CochainComplex.HomComplex
open scoped ENNReal ZeroObject
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian


namespace Lech
open Polynomial Filter
open scoped BigOperators

def EventuallyPolynomial (f : ℕ → ℚ) : Prop :=
  ∃ p : ℚ[X], ∀ᶠ n in atTop, f n = p.eval (n : ℚ)

end Lech


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_PowerSeriesFinDimension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MvPowerSeries
open scoped Classical
open scoped TensorProduct
open IsLocalRing
open MvPowerSeries IsLocalRing
open scoped ENNReal
open scoped ENNReal TensorProduct Classical DirectSum
open TensorProduct
open scoped TensorProduct nonZeroDivisors
open scoped nonZeroDivisors
open scoped BigOperators
open scoped nonZeroDivisors TensorProduct
open scoped Classical Pointwise
open CategoryTheory CategoryTheory.Limits
open CochainComplex CochainComplex.HomComplex
open scoped ENNReal ZeroObject
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian
open CategoryTheory


namespace Lech.PowerSeries
open MvPowerSeries
open scoped Topology
variable {σ k D : Type*} [Fintype σ] [CommRing k] [CommRing D]
  (φ : k →+* D) (I : Ideal D) [IsAdicComplete I D]
  (z : σ → D) (hz : ∀ i, z i ∈ I)

 
def eval : MvPowerSeries σ k →+* D := by
  let : WithIdeal k := ⟨⊥⟩
  let : WithIdeal D := ⟨I⟩
  let : DiscreteTopology k := is_bot_adic_iff.mp rfl
  have hcomp := (IsAdic.isAdicComplete_iff (I := I) (R := D) rfl).mp inferInstance
  let : CompleteSpace D := hcomp.1
  let : T2Space D := hcomp.2
  exact MvPowerSeries.eval₂Hom (φ := φ) (continuous_of_discreteTopology)
    ⟨fun i => WithIdeal.isTopologicallyNilpotent_of_mem (hz i), by
      rw [Filter.cofinite_eq_bot]; exact Filter.tendsto_bot⟩

lemma eval_C (a : k) : eval φ I z hz (C a) = φ a := by
  let : WithIdeal k := ⟨⊥⟩
  let : WithIdeal D := ⟨I⟩
  let : DiscreteTopology k := is_bot_adic_iff.mp rfl
  have hcomp := (IsAdic.isAdicComplete_iff (I := I) (R := D) rfl).mp inferInstance
  let : CompleteSpace D := hcomp.1
  let : T2Space D := hcomp.2
  have heval : MvPowerSeries.HasEval z :=
    ⟨fun i => WithIdeal.isTopologicallyNilpotent_of_mem (hz i), by
      rw [Filter.cofinite_eq_bot]; exact Filter.tendsto_bot⟩
  change MvPowerSeries.eval₂Hom (φ := φ) continuous_of_discreteTopology heval (C a) = _
  rw [MvPowerSeries.coe_eval₂Hom,MvPowerSeries.eval₂_C]

lemma eval_X (i : σ) : eval φ I z hz (X i) = z i := by
  let : WithIdeal k := ⟨⊥⟩
  let : WithIdeal D := ⟨I⟩
  let : DiscreteTopology k := is_bot_adic_iff.mp rfl
  have hcomp := (IsAdic.isAdicComplete_iff (I := I) (R := D) rfl).mp inferInstance
  let : CompleteSpace D := hcomp.1
  let : T2Space D := hcomp.2
  have heval : MvPowerSeries.HasEval z :=
    ⟨fun i => WithIdeal.isTopologicallyNilpotent_of_mem (hz i), by
      rw [Filter.cofinite_eq_bot]; exact Filter.tendsto_bot⟩
  change MvPowerSeries.eval₂Hom (φ := φ) continuous_of_discreteTopology heval (X i) = _
  rw [MvPowerSeries.coe_eval₂Hom,MvPowerSeries.eval₂_X]

end Lech.PowerSeries


namespace Lech.PowerSeries
open MvPowerSeries
variable (σ k : Type*) [Fintype σ] [CommRing k]

def variablesIdeal : Ideal (MvPowerSeries σ k) := Ideal.span (Set.range (X : σ → MvPowerSeries σ k))


lemma complete_variables : IsAdicComplete (variablesIdeal σ k) (MvPowerSeries σ k) := by
  exact inferInstanceAs (IsAdicComplete (Ideal.span (Set.range MvPowerSeries.X)) (MvPowerSeries σ k))

end Lech.PowerSeries


end

end OAI
end


