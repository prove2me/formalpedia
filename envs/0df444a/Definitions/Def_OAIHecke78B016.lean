-- Prove2me | Definitions.Def_OAIHecke78B016
-- name    : OAIHecke78B016
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-09T01:33:49.535156+00:00
-- url     : https://prove2.me/theorems/84e805d8-3b02-4cfb-8478-978115ce28e2
-- title:
--   OpenAI Hecke 7/8 split, definitions bundle 17 of 29
-- statement:
--   Definitions bundle 17 of 29 of the split of OpenAI's proof that finite-order Hecke $L$-functions over $\mathbb{Q}(\zeta_3)$ do not vanish for $\operatorname{Re} s > 7/8$: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/NumberTheory/DirichletL` (OpenAI, *The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane $\operatorname{Re} s > 7/8$*, September 30, 2026, family 003 of [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (definitions that choose witnesses of existence theorems or build structures carrying proofs need those proofs) and the instances and attribute-tagged lemmas of the same modules.
--
--   It imports the bundles `OAIHecke78B012`, `OAIHecke78B015` of this split, and through them their definitions. It also imports wurtle's published bundle `HeckeSevenEighths` (the comparator definitions of OpenAI's challenge statement: `Character`, `LFunction` and the theta-function pairs they are built from), which OpenAI's development defines identically.
--
--   Modules: `Eisenstein.InverseCuspCoordinates`, `Reciprocity.CubeCorrespondence`, `Reciprocity.PrimaryCongruences`, `Eisenstein.CubeResidueStrata`, `GaussSum.FiniteTranslations`, `Descent.FullProfile`, `Inversion.SecondProfileUniform`, `Descent.FirstProfileUniform`, `Hecke.IdealOperations`, `Hecke.Euler`, `Hecke.FiniteDeletion`, `Moments.HeckeTwist`, `Moments.HeckeHeight`, `Moments.HeckeSlots`, `Moments.HeckeExpansion`, `Moments.SourceRow`, `Moments.HeckeColumnWindow`, `Descent.FirstSecondHeightCost`, `Detector.HighEulerRational`, `Hecke.ModulusRefinement`, `Hecke.Origin`, `Hecke.LogDerivative`, `Hecke.RayFamily`, `Detector.FixedEuler`, `Detector.GlobalCorrection`, `Detector.MarkedRational`, `PrincipalMellinResidues`, `Hecke.Primitive`, `Hecke.Presentation`, `Hecke.PrincipalStrip`, `Detector.FiniteProductBounds`, `Detector.GaussianSeminorm`, `Detector.GaussianCoupled`, `Hecke.Dyadic`, `GammaZeroDetector`, `Hecke.DetectorWitnessArithmetic`, `GammaDetectorExpansion`, `Hecke.Signal`, `Hecke.SignalIdentity`, `Hecke.CommonProbe`, `Hecke.Conjugation`, `Hecke.DetectorPartition`, `Hecke.DetectorFourierActual`, `Hecke.DetectorTail`, `Hecke.DetectorZeros`, `Hecke.LogarithmicActual`, `Hecke.DyadicMellin`, `Hecke.DyadicContour`, `Hecke.DetectorFinite`, `Hecke.DetectorCommonFrequency`, `Hecke.DetectorDyadicCutoff`, `Hecke.InverseAmplificationScale`, `Hecke.InverseAmplificationProfiles`, `Hecke.PrimeDyadic`, `Hecke.PrimeAnnular`, `Hecke.PrimeDyadicEuler`, `Hecke.RayQuotient`, `Inversion.InitialDyadicAssembly`, `Inversion.InitialDyadicAssemblyBounds`, `Inversion.InitialDyadicAssemblyLive`, `Inversion.InitialDyadicAssemblyRetained`, `Inversion.InitialDyadicAssemblyTail`, `Inversion.InitialRawDictionary`, `Inversion.InitialExcludedEnergy`, `Moments.DivisorRows`, `Moments.DetectorDictionarySlots`, `Moments.DivisorRowEnergy`, `Moments.ReflectionDeletion`, `Moments.NaturalRowSourceMask`, `Moments.ReflectedAnnuli`, `Moments.FirstAnnularMajorant`, `Moments.FrequencyScaleSupremum`, `Moments.LogDyadic`, `Moments.ReflectedSeries`, `Moments.ReflectedTruncation`, `Moments.ZeroMeanBridge`, `Moments.SecondSectorRetained`, `Moments.SecondRetainedRows`, `Moments.SecondActiveDyadic`, `Moments.SecondWindowBudget`, `Moments.SecondDyadicRowSupport`, `Moments.SecondRetainedRatioScalar`, `PrimeRows.Ideal`, `PrimeRows.Product`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission. Comments are removed; no statement of OpenAI's was changed.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B012
import Definitions.Def_OAIHecke78B015

/-!
# OpenAI Hecke 7/8 split: definitions bundle OAIHecke78B016

OpenAI, *The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane
Re s > 7/8*, OpenAI Math Release, September 30, 2026, https://github.com/openai/math (family 003;
Lean in `lean/OAI/NumberTheory/DirichletL`, Apache License 2.0; vendored modules of
PrimeNumberTheoremAnd and rellich-kondrachov). Carved from the port to Lean 4.33.1 / Mathlib
0df444a, comments removed. Modules:
  Eisenstein.InverseCuspCoordinates
  Reciprocity.CubeCorrespondence
  Reciprocity.PrimaryCongruences
  Eisenstein.CubeResidueStrata
  GaussSum.FiniteTranslations
  Descent.FullProfile
  Inversion.SecondProfileUniform
  Descent.FirstProfileUniform
  Hecke.IdealOperations
  Hecke.Euler
  Hecke.FiniteDeletion
  Moments.HeckeTwist
  Moments.HeckeHeight
  Moments.HeckeSlots
  Moments.HeckeExpansion
  Moments.SourceRow
  Moments.HeckeColumnWindow
  Descent.FirstSecondHeightCost
  Detector.HighEulerRational
  Hecke.ModulusRefinement
  Hecke.Origin
  Hecke.LogDerivative
  Hecke.RayFamily
  Detector.FixedEuler
  Detector.GlobalCorrection
  Detector.MarkedRational
  PrincipalMellinResidues
  Hecke.Primitive
  Hecke.Presentation
  Hecke.PrincipalStrip
  Detector.FiniteProductBounds
  Detector.GaussianSeminorm
  Detector.GaussianCoupled
  Hecke.Dyadic
  GammaZeroDetector
  Hecke.DetectorWitnessArithmetic
  GammaDetectorExpansion
  Hecke.Signal
  Hecke.SignalIdentity
  Hecke.CommonProbe
  Hecke.Conjugation
  Hecke.DetectorPartition
  Hecke.DetectorFourierActual
  Hecke.DetectorTail
  Hecke.DetectorZeros
  Hecke.LogarithmicActual
  Hecke.DyadicMellin
  Hecke.DyadicContour
  Hecke.DetectorFinite
  Hecke.DetectorCommonFrequency
  Hecke.DetectorDyadicCutoff
  Hecke.InverseAmplificationScale
  Hecke.InverseAmplificationProfiles
  Hecke.PrimeDyadic
  Hecke.PrimeAnnular
  Hecke.PrimeDyadicEuler
  Hecke.RayQuotient
  Inversion.InitialDyadicAssembly
  Inversion.InitialDyadicAssemblyBounds
  Inversion.InitialDyadicAssemblyLive
  Inversion.InitialDyadicAssemblyRetained
  Inversion.InitialDyadicAssemblyTail
  Inversion.InitialRawDictionary
  Inversion.InitialExcludedEnergy
  Moments.DivisorRows
  Moments.DetectorDictionarySlots
  Moments.DivisorRowEnergy
  Moments.ReflectionDeletion
  Moments.NaturalRowSourceMask
  Moments.ReflectedAnnuli
  Moments.FirstAnnularMajorant
  Moments.FrequencyScaleSupremum
  Moments.LogDyadic
  Moments.ReflectedSeries
  Moments.ReflectedTruncation
  Moments.ZeroMeanBridge
  Moments.SecondSectorRetained
  Moments.SecondRetainedRows
  Moments.SecondActiveDyadic
  Moments.SecondWindowBudget
  Moments.SecondDyadicRowSupport
  Moments.SecondRetainedRatioScalar
  PrimeRows.Ideal
  PrimeRows.Product
-/

section

namespace OAI

noncomputable section

namespace CubicEisenstein

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology ComplexConjugate MatrixGroups Matrix

def inverseCuspCoordinates (c d : ℂ) (v : ℝ) (z : ℂ) : ℂ×ℝ :=
  (-d/c-star z/(c^2*((v^2+‖z‖^2:ℝ):ℂ)),v/(‖c‖^2*(v^2+‖z‖^2)))

lemma inverseCuspCoordinates_height_pos (c d : ℂ) (v : ℝ) (z : ℂ)
    (hc : c≠0) (hv : 0<v) : 0<(inverseCuspCoordinates c d v z).2 := by
  dsimp [inverseCuspCoordinates]
  positivity

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology ComplexConjugate

def horizontalWirtingerZ (f : ℂ→ℂ) (z : ℂ) : ℂ :=
  (1/2:ℂ)*(deriv (fun t : ℝ=>f (z+(t:ℂ))) 0-
    Complex.I*deriv (fun t : ℝ=>f (z+(t:ℂ)*Complex.I)) 0)

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology

open Filter MeasureTheory
open scoped BigOperators Classical Topology
open Finset AddChar MulChar EisensteinEmbedding

local notation "O" => ActualEisensteinCubic.O

def horizontalPhaseCLM (freq : ℂ) : ℂ →L[ℝ] ℂ :=
  (2*Real.pi*Complex.I:ℂ) •
    (freq • ContinuousLinearMap.id ℝ ℂ +
      (Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (freq • ContinuousLinearMap.id ℝ ℂ))

namespace SubexponentialBesselCoefficients
variable (coeff : SubexponentialBesselCoefficients)

def amplitudeDeriv (v : ℝ) (h : ActualEisensteinCubic.O) : ℂ :=
  if h=0 then 0 else coeff.value h*
    (schlafliBesselK (1/3) (4*Real.pi*‖cuspFrequency h‖*v)+
      (v:ℂ)*(4*Real.pi*‖cuspFrequency h‖:ℝ)*
        schlafliBesselK_cubic_derivative (4*Real.pi*‖cuspFrequency h‖*v))

def termFDeriv (h : ActualEisensteinCubic.O) (p : ℝ × ℂ) : (ℝ × ℂ) →L[ℝ] ℂ :=
  if h=0 then 0 else
    (ContinuousLinearMap.fst ℝ ℝ ℂ).smulRight
      (coeff.amplitudeDeriv p.1 h*ShortDraftTrace.breveE (cuspFrequency h*p.2))+
    coeff.term h p • (horizontalPhaseCLM (cuspFrequency h)).comp
      (ContinuousLinearMap.snd ℝ ℝ ℂ)

end SubexponentialBesselCoefficients
end

open Filter MeasureTheory Asymptotics
open scoped BigOperators Classical Topology

def truncatedCuspProfile (c : ℝ) (f : ℝ→ℂ) (x : ℝ) : ℂ :=
  if c<x then f x else 0

end CubicEisenstein

end

end OAI
end

section

namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

namespace CubicKubota

open scoped Classical MatrixGroups

section
open ActualEisensteinCubic CubicJacobiGlobal CubicRamified
local notation "Eis" => ActualEisensteinCubic.O

def cubeDiagonal (p : Eis) : Matrix (Fin 2) (Fin 2) Eis := !![p^3,0;0,1]

def cubeCorrespondence (p : Eis) : Subgroup (levelThree × levelThree) where
  carrier := {MN | cubeDiagonal p * (MN.1 : SL(2,Eis)).val =
    (MN.2 : SL(2,Eis)).val * cubeDiagonal p}
  one_mem' := by simp
  mul_mem' := by
    rintro ⟨M,N⟩ ⟨M',N'⟩ h h'
    change cubeDiagonal p * ((M : SL(2,Eis)).val * (M' : SL(2,Eis)).val) =
      ((N : SL(2,Eis)).val * (N' : SL(2,Eis)).val) * cubeDiagonal p
    calc
      _ = (cubeDiagonal p * (M : SL(2,Eis)).val) * (M' : SL(2,Eis)).val :=
        (Matrix.mul_assoc _ _ _).symm
      _ = ((N : SL(2,Eis)).val * cubeDiagonal p) * (M' : SL(2,Eis)).val := by rw [h]
      _ = (N : SL(2,Eis)).val * (cubeDiagonal p * (M' : SL(2,Eis)).val) := Matrix.mul_assoc _ _ _
      _ = (N : SL(2,Eis)).val * ((N' : SL(2,Eis)).val * cubeDiagonal p) := by rw [h']
      _ = _ := (Matrix.mul_assoc _ _ _).symm
  inv_mem' := by
    rintro ⟨M,N⟩ h
    change cubeDiagonal p * ((M : SL(2,Eis))⁻¹).val =
      ((N : SL(2,Eis))⁻¹).val * cubeDiagonal p
    calc
      _ = (((N : SL(2,Eis))⁻¹).val * ((N : SL(2,Eis)).val * cubeDiagonal p)) *
          ((M : SL(2,Eis))⁻¹).val := by
        simp only [← Matrix.mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul,
          inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul]
      _ = (((N : SL(2,Eis))⁻¹).val * (cubeDiagonal p * (M : SL(2,Eis)).val)) *
          ((M : SL(2,Eis))⁻¹).val := by rw [h]
      _ = _ := by
        simp only [Matrix.mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul,
          mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one, Matrix.mul_one]

def cubeCorrespondenceLeft (p : Eis) : cubeCorrespondence p →* levelThree :=
  (MonoidHom.fst levelThree levelThree).comp (cubeCorrespondence p).subtype

def cubeCorrespondenceRight (p : Eis) : cubeCorrespondence p →* levelThree :=
  (MonoidHom.snd levelThree levelThree).comp (cubeCorrespondence p).subtype

lemma cubeCorrespondence_entries (p : Eis) (MN : cubeCorrespondence p) :
    p^3 * ((MN.1.1 : levelThree) : SL(2,Eis)) 0 0 =
      (((MN.1.2 : levelThree) : SL(2,Eis)) 0 0) * p^3 ∧
    p^3 * ((MN.1.1 : levelThree) : SL(2,Eis)) 0 1 =
      (((MN.1.2 : levelThree) : SL(2,Eis)) 0 1) ∧
    (((MN.1.1 : levelThree) : SL(2,Eis)) 1 0) =
      (((MN.1.2 : levelThree) : SL(2,Eis)) 1 0) * p^3 ∧
    (((MN.1.1 : levelThree) : SL(2,Eis)) 1 1) =
      (((MN.1.2 : levelThree) : SL(2,Eis)) 1 1) := by
  have h := MN.property
  have h00 := congrArg (fun A : Matrix (Fin 2) (Fin 2) Eis => A 0 0) h
  have h01 := congrArg (fun A : Matrix (Fin 2) (Fin 2) Eis => A 0 1) h
  have h10 := congrArg (fun A : Matrix (Fin 2) (Fin 2) Eis => A 1 0) h
  have h11 := congrArg (fun A : Matrix (Fin 2) (Fin 2) Eis => A 1 1) h
  norm_num [cubeDiagonal, Matrix.mul_apply, Fin.sum_univ_two] at h00 h01 h10 h11
  exact ⟨h00,h01,h10,h11⟩

lemma cubeCorrespondenceLeft_injective (p : Eis) (hp : p ≠ 0) :
    Function.Injective (cubeCorrespondenceLeft p) := by
  intro x y h
  have hx := cubeCorrespondence_entries p x
  have hy := cubeCorrespondence_entries p y
  have hM : x.1.1=y.1.1 := h
  apply Subtype.ext
  apply Prod.ext hM
  apply Subtype.ext
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j
  · exact mul_right_cancel₀ (pow_ne_zero 3 hp) (hx.1.symm.trans (by rw [hM]; exact hy.1))
  · exact hx.2.1.symm.trans (by rw [hM]; exact hy.2.1)
  · exact mul_right_cancel₀ (pow_ne_zero 3 hp) (hx.2.2.1.symm.trans (by rw [hM]; exact hy.2.2.1))
  · exact hx.2.2.2.symm.trans (by rw [hM]; exact hy.2.2.2)

lemma cubeCorrespondenceRight_injective (p : Eis) (hp : p ≠ 0) :
    Function.Injective (cubeCorrespondenceRight p) := by
  intro x y h
  have hx := cubeCorrespondence_entries p x
  have hy := cubeCorrespondence_entries p y
  have hN : x.1.2=y.1.2 := h
  apply Subtype.ext
  refine Prod.ext ?_ hN
  apply Subtype.ext
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j
  · exact mul_left_cancel₀ (pow_ne_zero 3 hp) (hx.1.trans (by rw [hN]; exact hy.1.symm))
  · exact mul_left_cancel₀ (pow_ne_zero 3 hp) (hx.2.1.trans (by rw [hN]; exact hy.2.1.symm))
  · exact hx.2.2.1.trans (by rw [hN]; exact hy.2.2.1.symm)
  · exact hx.2.2.2.trans (by rw [hN]; exact hy.2.2.2.symm)

lemma cubeCorrespondence_value (p : Eis) (hp : p ≠ 0) (MN : cubeCorrespondence p) :
    value (cubeCorrespondenceLeft p MN) = value (cubeCorrespondenceRight p MN) := by
  have he := cubeCorrespondence_entries p MN
  let M : levelThree := MN.1.1
  let N : levelThree := MN.1.2
  have ha : (M : SL(2,Eis)) 0 0 = (N : SL(2,Eis)) 0 0 :=
    mul_left_cancel₀ (pow_ne_zero 3 hp) (he.1.trans (mul_comm _ _))
  have hc : (M : SL(2,Eis)) 1 0 = p^3 * (N : SL(2,Eis)) 1 0 :=
    he.2.2.1.trans (mul_comm _ _)
  have hd : (M : SL(2,Eis)) 0 0 * (M : SL(2,Eis)) 1 1 -
      (M : SL(2,Eis)) 0 1 * (M : SL(2,Eis)) 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using (M : SL(2,Eis)).property
  have hcop : IsCoprime p ((N : SL(2,Eis)) 0 0) := by
    refine ⟨-(M : SL(2,Eis)) 0 1 * p^2 * (N : SL(2,Eis)) 1 0,
      (M : SL(2,Eis)) 1 1,?_⟩
    rw [ha,hc] at hd
    linear_combination hd
  change symbol ((M : SL(2,Eis)) 1 0) ((M : SL(2,Eis)) 0 0) =
    symbol ((N : SL(2,Eis)) 1 0) ((N : SL(2,Eis)) 0 0)
  rw [ha,hc,symbol_mul_numerator _ _ _ (levelThree_primary N),
    symbol_pow_numerator _ _ (levelThree_primary N),
    symbol_cube_of_isCoprime _ _ (levelThree_primary N) hcop,one_mul]

lemma cubeCorrespondence_character (p : Eis) (hp : p ≠ 0) (MN : cubeCorrespondence p) :
    complexCharacter (cubeCorrespondenceLeft p MN) =
      complexCharacter (cubeCorrespondenceRight p MN) := by
  exact congrArg ConcreteTraceCRT.eisEmbedding (cubeCorrespondence_value p hp MN)

end

section
open ActualEisensteinCubic ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

def cubePrincipalLevel (p : Eis) : Subgroup levelThree :=
  ((Matrix.SpecialLinearGroup.map (n:=Fin 2)
    (Ideal.Quotient.mk (Ideal.span {(3:Eis)*p^3}))).comp levelThree.subtype).ker

lemma cubePrincipalLevel_entry (p : Eis) (M : cubePrincipalLevel p) (i j : Fin 2) :
    (3:Eis)*p^3 ∣ ((M.1 : levelThree) : SL(2,Eis)) i j-(if i=j then 1 else 0) := by
  have hm : Matrix.SpecialLinearGroup.map (n:=Fin 2)
      (Ideal.Quotient.mk (Ideal.span {(3:Eis)*p^3})) ((M.1 : levelThree) : SL(2,Eis)) = 1 := M.property
  have h := congrArg (fun N : SL(2,Eis ⧸ Ideal.span {(3:Eis)*p^3}) => N i j) hm
  change Ideal.Quotient.mk (Ideal.span {(3:Eis)*p^3})
    (((M.1 : levelThree) : SL(2,Eis)) i j) =
      (1 : Matrix (Fin 2) (Fin 2) (Eis ⧸ Ideal.span {(3:Eis)*p^3})) i j at h
  apply Ideal.mem_span_singleton.mp
  apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp
  simpa only [Matrix.one_apply, apply_ite, map_one, map_zero] using h

lemma cubePrincipalLevel_finiteIndex (p : Eis) (hp : p ≠ 0) :
    (cubePrincipalLevel p).FiniteIndex := by
  let : Finite (Eis ⧸ Ideal.span {(3:Eis)*p^3}) :=
    finite_quotient_span (mul_ne_zero (by norm_num) (pow_ne_zero 3 hp))
  unfold cubePrincipalLevel
  infer_instance

lemma cubePrincipalLevel_left_mate (p : Eis) (M : cubePrincipalLevel p) :
    ∃ N : levelThree, ((M.1 : levelThree),N) ∈ cubeCorrespondence p := by
  obtain ⟨c,hc⟩ : (3:Eis)*p^3 ∣ ((M.1 : levelThree) : SL(2,Eis)) 1 0 := by
    simpa using cubePrincipalLevel_entry p M 1 0
  let A : SL(2,Eis) := M.1
  let N : SL(2,Eis) := ⟨!![A 0 0,p^3*A 0 1;3*c,A 1 1],by
    have hd := A.property
    rw [Matrix.det_fin_two] at hd
    rw [Matrix.det_fin_two_of]
    change A 1 0=(3:Eis)*p^3*c at hc
    rw [hc] at hd
    linear_combination hd⟩
  have hN : N∈levelThree := by
    apply (mem_levelThree_iff_entries N).mpr
    intro i j
    fin_cases i <;> fin_cases j
    · exact levelThree_entry M.1 0 0
    · change (3:Eis)∣p^3*A 0 1-0
      simpa using dvd_mul_of_dvd_right (levelThree_upper M.1) (p^3)
    · change (3:Eis)∣3*c-0
      simp
    · exact levelThree_entry M.1 1 1
  refine ⟨⟨N,hN⟩,?_⟩
  change cubeDiagonal p*A.val=N.val*cubeDiagonal p
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [cubeDiagonal,N,Matrix.mul_apply,Fin.sum_univ_two]
  · ring
  · change A 1 0=(3:Eis)*p^3*c at hc
    change A 1 0=3*c*p^3
    rw [hc]
    ring

lemma cubePrincipalLevel_right_mate (p : Eis) (N : cubePrincipalLevel p) :
    ∃ M : levelThree, (M,(N.1 : levelThree)) ∈ cubeCorrespondence p := by
  obtain ⟨b,hb⟩ : (3:Eis)*p^3 ∣ ((N.1 : levelThree) : SL(2,Eis)) 0 1 := by
    simpa using cubePrincipalLevel_entry p N 0 1
  let A : SL(2,Eis) := N.1
  let M : SL(2,Eis) := ⟨!![A 0 0,3*b;p^3*A 1 0,A 1 1],by
    have hd := A.property
    rw [Matrix.det_fin_two] at hd
    rw [Matrix.det_fin_two_of]
    change A 0 1=(3:Eis)*p^3*b at hb
    rw [hb] at hd
    linear_combination hd⟩
  have hM : M∈levelThree := by
    apply (mem_levelThree_iff_entries M).mpr
    intro i j
    fin_cases i <;> fin_cases j
    · exact levelThree_entry N.1 0 0
    · change (3:Eis)∣3*b-0
      simp
    · change (3:Eis)∣p^3*A 1 0-0
      simpa using dvd_mul_of_dvd_right (levelThree_lower N.1) (p^3)
    · exact levelThree_entry N.1 1 1
  refine ⟨⟨M,hM⟩,?_⟩
  change cubeDiagonal p*M.val=A.val*cubeDiagonal p
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [cubeDiagonal,M,Matrix.mul_apply,Fin.sum_univ_two]
  · ring
  · change A 0 1=(3:Eis)*p^3*b at hb
    change p^3*(3*b)=A 0 1
    rw [hb]
    ring
  · ring

lemma cubePrincipalLevel_le_left_range (p : Eis) :
    cubePrincipalLevel p ≤ (cubeCorrespondenceLeft p).range := by
  intro M hM
  obtain ⟨N,hN⟩ := cubePrincipalLevel_left_mate p ⟨M,hM⟩
  exact ⟨⟨(M,N),hN⟩,rfl⟩

lemma cubePrincipalLevel_le_right_range (p : Eis) :
    cubePrincipalLevel p ≤ (cubeCorrespondenceRight p).range := by
  intro N hN
  obtain ⟨M,hM⟩ := cubePrincipalLevel_right_mate p ⟨N,hN⟩
  exact ⟨⟨(M,N),hM⟩,rfl⟩

lemma cubeCorrespondence_finite_covers (p : Eis) (hp : p ≠ 0) :
    Function.Injective (cubeCorrespondenceLeft p) ∧
    Function.Injective (cubeCorrespondenceRight p) ∧
    (cubeCorrespondenceLeft p).range.FiniteIndex ∧
    (cubeCorrespondenceRight p).range.FiniteIndex := by
  let : (cubePrincipalLevel p).FiniteIndex := cubePrincipalLevel_finiteIndex p hp
  exact ⟨cubeCorrespondenceLeft_injective p hp,cubeCorrespondenceRight_injective p hp,
    Subgroup.finiteIndex_of_le (cubePrincipalLevel_le_left_range p),
    Subgroup.finiteIndex_of_le (cubePrincipalLevel_le_right_range p)⟩

end

section
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein
local notation "Eis" => ActualEisensteinCubic.O

def cubeKernelCorrespondence (p : Eis) : Subgroup (cubeCorrespondence p) :=
  (finiteCubicMultiplier.comp (cubeCorrespondenceLeft p)).ker

def cubeKernelLeft (p : Eis) : cubeKernelCorrespondence p →* finiteCubicMultiplier.ker where
  toFun x := ⟨cubeCorrespondenceLeft p x.1,x.property⟩
  map_one' := by apply Subtype.ext; exact map_one (cubeCorrespondenceLeft p)
  map_mul' x y := by apply Subtype.ext; exact map_mul (cubeCorrespondenceLeft p) x.1 y.1

lemma cubeKernel_right_mem (p : Eis) (hp : p ≠ 0) (x : cubeKernelCorrespondence p) :
    cubeCorrespondenceRight p x.1 ∈ finiteCubicMultiplier.ker := by
  apply (finiteCubicMultiplier_eq_one _).mpr
  rw [←cubeCorrespondence_character p hp x.1]
  exact (finiteCubicMultiplier_eq_one _).mp x.property

def cubeKernelRight (p : Eis) (hp : p ≠ 0) :
    cubeKernelCorrespondence p →* finiteCubicMultiplier.ker where
  toFun x := ⟨cubeCorrespondenceRight p x.1,cubeKernel_right_mem p hp x⟩
  map_one' := by apply Subtype.ext; exact map_one (cubeCorrespondenceRight p)
  map_mul' x y := by apply Subtype.ext; exact map_mul (cubeCorrespondenceRight p) x.1 y.1

lemma cubeKernelLeft_range (p : Eis) :
    (cubeKernelLeft p).range =
      (cubeCorrespondenceLeft p).range.comap finiteCubicMultiplier.ker.subtype := by
  ext y
  constructor
  · rintro ⟨x,rfl⟩
    exact ⟨x.1,rfl⟩
  · rintro ⟨x,hx⟩
    have hmem : x∈cubeKernelCorrespondence p := by
      change finiteCubicMultiplier (cubeCorrespondenceLeft p x)=1
      rw [hx]
      exact y.property
    exact ⟨⟨x,hmem⟩,Subtype.ext hx⟩

lemma cubeKernelRight_range (p : Eis) (hp : p ≠ 0) :
    (cubeKernelRight p hp).range =
      (cubeCorrespondenceRight p).range.comap finiteCubicMultiplier.ker.subtype := by
  ext y
  constructor
  · rintro ⟨x,rfl⟩
    exact ⟨x.1,rfl⟩
  · rintro ⟨x,hx⟩
    have hmem : x∈cubeKernelCorrespondence p := by
      apply (finiteCubicMultiplier_eq_one _).mpr
      rw [cubeCorrespondence_character p hp x,hx]
      exact (finiteCubicMultiplier_eq_one _).mp y.property
    exact ⟨⟨x,hmem⟩,Subtype.ext hx⟩

lemma cubeKernel_finite_covers (p : Eis) (hp : p ≠ 0) :
    Function.Injective (cubeKernelLeft p) ∧ Function.Injective (cubeKernelRight p hp) ∧
    (cubeKernelLeft p).range.FiniteIndex ∧ (cubeKernelRight p hp).range.FiniteIndex := by
  have hcov := cubeCorrespondence_finite_covers p hp
  let := hcov.2.2.1
  let := hcov.2.2.2
  refine ⟨?_,?_,?_,?_⟩
  · intro x y h
    apply Subtype.ext
    apply hcov.1
    exact congrArg Subtype.val h
  · intro x y h
    apply Subtype.ext
    apply hcov.2.1
    exact congrArg Subtype.val h
  · rw [cubeKernelLeft_range]
    infer_instance
  · rw [cubeKernelRight_range]
    infer_instance

def cubeKernelLeftGlobal (p : Eis) : cubeKernelCorrespondence p →* SL(2,Eis) :=
  levelThree.subtype.comp (finiteCubicMultiplier.ker.subtype.comp (cubeKernelLeft p))

def cubeKernelRightGlobal (p : Eis) (hp : p ≠ 0) :
    cubeKernelCorrespondence p →* SL(2,Eis) :=
  levelThree.subtype.comp (finiteCubicMultiplier.ker.subtype.comp (cubeKernelRight p hp))

lemma cubeKernelLeftGlobal_le (p : Eis) :
    (cubeKernelLeftGlobal p).range ≤ globalKubotaKernel := by
  rintro M ⟨x,rfl⟩
  exact ⟨(cubeKernelLeft p x).1,(cubeKernelLeft p x).property,rfl⟩

lemma finiteIndex_subtype_image {G : Type*} [Group G] (H : Subgroup G)
    [H.FiniteIndex] (J : Subgroup H) [J.FiniteIndex] : (J.map H.subtype).FiniteIndex := by
  constructor
  rw [Subgroup.index_map_subtype]
  exact mul_ne_zero (Subgroup.FiniteIndex.index_ne_zero (H:=J))
    (Subgroup.FiniteIndex.index_ne_zero (H:=H))

lemma cubeKernelGlobal_finite_covers (p : Eis) (hp : p ≠ 0) :
    (cubeKernelLeftGlobal p).range.FiniteIndex ∧
    (cubeKernelRightGlobal p hp).range.FiniteIndex := by
  have hcov := cubeKernel_finite_covers p hp
  let := hcov.2.2.1
  let := hcov.2.2.2
  let : levelThree.FiniteIndex := levelThree_finiteIndex
  have hL : ((cubeKernelLeft p).range.map finiteCubicMultiplier.ker.subtype).FiniteIndex :=
    finiteIndex_subtype_image _ _
  have hR : ((cubeKernelRight p hp).range.map finiteCubicMultiplier.ker.subtype).FiniteIndex :=
    finiteIndex_subtype_image _ _
  constructor
  · rw [cubeKernelLeftGlobal,MonoidHom.range_comp,MonoidHom.range_comp]
    exact finiteIndex_subtype_image _ _
  · rw [cubeKernelRightGlobal,MonoidHom.range_comp,MonoidHom.range_comp]
    exact finiteIndex_subtype_image _ _

end

open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein
local notation "Eis" => ActualEisensteinCubic.O

end CubicKubota

open Filter MeasureTheory Asymptotics
open scoped BigOperators Classical Topology
open Finset AddChar MulChar EisensteinEmbedding

namespace CubicEisenstein
local notation "O" => ActualEisensteinCubic.O

def cuspBarProfile (f : HyperbolicSpace→ℂ) (z : ℂ) (v : ℝ) : ℂ :=
  horizontalWirtingerBar (fun w=>f (cuspCoordinateLift (v,w))) z

def cuspZProfile (f : HyperbolicSpace→ℂ) (z : ℂ) (v : ℝ) : ℂ :=
  horizontalWirtingerZ (fun w=>f (cuspCoordinateLift (v,w))) z

namespace SubexponentialBesselCoefficients
variable (coeff : SubexponentialBesselCoefficients)

def directionalSeries (direction : ℂ) (p : ℝ × ℂ) : ℂ :=
  ∑'h : ActualEisensteinCubic.O,coeff.directionalTerm h p.1 p.2 direction

end SubexponentialBesselCoefficients

end CubicEisenstein

end

end OAI
end

section

namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

section

open scoped Classical MatrixGroups
namespace CubicJacobiGlobal
open ActualEisensteinCubic CubicRamified
local notation "Eis" => ActualEisensteinCubic.O

lemma integer_congruence_primary_cases (c : Eis) (r : ℤ) (h : (3:Eis)∣c-(r:Eis)) :
    (3:Eis)∣c ∨ lambda^2∣c-1 ∨ lambda^2∣(-c)-1 := by
  have hr : (3:ℤ)∣r ∨ (3:ℤ)∣r-1 ∨ (3:ℤ)∣r+1 := by omega
  rcases hr with hr|hr|hr
  · left
    obtain ⟨t,ht⟩:=hr
    have hn:(3:Eis)∣(r:Eis):=⟨(t:Eis),by exact_mod_cast ht⟩
    simpa using dvd_add h hn
  · right;left
    obtain ⟨t,ht⟩:=hr
    have hn:(3:Eis)∣(r:Eis)-1:=⟨(t:Eis),by exact_mod_cast ht⟩
    exact lambda_sq_dvd_three.trans (by simpa using dvd_add h hn)
  · right;right
    obtain ⟨t,ht⟩:=hr
    have hn:(3:Eis)∣(r:Eis)+1:=⟨(t:Eis),by exact_mod_cast ht⟩
    apply lambda_sq_dvd_three.trans
    convert (preTransparency := .instances) dvd_neg.mpr (dvd_add h hn) using 1 ; ring

lemma symbol_three_shift_primary (c a t:Eis) (hc:lambda^2∣c-1) (ha:lambda^2∣a-1) :
    symbol c (a+3*t*c)=symbol c a := by
  have hs:=primary_add_multiple_three a c t ha
  calc
    _=symbol (a+3*t*c) c:=symbol_reciprocity _ _ (primary_ne_zero _ hc) (primary_ne_zero _ hs) hc hs
    _=symbol a c:=symbol_congr ⟨3*t,by ring⟩
    _=symbol c a:=(symbol_reciprocity _ _ (primary_ne_zero _ hc) (primary_ne_zero _ ha) hc ha).symm

lemma symbol_three_shift_integer (c a t:Eis) (r:ℤ)
    (ha:lambda^2∣a-1) (hc:(3:Eis)∣c-(r:Eis)) :
    symbol c (a+3*t*c)=symbol c a := by
  rcases integer_congruence_primary_cases c r hc with h|h|h
  · exact symbol_three_shift c a t ha h
  · exact symbol_three_shift_primary c a t h ha
  · have hh:=symbol_three_shift_primary (-c) a (-t) h ha
    have he:a+3*(-t)*(-c)=a+3*t*c:=by ring
    rw [he,symbol_neg_numerator _ _ (primary_add_multiple_three a c t ha),
      symbol_neg_numerator _ _ ha] at hh
    exact hh

end CubicJacobiGlobal
namespace CubicKubota
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein CubicJacobiGlobal CubicRamified
local notation "Eis" => ActualEisensteinCubic.O

lemma levelTwo_cube_phase_balance (A N:levelTwo) (p q:Eis) (j:ℕ)
    (hp:lambda^2∣p-1)
    (hA:lambda^2∣((A:SL(2,Eis)) 0 0)-1)
    (hN:lambda^2∣((N:SL(2,Eis)) 0 0)-1)
    (hx:(A:SL(2,Eis)) 0 0+3*q*(A:SL(2,Eis)) 1 0=p^j*(N:SL(2,Eis)) 0 0)
    (hc:(N:SL(2,Eis)) 1 0=p^(3-j)*(A:SL(2,Eis)) 1 0) :
    levelTwoComplexCharacter N *
        eisEmbedding (symbol ((A:SL(2,Eis)) 1 0) p)^j =
      levelTwoComplexCharacter A *
        eisEmbedding (symbol ((N:SL(2,Eis)) 0 0) p)^(3-j) := by
  have hs : symbol ((A:SL(2,Eis)) 1 0) ((A:SL(2,Eis)) 0 0) =
      symbol ((A:SL(2,Eis)) 1 0) p ^ j *
        symbol ((A:SL(2,Eis)) 1 0) ((N:SL(2,Eis)) 0 0) := by
    rw [←symbol_three_shift_integer _ _ q (levelTwoRight A 1 0) hA (levelTwo_entry_integer A 1 0),
      hx,symbol_mul_denominator,cubicSymbol_pow_denominator]
  rw [levelTwoComplexCharacter_primary N hN,levelTwoComplexCharacter_primary A hA,hc,
    symbol_mul_numerator _ _ _ hN,symbol_pow_numerator _ _ hN,
    symbol_reciprocity p ((N:SL(2,Eis)) 0 0) (primary_ne_zero _ hp) (primary_ne_zero _ hN) hp hN,
    hs,map_mul,map_pow,map_mul,map_pow]
  ring

lemma levelTwo_comparison_character (A N:levelTwo)
    (hNA:(N:SL(2,Eis))*(A:SL(2,Eis))⁻¹∈levelThree) :
    complexCharacter ⟨(N:SL(2,Eis))*(A:SL(2,Eis))⁻¹,hNA⟩ *
        levelTwoComplexCharacter A = levelTwoComplexCharacter N := by
  rw [←levelTwoComplexCharacter_restrict ⟨(N:SL(2,Eis))*(A:SL(2,Eis))⁻¹,hNA⟩]
  change levelTwoComplexCharacter (N*A⁻¹)*levelTwoComplexCharacter A=levelTwoComplexCharacter N
  rw [map_mul,map_inv,mul_assoc]
  have hA:levelTwoComplexCharacter A≠0:=by
    intro he
    have hh:=levelTwoComplexCharacter_cube A
    rw [he] at hh
    norm_num at hh
  rw [inv_mul_cancel₀ hA,mul_one]

lemma levelTwo_cube_comparison_phase (A N:levelTwo) (p q:Eis) (j:ℕ) (hj:j≤3)
    (hp:lambda^2∣p-1)
    (hA:lambda^2∣((A:SL(2,Eis)) 0 0)-1)
    (hN:lambda^2∣((N:SL(2,Eis)) 0 0)-1)
    (hx:(A:SL(2,Eis)) 0 0+3*q*(A:SL(2,Eis)) 1 0=p^j*(N:SL(2,Eis)) 0 0)
    (hc:(N:SL(2,Eis)) 1 0=p^(3-j)*(A:SL(2,Eis)) 1 0)
    (hC:IsCoprime ((A:SL(2,Eis)) 1 0) p)
    (hNA:(N:SL(2,Eis))*(A:SL(2,Eis))⁻¹∈levelThree) :
    complexCharacter ⟨(N:SL(2,Eis))*(A:SL(2,Eis))⁻¹,hNA⟩ =
      eisEmbedding (symbol (((N:SL(2,Eis)) 0 0)*((A:SL(2,Eis)) 1 0)) p)^(3-j) := by
  let a:=eisEmbedding (symbol ((A:SL(2,Eis)) 1 0) p)
  let b:=eisEmbedding (symbol ((N:SL(2,Eis)) 0 0) p)
  have ha3:a^3=1:=by
    dsimp [a]
    rw [←map_pow,symbol_cube_of_isCoprime _ _ hp hC,map_one]
  have hpow:a^j*a^(3-j)=1:=by rw [←pow_add,Nat.add_sub_of_le hj,ha3]
  have hbal:=levelTwo_cube_phase_balance A N p q j hp hA hN hx hc
  change levelTwoComplexCharacter N*a^j=levelTwoComplexCharacter A*b^(3-j) at hbal
  have he:levelTwoComplexCharacter N=levelTwoComplexCharacter A*(b*a)^(3-j):=by
    calc
      _=levelTwoComplexCharacter N*(a^j*a^(3-j)):=by rw [hpow,mul_one]
      _=(levelTwoComplexCharacter N*a^j)*a^(3-j):=(mul_assoc _ _ _).symm
      _=(levelTwoComplexCharacter A*b^(3-j))*a^(3-j):=by rw [hbal]
      _=_:=by rw [mul_pow];ring
  have hcomp:=levelTwo_comparison_character A N hNA
  have hbase:levelTwoComplexCharacter A≠0:=by
    intro he
    have hh:=levelTwoComplexCharacter_cube A
    rw [he] at hh
    norm_num at hh
  rw [symbol_mul_numerator _ _ _ hp,map_mul]
  change complexCharacter ⟨(N:SL(2,Eis))*(A:SL(2,Eis))⁻¹,hNA⟩=(b*a)^(3-j)
  apply mul_right_cancel₀ hbase
  rw [hcomp,he]
  ring

end CubicKubota
end

open scoped BigOperators Classical

namespace CubicEisenstein

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicRamified
local notation "Eis" => ActualEisensteinCubic.O

lemma ramified_cubicExp_nat_mul (n : ℕ) (t : ℤ) :
    cubicExp ((n:ℤ)*t)=cubicExp t^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_add,Nat.cast_one,add_mul,one_mul,cubicExp_add,ih,pow_succ]

lemma ramified_trace_symbol (a : Eis) (ha : lambda^2∣a-1) :
    symbol ramifiedTraceLambda a=linearRay 0 (-1) a := by
  have h := symbol_traceLambda_eq_linearRay a ha
  change symbol ramifiedTraceLambda a=linearRay 0 (-1) a at h
  exact h

lemma ramifiedSymbol_primaryCoord (j n : ℕ) (A B : ℤ) :
    symbol (omega^j*ramifiedTraceLambda^n) (primaryCoord A B)=
      cubicExp ((j:ℤ)*(2*A-B)-(n:ℤ)*B) := by
  rw [symbol_mul_numerator _ _ _ (primaryCoord_primary _ _),
    symbol_pow_numerator _ _ (primaryCoord_primary _ _) j,
    symbol_pow_numerator _ _ (primaryCoord_primary _ _) n,
    symbol_omega_eq_linearRay _ (primaryCoord_primary _ _),
    ramified_trace_symbol _ (primaryCoord_primary _ _),linearRay_primaryCoord,linearRay_primaryCoord,
    ←ramified_cubicExp_nat_mul,←ramified_cubicExp_nat_mul,←cubicExp_add]
  congr 1
  ring

def ramifiedAffineParameter (j n : ℕ) : Eis := (j:Eis)*ramifiedTraceLambda-(n:Eis)

lemma ramifiedAffineParameter_coords (j n : ℕ) (C D : ℤ) :
    (ActualEisensteinCoordinates.coords
      (ramifiedAffineParameter j n*ActualEisensteinCoordinates.eval C D)).2=
      (j:ℤ)*(2*C-D)-(n:ℤ)*D := by
  have hk : ramifiedAffineParameter j n=ActualEisensteinCoordinates.eval ((j:ℤ)-(n:ℤ)) (2*(j:ℤ)) := by
    change (j:Eis)*(1+2*omega)-(n:Eis)=(((j:ℤ)-(n:ℤ):ℤ):Eis)+((2*(j:ℤ):ℤ):Eis)*omega
    push_cast
    ring
  rw [hk,ActualEisensteinCoordinates.eval_mul,ShortDraftLatticeCount.coords_eval]
  ring

theorem ramified_symbol_primary_shift (j n : ℕ) (a x : Eis) (ha : lambda^2∣a-1) :
    eisEmbedding (symbol (omega^j*ramifiedTraceLambda^n) (a+3*x))=
      eisEmbedding (symbol (omega^j*ramifiedTraceLambda^n) a)*
        ShortDraftTrace.breveE (eisEmbedding (ramifiedAffineParameter j n*x)/eisLam/3) := by
  obtain ⟨A,B,rfl⟩ := exists_primaryCoord a ha
  let C := (ActualEisensteinCoordinates.coords x).1
  let D := (ActualEisensteinCoordinates.coords x).2
  have hx : x=ActualEisensteinCoordinates.eval C D := (ActualEisensteinCoordinates.eval_coords x).symm
  have hsum : primaryCoord A B+3*x=primaryCoord (A+C) (B+D) := by
    rw [hx,primaryCoord_eq,primaryCoord_eq]
    change 1+3*(A:Eis)+3*(B:Eis)*omega+3*((C:Eis)+(D:Eis)*omega)=_
    push_cast
    ring
  rw [hsum,ramifiedSymbol_primaryCoord,ramifiedSymbol_primaryCoord]
  have ht := breveE_real_trace_of_O (3:ℝ) (ramifiedAffineParameter j n*x)
  norm_num only [Complex.ofReal_ofNat] at ht
  rw [ht,hx,ramifiedAffineParameter_coords,←embedding_cubicExp,←map_mul,←cubicExp_add]
  apply congrArg eisEmbedding
  apply congrArg cubicExp
  ring

lemma ramified_symbol_primary_shift_signed (j n : ℕ) (r a x : Eis)
    (hr : r=omega^j*ramifiedTraceLambda^n ∨ r=-(omega^j*ramifiedTraceLambda^n))
    (ha : lambda^2∣a-1) :
    eisEmbedding (symbol r (a+3*x))=eisEmbedding (symbol r a)*
      ShortDraftTrace.breveE (eisEmbedding (ramifiedAffineParameter j n*x)/eisLam/3) := by
  rcases hr with rfl|rfl
  · exact ramified_symbol_primary_shift j n a x ha
  · rw [symbol_neg_numerator _ _ (primary_add_three a x ha),symbol_neg_numerator _ _ ha]
    exact ramified_symbol_primary_shift j n a x ha

end
section

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicRamified
local notation "Eis" => ActualEisensteinCubic.O

lemma ramifiedTraceLambda_square : ramifiedTraceLambda^2=(-3:Eis) := by
  unfold ramifiedTraceLambda
  linear_combination 4*ramified_omega_relation

lemma ramified_character_coprime (j n : ℕ) (r a : Eis)
    (hr : r=omega^j*ramifiedTraceLambda^n ∨ r=-(omega^j*ramifiedTraceLambda^n))
    (ha : lambda^2∣a-1) : IsCoprime r a := by
  have hc3 := (primary_coprime_three a ha).symm
  have ht : ramifiedTraceLambda∣(3:Eis) := by
    refine ⟨-ramifiedTraceLambda,?_⟩
    linear_combination ramifiedTraceLambda_square
  have hcT := hc3.of_isCoprime_of_dvd_left ht
  have hcW : IsCoprime omega a := by
    refine ⟨omega^2,0,?_⟩
    rw [zero_mul,add_zero,←pow_succ,omega_primitive.pow_eq_one]
  have hc : IsCoprime (omega^j*ramifiedTraceLambda^n) a := hcW.pow_left.mul_left hcT.pow_left
  rcases hr with rfl|rfl
  · exact hc
  · exact hc.neg_left

lemma affineCusp_phase_identity (h h1 q a k c x : Eis)
    (ha : a≠0) (hq : q≠0) (hh : h=q*h1) (hk : 3*k=h1+c*a) :
    ShortDraftTrace.breveE (eisEmbedding (c*x)/eisLam/3)*
      ShortDraftTrace.breveE (ninthCuspFrequency h*eisEmbedding (a+3*x)/eisEmbedding (q*a))=
      ShortDraftTrace.breveE (ninthCuspFrequency h/eisEmbedding q)*residueAdditive (3*k) a x := by
  have hk' : eisEmbedding k=(eisEmbedding h1+eisEmbedding c*eisEmbedding a)/3 := by
    apply (eq_div_iff (by norm_num : (3:ℂ)≠0)).mpr
    have he := congrArg eisEmbedding hk
    simp only [map_mul,map_add,map_ofNat] at he
    linear_combination he
  rw [←AddChar.map_add_eq_mul]
  unfold residueAdditive
  rw [←AddChar.map_add_eq_mul]
  apply congrArg ShortDraftTrace.breveE
  rw [hh]
  simp only [ninthCuspFrequency,cuspFrequency,map_add,map_mul,map_ofNat]
  rw [hk']
  field_simp [eisEmbedding_ne_zero ha,eisEmbedding_ne_zero hq,eisLam_ne_zero]
  ;ring

def ramifiedAffineGauss (h q r a : Eis) : ℂ :=
  ∑'x:CubicUnitResidue a,
    (eisEmbedding (symbol r (a+3*GaussianShiftedPartition.representative a x.val))*
      eisEmbedding (symbol (a+3*GaussianShiftedPartition.representative a x.val) a))*
      ShortDraftTrace.breveE (ninthCuspFrequency h*
        eisEmbedding (a+3*GaussianShiftedPartition.representative a x.val)/eisEmbedding (q*a))

lemma ramifiedAffineGauss_factor (h h1 q r a k : Eis) (j n : ℕ)
    (ha : a≠0) (hprimary : lambda^2∣a-1) (hq : q≠0)
    (hr : r=omega^j*ramifiedTraceLambda^n ∨ r=-(omega^j*ramifiedTraceLambda^n))
    (hh : h=q*h1) (hk : 3*k=h1+ramifiedAffineParameter j n*a) :
    ramifiedAffineGauss h q r a=
      ShortDraftTrace.breveE (ninthCuspFrequency h/eisEmbedding q)*
        (eisEmbedding (symbol r a)*eisEmbedding (symbol 3 a))*cubicUnitGaussSum k a := by
  rw [ramifiedAffineGauss,cubicUnitGaussSum,←tsum_mul_left]
  apply tsum_congr
  intro x
  let t := GaussianShiftedPartition.representative a x.val
  have hs : symbol (a+3*t) a=symbol (3*t) a := symbol_congr ⟨1,by ring⟩
  change (eisEmbedding (symbol r (a+3*t))*eisEmbedding (symbol (a+3*t) a))*
    ShortDraftTrace.breveE (ninthCuspFrequency h*eisEmbedding (a+3*t)/eisEmbedding (q*a))=_
  rw [ramified_symbol_primary_shift_signed j n r a t hr hprimary,hs,
    symbol_mul_numerator _ _ _ hprimary]
  rw [map_mul eisEmbedding (symbol 3 a) (symbol t a)]
  have hp := affineCusp_phase_identity h h1 q a k (ramifiedAffineParameter j n) t ha hq hh hk
  calc
    _ = (eisEmbedding (symbol r a)*eisEmbedding (symbol 3 a)*eisEmbedding (symbol t a))*
      (ShortDraftTrace.breveE (eisEmbedding (ramifiedAffineParameter j n*t)/eisLam/3)*
        ShortDraftTrace.breveE (ninthCuspFrequency h*eisEmbedding (a+3*t)/eisEmbedding (q*a))) := by ring
    _ = _ := by rw [hp];ring

theorem ramifiedAffineGauss_eq_unramified (h h1 q r a k : Eis) (j n : ℕ)
    (ha : a≠0) (hprimary : lambda^2∣a-1) (hq : q≠0)
    (hr : r=omega^j*ramifiedTraceLambda^n ∨ r=-(omega^j*ramifiedTraceLambda^n))
    (hh : h=q*h1) (hk : 3*k=h1+ramifiedAffineParameter j n*a) :
    ramifiedAffineGauss h q r a=
      ShortDraftTrace.breveE (ninthCuspFrequency h/eisEmbedding q)*
        cubicUnitGaussSum (3*r^2*h1) a := by
  rw [ramifiedAffineGauss_factor h h1 q r a k j n ha hprimary hq hr hh hk]
  have hcop := ramified_character_coprime j n r a hr hprimary
  have hcop3 : IsCoprime (3*r^2) a := (primary_coprime_three a hprimary).symm.mul_left hcop.pow_left
  have hp := cubicUnitGaussSum_phase_shift k (r^2) a ha hprimary hcop3
  have hc := symbol_cube_of_isCoprime r a hprimary hcop
  have hchars : eisEmbedding (symbol (r^2) a)*eisEmbedding (symbol (3*r^2) a)=
      eisEmbedding (symbol r a)*eisEmbedding (symbol 3 a) := by
    rw [←map_mul,←symbol_mul_numerator _ _ a hprimary,
      show r^2*(3*r^2)=3*r^4 by ring,symbol_mul_numerator _ _ a hprimary,
      symbol_pow_numerator _ _ hprimary 4,pow_succ,hc,one_mul,map_mul]
    ring
  rw [hchars] at hp
  have hcong : a∣k*(9*r^2)-3*r^2*h1 := by
    refine ⟨3*r^2*ramifiedAffineParameter j n,?_⟩
    linear_combination 3*r^2*hk
  have hg := cubicUnitGaussSum_frequency_congr (k*(9*r^2)) (3*r^2*h1) a ha hcong
  calc
    _ = ShortDraftTrace.breveE (ninthCuspFrequency h/eisEmbedding q)*
      (eisEmbedding (symbol r a)*eisEmbedding (symbol 3 a)*cubicUnitGaussSum k a) := by ring
    _ = _ := by rw [hp,hg]

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology Pointwise

open ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O

def eisensteinUnitRotation (u : ActualEisensteinCubic.Oˣ) : ℂ≃ₗᵢ[ℝ]ℂ where
  toFun z := eisEmbedding (u:ActualEisensteinCubic.O)*z
  invFun z := eisEmbedding (↑u⁻¹:ActualEisensteinCubic.O)*z
  left_inv z := by
    dsimp only
    rw [←mul_assoc,←map_mul]
    simp
  right_inv z := by
    dsimp only
    rw [←mul_assoc,←map_mul]
    simp
  map_add' z w := mul_add _ _ _
  map_smul' t z := by
    simp only [RingHom.id_apply,Complex.real_smul]
    ring
  norm_map' z := by
    change ‖eisEmbedding (u:ActualEisensteinCubic.O)*z‖=‖z‖
    rw [norm_mul,GaussGeneratorTransport.norm_eisEmbedding_unit,one_mul]

def eisensteinUnitEquiv (u : ActualEisensteinCubic.Oˣ) : ActualEisensteinCubic.O≃ActualEisensteinCubic.O where
  toFun x := (u:ActualEisensteinCubic.O)*x
  invFun x := (↑u⁻¹:ActualEisensteinCubic.O)*x
  left_inv x := by dsimp only; rw [←mul_assoc];simp
  right_inv x := by dsimp only; rw [←mul_assoc];simp

def periodUnitEquiv (u : ActualEisensteinCubic.Oˣ) : periodLattice≃periodLattice :=
  (periodEquiv.symm.trans (eisensteinUnitEquiv u)).trans periodEquiv

lemma periodUnitEquiv_val (u : ActualEisensteinCubic.Oˣ) (x : periodLattice) :
    (periodUnitEquiv u x:ℂ)=eisEmbedding (u:ActualEisensteinCubic.O)*(x:ℂ) := by
  obtain ⟨n,rfl⟩ := periodEquiv.surjective x
  dsimp only [periodUnitEquiv,Equiv.trans_apply]
  rw [Equiv.symm_apply_apply]
  change (periodEquiv ((u:ActualEisensteinCubic.O)*n):ℂ)=eisEmbedding (u:ActualEisensteinCubic.O)*(periodEquiv n:ℂ)
  change 3*eisEmbedding ((u:ActualEisensteinCubic.O)*n)=eisEmbedding (u:ActualEisensteinCubic.O)*(3*eisEmbedding n)
  rw [map_mul]
  ring

lemma periodDomain_unit_rotation (u : ActualEisensteinCubic.Oˣ) :
    IsAddFundamentalDomain periodLattice (eisensteinUnitRotation u '' periodDomain) volume := by
  apply periodDomain_fundamental.image_of_equiv (eisensteinUnitRotation u).toEquiv
    (eisensteinUnitRotation u).symm.measurePreserving.quasiMeasurePreserving (periodUnitEquiv u⁻¹)
  intro n z
  change eisEmbedding (u:ActualEisensteinCubic.O)*((periodUnitEquiv u⁻¹ n:ℂ)+z)=
    (n:ℂ)+eisEmbedding (u:ActualEisensteinCubic.O)*z
  rw [periodUnitEquiv_val,mul_add,←mul_assoc,←map_mul]
  simp

theorem period_integral_unit_rotation (f : ℂ→ℂ)
    (hp : ∀n : ActualEisensteinCubic.O,∀z : ℂ,f (z+3*eisEmbedding n)=f z) (u : ActualEisensteinCubic.Oˣ) :
    (∫z in periodDomain,f (eisEmbedding (u:ActualEisensteinCubic.O)*z))=∫z in periodDomain,f z := by
  have hperiod (n : periodLattice) (z : ℂ) : f (n+ᵥz)=f z := by
    obtain ⟨m,rfl⟩ := periodEquiv.surjective n
    change f (3*eisEmbedding m+z)=f z
    simpa only [add_comm] using hp m z
  have heq := periodDomain_fundamental.setIntegral_eq (periodDomain_unit_rotation u) hperiod
  have hchange := (eisensteinUnitRotation u).measurePreserving.setIntegral_image_emb
    (eisensteinUnitRotation u).toHomeomorph.measurableEmbedding f periodDomain
  exact hchange.symm.trans heq.symm

theorem period_integral_unit_affine (f : ℂ→ℂ)
    (hp : ∀n : ActualEisensteinCubic.O,∀z : ℂ,f (z+3*eisEmbedding n)=f z) (u : ActualEisensteinCubic.Oˣ) (b : ℂ) :
    (∫z in periodDomain,f (eisEmbedding (u:ActualEisensteinCubic.O)*z+b))=∫z in periodDomain,f z := by
  have hg : ∀n : ActualEisensteinCubic.O,∀z : ℂ,(fun w=>f (w+b)) (z+3*eisEmbedding n)=(fun w=>f (w+b)) z := by
    intro n z
    dsimp
    rw [show z+3*eisEmbedding n+b=(z+b)+3*eisEmbedding n by ring,hp]
  rw [period_integral_unit_rotation (fun w=>f (w+b)) hg u]
  simpa only [add_comm] using period_integral_translation f hp b

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

open ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O

lemma integral_upper_triangular_action (T : SL(2,ActualEisensteinCubic.O)) (hc : T 1 0=0)
    (z : ℂ) (v : ℝ) (hv : 0<v) :
    integralComplexMatrix T • upperPoint z v hv=
      upperPoint (eisEmbedding (T 0 0)^2*z+eisEmbedding (T 0 0*T 0 1)) v hv := by
  have hdet : T 0 0*T 1 1=1 := by
    simpa only [Matrix.det_fin_two,hc,mul_zero,sub_zero] using T.property
  let u : ActualEisensteinCubic.Oˣ := ⟨T 1 1,T 0 0,by rw [mul_comm,hdet],hdet⟩
  have hn : ‖eisEmbedding (T 1 1)‖=1 := GaussGeneratorTransport.norm_eisEmbedding_unit u
  have hprod : eisEmbedding (T 1 1)*star (eisEmbedding (T 1 1))=1 := by
    simpa only [Complex.star_def,Complex.normSq_eq_norm_sq,hn,one_pow,Complex.ofReal_one] using
      Complex.mul_conj (eisEmbedding (T 1 1))
  have hstar : star (eisEmbedding (T 1 1))=eisEmbedding (T 0 0) := by
    have hnon : eisEmbedding (T 1 1)≠0 := by
      intro hz
      rw [hz,norm_zero] at hn
      exact zero_ne_one hn
    apply mul_left_cancel₀ hnon
    rw [hprod,←map_mul,mul_comm,hdet,map_one]
  rw [mobius_upperPoint]
  apply upperPoint_congr
  · simp only [integralComplexMatrix_apply,hc,map_zero,zero_mul,zero_add,star_zero,
      mul_zero,add_zero,norm_zero,hn,one_pow,hstar,map_mul]
    norm_num
    ; ring
  · simp only [integralComplexMatrix_apply,hc,map_zero,zero_mul,zero_add,norm_zero,
      hn,one_pow,]
    norm_num

theorem period_integral_upper_triangular
    (F : HyperbolicSpace→ℂ) (v : ℝ) (hv : 0<v)
    (hp : ∀n : ActualEisensteinCubic.O,∀z : ℂ,
      F (upperPoint (3*(z+3*eisEmbedding n)) v hv)=F (upperPoint (3*z) v hv))
    (T : SL(2,ActualEisensteinCubic.O)) (hc : T 1 0=0) :
    (∫z in periodDomain,F (integralComplexMatrix T • upperPoint (3*z) v hv))=
      ∫z in periodDomain,F (upperPoint (3*z) v hv) := by
  have hdet : T 0 0*T 1 1=1 := by
    simpa only [Matrix.det_fin_two,hc,mul_zero,sub_zero] using T.property
  let u : ActualEisensteinCubic.Oˣ := ⟨T 0 0,T 1 1,hdet,by rw [mul_comm,hdet]⟩
  let f : ℂ→ℂ := fun z=>F (upperPoint (3*z) v hv)
  have he (z : ℂ) : F (integralComplexMatrix T • upperPoint (3*z) v hv)=
      f (eisEmbedding (↑(u^2):ActualEisensteinCubic.O)*z+eisEmbedding (T 0 0*T 0 1)/3) := by
    rw [integral_upper_triangular_action T hc]
    dsimp only [f]
    congr 2
    simp only [Units.val_pow_eq_pow_val,map_pow]
    ring
  simp_rw [he]
  exact period_integral_unit_affine f hp (u^2) _

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology ENNReal

local notation "O" => ActualEisensteinCubic.O
namespace SubexponentialBesselCoefficients

lemma series_scaled_three_average_zero (coeff : SubexponentialBesselCoefficients)
    (v : ℝ) (hv : 0<v) : (∫z in periodDomain,coeff.series (v,3*z))=0 := by
  let : Countable ActualEisensteinCubic.O := ActualEisensteinCubic.latticeCoordEquiv.injective.countable
  let : IsFiniteMeasure (volume.restrict periodDomain) := isFiniteMeasure_restrict.mpr (by
    rw [periodDomain_volume]
    exact ENNReal.ofReal_ne_top)
  let f : ActualEisensteinCubic.O→ℂ→ℂ := fun h z => coeff.term h (v,3*z)
  have hc (h : ActualEisensteinCubic.O) : Continuous (f h) := by
    change Continuous (fun z : ℂ => coeff.term h (v,3*z))
    simp_rw [coeff.term_eq_amplitude v hv h]
    change Continuous (fun z : ℂ => coeff.amplitude v h*
      Complex.exp (2*Real.pi*Complex.I*((cuspFrequency h*(3*z))+
        starRingEnd ℂ (cuspFrequency h*(3*z)))))
    fun_prop
  obtain ⟨C,hC,hbound⟩ := coeff.slab_bound v v hv le_rfl
  have hfbound (h : ActualEisensteinCubic.O) (z : ℂ) : ‖f h z‖≤C*Real.exp (-(Real.pi*v)*‖cuspFrequency h‖) :=
    hbound h (v,3*z) ⟨le_rfl,le_rfl⟩
  have hi (h : ActualEisensteinCubic.O) : IntegrableOn (f h) periodDomain volume :=
    (integrable_const (C*Real.exp (-(Real.pi*v)*‖cuspFrequency h‖))).mono'
      (hc h).aestronglyMeasurable (Eventually.of_forall (hfbound h))
  have hnorm (h : ActualEisensteinCubic.O) : (∫z in periodDomain,‖f h z‖)≤
      volume.real periodDomain*(C*Real.exp (-(Real.pi*v)*‖cuspFrequency h‖)) := by
    have hh := integral_mono_ae (hi h).norm (integrable_const (C*Real.exp (-(Real.pi*v)*‖cuspFrequency h‖)))
      (Eventually.of_forall (hfbound h))
    simpa only [setIntegral_const,smul_eq_mul] using hh
  have hs : Summable (fun h : ActualEisensteinCubic.O => ∫z in periodDomain,‖f h z‖) := by
    apply Summable.of_nonneg_of_le (fun h => integral_nonneg (fun z => norm_nonneg _)) hnorm
    exact ((summable_exp_neg_cuspFrequency_norm (Real.pi*v) (mul_pos Real.pi_pos hv)).mul_left C).mul_left
      (volume.real periodDomain)
  have hterm (h : ActualEisensteinCubic.O) : (∫z in periodDomain,f h z)=0 := by
    have he (z : ℂ) : cuspFrequency h*(3*z)= -cuspFrequency (-(3*h))*z := by
      simp only [cuspFrequency,map_neg,map_mul,map_ofNat]
      ring
    change (∫z in periodDomain,coeff.term h (v,3*z))=0
    simp_rw [coeff.term_eq_amplitude v hv h,he]
    rw [integral_const_mul,integral_cusp_character]
    by_cases hh : h=0
    · simp [hh,amplitude]
    · have hk : -(3*h)≠(0:ActualEisensteinCubic.O) := neg_ne_zero.mpr (mul_ne_zero (by norm_num) hh)
      simp [hk]
  change (∫z in periodDomain,∑'h : ActualEisensteinCubic.O,f h z)=0
  rw [←integral_tsum_of_summable_integral_norm hi hs]
  simp_rw [hterm]
  exact tsum_zero

lemma fullFunction_scaled_three_average (coeff : SubexponentialBesselCoefficients)
    (c : ℂ) (v : ℝ) (hv : 0<v) :
    (∫z in periodDomain,coeff.fullFunction c (upperPoint (3*z) v hv))=
      ((9*Real.sqrt 3/2:ℝ):ℂ)*c*(v:ℂ)^(2/3:ℂ) := by
  let : IsFiniteMeasure (volume.restrict periodDomain) := isFiniteMeasure_restrict.mpr (by
    rw [periodDomain_volume]
    exact ENNReal.ofReal_ne_top)
  have hc : Continuous (fun z : ℂ=>coeff.series (v,3*z)) :=
    (coeff.series_height_continuous v hv).comp (continuous_const.mul continuous_id)
  simp only [fullFunction,function,hyperbolicHeight_upperPoint,hyperbolicHorizontal_upperPoint]
  rw [integral_add (integrable_const _) (periodDomain_integrable_of_continuous _ hc),
    series_scaled_three_average_zero coeff v hv,add_zero,setIntegral_const]
  rw [Measure.real,periodDomain_volume,ENNReal.toReal_ofReal (by positivity)]
  simp only [Complex.real_smul]
  ring

end SubexponentialBesselCoefficients

theorem cubicSource_scaled_three_average (v : ℝ) (hv : 0<v) :
    (∫z in periodDomain,cubicSourceResidualFunction (upperPoint (3*z) v hv))=
      ((9*Real.sqrt 3/2:ℝ):ℂ)*((3*(Real.pi:ℂ))*constantArithmeticResidue)*(v:ℂ)^(2/3:ℂ) := by
  rw [cubicSourceResidualFunction_eq_bessel]
  exact sourceBesselCoefficients.fullFunction_scaled_three_average _ v hv

end CubicEisenstein

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

namespace CubicEisenstein
open ConcreteTraceCRT CubicKubota EisensteinCuspModThree
local notation "O" => ActualEisensteinCubic.O

lemma lowerCuspMatrix_zero : lowerCuspMatrix (0:ActualEisensteinCubic.O)=1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lowerCuspMatrix]

lemma cubicSource_scaled_periodic (v : ℝ) (hv : 0<v) (n : ActualEisensteinCubic.O) (z : ℂ) :
    cubicSourceResidualFunction (upperPoint (3*(z+3*eisEmbedding n)) v hv)=
      cubicSourceResidualFunction (upperPoint (3*z) v hv) := by
  have he : 3*(z+3*eisEmbedding n)=3*z+3*eisEmbedding (3*n) := by
    rw [map_mul,map_ofNat]
    ring
  rw [cubicSourceResidualFunction_eq_bessel,he]
  exact sourceBesselFunction_period v hv (3*z) (3*n)

lemma sourceCuspRepresentative_periodic (j : Fin 3) (v : ℝ) (hv : 0<v) (n : ActualEisensteinCubic.O) (z : ℂ) :
    cubicSourceResidualFunction (integralComplexMatrix (cuspRepresentative j) •
      upperPoint (3*(z+3*eisEmbedding n)) v hv)=
    cubicSourceResidualFunction (integralComplexMatrix (cuspRepresentative j) •
      upperPoint (3*z) v hv) := by
  fin_cases j
  · simpa [cuspRepresentative,cuspParameter,lowerCuspMatrix_zero] using cubicSource_scaled_periodic v hv n z
  · simpa [cuspRepresentative,cuspParameter,ramifiedSourceFunction] using ramifiedSource_scaled_periodic10 v hv n z
  · simpa [cuspRepresentative,cuspParameter,ramifiedSourceFunction] using ramifiedSource_scaled_periodic19 v hv n z

def sourcePrincipalCuspConstant : ℂ :=
  ((9*Real.sqrt 3/2:ℝ):ℂ)*((3*(Real.pi:ℂ))*constantArithmeticResidue)

lemma sourceCuspRepresentative_average (j : Fin 3) (v : ℝ) (hv : 0<v) :
    (∫z in periodDomain,cubicSourceResidualFunction
      (integralComplexMatrix (cuspRepresentative j) • upperPoint (3*z) v hv))=
      (if j=0 then sourcePrincipalCuspConstant else 0)*(v:ℂ)^(2/3:ℂ) := by
  fin_cases j
  · simpa [cuspRepresentative,cuspParameter,lowerCuspMatrix_zero,sourcePrincipalCuspConstant] using
      cubicSource_scaled_three_average v hv
  · simpa [cuspRepresentative,cuspParameter,ramifiedSourceFunction] using ramifiedSource_zero_mode10 v hv
  · simpa [cuspRepresentative,cuspParameter,ramifiedSourceFunction] using ramifiedSource_zero_mode19 v hv

lemma sourceCusp_average_of_decomposition (M : SL(2,ActualEisensteinCubic.O)) (G : levelTwo) (j : Fin 3)
    (T : SL(2,ActualEisensteinCubic.O)) (hT : T 1 0=0) (hM : M=(G:SL(2,ActualEisensteinCubic.O))*cuspRepresentative j*T)
    (v : ℝ) (hv : 0<v) :
    (∫z in periodDomain,cubicSourceResidualFunction (integralComplexMatrix M • upperPoint (3*z) v hv))=
      (levelTwoComplexCharacter G*(if j=0 then sourcePrincipalCuspConstant else 0))*(v:ℂ)^(2/3:ℂ) := by
  have he (z : ℂ) : cubicSourceResidualFunction (integralComplexMatrix M • upperPoint (3*z) v hv)=
      levelTwoComplexCharacter G*cubicSourceResidualFunction
        (integralComplexMatrix (cuspRepresentative j) • (integralComplexMatrix T • upperPoint (3*z) v hv)) := by
    rw [hM,map_mul,map_mul,mul_smul,mul_smul,cubicSourceResidualFunction_automorphy]
  simp_rw [he]
  rw [integral_const_mul]
  have hi := period_integral_upper_triangular
    (fun w=>cubicSourceResidualFunction (integralComplexMatrix (cuspRepresentative j) • w))
    v hv (sourceCuspRepresentative_periodic j v hv) T hT
  rw [hi,sourceCuspRepresentative_average]
  ring

def sourceCuspConstant (M : SL(2,ActualEisensteinCubic.O)) : ℂ :=
  ∫z in periodDomain,cubicSourceResidualFunction (integralComplexMatrix M • upperPoint (3*z) 1 (by norm_num))

theorem sourceCusp_average_all (M : SL(2,ActualEisensteinCubic.O)) (v : ℝ) (hv : 0<v) :
    (∫z in periodDomain,cubicSourceResidualFunction (integralComplexMatrix M • upperPoint (3*z) v hv))=
      sourceCuspConstant M*(v:ℂ)^(2/3:ℂ) := by
  obtain ⟨G,j,T,hT,_,_,hM⟩ := three_cusp_decomposition M
  have h1 := sourceCusp_average_of_decomposition M G j T hT hM 1 (by norm_num)
  have hc : sourceCuspConstant M=levelTwoComplexCharacter G*(if j=0 then sourcePrincipalCuspConstant else 0) := by
    simpa only [sourceCuspConstant,Complex.ofReal_one,Complex.one_cpow,mul_one] using h1
  rw [hc]
  exact sourceCusp_average_of_decomposition M G j T hT hM v hv

theorem sourceCuspConstant_decomposition (M : SL(2,ActualEisensteinCubic.O)) (G : levelTwo) (j : Fin 3)
    (T : SL(2,ActualEisensteinCubic.O)) (hT : T 1 0=0) (hM : M=(G:SL(2,ActualEisensteinCubic.O))*cuspRepresentative j*T) :
    sourceCuspConstant M=levelTwoComplexCharacter G*(if j=0 then sourcePrincipalCuspConstant else 0) := by
  simpa only [sourceCuspConstant,Complex.ofReal_one,Complex.one_cpow,mul_one] using
    sourceCusp_average_of_decomposition M G j T hT hM 1 (by norm_num)

lemma sourcePrincipalCuspConstant_ne_zero : sourcePrincipalCuspConstant≠0 := by
  unfold sourcePrincipalCuspConstant
  apply mul_ne_zero
  · exact Complex.ofReal_ne_zero.mpr (ne_of_gt (by positivity))
  · exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      constantArithmeticResidue_ne_zero

lemma sourceCuspConstant_zero_iff (M : SL(2,ActualEisensteinCubic.O)) (G : levelTwo) (j : Fin 3)
    (T : SL(2,ActualEisensteinCubic.O)) (hT : T 1 0=0) (hM : M=(G:SL(2,ActualEisensteinCubic.O))*cuspRepresentative j*T) :
    sourceCuspConstant M=0 ↔ j≠0 := by
  have hG : levelTwoComplexCharacter G≠0 := by
    intro hz
    have hn := norm_levelTwoComplexCharacter G
    rw [hz,norm_zero] at hn
    exact zero_ne_one hn
  rw [sourceCuspConstant_decomposition M G j T hT hM]
  by_cases hj : j=0 <;> simp [hj,hG,sourcePrincipalCuspConstant_ne_zero]

lemma sourceCuspConstant_left (G : levelTwo) (M : SL(2,ActualEisensteinCubic.O)) :
    sourceCuspConstant ((G:SL(2,ActualEisensteinCubic.O))*M)=levelTwoComplexCharacter G*sourceCuspConstant M := by
  unfold sourceCuspConstant
  simp_rw [map_mul,mul_smul,cubicSourceResidualFunction_automorphy]
  exact integral_const_mul _ _

lemma sourceCuspConstant_upper_right (M T : SL(2,ActualEisensteinCubic.O)) (hT : T 1 0=0) :
    sourceCuspConstant (M*T)=sourceCuspConstant M := by
  obtain ⟨G,j,S,hS,_,_,hM⟩ := three_cusp_decomposition M
  have hST : (S*T) 1 0=0 := by
    change (∑k : Fin 2,S 1 k*T k 0)=0
    rw [Fin.sum_univ_two,hS,hT]
    ring
  have he : M*T=(G:SL(2,ActualEisensteinCubic.O))*cuspRepresentative j*(S*T) := by rw [hM]; group
  rw [sourceCuspConstant_decomposition (M*T) G j (S*T) hST he,
    sourceCuspConstant_decomposition M G j S hS hM]

end CubicEisenstein

end

end OAI
end

section

namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

namespace CubicEisenstein

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology

local notation "O" => ActualEisensteinCubic.O
namespace SubexponentialBesselCoefficients

theorem series_cusp_decay (coeff : SubexponentialBesselCoefficients) (a : ℝ) (ha : 0<a) :
    ∃C : ℝ,0≤C ∧ ∀v z,a≤v → ‖coeff.series (v,z)‖≤C*Real.exp (-residualCuspDecayRate*v) := by
  obtain ⟨D,hD,hterm⟩ := coeff.term_cusp_bound a ha
  let S : ℝ := ∑'h : ActualEisensteinCubic.O,Real.exp (-(Real.pi*a/2)*‖cuspFrequency h‖)
  have hS : 0≤S := tsum_nonneg (fun h => (Real.exp_pos _).le)
  have hs := summable_exp_neg_cuspFrequency_norm (Real.pi*a/2) (by positivity)
  refine ⟨D*S*(2/(2*residualCuspDecayRate)),by have := residualCuspDecayRate_pos;positivity,?_⟩
  intro v z hav
  have hv : 0<v := ha.trans_le hav
  have hb (h : ActualEisensteinCubic.O) : ‖coeff.term h (v,z)‖≤
      (D*v*Real.exp (-(2*residualCuspDecayRate)*v))*Real.exp (-(Real.pi*a/2)*‖cuspFrequency h‖) := by
    by_cases hh : h=0
    · simp only [term,if_pos hh,norm_zero]
      positivity
    have he : Real.exp (-(Real.pi*v)*‖cuspFrequency h‖)≤
        Real.exp (-(2*residualCuspDecayRate)*v)*Real.exp (-(Real.pi*a/2)*‖cuspFrequency h‖) := by
      rw [←Real.exp_add]
      apply Real.exp_le_exp.mpr
      have h1 := mul_le_mul_of_nonneg_left (cuspFrequency_norm_lower h hh)
        (show 0≤Real.pi*v/2 by positivity)
      have h2 := mul_le_mul_of_nonneg_left hav (show 0≤Real.pi*‖cuspFrequency h‖/2 by positivity)
      unfold residualCuspDecayRate
      nlinarith
    exact (hterm h v z hav).trans ((mul_le_mul_of_nonneg_left he (by positivity)).trans_eq (by ring))
  have hsum := tsum_of_norm_bounded (hs.hasSum.mul_left (D*v*Real.exp (-(2*residualCuspDecayRate)*v))) hb
  calc
    _ ≤ (D*v*Real.exp (-(2*residualCuspDecayRate)*v))*S := hsum
    _ = (D*S)*(v*Real.exp (-(2*residualCuspDecayRate)*v)) := by ring
    _ ≤ (D*S)*((2/(2*residualCuspDecayRate))*Real.exp (-((2*residualCuspDecayRate)/2)*v)) :=
      mul_le_mul_of_nonneg_left (norm_mul_exp_neg_bound (2*residualCuspDecayRate) v
        (mul_pos (by norm_num) residualCuspDecayRate_pos)) (mul_nonneg hD hS)
    _ = _ := by
      rw [show -((2*residualCuspDecayRate)/2)*v=-residualCuspDecayRate*v by ring]
      ring

theorem series_cubic_decay (coeff : SubexponentialBesselCoefficients) (a : ℝ) (ha : 0<a) :
    ∃C : ℝ,0≤C ∧ ∀v z,a≤v → ‖coeff.series (v,z)‖≤C/v^3 := by
  obtain ⟨C,hC,hbound⟩ := coeff.series_cusp_decay a ha
  let k := residualCuspDecayRate
  have hk : 0<k := residualCuspDecayRate_pos
  refine ⟨C*(6/k^3),by positivity,?_⟩
  intro v z hav
  have hv : 0<v := ha.trans_le hav
  have he : Real.exp (-k*v)*v^3≤6/k^3 := by
    have hb := Real.pow_div_factorial_le_exp (k*v) (mul_nonneg hk.le hv.le) 3
    norm_num only [Nat.factorial] at hb
    have hm := mul_le_mul_of_nonneg_right hb (Real.exp_pos (-k*v)).le
    rw [←Real.exp_add,show k*v+ -k*v=0 by ring,Real.exp_zero] at hm
    apply (le_div_iff₀ (pow_pos hk 3)).mpr
    nlinarith [hm]
  apply (le_div_iff₀ (pow_pos hv 3)).mpr
  calc
    _ ≤ (C*Real.exp (-k*v))*v^3 := mul_le_mul_of_nonneg_right (hbound v z hav) (pow_nonneg hv.le 3)
    _ = C*(Real.exp (-k*v)*v^3) := by ring
    _ ≤ C*(6/k^3) := mul_le_mul_of_nonneg_left he hC

theorem fullFunction_zero_cubic_decay (coeff : SubexponentialBesselCoefficients) (a : ℝ) (ha : 0<a) :
    ∃C : ℝ,0≤C ∧ ∀v (hv : 0<v) z,a≤v →
      ‖coeff.fullFunction 0 (upperPoint z v hv)‖≤C/v^3 := by
  obtain ⟨C,hC,hbound⟩ := coeff.series_cubic_decay a ha
  refine ⟨C,hC,fun v hv z hav => ?_⟩
  simpa only [fullFunction,zero_mul,zero_add,function,hyperbolicHeight_upperPoint,hyperbolicHorizontal_upperPoint]
    using hbound v z hav

end SubexponentialBesselCoefficients
end

open scoped BigOperators Classical MatrixGroups Matrix

section
open ActualEisensteinCubic CubicKubota ConcreteTraceCRT CompletedGauss
open PrimaryIdealUnitReindex (GoodIdeal GoodElement)
local notation "Eis" => ActualEisensteinCubic.O
local notation "ramLambda" => (omega-1:Eis)

lemma halfPrimary_lambda_dvd_three : ramLambda ∣ (3:Eis) := by
  exact (dvd_pow_self ramLambda (by decide : (2:ℕ)≠0)).trans lambda_sq_dvd_three

lemma halfPrimary_lambda_not_dvd_one : ¬ramLambda ∣ (1:Eis) := by
  intro h
  exact PrimaryIdealUnitReindex.lambda_prime_actual.not_isUnit (isUnit_of_dvd_one h)

lemma halfPrimary_omega_pow (j:ℕ) : ramLambda ∣ omega^j-1 := by
  simpa only [one_pow] using sub_dvd_pow_sub_pow omega (1:Eis) j

lemma halfPrimary_not_negative (j:ℕ) : ¬ramLambda ∣ -(omega^j)-1 := by
  intro h
  have h2 : ramLambda ∣ (2:Eis) := by
    have hh:=dvd_add h (halfPrimary_omega_pow j)
    convert (preTransparency := .instances) dvd_neg.mpr hh using 1 ;ring
  apply halfPrimary_lambda_not_dvd_one
  convert (preTransparency := .instances) dvd_sub halfPrimary_lambda_dvd_three h2 using 1 ;ring

abbrev HalfPrimary := {b:Eis // ramLambda ∣ b-1}

lemma halfPrimary_not_dvd (b:HalfPrimary) : ¬ramLambda∣b.val := by
  intro h
  apply halfPrimary_lambda_not_dvd_one
  convert (preTransparency := .instances) dvd_sub h b.2 using 1 ;ring

def halfPrimaryFromAssociate (p:Fin 3×PrimaryLower) : HalfPrimary :=
  ⟨omega^p.1.val*p.2.val,by
    have ha:ramLambda∣p.2.val-1:=halfPrimary_lambda_dvd_three.trans p.2.2
    convert (preTransparency := .instances) dvd_add ((halfPrimary_omega_pow p.1.val).mul_right p.2.val) ha using 1 ;ring⟩

lemma halfPrimaryFromAssociate_injective : Function.Injective halfPrimaryFromAssociate := by
  intro p q hpq
  have he:omega^p.1.val*p.2.val=omega^q.1.val*q.2.val:=congrArg Subtype.val hpq
  have hunit (j:Fin 3):IsUnit (omega^j.val):=(omega_primitive.isUnit (by decide)).pow _
  have hs:(Ideal.span {p.2.val}:Ideal Eis)=Ideal.span {q.2.val}:=by
    simpa only [Ideal.span_singleton_mul_left_unit (hunit p.1),
      Ideal.span_singleton_mul_left_unit (hunit q.1)] using
      congrArg (fun z:Eis=>(Ideal.span {z}:Ideal Eis)) he
  have hab:p.2=q.2:=by
    apply Subtype.ext
    have hg:=congrArg primaryGenerator hs
    simpa only [primaryGenerator_span p.2.val (primaryLower_ne_zero p.2) (primaryLower_primary p.2),
      primaryGenerator_span q.2.val (primaryLower_ne_zero q.2) (primaryLower_primary q.2)] using hg
  have hj:p.1=q.1:=by
    apply Fin.ext
    apply omega_primitive.pow_inj p.1.isLt q.1.isLt
    rw [hab] at he
    exact mul_right_cancel₀ (primaryLower_ne_zero q.2) he
  exact Prod.ext hj hab

lemma halfPrimaryFromAssociate_surjective : Function.Surjective halfPrimaryFromAssociate := by
  intro b
  let z:GoodElement:=⟨b.val,PrimaryIdealUnitReindex.primaryGenerator_span_ne_zero_iff b.val |>.mpr
    (halfPrimary_not_dvd b)⟩
  let p:=PrimaryIdealUnitReindex.unitIdealEquiv.symm z
  have he:(p.1:Eis)*primaryGenerator p.2.val=b.val:=
    congrArg Subtype.val (PrimaryIdealUnitReindex.unitIdealEquiv.apply_symm_apply z)
  let a:PrimaryLower:=primaryLowerIdealEquiv.symm p.2
  have ha:a.val=primaryGenerator p.2.val:=rfl
  have hea:(p.1:Eis)*a.val=b.val:=by simpa only [ha] using he
  have hu:ramLambda∣(p.1:Eis)-1:=by
    have hpa:ramLambda∣a.val-1:=halfPrimary_lambda_dvd_three.trans a.2
    have hh:=dvd_sub b.2 (hpa.mul_left (p.1:Eis))
    rw [←hea] at hh
    convert (preTransparency := .instances) hh using 1 ;ring
  obtain ⟨j,hj|hj⟩:=unit_eq_sign_omega p.1
  · exact ⟨(j,a),Subtype.ext (by simpa only [halfPrimaryFromAssociate,hj] using hea)⟩
  · exact (halfPrimary_not_negative j.val (by simpa only [hj] using hu)).elim

def halfPrimaryAssociateEquiv : Fin 3×PrimaryLower ≃ HalfPrimary :=
  Equiv.ofBijective halfPrimaryFromAssociate
    ⟨halfPrimaryFromAssociate_injective,halfPrimaryFromAssociate_surjective⟩

end

open ActualEisensteinCubic CubicKubota ConcreteTraceCRT
local notation "Eis" => ActualEisensteinCubic.O

def unitCuspUpper (b : Eis) : SL(2,Eis) := ⟨!![1,b;0,1],by simp [Matrix.det_fin_two]⟩
def unitCuspDiagonal (u : Eisˣ) : SL(2,Eis) := ⟨!![(u:Eis),0;0,(↑u⁻¹:Eis)],by
  simp [Matrix.det_fin_two]⟩

theorem rational_cusp_lower_factor (u : Eisˣ) (n : ℤ) :
    rationalEmbedding ModularGroup.S*unitCuspUpper (n:Eis)*lowerCuspMatrix (u:Eis)=
      unitCuspDiagonal (-u)*lowerCuspMatrix (-(u:Eis)*(1+(n:Eis)*(u:Eis)))*
        unitCuspUpper (↑u⁻¹:Eis) := by
  apply Subtype.ext
  change ((!![(0 : ℤ), -1; 1, 0]).map (Int.castRingHom Eis) *
    !![1, (n : Eis); 0, 1] * !![1, 0; (u : Eis), 1]) =
    (!![(↑(-u) : Eis), 0; 0, (↑(-u)⁻¹ : Eis)] *
      !![1, 0; -(u : Eis) * (1 + (n : Eis) * (u : Eis)), 1] *
      !![1, (↑u⁻¹ : Eis); 0, 1])
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, neg_mul, Units.val_neg,
      mul_add, add_mul, mul_assoc, add_comm]

lemma unitCuspUpper_section (b : Eis) (z : ℂ) (v : ℝ) (hv : 0<v) :
    integralComplexMatrix (unitCuspUpper b)*upperSection z v hv=
      upperSection (z+eisEmbedding b) v hv := by
  apply Subtype.ext
  change ((!![1, b; 0, 1] : Matrix (Fin 2) (Fin 2) Eis).map eisEmbedding *
    !![(Real.sqrt v : ℂ), z / Real.sqrt v; 0, (Real.sqrt v : ℂ)⁻¹]) =
    !![(Real.sqrt v : ℂ), (z + eisEmbedding b) / Real.sqrt v;
      0, (Real.sqrt v : ℂ)⁻¹]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  ring

end CubicEisenstein

open scoped Classical MatrixGroups
namespace CubicEisenstein

section
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicKubota
local notation "Eis" => ActualEisensteinCubic.O

abbrev CubeResidueStrata (p:Eis) := Σj:Fin 4,CubicUnitResidue (p^(3-j.val))

def cubeResidueStratumMap (p:Eis) (x:CubeResidueStrata p) : Eis⧸Ideal.span {p^3} :=
  Ideal.Quotient.mk _ (p^x.1.val * GaussianShiftedPartition.representative (p^(3-x.1.val)) x.2.1)

lemma unit_rep_coprime (c:Eis) (x:CubicUnitResidue c) :
    IsCoprime c (GaussianShiftedPartition.representative c x.1) := by
  apply (isUnit_quotient_span_iff c _).mp
  simpa only [GaussianShiftedPartition.representative_spec] using x.2

lemma cube_strata_exponents (p:Eis) (hp:Prime p) (j k:Fin 4)
    (b d:Eis) (hb:IsCoprime (p^(3-j.val)) b)
    (he:p^3∣p^j.val*b-p^k.val*d) : ¬j.val<k.val := by
  intro hjk
  have hj3:j.val+1≤3:=by omega
  have hjk':j.val+1≤k.val:=by omega
  have h1:p^(j.val+1)∣p^j.val*b-p^k.val*d:=
    (pow_dvd_pow p hj3).trans he
  have h2:p^(j.val+1)∣p^k.val*d:=
    dvd_mul_of_dvd_left (pow_dvd_pow p hjk') d
  have h3:p^(j.val+1)∣p^j.val*b:=by
    simpa only [sub_add_cancel] using dvd_add h1 h2
  rw [pow_succ] at h3
  have hpb:p∣b:=(mul_dvd_mul_iff_left (pow_ne_zero j.val hp.ne_zero)).mp h3
  have hpc:IsCoprime p b:=hb.of_isCoprime_of_dvd_left
    (dvd_pow_self p (by omega:3-j.val≠0))
  exact (hp.coprime_iff_not_dvd.mp hpc) hpb

lemma cubeResidueStratumMap_injective (p:Eis) (hp:Prime p) :
    Function.Injective (cubeResidueStratumMap p) := by
  rintro ⟨j,b⟩ ⟨k,d⟩ he
  have hd:p^3∣p^j.val*GaussianShiftedPartition.representative (p^(3-j.val)) b.1-
      p^k.val*GaussianShiftedPartition.representative (p^(3-k.val)) d.1 :=
    Ideal.mem_span_singleton.mp ((Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp he)
  have hle:=cube_strata_exponents p hp j k _ _ (unit_rep_coprime _ b) hd
  have hge:=cube_strata_exponents p hp k j _ _ (unit_rep_coprime _ d)
    (by simpa only [neg_sub] using dvd_neg.mpr hd)
  have hjk:j=k:=Fin.ext (by omega)
  subst k
  have hpow:p^3=p^j.val*p^(3-j.val):=by rw [←pow_add,Nat.add_sub_of_le (by omega:j.val≤3)]
  rw [hpow,←mul_sub] at hd
  have hrep:p^(3-j.val)∣GaussianShiftedPartition.representative (p^(3-j.val)) b.1-
      GaussianShiftedPartition.representative (p^(3-j.val)) d.1:=
    (mul_dvd_mul_iff_left (pow_ne_zero j.val hp.ne_zero)).mp hd
  have hbd:b=d:=by
    apply Subtype.ext
    rw [←GaussianShiftedPartition.representative_spec (p^(3-j.val)) b.1,
      ←GaussianShiftedPartition.representative_spec (p^(3-j.val)) d.1]
    exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr (Ideal.mem_span_singleton.mpr hrep)
  subst d
  rfl

lemma cubeResidueStratumMap_surjective (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1) :
    Function.Surjective (cubeResidueStratumMap p) := by
  intro r
  let a:=GaussianShiftedPartition.representative (p^3) r
  let A:SL(2,Eis):=⟨!![a,-1;1,0],by simp [Matrix.det_fin_two_of]⟩
  obtain ⟨j,hj,N,hx,hc,hNA,hjN,hupper⟩:=cube_average_cusp_reduction A p 0 hp hprimary
  have ha:a=p^j*N 0 0:=by simpa [A] using hx
  have hc':p^3=p^j*N 1 0:=by simpa [A] using hc
  have hpow:p^3=p^j*p^(3-j):=by rw [←pow_add,Nat.add_sub_of_le hj]
  have hN10:N 1 0=p^(3-j):=by
    apply mul_left_cancel₀ (pow_ne_zero j hp.ne_zero)
    exact hc'.symm.trans hpow
  have hcop:IsCoprime (p^(3-j)) (N 0 0):=by
    refine ⟨-N 0 1,N 1 1,?_⟩
    have hd:N 0 0*N 1 1-N 0 1*N 1 0=1:=by
      simpa only [Matrix.det_fin_two] using N.property
    rw [hN10] at hd
    linear_combination hd
  let b:CubicUnitResidue (p^(3-j)):=⟨Ideal.Quotient.mk _ (N 0 0),
    (isUnit_quotient_span_iff _ _).mpr hcop⟩
  refine ⟨⟨⟨j,by omega⟩,b⟩,?_⟩
  change Ideal.Quotient.mk (Ideal.span {p^3})
      (p^j*GaussianShiftedPartition.representative (p^(3-j)) b.1)=r
  rw [←GaussianShiftedPartition.representative_spec (p^3) r]
  apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
  apply Ideal.mem_span_singleton.mpr
  change p^3∣p^j*GaussianShiftedPartition.representative (p^(3-j)) b.1-a
  rw [ha,←mul_sub,hpow]
  exact mul_dvd_mul_left (p^j) (gaussRep_mk_congr (p^(3-j)) (N 0 0))

def cubeResidueStrataEquiv (p:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1) :
    CubeResidueStrata p≃(Eis⧸Ideal.span {p^3}) :=
  Equiv.ofBijective (cubeResidueStratumMap p)
    ⟨cubeResidueStratumMap_injective p hp,cubeResidueStratumMap_surjective p hp hprimary⟩

end

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicKubota
local notation "Eis" => ActualEisensteinCubic.O

def cubeStratumSymbol (p C:Eis) (j:Fin 4) (b:CubicUnitResidue (p^(3-j.val))) : ℂ :=
  eisEmbedding (symbol (GaussianShiftedPartition.representative (p^(3-j.val)) b.1*C) (p^(3-j.val)))

lemma unit_stratum_symbol_gauss (p C:Eis) (hp:lambda^2∣p-1) (n:ℕ) :
    (∑' b:CubicUnitResidue (p^n),
      eisEmbedding (symbol (GaussianShiftedPartition.representative (p^n) b.1*C) (p^n))) =
      cubicUnitGaussSum 0 (p^n)*eisEmbedding (symbol C (p^n)) := by
  rw [cubicUnitGaussSum]
  simp only [mul_zero,residueAdditive,map_zero,cuspFrequency,zero_div,zero_mul,
    AddChar.map_zero_eq_one,mul_one]
  rw [←tsum_mul_right]
  apply tsum_congr
  intro b
  rw [symbol_mul_numerator _ _ _ (primary_pow_congruence p hp n),map_mul]

lemma cubeStratumSymbol_sum (p C:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1)
    (hC:IsCoprime C p) (j:Fin 4) :
    (∑' b:CubicUnitResidue (p^(3-j.val)), cubeStratumSymbol p C j b) =
      if j=0 then (Ideal.absNorm (Ideal.span {p}):ℂ)^2*((Ideal.absNorm (Ideal.span {p}):ℂ)-1)
      else if j=3 then 1 else 0 := by
  have h3:eisEmbedding (symbol C (p^3))=1:=by
    rw [cubicSymbol_pow_denominator,symbol_cube_of_isCoprime C p hprimary hC,map_one]
  unfold cubeStratumSymbol
  rw [unit_stratum_symbol_gauss p C hprimary (3-j.val)]
  fin_cases j
  · have hh:=cubicUnitGaussSum_prime_power_zero p hp hprimary 2
    norm_num at hh ⊢
    rw [hh,h3,mul_one]
  · have hh:=cubicUnitGaussSum_prime_power_zero p hp hprimary 1
    norm_num at hh ⊢
    simp [hh]
  · have hh:=cubicUnitGaussSum_prime_power_zero p hp hprimary 0
    norm_num at hh ⊢
    simp [hh]
  · simp

lemma cubeStrata_weighted_sum (p C:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1)
    (hC:IsCoprime C p) (w:Fin 4→ℂ) :
    (∑ j:Fin 4, w j * ∑' b:CubicUnitResidue (p^(3-j.val)), cubeStratumSymbol p C j b) =
      w 0*(Ideal.absNorm (Ideal.span {p}):ℂ)^2*((Ideal.absNorm (Ideal.span {p}):ℂ)-1)+w 3 := by
  simp_rw [cubeStratumSymbol_sum p C hp hprimary hC]
  simp [Fin.sum_univ_succ]
  ring

end CubicEisenstein

open scoped Classical MatrixGroups
namespace CubicKubota
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein CubicJacobiGlobal CubicRamified
local notation "Eis" => ActualEisensteinCubic.O

lemma comparison_mod_three (A N:SL(2,Eis)) (hNA:N*A⁻¹∈levelThree) (i j:Fin 2) :
    (3:Eis)∣N i j-A i j := by
  have hh:Matrix.SpecialLinearGroup.map (n:=Fin 2)
      (Ideal.Quotient.mk (Ideal.span {(3:Eis)})) (N*A⁻¹)=1:=hNA
  rw [map_mul,map_inv] at hh
  have he:=mul_inv_eq_one.mp hh
  have he' :=congrArg (fun B:SL(2,Eis⧸Ideal.span {(3:Eis)})=>B i j) he
  exact Ideal.mem_span_singleton.mp ((Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp he')

lemma comparison_primary (A N:SL(2,Eis)) (hNA:N*A⁻¹∈levelThree)
    (hA:lambda^2∣A 0 0-1) : lambda^2∣N 0 0-1 := by
  have hh:=lambda_sq_dvd_three.trans (comparison_mod_three A N hNA 0 0)
  simpa only [sub_add_sub_cancel] using dvd_add hh hA

lemma comparison_levelTwo (A:levelTwo) (N:SL(2,Eis))
    (hNA:N*(A:SL(2,Eis))⁻¹∈levelThree) : N∈levelTwo := by
  have hh:=Subgroup.mul_mem levelTwo (levelThree_le_levelTwo hNA) A.property
  simpa only [inv_mul_cancel_right] using hh

lemma levelTwo_cube_zero_phase (A N:levelTwo) (p q:Eis)
    (hp:lambda^2∣p-1)
    (hA:lambda^2∣((A:SL(2,Eis)) 0 0)-1)
    (hN:lambda^2∣((N:SL(2,Eis)) 0 0)-1)
    (hx:(A:SL(2,Eis)) 0 0+3*q*(A:SL(2,Eis)) 1 0=(N:SL(2,Eis)) 0 0)
    (hc:(N:SL(2,Eis)) 1 0=p^3*(A:SL(2,Eis)) 1 0)
    (hNA:(N:SL(2,Eis))*(A:SL(2,Eis))⁻¹∈levelThree) :
    complexCharacter ⟨(N:SL(2,Eis))*(A:SL(2,Eis))⁻¹,hNA⟩=1 := by
  have hcop:IsCoprime ((N:SL(2,Eis)) 0 0) p:=by
    refine ⟨(N:SL(2,Eis)) 1 1,-(N:SL(2,Eis)) 0 1*p^2*(A:SL(2,Eis)) 1 0,?_⟩
    have hd:(N:SL(2,Eis)) 0 0*(N:SL(2,Eis)) 1 1-
        (N:SL(2,Eis)) 0 1*(N:SL(2,Eis)) 1 0=1:=by
      simpa only [Matrix.det_fin_two] using (N:SL(2,Eis)).property
    rw [hc] at hd
    linear_combination hd
  have hcube:eisEmbedding (symbol ((N:SL(2,Eis)) 0 0) p)^3=1:=by
    rw [←map_pow,symbol_cube_of_isCoprime _ _ hp hcop,map_one]
  have hb:=levelTwo_cube_phase_balance A N p q 0 hp hA hN (by simpa using hx) (by simpa using hc)
  simp only [pow_zero,mul_one,Nat.sub_zero,hcube] at hb
  have hcomp:=levelTwo_comparison_character A N hNA
  have hbase:levelTwoComplexCharacter A≠0:=by
    intro he
    have hh:=levelTwoComplexCharacter_cube A
    rw [he] at hh
    norm_num at hh
  apply mul_right_cancel₀ hbase
  rw [one_mul,hcomp,hb]

lemma cube_exponent_zero_of_lower_divisible (A N:SL(2,Eis)) (p q:Eis) (j:ℕ)
    (hp:Prime p) (hC:p∣A 1 0)
    (hx:A 0 0+3*q*A 1 0=p^j*N 0 0) : j=0 := by
  by_contra hj
  have hpx:p∣A 0 0+3*q*A 1 0:=by
    rw [hx]
    exact dvd_mul_of_dvd_left (dvd_pow_self p hj) (N 0 0)
  have hpa:p∣A 0 0:=by
    simpa only [add_sub_cancel_right] using dvd_sub hpx (dvd_mul_of_dvd_right hC (3*q))
  have hone:p∣(1:Eis):=by
    have hh:=dvd_sub (dvd_mul_of_dvd_left hpa (A 1 1)) (dvd_mul_of_dvd_right hC (A 0 1))
    have hd:A 0 0*A 1 1-A 0 1*A 1 0=1:=by
      simpa only [Matrix.det_fin_two] using A.property
    rwa [hd] at hh
  exact hp.not_isUnit (isUnit_of_dvd_one hone)

end CubicKubota

namespace CubicEisenstein
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CubicKubota
local notation "Eis" => ActualEisensteinCubic.O

lemma cube_affine_coefficient_unit (p C:Eis) (hprimary:lambda^2∣p-1) (hC:IsCoprime C p) :
    IsUnit (Ideal.Quotient.mk (Ideal.span {p^3}) (3*C)) := by
  obtain ⟨t,ht⟩:=(three_dvd_primary_sub_one p hprimary)
  have hp3:IsCoprime p (3:Eis):=by
    refine ⟨1,-t,?_⟩
    linear_combination ht
  apply (isUnit_quotient_span_iff _ _).mpr
  exact hp3.pow_left.mul_right hC.symm.pow_left

def cubeCuspAffineEquiv (p A C:Eis) (hprimary:lambda^2∣p-1) (hC:IsCoprime C p) :
    (Eis⧸Ideal.span {p^3})≃(Eis⧸Ideal.span {p^3}) := by
  let a:=Ideal.Quotient.mk (Ideal.span {p^3}) A
  let u:Units (Eis⧸Ideal.span {p^3}):=(cube_affine_coefficient_unit p C hprimary hC).unit
  exact {
    toFun:=fun r=>a+(u:_) * r
    invFun:=fun r=>(↑u⁻¹:_)*(r-a)
    left_inv:=by
      intro r
      simp only [add_sub_cancel_left,←mul_assoc,Units.inv_mul,one_mul]
    right_inv:=by
      intro r
      simp only [←mul_assoc,Units.mul_inv,one_mul,add_sub_cancel] }

lemma cubeCuspAffineEquiv_apply (p A C:Eis) (hprimary:lambda^2∣p-1) (hC:IsCoprime C p)
    (r:Eis⧸Ideal.span {p^3}) :
    cubeCuspAffineEquiv p A C hprimary hC r=
      Ideal.Quotient.mk (Ideal.span {p^3}) A+
        Ideal.Quotient.mk (Ideal.span {p^3}) (3*C)*r := by
  simp only [cubeCuspAffineEquiv,IsUnit.unit_spec]
  rfl

lemma cubeCuspAffineEquiv_mk (p A C q:Eis) (hprimary:lambda^2∣p-1) (hC:IsCoprime C p) :
    cubeCuspAffineEquiv p A C hprimary hC (Ideal.Quotient.mk _ q)=
      Ideal.Quotient.mk (Ideal.span {p^3}) (A+3*q*C) := by
  rw [cubeCuspAffineEquiv_apply]
  simp only [map_add,map_mul]
  ring

end CubicEisenstein

open scoped Classical MatrixGroups BigOperators
namespace CubicKubota
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

structure CubeCuspData (A:SL(2,Eis)) (p q:Eis) where
  exponent : Fin 4
  matrix : SL(2,Eis)
  first : A 0 0+3*q*A 1 0=p^exponent.val*matrix 0 0
  second : p^3*A 1 0=p^exponent.val*matrix 1 0
  congruent : matrix*A⁻¹∈levelThree

def actualCubeCuspData (A:SL(2,Eis)) (p q:Eis) (hp:Prime p) (hprimary:lambda^2∣p-1) :
    CubeCuspData A p q := by
  let h:=cube_average_cusp_reduction A p q hp hprimary
  let j:=Classical.choose h
  have hj:j≤3:=(Classical.choose_spec h).1
  let N:=Classical.choose (Classical.choose_spec h).2
  have hN:=(Classical.choose_spec (Classical.choose_spec h).2)
  exact ⟨⟨j,by omega⟩,N,hN.1,hN.2.1,hN.2.2.1⟩

namespace CubeCuspData
variable {A:SL(2,Eis)} {p q:Eis}

lemma lower_eq (d:CubeCuspData A p q) (hp:p≠0) :
    d.matrix 1 0=p^(3-d.exponent.val)*A 1 0 := by
  apply mul_left_cancel₀ (pow_ne_zero d.exponent.val hp)
  rw [←d.second,←mul_assoc,←pow_add,Nat.add_sub_of_le (by omega:d.exponent.val≤3)]

lemma unit_top (d:CubeCuspData A p q) (hp:p≠0) :
    IsUnit (Ideal.Quotient.mk (Ideal.span {p^(3-d.exponent.val)}) (d.matrix 0 0)) := by
  apply (isUnit_quotient_span_iff _ _).mpr
  refine ⟨-d.matrix 0 1*A 1 0,d.matrix 1 1,?_⟩
  have hd:d.matrix 0 0*d.matrix 1 1-d.matrix 0 1*d.matrix 1 0=1:=by
    simpa only [Matrix.det_fin_two] using d.matrix.property
  rw [d.lower_eq hp] at hd
  linear_combination hd

def stratum (d:CubeCuspData A p q) (hp:p≠0) : CubeResidueStrata p :=
  ⟨d.exponent,⟨Ideal.Quotient.mk _ (d.matrix 0 0),d.unit_top hp⟩⟩

lemma stratum_map (d:CubeCuspData A p q) (hp:p≠0) :
    cubeResidueStratumMap p (d.stratum hp)=
      Ideal.Quotient.mk (Ideal.span {p^3}) (A 0 0+3*q*A 1 0) := by
  apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
  apply Ideal.mem_span_singleton.mpr
  change p^3∣p^d.exponent.val*GaussianShiftedPartition.representative
    (p^(3-d.exponent.val)) (Ideal.Quotient.mk _ (d.matrix 0 0))-(A 0 0+3*q*A 1 0)
  rw [d.first,←mul_sub]
  have hpow:p^3=p^d.exponent.val*p^(3-d.exponent.val):=by
    rw [←pow_add,Nat.add_sub_of_le (by omega:d.exponent.val≤3)]
  rw [hpow]
  exact mul_dvd_mul_left _ (gaussRep_mk_congr _ _)

lemma comparison_phase (A2:levelTwo) (d:CubeCuspData (A2:SL(2,Eis)) p q)
    (hp:Prime p) (hprimary:lambda^2∣p-1)
    (hA:lambda^2∣((A2:SL(2,Eis)) 0 0)-1)
    (hC:IsCoprime ((A2:SL(2,Eis)) 1 0) p) :
    complexCharacter ⟨d.matrix*(A2:SL(2,Eis))⁻¹,d.congruent⟩ =
      cubeStratumSymbol p ((A2:SL(2,Eis)) 1 0) d.exponent (d.stratum hp.ne_zero).2 := by
  let N2:levelTwo:=⟨d.matrix,comparison_levelTwo A2 d.matrix d.congruent⟩
  have hN:lambda^2∣d.matrix 0 0-1:=comparison_primary _ _ d.congruent hA
  have he:=levelTwo_cube_comparison_phase A2 N2 p q d.exponent.val
    (by omega:d.exponent.val≤3) hprimary hA hN d.first (d.lower_eq hp.ne_zero) hC d.congruent
  rw [he]
  unfold cubeStratumSymbol
  rw [←map_pow,←cubicSymbol_pow_denominator]
  apply congrArg eisEmbedding
  apply symbol_congr
  have hd:=gaussRep_mk_congr (p^(3-d.exponent.val)) (d.matrix 0 0)
  change p^(3-d.exponent.val)∣d.matrix 0 0*((A2:SL(2,Eis)) 1 0)-
    GaussianShiftedPartition.representative (p^(3-d.exponent.val))
      (Ideal.Quotient.mk _ (d.matrix 0 0))*((A2:SL(2,Eis)) 1 0)
  convert (preTransparency := .instances) dvd_mul_of_dvd_left (dvd_neg.mpr hd) ((A2:SL(2,Eis)) 1 0) using 1 ; ring

end CubeCuspData
end CubicKubota

end

end OAI
end

section

namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

namespace CubicEisenstein

section
open scoped BigOperators Classical
open MeasureTheory
open Finset AddChar MulChar EisensteinEmbedding

section
local notation "Eis" => ActualEisensteinCubic.O

def finiteTranslationMultiplier {ι : Type*} [Fintype ι]
    (shift weight : ι→ℂ) (h : Eis) : ℂ :=
  ∑i,weight i*ShortDraftTrace.breveE (cuspFrequency h*shift i)

lemma finiteTranslationMultiplier_norm {ι : Type*} [Fintype ι]
    (shift weight : ι→ℂ) (h : Eis) :
    ‖finiteTranslationMultiplier shift weight h‖≤∑i,‖weight i‖ := by
  unfold finiteTranslationMultiplier
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  rw [norm_mul,breveE_norm,mul_one]

namespace SubexponentialBesselCoefficients

def finiteTranslate {ι : Type*} [Fintype ι] (coeff : SubexponentialBesselCoefficients)
    (shift weight : ι→ℂ) : SubexponentialBesselCoefficients where
  value h := finiteTranslationMultiplier shift weight h*coeff.value h
  growth epsilon he := by
    obtain ⟨C,hC,hbound⟩:=coeff.growth epsilon he
    refine ⟨(∑i,‖weight i‖)*C,by positivity,?_⟩
    intro h hh
    rw [norm_mul]
    calc
      _ ≤ (∑i,‖weight i‖)*(C*Real.exp (epsilon*‖cuspFrequency h‖)) :=
        mul_le_mul (finiteTranslationMultiplier_norm shift weight h) (hbound h hh)
          (norm_nonneg _) (Finset.sum_nonneg (fun _ _=>norm_nonneg _))
      _ = _ := by ring

end SubexponentialBesselCoefficients

end

section
local notation "Eis" => ActualEisensteinCubic.O

def finiteAdditiveFourierCoeff {R : Type*} [CommRing R] [Fintype R]
    (ψ : AddChar R ℂ) (φ : R→ℂ) (h : R) : ℂ :=
  (∑x,φ x*ψ (-h*x))/(Fintype.card R:ℂ)

def thetaFourierTranslation (c : Eis) (h : Eis⧸Ideal.span {c}) : ℂ :=
  ConcreteTraceCRT.eisLam^2*ConcreteTraceCRT.eisEmbedding (Quotient.out h)/
    ConcreteTraceCRT.eisEmbedding c

end

section
local notation "Eis" => ActualEisensteinCubic.O

def finiteConjugateSource {ι : Type*} [Fintype ι]
    (shift weight : ι→ℂ) (v : ℝ) (hv : 0<v) (z : ℂ) : ℂ :=
  ∑i,weight i*cubicSourceConjugateFunction (upperPoint (z+shift i) v hv)

def traceTwistedConjugateSource (c : Eis) (hc : c≠0)
    [Fintype (Eis⧸Ideal.span {c})] (φ : (Eis⧸Ideal.span {c})→ℂ)
    (v : ℝ) (hv : 0<v) (z : ℂ) : ℂ :=
  finiteConjugateSource (thetaFourierTranslation c)
    (finiteAdditiveFourierCoeff (quotientTrace c hc) φ) v hv z

end

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal CompletedGauss
local notation "Eis" => ActualEisensteinCubic.O

def fixedThetaTwist (Ψ : Eis→*ℂ) (x : Eis) : ℂ :=
  if lambda^2∣x-1 then eisEmbedding (symbol ramifiedTraceLambda x)*Ψ x else 0

def fixedThetaQuotient (Ψ : Eis→*ℂ) (c : Eis) (x : Eis⧸Ideal.span {c}) : ℂ :=
  fixedThetaTwist Ψ (Quotient.out x)

end

open ActualEisensteinCubic CompletedGauss CubicJacobiGlobal
local notation "Eis" => ActualEisensteinCubic.O

end CubicEisenstein

end

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge EisensteinSchwartzPoisson JointLogSeparation
noncomputable section

def rootSchwartz {ι : Type*} (U : ι → ℝ → ℂ)
    (hU : ∀ i, ContDiff ℝ ∞ (U i)) (hS : ∀ i, HasCompactSupport (U i))
    (i : ι) : 𝓢(ℝ, ℂ) := (hS i).toSchwartzMap (hU i)

@[simp] theorem rootSchwartz_apply {ι : Type*} (U : ι → ℝ → ℂ)
    (hU : ∀ i, ContDiff ℝ ∞ (U i)) (hS : ∀ i, HasCompactSupport (U i))
    (i : ι) (y : ℝ) : rootSchwartz U hU hS i y = U i y := rfl

def secondRootSchwartz (V : Fin 6 → ℝ → ℂ)
    (hV : ∀ i, ContDiff ℝ ∞ (V i)) (hS : ∀ i, HasCompactSupport (V i)) :
    Fin 6 → 𝓢(ℝ, ℂ) :=
  rootSchwartz (secondRootWindows V)
    (fun i => (secondRootWindows_smooth_compact V hV hS i).1)
    (fun i => (secondRootWindows_smooth_compact V hV hS i).2)

end
end SevenEighths.InverseMoment

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge JointLogSeparation EisensteinSchwartzPoisson
open SevenEighths.InverseMoment
open SevenEighths.InverseInitialProfile
open SevenEighths.InverseAmbientProfileTower
namespace SevenEighths.InverseSecondProfileUniform

def rooted (g : 𝓢(ℝ, ℂ)) (M a : ℝ)
    (hg : Function.support g ⊆ Set.Icc (-M) M) : 𝓢(ℝ, ℂ) :=
  InverseClippingProfiles.rootSchwartz g M 0 1 0 a 0 zero_lt_one (by simp) hg

@[simp] theorem rooted_apply (g : 𝓢(ℝ, ℂ)) (M a : ℝ)
    (hg : Function.support g ⊆ Set.Icc (-M) M) (y : ℝ) :
    rooted g M a hg y = (Real.exp (a*y) : ℂ)*g y := by
  simp [rooted, InverseClippingProfiles.rootedWindow, InverseClippingProfiles.logWindow]

def translated (g : 𝓢(ℝ, ℂ)) (ρ : ℝ) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.compSubConstCLM ℂ (-ρ) g

@[simp] theorem translated_apply (g : 𝓢(ℝ, ℂ)) (ρ y : ℝ) :
    translated g ρ y = g (y+ρ) := by simp [translated]

def normalization (ρ : Fin 6 → ℝ) (c₁ c₂ L : ℝ) : ℝ :=
  Real.exp (-6*L - ∑ i, InverseClippingProfiles.secondBalancedSlope i*ρ i +
    (Real.log c₁+Real.log c₂)/2)

def density (g : Fin 6 → 𝓢(ℝ, ℂ)) (g₁ g₂ b₃ : 𝓢(ℝ, ℂ))
    (ρ : Fin 6 → ℝ) (c₁ c₂ θ₁ θ₂ L : ℝ) (p : Ambient (Fin 6)) : ℂ :=
  (normalization ρ c₁ c₂ L : ℂ) *
    fullProfileDensity (fun i => translated (g i) (ρ i))
      (𝓕 (clippedTwist g₁ c₁ θ₁)) (𝓕 (clippedTwist g₂ c₂ θ₂)) b₃ p

def profile (g : Fin 6 → 𝓢(ℝ, ℂ)) (g₁ g₂ Φ : 𝓢(ℝ, ℂ))
    (ρ : Fin 6 → ℝ) (c₁ c₂ θ₁ θ₂ R L : ℝ) (y : Fin 6 → ℝ) : ℂ :=
  (normalization ρ c₁ c₂ L : ℂ) *
    ((∏ i, translated (g i) (ρ i) (y i)) *
      clippedTwist g₁ c₁ θ₁ (∑ i, secondLeftSlope i*y i) *
      clippedTwist g₂ c₂ θ₂ (∑ i, secondRightSlope i*y i) *
      paperRadialFourier Φ (R*Real.exp (∑ i, secondKernelSlope i*y i)))

def positiveSource (g : 𝓢(ℝ, ℂ)) (c θ x : ℝ) : ℂ :=
  logPhase θ (Real.log x)*g (Real.log x+Real.log c)

end SevenEighths.InverseSecondProfileUniform

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge JointLogSeparation EisensteinSchwartzPoisson
open SevenEighths.InverseMoment
open SevenEighths.InverseInitialProfile
open SevenEighths.InverseAmbientProfileTower
namespace SevenEighths.InverseMomentFirstProfileUniform

def rooted (g : 𝓢(ℝ, ℂ)) (M a : ℝ)
    (hg : Function.support g ⊆ Set.Icc (-M) M) : 𝓢(ℝ, ℂ) :=
  InverseClippingProfiles.rootSchwartz g M 0 1 0 a 0 zero_lt_one (by simp) hg

@[simp] theorem rooted_apply (g : 𝓢(ℝ, ℂ)) (M a : ℝ)
    (hg : Function.support g ⊆ Set.Icc (-M) M) (y : ℝ) :
    rooted g M a hg y = (Real.exp (a*y) : ℂ)*g y := by
  simp [rooted, InverseClippingProfiles.rootedWindow, InverseClippingProfiles.logWindow]

def translated (g : 𝓢(ℝ, ℂ)) (ρ : ℝ) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.compSubConstCLM ℂ (-ρ) g

@[simp] theorem translated_apply (g : 𝓢(ℝ, ℂ)) (ρ y : ℝ) :
    translated g ρ y = g (y+ρ) := by simp [translated]

def normalization (ρ : Fin 9 → ℝ) (c₁ c₂ L : ℝ) : ℝ :=
  Real.exp (-(9/2:ℝ)*L - ∑ i, InverseClippingProfiles.firstBalancedSlope i*ρ i +
    (Real.log c₁+Real.log c₂)/2)

def density (g : Fin 9 → 𝓢(ℝ, ℂ)) (g₁ g₂ b₃ : 𝓢(ℝ, ℂ))
    (ρ : Fin 9 → ℝ) (c₁ c₂ θ₁ θ₂ L : ℝ) (p : Ambient (Fin 9)) : ℂ :=
  (normalization ρ c₁ c₂ L : ℂ) *
    fullProfileDensity (fun i => translated (g i) (ρ i))
      (𝓕 (clippedTwist g₁ c₁ θ₁)) (𝓕 (clippedTwist g₂ c₂ θ₂)) b₃ p

def profile (g : Fin 9 → 𝓢(ℝ, ℂ)) (g₁ g₂ Φ : 𝓢(ℝ, ℂ))
    (ρ : Fin 9 → ℝ) (c₁ c₂ θ₁ θ₂ R L : ℝ) (y : Fin 9 → ℝ) : ℂ :=
  (normalization ρ c₁ c₂ L : ℂ) *
    ((∏ i, translated (g i) (ρ i) (y i)) *
      clippedTwist g₁ c₁ θ₁ (∑ i, firstLeftSlope i*y i) *
      clippedTwist g₂ c₂ θ₂ (∑ i, firstRightSlope i*y i) *
      paperRadialFourier Φ (R*Real.exp (∑ i, firstKernelSlope i*y i)))

def positiveSource (g : 𝓢(ℝ, ℂ)) (c θ x : ℝ) : ℂ :=
  logPhase θ (Real.log x)*g (Real.log x+Real.log c)

end SevenEighths.InverseMomentFirstProfileUniform

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.HeckeFamily

instance instIsPrincipalIdealRingO_solutions_p2 : IsPrincipalIdealRing O := IsCyclotomicExtension.Rat.three_pid K

theorem idealCoeff_product (χ ψ : Character) (I : Ideal O) :
    idealCoeff (χ.product ψ) I = idealCoeff χ I * idealCoeff ψ I :=
  IdealCharacter.ofResidue_product _ _ _ _ _ _ I

end SevenEighths.HeckeFamily

end

end OAI
end

section

namespace OAI

noncomputable section
namespace SevenEighths.HeckeFamily

instance instIsPrincipalIdealRingO_solutions_p0 : IsPrincipalIdealRing O := IsCyclotomicExtension.Rat.three_pid K

theorem idealCoeff_norm_le_one (χ : Character) (I : Ideal O) : ‖idealCoeff χ I‖ ≤ 1 := by
  let : Finite (O ⧸ χ.modulus) := Ring.HasFiniteQuotients.finiteQuotient χ.modulus_ne_bot
  exact IdealCharacter.norm_ofResidue_le_one χ.modulus χ.residue χ.unit_trivial I

theorem idealTerm_eq_weighted (χ : Character) (s : ℂ) (I : Ideal O) :
    idealTerm χ s I = IdealEuler.weighted (idealCoeff χ) s I := by
  change idealCoeff χ I / (Ideal.absNorm I : ℂ)^s =
    idealCoeff χ I * CubicEisenstein.fullIdealWeight s I
  by_cases hI : I = 0
  · rw [hI, map_zero]
    simp
  · simp only [CubicEisenstein.fullIdealWeight, hI, ite_false,
      Complex.cpow_neg, div_eq_mul_inv]

theorem LFunction_eq_series (χ : Character) {s : ℂ} (hs : 1 < s.re) :
    LFunction χ s = IdealEuler.series (idealCoeff χ) s := by
  rw [LFunction_eq_ideal_tsum χ hs]
  exact tsum_congr (idealTerm_eq_weighted χ s)

theorem LFunction_ne_zero_of_one_lt_re (χ : Character) {s : ℂ} (hs : 1 < s.re) :
    LFunction χ s ≠ 0 := by
  rw [LFunction_eq_series χ hs]
  exact IdealEuler.series_ne_zero (idealCoeff χ) (idealCoeff_norm_le_one χ) s hs

end SevenEighths.HeckeFamily

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.HeckeFiniteDeletion
open HeckeFamily HeckeReciprocal

def factors (M : Ideal O) (ψ : Character) : ℂ → ℂ :=
  EulerFactors.deletedProduct (SmoothMobiusCorrection.primeSet M)
    (fun P => Ideal.absNorm P.val) (fun P => idealCoeff ψ P.val)

end SevenEighths.HeckeFiniteDeletion

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentHeckeTwist
open HeckeFamily
open CenteredMomentLattice CenteredMomentTwist
open EisensteinSchwartzPoisson
local notation "O" => ActualEisensteinCubic.O

def twistedIdealSum (χ : Character) (W : ℝ → ℂ) (t X : ℝ) : ℂ :=
  ∑' I : Ideal O, idealCoeff χ I*(Ideal.absNorm I:ℂ)^(Complex.I*t)*W ((Ideal.absNorm I:ℝ)/X)

end SevenEighths.CenteredMomentHeckeTwist

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentHeckeHeight
open HeckeFamily CenteredMomentHeckeTwist
open CenteredMomentLattice CenteredMomentTwist
open QuadraticInitialBound EisensteinSchwartzPoisson
local notation "O" => ActualEisensteinCubic.O

def rowTwistedSum (η : Character) (m A₀ z : O) (W : ℝ → ℂ) (t X : ℝ) : ℂ :=
  ∑' I : Ideal O, (idealCoeff η I*CanonicalRowCompletion.idealRowHom (m^6*(A₀*z)) I)*
    (Ideal.absNorm I:ℂ)^(Complex.I*t)*W ((Ideal.absNorm I:ℝ)/X)

end SevenEighths.CenteredMomentHeckeHeight

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentHeckeSlots
open HeckeFamily CenteredMomentHeckeHeight CenteredMomentTwist
local notation "O" => ActualEisensteinCubic.O

def rowSlot (η : Character) (m A z : O) (S : Finset (Ideal O))
    (β : Ideal O → ℂ) (t : ℝ) : ℂ :=
  ∑ P ∈ S, β P * (idealCoeff η P * CanonicalRowCompletion.idealRowHom (m^6*(A*z)) P) *
    (Ideal.absNorm P:ℂ)^(Complex.I*t)

variable {ι : Type*} [Fintype ι]

def centeredSlotRow (η : Character) (m A z : O) (W₁ W₂ : ℝ → ℂ)
    (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ)
    (p : ι → ℝ) (t X₁ X₂ Y₁ Y₂ T : ℝ) : ℂ :=
  (Real.sqrt (T*∏ i,p i):ℂ)⁻¹ *
    ((rowTwistedSum η m A z W₁ t X₁*rowTwistedSum η m A z W₂ t X₂-
      rowTwistedSum η m A z W₁ t Y₁*rowTwistedSum η m A z W₂ t Y₂)*
      ∏ i,rowSlot η m A z (S i) (β i) t)

end SevenEighths.CenteredMomentHeckeSlots

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentHeckeExpansion
open HeckeFamily CenteredMomentHeckeHeight CenteredMomentHeckeSlots
open CenteredMomentRectangle CenteredMomentPrimary CenteredMomentTwist
local notation "O" => ActualEisensteinCubic.O

def rowWeight (η : Character) (m A z : O) (t : ℝ) : Ideal O →*₀ ℂ where
  toFun I := (idealCoeff η I*CanonicalRowCompletion.idealRowHom (m^6*(A*z)) I)*
    (Ideal.absNorm I:ℂ)^(Complex.I*t)
  map_one' := by simp only [map_one,Nat.cast_one,Complex.one_cpow,one_mul]
  map_zero' := by simp only [map_zero,zero_mul,mul_zero]
  map_mul' I J := by
    have hpow : ((Ideal.absNorm I:ℂ)*(Ideal.absNorm J:ℂ))^(Complex.I*t) =
        (Ideal.absNorm I:ℂ)^(Complex.I*t)*(Ideal.absNorm J:ℂ)^(Complex.I*t) := by
      exact_mod_cast Complex.mul_cpow_ofReal_nonneg
        (Nat.cast_nonneg (Ideal.absNorm I) : (0:ℝ) ≤ Ideal.absNorm I)
        (Nat.cast_nonneg (Ideal.absNorm J) : (0:ℝ) ≤ Ideal.absNorm J) (Complex.I*t)
    simp only [map_mul,Nat.cast_mul,hpow]
    ring

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

end SevenEighths.CenteredMomentHeckeExpansion

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSourceRow
open CenteredMomentHeckeExpansion HeckeFamily CanonicalRowCompletion
open CanonicalQuadraticSieve ConcretePrimeRowBridge CompletedGauss
local notation "O" => ActualEisensteinCubic.O

def supportedColumns (S : Finset (Ideal O)) : Finset (Ideal O) := S.filter Supported

theorem primary_span_supported (I : Ideal O) (hI : Supported I) : Ideal.span {primaryGenerator I}=I := by
  have hn : primaryGenerator I ≠ 0 := by
    have hs : Supported (Ideal.span {idealGenerator I}) := by rw [span_idealGenerator]; exact hI
    have hg := (PrimaryIdealUnitReindex.primaryGenerator_span_ne_zero_iff (idealGenerator I)).mpr
      ((supported_span_iff _).mp hs).1
    simpa only [span_idealGenerator] using hg
  exact (primaryGenerator_spec I hn).1

def sourceGenerator (S : Finset (Ideal O)) (I : supportedColumns S) : O := primaryGenerator I

theorem sourceGenerator_supported (S : Finset (Ideal O)) (I : supportedColumns S) :
    Supported (Ideal.span {sourceGenerator S I}) := by
  have hI := (Finset.mem_filter.mp I.property).2
  rw [sourceGenerator,primary_span_supported I hI]
  exact hI

def finiteHeckeEnergy (η : Character) (m A : O) (t : ℝ)
    (S : Finset (Ideal O)) (c : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) : ℂ :=
  ∑' z : O,((‖∑ I∈S,c I*rowWeight η m A z t I‖^2:ℝ):ℂ)*
    W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)

end SevenEighths.CenteredMomentSourceRow

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff FourierTransform
open MeasureTheory

namespace SevenEighths.CenteredMomentHeckeColumnWindow
open FourierBridge HeckeFamily CenteredMomentSmooth
open CenteredMomentTwist
local notation "O" => ActualEisensteinCubic.O

def heightCoeff (τ : Character) (t : ℝ) (I : Ideal O) : ℂ :=
  idealCoeff τ I*(Ideal.absNorm I:ℂ)^(Complex.I*t)

def rootProfile (V : ℝ → ℂ) (hVc : HasCompactSupport V) (hVs : ContDiff ℝ ∞ V) : 𝓢(ℝ,ℂ) :=
  (hVc.mul_right (f':=fun u : ℝ => (Real.exp (-u/2):ℂ))).toSchwartzMap
    (hVs.mul (Complex.ofRealCLM.contDiff.comp
      (Real.contDiff_exp.comp (contDiff_id.neg.div_const 2))))

def columnDensity (V : ℝ → ℂ) (hVc : HasCompactSupport V) (hVs : ContDiff ℝ ∞ V) : 𝓢(ℝ,ℂ) :=
  𝓕 (rootProfile V hVc hVs)

end SevenEighths.CenteredMomentHeckeColumnWindow

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseMomentFirstSecondHeightCost
open InverseMoment InverseAmbientProfileTower JointLogSeparation FourierBridge
open InverseMomentFirstOriginalProfile

def firstDegree (degree : ℕ) : ℕ := 2*InverseClippingProfiles.momentOrder (2*degree)

def firstHeight (negative : Bool) (z : Frequency×(Fin 9→ℝ)) : ℝ :=
  profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 (if negative then 7 else 8)

def stepBudget (C Cbin Czero Ctail A Z F eta tau pi epschild saving : ℝ) : ℝ :=
  Czero*Z^(F+17*eta+tau+pi)+
    C*A*(1+Cbin*Real.log Z)^4*Z^(F+48*eta+tau+pi+epschild)+Ctail*Z^(-saving)

end SevenEighths.InverseMomentFirstSecondHeightCost
end

end OAI
end

section

namespace OAI

noncomputable section
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open ProbeEuler ProbeRow ConcretePrimeRowBridge
local notation "O" => ActualEisensteinCubic.O

lemma supported_primeGenerator_prime (P : PrimeIdeal) (hs : Supported P.val) :
    Prime (primaryGenerator P.val) := by
  apply (Ideal.span_singleton_prime (supported_primaryGenerator_ne_zero P.val hs)).mp
  rw [span_primaryGenerator_of_supported P.val hs]
  exact Ideal.isPrime_of_prime P.property

def idealClosedCorrection (η : HeckeFamily.Character) (P : PrimeIdeal) (x w z : ℂ) : ℂ :=
  unramifiedClosed (Ideal.absNorm P.val) (actualAPhase η (primaryGenerator P.val))
    (HeckeFamily.idealCoeff η P.val) 1 x w z

end SevenEighths.ProbePhysical
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.HeckeFamily
local instance instIsPrincipalIdealRingO_solutions : IsPrincipalIdealRing O := IsCyclotomicExtension.Rat.three_pid K

def Character.refineModulus (η : Character) (M : Ideal O) (hM : M ≠ ⊥)
    (hle : M ≤ η.modulus) : Character :=
  Character.ofResidue M hM (ResidueCharacter.inflate hle η.residue)
    (ResidueCharacter.inflate_global_units hle η.residue η.unit_trivial)

theorem idealCoeff_refineModulus (η : Character) (M : Ideal O) (hM : M ≠ ⊥)
    (hle : M ≤ η.modulus) (I : Ideal O) :
    idealCoeff (η.refineModulus M hM hle) I =
      if IsCoprime I M then idealCoeff η I else 0 :=
  IdealCharacter.ofResidue_source_mask M η.modulus _ _ _ _
    (ResidueCharacter.inflate_mk hle η.residue) I

theorem idealCoeff_source_mask (η : Character) (I : Ideal O) :
    idealCoeff η I = if IsCoprime I η.modulus then idealCoeff η I else 0 := by
  apply IdealCharacter.ofResidue_source_mask η.modulus η.modulus η.residue η.residue
    η.unit_trivial η.unit_trivial _ I
  intro n
  split_ifs with hn
  · rfl
  · exact MulChar.map_nonunit _ hn

def Character.excludePrimes (η : Character) (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) : Character :=
  η.refineModulus (η.modulus * ∏ P ∈ S, P)
    (mul_ne_zero η.modulus_ne_bot (Finset.prod_ne_zero_iff.mpr (fun P hP => (hS P hP).ne_zero)))
    Ideal.mul_le_left

theorem idealCoeff_excludePrimes (η : Character) (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (I : Ideal O) :
    idealCoeff (η.excludePrimes S hS) I =
      if ∀ P ∈ S, IsCoprime I P then idealCoeff η I else 0 := by
  rw [Character.excludePrimes, idealCoeff_refineModulus, IsCoprime.mul_right_iff,
    IsCoprime.prod_right_iff]
  by_cases hη : IsCoprime I η.modulus
  · simp only [hη, true_and]
  · have hz : idealCoeff η I = 0 := by simpa only [hη, ite_false] using idealCoeff_source_mask η I
    simp [hη, hz]

end SevenEighths.HeckeFamily

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.HeckeOrigin
open HeckeFamily HeckeTheta

def poleRemoved (χ : Character) (s : ℂ) : ℂ :=
  (Real.pi : ℂ)^s * (Complex.Gamma (s+1))⁻¹ *
    HeckeMellinIdentity.regularized (pair (coefficients χ)) s / 6

theorem poleRemoved_entire (χ : Character) : Differentiable ℂ (poleRemoved χ) := by
  have hGamma : Differentiable ℂ (fun s : ℂ => (Complex.Gamma (s+1))⁻¹) :=
    Complex.differentiable_one_div_Gamma.comp (differentiable_id.add_const 1)
  exact (((differentiable_id.const_cpow (Or.inl
    (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))).mul hGamma).mul
      (HeckeMellinIdentity.regularized_entire _)).div_const 6

theorem poleRemoved_eq (χ : Character) {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    poleRemoved χ s = (s-1) * LFunction χ s := by
  unfold poleRemoved LFunction continuedLattice latticeL completed
  rw [HeckeMellinIdentity.regularized_eq _ (pair_k _) h0 h1,
    Complex.Gamma_add_one s h0, mul_inv_rev]
  field_simp

theorem poleRemoved_one (χ : Character) :
    poleRemoved χ 1 = HeckeReciprocal.regularizedL χ 1 := by
  rw [HeckeReciprocal.regularizedL_at_one]
  simp [poleRemoved, HeckeMellinIdentity.regularized,
    Complex.Gamma_add_one 1 one_ne_zero,
    show (pair (coefficients χ)).ε = 1 from rfl]

theorem poleRemoved_one_ne_zero (χ : Character) (hχ : χ.residue = 1) :
    poleRemoved χ 1 ≠ 0 := by
  rw [poleRemoved_one]
  exact HeckeReciprocal.regularizedL_ne_zero_at_one χ hχ

def continued (χ : Character) (s : ℂ) : ℂ :=
  if χ.residue = 1 then poleRemoved χ s / (s-1) else LFunction χ s

end SevenEighths.HeckeOrigin

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical Topology
namespace SevenEighths.HeckeLogDerivative
open HeckeFamily

def coeff (χ : Character) : ℕ → ℂ := IdealLogDerivative.coeff (idealCoeff χ)

end SevenEighths.HeckeLogDerivative

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.HeckeRayFamily
open HeckeFamily

variable (M : Ideal O) [NeZero M]
local instance instFiniteQuotientOIdeal_solutions : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
local instance instIsPrincipalIdealRingO_solutions : IsPrincipalIdealRing O := IsCyclotomicExtension.Rat.three_pid K

def character (χ : RayOrthogonality.rayCharacters M) : Character :=
  Character.ofResidue M (NeZero.ne M) χ.val ((RayOrthogonality.mem_rayCharacters_iff M χ.val).mp χ.property)

theorem idealCoeff_character (χ : RayOrthogonality.rayCharacters M) (I : Ideal O) :
    idealCoeff (character M χ) I = RayOrthogonality.idealCharacter M χ I := rfl

end SevenEighths.HeckeRayFamily

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic HeckeFamily
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma fixedPrimeProduct_ne_zero (S : Finset Id) (hS : ∀P∈S,Prime P) :
    (∏P∈S,P)≠0 := Finset.prod_ne_zero_iff.mpr (fun P hP=>(hS P hP).ne_zero)

def fixedSourcePrincipal (S : Finset Id) (hS : ∀P∈S,Prime P) : Character :=
  letI : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS⟩
  HeckeRayFamily.character (∏P∈S,P) 1

lemma prime_coprime_fixedProduct (S : Finset Id) (hS : ∀P∈S,Prime P) (P : PrimeIdeal) :
    IsCoprime P.val (∏Q∈S,Q) ↔ P.val∉S := by
  rw [IsCoprime.prod_right_iff]
  constructor
  · intro h hP
    exact P.property.not_isUnit (isCoprime_self.mp (h P.val hP))
  · intro h Q hQ
    exact primeIdeal_coprime P ⟨Q,hS Q hQ⟩ (fun he=>h ((congrArg Subtype.val he).symm ▸ hQ))

lemma fixedSourcePrincipal_prime (S : Finset Id) (hS : ∀P∈S,Prime P) (P : PrimeIdeal) :
    idealCoeff (fixedSourcePrincipal S hS) P.val=if P.val∈S then 0 else 1 := by
  unfold fixedSourcePrincipal
  rw [HeckeRayFamily.idealCoeff_character,RayOrthogonality.idealCharacter_one]
  change (if P.val=0 then (0:ℂ) else if IsCoprime P.val (∏Q∈S,Q) then 1 else 0)=_
  simp only [P.property.ne_zero,ite_false,prime_coprime_fixedProduct S hS P]
  split_ifs <;> simp_all

lemma excludedTarget_prime (η : Character) (S : Finset Id) (hS : ∀P∈S,Prime P) (P : PrimeIdeal) :
    idealCoeff (η.excludePrimes S hS) P.val=if P.val∈S then 0 else idealCoeff η P.val := by
  rw [idealCoeff_excludePrimes]
  have he : (∀Q∈S,IsCoprime P.val Q) ↔ P.val∉S := by
    rw [←IsCoprime.prod_right_iff]
    exact prime_coprime_fixedProduct S hS P
  simp only [he]
  split_ifs <;> simp_all

end SevenEighths.ProbePhysical
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic ProbeEuler CompletedGauss
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def globalPrimeDefectBound (P : PrimeIdeal) : ℝ :=
  240*(Ideal.absNorm P.val:ℝ)^(-(17/10:ℝ))

def globalClosedCorrection (η : HeckeFamily.Character) (S : Finset Id) (x w z : ℂ) : ℂ :=
  ∏' P : {P : PrimeIdeal // P.val∉S},idealClosedCorrection η P.val x w z

lemma globalPrimeDefectBound_nonneg (P : PrimeIdeal) : 0≤globalPrimeDefectBound P := by
  unfold globalPrimeDefectBound
  positivity

lemma globalPrimeDefectBound_summable : Summable globalPrimeDefectBound := by
  have h := (CubicEisenstein.fullIdealWeight_summable_norm ((17/10:ℝ):ℂ) (by norm_num)).comp_injective
    (Subtype.val_injective : Function.Injective (fun P : PrimeIdeal=>P.val))
  apply (h.mul_left 240).congr
  intro P
  change 240*‖CubicEisenstein.fullIdealWeight ((17/10:ℝ):ℂ) P.val‖=globalPrimeDefectBound P
  unfold globalPrimeDefectBound CubicEisenstein.fullIdealWeight
  simp only [P.property.ne_zero,ite_false]
  rw [Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr P.property.ne_zero))]
  norm_num

structure CorrectionTail (S : Finset Id) : Prop where
  norm_four : ∀P : PrimeIdeal,P.val∉S → 4≤Ideal.absNorm P.val
  small : (∑' P : {P : PrimeIdeal // P.val∉S},globalPrimeDefectBound P.val)≤1/6

lemma CorrectionTail.summable {S : Finset Id} (_h : CorrectionTail S) :
    Summable (fun P : {P : PrimeIdeal // P.val∉S}=>globalPrimeDefectBound P.val) :=
  globalPrimeDefectBound_summable.subtype _

end SevenEighths.ProbePhysical
end

end OAI
end

section

namespace OAI

noncomputable section
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open ProbeEuler ProbeRow ConcretePrimeRowBridge
local notation "O" => ActualEisensteinCubic.O

def idealMarkedClosed (η : HeckeFamily.Character) (P : PrimeIdeal) (x w z : ℂ) : ℂ :=
  let Q : ℝ := Ideal.absNorm P.val
  let R := coordR Q (actualAPhase η (primaryGenerator P.val)) x z
  markedFactor R (coordV Q z) (Q:ℂ)⁻¹ (coordK Q (HeckeFamily.idealCoeff η P.val) x w)
    (-coordD Q (HeckeFamily.idealCoeff η P.val) 1 x+coordW Q 1 w*R) 1

end SevenEighths.ProbePhysical
end

end OAI
end

section

namespace OAI

noncomputable section
open MeasureTheory Set Filter Complex
open scoped Topology
namespace SevenEighths.PrincipalMellinResidues
open ProbePhysical

structure BoundaryControl (F : ℂ → ℂ) (a b : ℝ) : Prop where
  left : Integrable (fun t : ℝ => F ((a:ℂ)+t*I))
  right : Integrable (fun t : ℝ => F ((b:ℂ)+t*I))
  lower : Tendsto (fun T : ℝ => ∫ x : ℝ in a..b, F ((x:ℂ)+(-T)*I)) atTop (𝓝 0)
  upper : Tendsto (fun T : ℝ => ∫ x : ℝ in a..b, F ((x:ℂ)+T*I)) atTop (𝓝 0)

open HeckeFamily

abbrev fixedPrincipal (M : Ideal O) [NeZero M] : Character :=
  HeckeRayFamily.character M 1

def fixedPrincipalResidue (M : Ideal O) [NeZero M] : ℂ :=
  HeckeReciprocal.regularizedL (fixedPrincipal M) 1

def sourceMultiplier (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ)
    (eta : Character) (s : ℂ) (H B : ℂ → ℂ → ℂ) (w z : ℂ) : ℂ :=
  (X:ℂ)^(1/2-z) * (Z:ℂ)^(s+z-1) * (Y:ℂ)^(w-1) *
    Complex.exp ((s+z-1)^2) *
    mellin (EisensteinSchwartzPoisson.paperRadialFourier W0) z * mellin W1 w /
      LFunction eta s * H w z * B w z

def sourceResidueConstant (W0 W1 : SchwartzMap ℝ ℂ) (M : Ideal O) [NeZero M] : ℂ :=
  mellin W1 1 * mellin (EisensteinSchwartzPoisson.paperRadialFourier W0) (1/6) *
    fixedPrincipalResidue M ^ 2 / 6

end SevenEighths.PrincipalMellinResidues

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators
namespace SevenEighths.HeckePrimitive
open HeckeFamily

variable (c : O) [NeZero c]

theorem span_ne_bot : Ideal.span ({c} : Set O) ≠ ⊥ := by
  simpa only [ne_eq, Ideal.span_singleton_eq_bot] using NeZero.ne c

instance instFintypeQuotientOIdealSpanSingletonSet_solutions : Fintype (O ⧸ Ideal.span {c}) := by
  letI : Finite (O ⧸ Ideal.span {c}) := Ring.HasFiniteQuotients.finiteQuotient (span_ne_bot c)
  exact Fintype.ofFinite _

def character (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hu : ∀ u : Oˣ, χ (Ideal.Quotient.mk (Ideal.span {c}) (u : O)) = 1) : Character :=
  Character.ofResidue (Ideal.span {c}) (span_ne_bot c) χ hu

omit [NeZero c] in
theorem inverse_unit_trivial (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hu : ∀ u : Oˣ, χ (Ideal.Quotient.mk (Ideal.span {c}) (u : O)) = 1) :
    ∀ u : Oˣ, χ⁻¹ (Ideal.Quotient.mk (Ideal.span {c}) (u : O)) = 1 := by
  intro u
  rw [MulChar.inv_apply_eq_inv', hu, inv_one]

def scale : ℝ := GaussianTheta.parameter c 1

theorem scale_pos : 0 < scale c := GaussianTheta.parameter_pos c 1 zero_lt_one

omit [NeZero c] in
theorem parameter_eq_scale_mul (t : ℝ) : GaussianTheta.parameter c t = scale c * t := by
  unfold scale GaussianTheta.parameter
  ring

theorem gaussianTheta_eq (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hu : ∀ u : Oˣ, χ (Ideal.Quotient.mk (Ideal.span {c}) (u : O)) = 1) (t : ℝ) :
    GaussianTheta.theta c χ t = HeckeTheta.theta (coefficients (character c χ hu))
      (scale c * t) := by
  unfold GaussianTheta.theta HeckeTheta.theta
  rw [← coordinateEquiv.tsum_eq]
  apply tsum_congr
  intro n
  rw [periodicCoeff_eq_elementCoeff]
  change χ (Ideal.Quotient.mk (Ideal.span {c}) (coordinateElement n.1 n.2)) *
      GaussianTheta.gaussian (GaussianTheta.parameter c t)
        (ConcreteTraceCRT.eisEmbedding (coordinateElement n.1 n.2)) = _
  congr 1
  unfold GaussianTheta.gaussian
  rw [Complex.ofReal_exp]
  congr 1
  rw [← Complex.ofReal_pow, ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span,
    ← normForm_eq_absNorm_span, parameter_eq_scale_mul]
  push_cast
  ring

def pair (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hu : ∀ u : Oˣ, χ (Ideal.Quotient.mk (Ideal.span {c}) (u : O)) = 1)
    (hp : FiniteFourier.IsPrimitiveOnIdeals χ) : WeakFEPair ℂ :=
  PeriodicThetaRegularity.primitivePair
    (coefficients (character c χ hu))
    (coefficients (character c χ⁻¹ (inverse_unit_trivial c χ hu)))
    (scale c) (scale_pos c) (TraceCharacter.normalizedGauss c χ)
    (GaussianTheta.theta_root_nonzero c χ hp) (by
      intro t ht
      have h := GaussianTheta.theta_inversion c χ hp t ht
      rw [gaussianTheta_eq c χ hu,
        gaussianTheta_eq c χ⁻¹ (inverse_unit_trivial c χ hu)] at h
      simpa only [mul_one_div] using h)

@[simp] theorem pair_f (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hu : ∀ u : Oˣ, χ (Ideal.Quotient.mk (Ideal.span {c}) (u : O)) = 1)
    (hp : FiniteFourier.IsPrimitiveOnIdeals χ) (t : ℝ) :
    (pair c χ hu hp).f t = GaussianTheta.theta c χ t :=
  (gaussianTheta_eq c χ hu t).symm

@[simp] theorem pair_g (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hu : ∀ u : Oˣ, χ (Ideal.Quotient.mk (Ideal.span {c}) (u : O)) = 1)
    (hp : FiniteFourier.IsPrimitiveOnIdeals χ) (t : ℝ) :
    (pair c χ hu hp).g t = GaussianTheta.theta c χ⁻¹ t :=
  (gaussianTheta_eq c χ⁻¹ (inverse_unit_trivial c χ hu) t).symm

def completedL (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hu : ∀ u : Oˣ, χ (Ideal.Quotient.mk (Ideal.span {c}) (u : O)) = 1)
    (hp : FiniteFourier.IsPrimitiveOnIdeals χ) (s : ℂ) : ℂ :=
  (pair c χ hu hp).Λ s / 6

end SevenEighths.HeckePrimitive

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical Topology
namespace SevenEighths.HeckePresentation
open HeckeFamily

def generator (η : Character) : O := ConcretePrimeRowBridge.idealGenerator η.modulus

instance instNeZeroOGenerator (η : Character) : NeZero (generator η) :=
  ⟨ConcretePrimeRowBridge.idealGenerator_ne_zero η.modulus η.modulus_ne_bot⟩

theorem span_generator (η : Character) : Ideal.span {generator η} = η.modulus :=
  ConcretePrimeRowBridge.span_idealGenerator η.modulus

def quotientEquiv (η : Character) : (O ⧸ Ideal.span {generator η}) ≃+* (O ⧸ η.modulus) :=
  Ideal.quotEquivOfEq (span_generator η)

def principalResidue (η : Character) : MulChar (O ⧸ Ideal.span {generator η}) ℂ :=
  CharacterTransport.pullback (quotientEquiv η) η.residue

@[simp] theorem principalResidue_mk (η : Character) (z : O) :
    principalResidue η (Ideal.Quotient.mk (Ideal.span {generator η}) z) =
      elementCoeff η z := by
  simp only [principalResidue, CharacterTransport.pullback_apply, quotientEquiv,
    Ideal.quotEquivOfEq_mk, elementCoeff]

theorem principalResidue_unit (η : Character) (u : Oˣ) :
    principalResidue η (Ideal.Quotient.mk (Ideal.span {generator η}) (u : O)) = 1 := by
  rw [principalResidue_mk]
  exact η.unit_trivial u

def principalCharacter (η : Character) : Character :=
  HeckePrimitive.character (generator η) (principalResidue η) (principalResidue_unit η)

@[simp] theorem principalCharacter_elementCoeff (η : Character) (z : O) :
    elementCoeff (principalCharacter η) z = elementCoeff η z := principalResidue_mk η z

end SevenEighths.HeckePresentation

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical Topology
open Set MeasureTheory
namespace SevenEighths.HeckePrincipalStrip
open HeckeFamily HeckeTheta

def normalized (η : Character) (s : ℂ) : ℂ := HeckeOrigin.poleRemoved η s / (s+2)

def sourceNormalized (η : Character) (s : ℂ) : ℂ :=
  HeckeOrigin.poleRemoved η s / (s+1)

end SevenEighths.HeckePrincipalStrip

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
open Complex Set MeasureTheory
namespace SevenEighths.ProbeFiniteProductBounds
open ActualEisensteinCubic CompletedGauss ProbePhysical ProbeEuler ProbeLocal
open HeckeFamily PrincipalMellinResidues ProbeMellinBoundary
local notation "Id" => Ideal ActualEisensteinCubic.O

def localMultiplier (η : Character) (P : PrimeIdeal) (x w z : ℂ) : ℂ :=
  let Q : ℝ := Ideal.absNorm P.val
  (Q : ℂ)^(z-1) *
    (compensatedReplacement (coordV Q z) (coordW Q 1 w)
      (coordD Q (idealCoeff η P.val) 1 x) (idealMarkedClosed η P x w z)
      (star (idealCoeff η P.val)*(Q : ℂ)^x) ((Q : ℂ)^(-w)) /
      idealClosedCorrection η P x w z)

def slotMultiplier {ι : Type*} (η : Character) (J : Finset ι)
    (T : ι → Finset PrimeIdeal) (b : ι → PrimeIdeal → ℂ) (x w z : ℂ) : ℂ :=
  ∏ j ∈ J, ∑ P ∈ T j, b j P * localMultiplier η P x w z

def localBound (Bx Bz : ℝ) (P : PrimeIdeal) : ℝ :=
  (Ideal.absNorm P.val : ℝ)^(Bz-1) * (400*(1+(Ideal.absNorm P.val : ℝ)^Bx))

def slotBound {ι : Type*} (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (Bx Bz : ℝ) : ℝ :=
  ∏ j ∈ J, ∑ P ∈ T j, ‖b j P‖ * localBound Bx Bz P

def windowMultiplier {ι : Type*} (η : Character) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (W : ι → ℝ → ℂ) (scale : ι → ℝ) (s w z : ℂ) : ℂ :=
  slotMultiplier η J T (fun j P => W j ((Ideal.absNorm P.val : ℝ)/scale j)) s w z

@[simp] theorem slotMultiplier_empty {ι : Type*} (η : Character) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (s w z : ℂ) : slotMultiplier η ∅ T b s w z = 1 := by
  simp [slotMultiplier]

end SevenEighths.ProbeFiniteProductBounds
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical ContDiff Topology SchwartzMap
open Filter Set
namespace SevenEighths.ProbePhysical

def gaussianFixedWindow (y : ℝ) : ℂ := gaussianAnnulus y/(Real.sqrt y:ℂ)

lemma gaussianProfile_scaled_smooth (r : ℝ) (hr : 0< r) (y : ℝ) (hy : 0<y) :
    ContDiffAt ℝ ∞ (fun x : ℝ=>gaussianMellinProfile (r*x)) y := by
  have hf : ContDiffAt ℂ ∞ (fun z : ℂ=>gaussianLog ((r:ℂ)*z)) (y:ℂ) :=
    (gaussianLog_scaled_analytic r hr (y:ℂ) hy).contDiffAt
  have hh := (hf.restrict_scalars ℝ).comp y Complex.ofRealCLM.contDiff.contDiffAt
  simpa only [Function.comp_def,Complex.ofRealCLM_apply,←Complex.ofReal_mul,gaussianLog_ofReal] using hh

end SevenEighths.ProbePhysical
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical ContDiff Topology SchwartzMap FourierTransform
open MeasureTheory Filter Set FourierBridge LocalLogFourier
namespace SevenEighths.ProbePhysical

def gaussianJointDensity (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ)) (R : ℝ) : SchwartzMap ℝ ℂ :=
  𝓕 (gaussianLogWindow V hV R)

lemma gaussianProfile_positive_smooth : ContDiffOn ℝ ∞ gaussianMellinProfile (Set.Ioi 0) := by
  intro y hy
  have hh := (gaussianProfile_scaled_smooth 1 (by norm_num) y hy).contDiffWithinAt (s:=Set.Ioi 0)
  simpa only [one_mul] using hh

end SevenEighths.ProbePhysical
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
open MeasureTheory Set
namespace SevenEighths.HeckeDyadic
open HeckeFamily

abbrev NonzeroIdeal := UnrestrictedIdealReindex.NonzeroIdeal

instance instCountableO_solutions_p0 : Countable O := ActualEisensteinCubic.latticeCoordEquiv.injective.countable
instance instCountableIdealO_solutions_p0 : Countable (Ideal O) := ConcretePrimeRowBridge.idealGenerator_injective.countable

def norm (I : NonzeroIdeal) : ℝ := I.val.absNorm

def coefficient (χ : Character) (inverse : Bool) (I : Ideal O) : ℂ :=
  if inverse then (UniqueFactorizationMonoid.moebius I : ℂ)*idealCoeff χ I else idealCoeff χ I

@[simp] theorem coefficient_zero (χ : Character) (inverse : Bool) : coefficient χ inverse 0 = 0 := by
  cases inverse
  · exact idealCoeff_zero χ
  · change (UniqueFactorizationMonoid.moebius (0 : Ideal O) : ℂ)*idealCoeff χ 0 = 0
    rw [idealCoeff_zero, mul_zero]

def shift (σ ω : ℝ) : ℂ := (σ : ℂ)-(ω : ℂ)*Complex.I

@[simp] theorem shift_re (σ ω : ℝ) : (shift σ ω).re = σ := by simp [shift]

def summand (χ : Character) (inverse : Bool) (W : ℝ → ℂ)
    (D σ ω : ℝ) (I : NonzeroIdeal) : ℂ :=
  coefficient χ inverse I.val * W (norm I/D) * ((norm I/D : ℝ) : ℂ)^(-shift σ ω)

def polynomial (χ : Character) (inverse : Bool) (W : ℝ → ℂ) (D σ ω : ℝ) : ℂ :=
  (D : ℂ)^(-(1/2 : ℂ)) * ∑' I : NonzeroIdeal, summand χ inverse W D σ ω I

def series (χ : Character) (inverse : Bool) (s : ℂ) : ℂ :=
  if inverse then HeckeReciprocal.reciprocal χ s else LFunction χ s

end SevenEighths.HeckeDyadic

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
open MeasureTheory Set Filter Complex

namespace SevenEighths.GammaZeroDetector

def cancelledKernel (f g : ℂ → ℂ) (Y : ℝ) (z : ℂ) : ℂ :=
  (Y : ℂ) ^ z * Gamma (z + 1) * dslope f 0 z * g z

def literalKernel (f g : ℂ → ℂ) (Y : ℝ) (z : ℂ) : ℂ :=
  (Y : ℂ) ^ z * Gamma z * f z * g z

open HeckeFamily

def cutoffSet (D : ℝ) : Finset (Ideal O) :=
  ConcretePrimeRowBridge.idealsUpTo ⌊2*D⌋₊

def cutoffTerm (χ : Character) (V : ℝ → ℂ) (D : ℝ) (J : Ideal O) (s : ℂ) : ℂ :=
  HeckeDyadic.coefficient χ true J * V ((J.absNorm : ℝ)/D) *
    CubicEisenstein.fullIdealWeight s J

def cutoff (χ : Character) (V : ℝ → ℂ) (D : ℝ) (s : ℂ) : ℂ :=
  ∑ J ∈ cutoffSet D, cutoffTerm χ V D J s

@[simp] theorem cutoffTerm_zero (χ : Character) (V : ℝ → ℂ) (D : ℝ) (s : ℂ) :
    cutoffTerm χ V D 0 s = 0 := by
  simp [cutoffTerm, CubicEisenstein.fullIdealWeight]

def detectorIntegrand (χ : Character) (V : ℝ → ℂ) (D Y : ℝ) (ρ z : ℂ) : ℂ :=
  (Y : ℂ)^z * Gamma z * LFunction χ (ρ+z) * cutoff χ V D (ρ+z)

def detectorIntegral (χ : Character) (V : ℝ → ℂ) (D Y : ℝ) (ρ : ℂ) : ℂ :=
  ((2*Real.pi : ℝ) : ℂ)⁻¹ * ∫ t : ℝ, detectorIntegrand χ V D Y ρ (2+t*I)

end SevenEighths.GammaZeroDetector

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.HeckeDetectorWitnessArithmetic
open HeckeFamily UniqueFactorizationMonoid CompletedGauss
local notation "O" => HeckeFamily.O

def cutoffCoefficient (V : ℝ → ℂ) (D : ℝ) (I : Ideal O) : ℂ :=
  if I = 0 then 0 else
    ∑' p : MulFiber I, (moebius p.val.1 : ℂ) * V ((Ideal.absNorm p.val.1 : ℝ) / D)

def exponentialTerm (χ : Character) (V : ℝ → ℂ) (D : ℝ) (s : ℂ) (Y : ℝ) (I : Ideal O) : ℂ :=
  cutoffCoefficient V D I * IdealEuler.weighted (idealCoeff χ) s I *
    Complex.exp (-((Ideal.absNorm I : ℝ) : ℂ) / (Y : ℂ))

end SevenEighths.HeckeDetectorWitnessArithmetic

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
open MeasureTheory Set Filter Complex
namespace SevenEighths.GammaDetectorExpansion
open GammaZeroDetector HeckeFamily

def line (t : ℝ) : ℂ := 2+t*I

@[simp] theorem line_re (t : ℝ) : (line t).re = 2 := by simp [line]
@[simp] theorem line_im (t : ℝ) : (line t).im = t := by simp [line]

def gammaTerm (a : ℂ) (N : ℝ) (ρ : ℂ) (Y : ℝ) (t : ℝ) : ℂ :=
  (Y : ℂ)^(line t)*Gamma (line t)*a*(N : ℂ)^(-(ρ+line t))

@[simp] theorem gammaTerm_zero (N : ℝ) (ρ : ℂ) (Y t : ℝ) : gammaTerm 0 N ρ Y t = 0 := by
  simp [gammaTerm]

instance instCountableO_solutions : Countable O := ActualEisensteinCubic.latticeCoordEquiv.injective.countable
instance instCountableIdealO_solutions : Countable (Ideal O) := ConcretePrimeRowBridge.idealGenerator_injective.countable

def pairCoefficient (χ : Character) (V : ℝ → ℂ) (D : ℝ) (p : Ideal O × Ideal O) : ℂ :=
  (UniqueFactorizationMonoid.moebius p.1 : ℂ) * V ((p.1.absNorm : ℝ)/D) *
    idealCoeff χ (p.1*p.2)

def pairNorm (p : Ideal O × Ideal O) : ℝ := (p.1*p.2).absNorm

def pairExponential (χ : Character) (V : ℝ → ℂ) (D : ℝ) (ρ : ℂ) (Y : ℝ)
    (p : Ideal O × Ideal O) : ℂ :=
  pairCoefficient χ V D p*(pairNorm p : ℂ)^(-ρ)*Complex.exp (-(pairNorm p : ℂ)/(Y : ℂ))

end SevenEighths.GammaDetectorExpansion

end

end OAI
end

section

namespace OAI

noncomputable section

open MeasureTheory Set Filter Asymptotics Complex
open scoped Topology FourierTransform
namespace SevenEighths.HeckeSignal
open HeckeFamily Continuation

def quotient (χ : Character) (H : ℂ → ℂ) (s : ℂ) : ℂ :=
  H s * HeckeReciprocal.reciprocal χ s

def amplitude (χ : Character) (H : ℂ → ℂ) (s : ℂ) : ℂ :=
  Complex.exp ((s - 5/6)^2) * quotient χ H s

def signal (χ : Character) (H : ℂ → ℂ) (c : ℝ) (x : ℝ) : ℂ :=
  (x : ℂ)^(c : ℂ) * mellinInv (-2) (fun s => amplitude χ H (-s)) x

def quotientBound : ℝ := (3/2) * HeckeReciprocalBound.bound 2

def endpointConstant (B : ℝ) : ℝ :=
  ‖(1 / (2 * Real.pi) : ℂ)‖ * Real.exp ((B-5/6)^2) * quotientBound *
    ∫ y : ℝ, Real.exp (-(y^2))

end SevenEighths.HeckeSignal

end

end OAI
end

section

namespace OAI

noncomputable section
open MeasureTheory Set Filter Asymptotics Complex
open scoped Topology Classical
namespace SevenEighths.HeckeSignal
open HeckeFamily Continuation

def targetRegularizer (χ : Character) (s : ℂ) : ℂ :=
  if χ.residue = 1 then s-1 else 1

def regularL (χ : Character) (s : ℂ) : ℂ :=
  if χ.residue = 1 then HeckeOrigin.poleRemoved χ s else LFunction χ s

end SevenEighths.HeckeSignal

end

end OAI
end

section

namespace OAI

noncomputable section
open Filter Asymptotics
open scoped Classical
namespace SevenEighths.HeckeCommonProbe
open HeckeFamily HeckeZeroSupremum

def PrimitiveContract (ω σ : ℝ) : Prop :=
  ∀ η : Character, FiniteFourier.IsPrimitiveOnIdeals η.residue →
    ∃ (χ : Character) (H : ℂ → ℂ) (J : ℝ → ℂ),
      (∀ I, idealCoeff χ I = if IsCoprime I χ.modulus then idealCoeff η I else 0) ∧
      AnalyticOnNhd ℂ H {s : ℂ | 7/8 < s.re} ∧
      (∀ s : ℂ, 7/8 < s.re → ‖H s - 1‖ ≤ 1/2) ∧
      J =O[atTop] (fun x : ℝ => x^(3/16+ω)) ∧
      (fun x => J x - HeckeSignal.signal χ H (-11/16) x) =O[atTop]
        (fun x : ℝ => x^(beta-11/16-σ))

def UniformCommonProbe : Prop :=
  7/8 < beta → ∃ ω σ : ℝ,
    0 < ω ∧ ω < beta-7/8 ∧ 0 < σ ∧ PrimitiveContract ω σ

end SevenEighths.HeckeCommonProbe

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical Topology ComplexConjugate
open Complex
namespace SevenEighths.HeckeFamily

theorem idealCoeff_inverse_conj (χ : Character) (J : Ideal O) :
    idealCoeff χ.inverse J=conj (idealCoeff χ J) := by
  let : Finite (O ⧸ χ.modulus) := Ring.HasFiniteQuotients.finiteQuotient χ.modulus_ne_bot
  by_cases hJ : J=0
  · subst J
    rw [map_zero,map_zero,map_zero]
  have hg := ConcretePrimeRowBridge.idealGenerator_ne_zero J hJ
  rw [←ConcretePrimeRowBridge.span_idealGenerator J,
    idealCoeff_span χ.inverse hg,idealCoeff_span χ hg]
  exact (MulChar.star_apply' χ.residue _).symm

end SevenEighths.HeckeFamily

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.HeckeDetectorPartition
open DyadicTransfer

theorem annular_support (V : ℝ → ℂ)
    (hsmall : ∀ y : ℝ, 0 ≤ y → y ≤ 1 → V y = 1)
    (hlarge : ∀ y : ℝ, 2 ≤ y → V y = 0)
    (x : ℝ) (hx : 0 ≤ x) (j : ℕ)
    (hne : annularCutoff V (x/(2 : ℝ)^j) ≠ 0) :
    (2 : ℝ)^j / 2 < x ∧ x < 2*(2 : ℝ)^j := by
  have hp : 0 < (2 : ℝ)^j := by positivity
  have hy : 0 ≤ x/(2 : ℝ)^j := div_nonneg hx hp.le
  have hlo : 1/2 < x/(2 : ℝ)^j := by
    by_contra h
    have hh := le_of_not_gt h
    apply hne
    rw [annularCutoff, hsmall _ hy (by linarith), hsmall _ (by positivity) (by linarith)]
    ring
  have hhi : x/(2 : ℝ)^j < 2 := by
    by_contra h
    apply hne
    exact annularCutoff_eq_zero_of_two_le V hlarge (le_of_not_gt h)
  constructor
  · have := (lt_div_iff₀ hp).mp hlo
    linarith
  · exact (div_lt_iff₀ hp).mp hhi

def length (X : ℝ) : ℕ := ⌈Real.logb 2 X⌉₊

def pairCoefficient (χ : HeckeFamily.Character) (V T : ℝ → ℂ)
    (D Y U : ℝ) (s : ℂ) (p : Ideal HeckeFamily.O × Ideal HeckeFamily.O) : ℂ :=
  (UniqueFactorizationMonoid.moebius p.1 : ℂ) * V ((Ideal.absNorm p.1 : ℝ)/D) *
    IdealEuler.weighted (HeckeFamily.idealCoeff χ) s (p.1*p.2) *
    Complex.exp (-((Ideal.absNorm (p.1*p.2) : ℝ) : ℂ)/(Y : ℂ)) *
    (1-V (2*(Ideal.absNorm (p.1*p.2) : ℝ)/D)) * T ((Ideal.absNorm (p.1*p.2) : ℝ)/U)

end SevenEighths.HeckeDetectorPartition

end

end OAI
end

section

namespace OAI

namespace SevenEighths.HeckeDetectorFourier
open MeasureTheory
open scoped BigOperators Classical ContDiff FourierTransform SchwartzMap
open HeckeFamily HeckeDetectorProfiles
noncomputable section

def inverseCoefficient (χ : Character) (V W : ℝ → ℂ) (Dstar D : ℝ) (s : ℂ) (I : Ideal O) : ℂ :=
  (UniqueFactorizationMonoid.moebius I : ℂ)*IdealEuler.weighted (idealCoeff χ) s I*
    V ((Ideal.absNorm I : ℝ)/Dstar)*W ((Ideal.absNorm I : ℝ)/D)

def plainCoefficient (χ : Character) (W : ℝ → ℂ) (N : ℝ) (s : ℂ) (I : Ideal O) : ℂ :=
  IdealEuler.weighted (idealCoeff χ) s I*W ((Ideal.absNorm I : ℝ)/N)

end
end SevenEighths.HeckeDetectorFourier

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical Topology
open Filter
namespace SevenEighths.HeckeDetectorTail
open HeckeFamily HeckeDetectorWitnessArithmetic CompletedGauss
open IdealMobiusDivisorSum UniqueFactorizationMonoid
local notation "O" => HeckeFamily.O

def terminalRemainder (χ : Character) (V T : ℝ → ℂ) (D Y U : ℝ) (s : ℂ) (I : Ideal O) : ℂ :=
  exponentialTerm χ V D s Y I * (1-V (2*(Ideal.absNorm I : ℝ)/D)) *
    (1-T ((Ideal.absNorm I : ℝ)/U))

def terminalTerm (χ : Character) (V T : ℝ → ℂ) (D Y U : ℝ) (s : ℂ) (I : Ideal O) : ℂ :=
  exponentialTerm χ V D s Y I * (1-V (2*(Ideal.absNorm I : ℝ)/D)) *
    T ((Ideal.absNorm I : ℝ)/U)

end SevenEighths.HeckeDetectorTail

end

end OAI
end

section

namespace OAI

noncomputable section
open Set Filter
open scoped Classical Topology
namespace SevenEighths.HeckeDetectorZeros
open HeckeFamily

def rectangle (T : ℝ) : Set ℂ :=
  {s | (51/100 : ℝ) ≤ s.re ∧ s.re ≤ 1 ∧ |s.im| ≤ T}

theorem rectangle_compact (T : ℝ) : IsCompact (rectangle T) := by
  have heq : rectangle T = Set.Icc (51/100 : ℝ) 1 ×ℂ Set.Icc (-T) T := by
    ext z
    simp only [rectangle, Set.mem_ofPred_eq, Complex.mem_reProdIm, Set.mem_Icc, abs_le]
    tauto
  rw [heq]
  exact isCompact_Icc.reProdIm isCompact_Icc

def zeros (χ : Character) (T : ℝ) : Set ℂ := {s ∈ rectangle T | LFunction χ s = 0}

theorem zeros_finite (χ : Character) (hχ : χ.residue ≠ 1) (T : ℝ) :
    (zeros χ T).Finite := by
  have ha : AnalyticOnNhd ℂ (LFunction χ) Set.univ :=
    Complex.analyticOnNhd_univ_iff_differentiable.mpr (LFunction_entire_nonprincipal χ hχ)
  have hcod := ha.preimage_zero_mem_codiscreteWithin
    (LFunction_ne_zero_of_one_lt_re χ (by norm_num : 1 < (2 : ℂ).re))
    (Set.mem_univ (2 : ℂ)) isConnected_univ
  have hfin := (rectangle_compact T).finite_sdiff_of_mem_codiscreteWithin
    (codiscreteWithin_mono (Set.subset_univ (rectangle T)) hcod)
  convert (preTransparency := .instances) hfin using 1
  ext s
  simp [zeros]

def zeroFinset (χ : Character) (hχ : χ.residue ≠ 1) (T : ℝ) : Finset ℂ :=
  (zeros_finite χ hχ T).toFinset

@[simp] theorem mem_zeroFinset (χ : Character) (hχ : χ.residue ≠ 1) (T : ℝ) (s : ℂ) :
    s ∈ zeroFinset χ hχ T ↔
      (51/100 : ℝ) ≤ s.re ∧ s.re ≤ 1 ∧ |s.im| ≤ T ∧ LFunction χ s = 0 := by
  simp only [zeroFinset, Set.Finite.mem_toFinset, zeros, rectangle, Set.mem_ofPred_eq]
  tauto

variable {ι : Type*} [Fintype ι]

def familyZeros (χ : ι → Character) (hχ : ∀ i, (χ i).residue ≠ 1) (T : ℝ) :
    Finset (ι × ℂ) :=
  Finset.univ.biUnion (fun i => (zeroFinset (χ i) (hχ i) T).image (fun s => (i,s)))

@[simp] theorem mem_familyZeros (χ : ι → Character) (hχ : ∀ i, (χ i).residue ≠ 1)
    (T : ℝ) (i : ι) (s : ℂ) :
    (i,s) ∈ familyZeros χ hχ T ↔
      (51/100 : ℝ) ≤ s.re ∧ s.re ≤ 1 ∧ |s.im| ≤ T ∧ LFunction (χ i) s = 0 := by
  simp [familyZeros]

def realParts (χ : ι → Character) (hχ : ∀ i, (χ i).residue ≠ 1) (T : ℝ) : Finset ℝ :=
  insert (51/100) ((familyZeros χ hχ T).image (fun p => p.2.re))

theorem realParts_nonempty (χ : ι → Character) (hχ : ∀ i, (χ i).residue ≠ 1) (T : ℝ) :
    (realParts χ hχ T).Nonempty := Finset.insert_nonempty _ _

def zeroMaximum (χ : ι → Character) (hχ : ∀ i, (χ i).residue ≠ 1) (T : ℝ) : ℝ :=
  (realParts χ hχ T).max' (realParts_nonempty χ hχ T)

end SevenEighths.HeckeDetectorZeros

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical Topology
open Set Metric
namespace SevenEighths.HeckeLogarithmicActual
open HeckeFamily HeckeLogarithmic

def eulerLog (η : Character) : ℂ → ℂ :=
  if η.residue = 1 then HeckeEulerLog.principalEulerLog (idealCoeff η)
  else HeckeEulerLog.eulerLog (idealCoeff η)

def innerBound : ℝ := 3+HeckeEulerLog.eulerLogBound

end SevenEighths.HeckeLogarithmicActual

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open MeasureTheory Set
namespace SevenEighths.HeckeDyadic
open HeckeFamily

instance instCountableO_solutions_p1 : Countable O := ActualEisensteinCubic.latticeCoordEquiv.injective.countable
instance instCountableIdealO_solutions_p1 : Countable (Ideal O) := ConcretePrimeRowBridge.idealGenerator_injective.countable

def twistedCoefficient (χ : Character) (inverse : Bool) (σ freq : ℝ) (I : NonzeroIdeal) : ℂ :=
  coefficient χ inverse I.val * (norm I : ℂ)^(-shift σ freq)

end SevenEighths.HeckeDyadic

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open MeasureTheory Set Complex
namespace SevenEighths.HeckeDyadic
open HeckeFamily

def integrand (χ : Character) (inverse : Bool) (W : ℝ → ℂ)
    (D σ freq : ℝ) (s : ℂ) : ℂ :=
  mellin W s * (D : ℂ)^(s+shift σ freq-(1/2 : ℂ)) *
    series χ inverse (s+shift σ freq)

end SevenEighths.HeckeDyadic

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.HeckeDetectorFinite
open HeckeFamily HeckeDetectorWitnessArithmetic HeckeDetectorTail HeckeDetectorPartition
open CompletedGauss ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O

def pairSet (U : ℝ) : Finset (Ideal O × Ideal O) :=
  (idealsUpTo ⌈2*U⌉₊) ×ˢ (idealsUpTo ⌈2*U⌉₊)

def dyadicBlock (χ : Character) (V T : ℝ → ℂ) (D Y U : ℝ) (s : ℂ) (j k : ℕ) : ℂ :=
  ∑ p ∈ pairSet U, pairCoefficient χ V T D Y U s p *
    DyadicTransfer.annularCutoff V ((Ideal.absNorm p.1 : ℝ)/(2 : ℝ)^j) *
    DyadicTransfer.annularCutoff V ((Ideal.absNorm p.2 : ℝ)/(2 : ℝ)^k)

end SevenEighths.HeckeDetectorFinite

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical ContDiff FourierTransform SchwartzMap
namespace SevenEighths.HeckeDetectorFrequency
open HeckeFamily HeckeDetectorProfiles HeckeDetectorFourier
open HeckeDetectorCoefficientBounds HeckeDetectorFinite HeckeDetectorPartition
local notation "O" => HeckeFamily.O

def phaseProduct (χ : Character) (D U : ℝ) (s : ℂ) (j k : ℕ) (t : ℝ) : ℂ :=
  phasePolynomial (expandedSet U)
    (inverseCoefficient χ cutoff (DyadicTransfer.annularCutoff cutoff) D ((2 : ℝ)^j) s)
    (fun I => Real.log ((Ideal.absNorm I : ℝ)/(2 : ℝ)^j)) t *
  phasePolynomial (expandedSet U)
    (plainCoefficient χ (DyadicTransfer.annularCutoff cutoff) ((2 : ℝ)^k) s)
    (fun I => Real.log ((Ideal.absNorm I : ℝ)/(2 : ℝ)^k)) t

end SevenEighths.HeckeDetectorFrequency

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical ContDiff
open Set
namespace SevenEighths.HeckeDetectorDyadicProfiles
open HeckeDetectorProfiles

lemma exists_positive_annular : ∃ W : ℝ→ℂ,
    ContDiff ℝ ∞ W ∧ Function.support W⊆Icc (1/4) (9/4) ∧
    ∀ x : ℝ, 0≤x → W x=DyadicTransfer.annularCutoff cutoff x := by
  obtain ⟨g,hgc,hgs,hgone,hgsupp,hgzero⟩ :=
    FourierBridge.exists_complex_smooth_cutoff 3 (by norm_num)
  let W : ℝ→ℂ := fun x => g (4*x-5)*DyadicTransfer.annularCutoff cutoff x
  have hs : ContDiff ℝ ∞ (DyadicTransfer.annularCutoff cutoff) :=
    (cutoff.smooth ⊤).sub ((cutoff.smooth ⊤).comp (by fun_prop))
  refine ⟨W,(hgs.comp (by fun_prop)).mul hs,?_,?_⟩
  · intro x hx
    have hg : g (4*x-5)≠0 := (mul_ne_zero_iff.mp hx).1
    have hh := hgsupp (subset_tsupport g hg)
    constructor <;> norm_num at hh <;> linarith [hh.1,hh.2]
  · intro x hx
    by_cases hh : DyadicTransfer.annularCutoff cutoff x=0
    · simp [W,hh]
    have ha := HeckeDetectorPartition.annular_support cutoff cutoff_one cutoff_zero x hx 0
      (by simpa using hh)
    norm_num at ha
    have hg : g (4*x-5)=1 := hgone _ (abs_le.mpr ⟨by linarith [ha.1],by linarith [ha.2]⟩)
    simp only [W,hg,one_mul]

def positiveAnnular : ℝ→ℂ := Classical.choose exists_positive_annular

lemma positiveAnnular_smooth : ContDiff ℝ ∞ positiveAnnular :=
  (Classical.choose_spec exists_positive_annular).1

lemma positiveAnnular_support : Function.support positiveAnnular⊆Icc (1/4) (9/4) :=
  (Classical.choose_spec exists_positive_annular).2.1

end SevenEighths.HeckeDetectorDyadicProfiles

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff Topology
open MeasureTheory Set Complex
namespace SevenEighths.HeckeInverseAmplification
open HeckeFamily HeckeDyadic HeckeDetectorDyadicBridge

def scaleProfile (W : ℝ→ℂ) (y : ℝ) : ℂ := -W y/2-(y : ℂ)*deriv W y

def scaleSum (χ : Character) (W : ℝ→ℂ) (S : Finset (Ideal O)) (l : ℝ) : ℂ :=
  Complex.exp (-(l : ℂ)/2)*∑ J∈S,
    coefficient χ true J*W ((J.absNorm : ℝ)*Real.exp (-l))

theorem scaleProfile_support (W : ℝ→ℂ) (a b : ℝ)
    (hs : Function.support W⊆Icc a b) : Function.support (scaleProfile W)⊆Icc a b := by
  intro y hy
  by_contra hn
  have hw : W y=0 := by by_contra hw; exact hn (hs hw)
  have hd : deriv W y=0 := by
    apply deriv_of_notMem_tsupport
    exact fun h => hn ((closure_minimal hs isClosed_Icc) h)
  exact hy (by simp [scaleProfile,hw,hd])

end SevenEighths.HeckeInverseAmplification

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical ContDiff Topology
open Set Filter Complex
namespace SevenEighths.HeckeInverseAmplification
open HeckeFamily HeckeDyadic

def twistProfile (W : ℝ→ℂ) (σ freq x : ℝ) : ℂ := W x*(x : ℂ)^(-shift σ freq)

theorem twistProfile_support (W : ℝ→ℂ) (σ freq : ℝ) :
    Function.support (twistProfile W σ freq)⊆Function.support W := by
  intro x hx hw
  exact hx (by simp [twistProfile,hw])

theorem twistProfile_smooth (W : ℝ→ℂ) (σ freq a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W) :
    ContDiff ℝ ∞ (twistProfile W σ freq) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : 0<x
  · have he : twistProfile W σ freq =ᶠ[nhds x]
        (fun y : ℝ => W y*Complex.exp ((Real.log y : ℂ)*(-shift σ freq))) := by
      filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
      unfold twistProfile
      rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hy.ne'),
        ←Complex.ofReal_log hy.le]
    apply ContDiffAt.congr_of_eventuallyEq _ he
    apply hW.contDiffAt.mul
    apply Complex.contDiff_exp.contDiffAt.comp x
    have hl : ContDiffAt ℝ ∞ (fun y : ℝ => (Real.log y : ℂ)) x :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp x (Real.contDiffAt_log.mpr hx.ne')
    exact hl.mul contDiffAt_const
  · have hxa : x<a := lt_of_le_of_lt (le_of_not_gt hx) ha
    have he : twistProfile W σ freq =ᶠ[nhds x] (fun _ => 0) := by
      filter_upwards [isOpen_Iio.mem_nhds hxa] with y hy
      have hw : W y=0 := by
        by_contra hn
        exact (not_le_of_gt hy) (hs hn).1
      simp [twistProfile,hw]
    exact contDiffAt_const.congr_of_eventuallyEq he

end SevenEighths.HeckeInverseAmplification

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open MeasureTheory Set
namespace SevenEighths.HeckePrimeDyadic
open HeckeFamily HeckeDyadic

instance instCountableO_solutions : Countable O := ActualEisensteinCubic.latticeCoordEquiv.injective.countable
instance instCountableIdealO_solutions : Countable (Ideal O) := ConcretePrimeRowBridge.idealGenerator_injective.countable

def coefficient (χ : Character) (I : Ideal O) : ℂ :=
  (IdealMangoldt.value I : ℂ) * idealCoeff χ I

@[simp] theorem coefficient_zero (χ : Character) : coefficient χ 0 = 0 := by
  unfold coefficient
  rw [IdealMangoldt.value_zero, Complex.ofReal_zero, zero_mul]

def series (χ : Character) (s : ℂ) : ℂ := -deriv (LFunction χ) s / LFunction χ s

def twistedCoefficient (χ : Character) (σ freq : ℝ) (I : NonzeroIdeal) : ℂ :=
  coefficient χ I.val * (norm I : ℂ)^(-shift σ freq)

def summand (χ : Character) (W : ℝ → ℂ) (D σ freq : ℝ) (I : NonzeroIdeal) : ℂ :=
  coefficient χ I.val * W (norm I/D) * ((norm I/D : ℝ) : ℂ)^(-shift σ freq)

def polynomial (χ : Character) (W : ℝ → ℂ) (D σ freq : ℝ) : ℂ :=
  (D : ℂ)^(-(1/2 : ℂ)) * ∑' I : NonzeroIdeal, summand χ W D σ freq I

end SevenEighths.HeckePrimeDyadic

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
open Set
namespace SevenEighths.HeckePrimeAnnular
open HeckeFamily HeckeDyadic ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O

def annulusSet (b D : ℝ) : Finset (Ideal O) := idealsUpTo ⌊max 1 b*D⌋₊

def annularWeight (W : ℝ→ℂ) (D σ freq : ℝ) (I : Ideal O) : ℂ :=
  W ((I.absNorm : ℝ)/D)*(((I.absNorm : ℝ)/D : ℝ) : ℂ)^(-shift σ freq)

def primePolynomial (χ : Character) (W : ℝ→ℂ) (b D σ freq : ℝ) : ℂ :=
  (D : ℂ)^(-(1/2 : ℂ))*∑ I∈(annulusSet b D).filter Prime,
    idealCoeff χ I*annularWeight W D σ freq I

theorem fixed_profile_norm_bound (W : ℝ→ℂ) (hW : Continuous W)
    (a b lo hi : ℝ) (ha : 0<a) :
    ∃ B : ℝ, 0<B ∧ ∀ σ∈Icc lo hi, ∀ y∈Icc a b, ‖W y‖*y^(-σ)≤B := by
  let K : Set (ℝ×ℝ) := Icc lo hi ×ˢ Icc a b
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hc : ContinuousOn (fun p : ℝ×ℝ => ‖W p.2‖*p.2^(-p.1)) K := by
    apply (hW.comp continuous_snd).norm.continuousOn.mul
    exact continuous_snd.continuousOn.rpow continuous_fst.neg.continuousOn
      (fun p hp => Or.inl (ne_of_gt (ha.trans_le hp.2.1)))
  obtain ⟨M,hM⟩ := hK.bddAbove_image hc
  refine ⟨|M|+1,by positivity,?_⟩
  intro σ hσ y hy
  exact (hM (Set.mem_image_of_mem _ (show (σ,y)∈K from ⟨hσ,hy⟩))).trans
    (by linarith [le_abs_self M])

end SevenEighths.HeckePrimeAnnular

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
namespace SevenEighths.HeckePrimeDyadic
open HeckeFamily HeckeDyadic

def eulerBound (b : ℝ) : ℝ :=
  ∑' I : NonzeroIdeal, IdealMangoldt.value I.val * (norm I)^(-b)

end SevenEighths.HeckePrimeDyadic

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.HeckeRayQuotient
open HeckeFamily
variable (M : Ideal O) [NeZero M]
local instance instFiniteQuotientOIdeal_solutions : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
local instance instIsPrincipalIdealRingO_solutions : IsPrincipalIdealRing O := IsCyclotomicExtension.Rat.three_pid K
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

def character (χ : RayQuotient.Characters M H) : Character :=
  HeckeRayFamily.character M (RayQuotient.toFullRay M H hH χ)

end SevenEighths.HeckeRayQuotient

end

end OAI
end

section

namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
open ActualEisensteinCubic CompletedGauss FirstPassCubeLabels SecondPassArithmetic
namespace SevenEighths.InverseInitialDyadicAssembly
local notation "Eis" => ActualEisensteinCubic.O
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure
open InverseInitialEnergyCallerModes InverseInitialEnergyCallerSource
open InverseInitialEnergyCallerWindows InverseInitialProfile InverseInitialClippedColumns
open InverseInitialKernelBridge InverseSecondChildWindows
open CenteredMomentSectorLocalization CenteredMomentDyadicCount

abbrev Windows (a b : Fin 4→ℝ) := ∀ i:Fin 4,↥(indices (a i) (b i))

def exponent (Z:ℝ) (k:ℤ) : ℝ := Real.logb Z (dyadicScale k)

def cutoff : Fin 4→ℝ→ℂ := fun _ y=>(annulus y:ℂ)

def weight (k:Fin 4→ℤ) (q:Fin 4→ℝ) : ℂ :=
  ∏i:Fin 4,(dyadicWeight (k i) (q i):ℂ)

variable {ι:Type*}[DecidableEq ι](p:ι→Eis)

def sourceNorms (x:Source (ι:=ι) 0) : Fin 4→ℝ :=
  fun i=>coordinates p (sourcePoint x ∅ ∅) (outerIndex i)

variable (hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

end SevenEighths.InverseInitialDyadicAssembly

end

end OAI
end

section

namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
open ActualEisensteinCubic CompletedGauss FirstPassCubeLabels SecondPassArithmetic
namespace SevenEighths.InverseInitialDyadicAssembly
local notation "Eis"=>ActualEisensteinCubic.O
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure
open InverseInitialEnergyCallerModes InverseInitialEnergyCallerSource
open InverseInitialEnergyCallerWindows InverseInitialProfile InverseInitialClippedColumns
open CenteredMomentSectorLocalization CenteredMomentDyadicCount

variable {ι:Type*}[DecidableEq ι](p:ι→Eis)
  (hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

def windowBlock (pool:Finset ι)(S:Finset (Source (ι:=ι) 0))
    (w:Source (ι:=ι) 0→ℂ)(Ψ:Eis→*ℂ)(j:Eis)(marks:Finset ι→ℂ)
    (W₁ W₂:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(Z D m:ℝ)(k:Fin 4→ℤ) : ℂ :=
  physicalBlock p hp hcop hg
    (pointSource pool (windowSource p S cutoff Z D
      (exponent Z (k 0)) (exponent Z (k 2)) (exponent Z (k 1)) (exponent Z (k 3))))
    ((fun x=>w x*outerCutoff cutoff (sourceRelative p x Z D
      (exponent Z (k 0)) (exponent Z (k 2)) (exponent Z (k 1)) (exponent Z (k 3))))∘erasePoint)
    Ψ j marks W₁ W₂ Φ Z D m

end SevenEighths.InverseInitialDyadicAssembly

end

end OAI
end

section

namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
open ActualEisensteinCubic CompletedGauss FirstPassCubeLabels SecondPassArithmetic
namespace SevenEighths.InverseInitialDyadicAssembly
local notation "Eis"=>ActualEisensteinCubic.O
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure
open InverseInitialEnergyCallerModes InverseInitialEnergyCallerSource
open InverseInitialEnergyCallerWindows InverseInitialProfile InverseInitialClippedColumns

variable {ι:Type*}[DecidableEq ι](p:ι→Eis)

def cappedSource (S:Finset (Source (ι:=ι) 0))(a b:Fin 4→ℝ) : Finset (Source (ι:=ι) 0) :=
  S.filter (fun x=>∀i,sourceNorms p x i∈Set.Icc (a i) (b i))

variable (hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

end SevenEighths.InverseInitialDyadicAssembly

end

end OAI
end

section

namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseInitialDyadicAssembly
open InverseInitialProfile CenteredMomentSectorLocalization CenteredMomentDyadicCount
open Filter

def retainedWindows (a b:Fin 4→ℝ)(Z D m L:ℝ) : Finset (Windows a b) :=
  Finset.univ.filter (fun k=>radialCenter m (exponent Z (k 3).val)
    (exponent Z (k 1).val) D (exponent Z (k 0).val)≤L)

def tailWindows (a b:Fin 4→ℝ)(Z D m L:ℝ) : Finset (Windows a b) :=
  Finset.univ.filter (fun k=>L< radialCenter m (exponent Z (k 3).val)
    (exponent Z (k 1).val) D (exponent Z (k 0).val))

end SevenEighths.InverseInitialDyadicAssembly

end

end OAI
end

section

namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
open ActualEisensteinCubic CompletedGauss FirstPassCubeLabels SecondPassArithmetic
namespace SevenEighths.InverseInitialDyadicAssembly
local notation "Eis"=>ActualEisensteinCubic.O
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure
open InverseInitialEnergyCallerModes InverseInitialEnergyCallerSource
open InverseInitialEnergyCallerWindows InverseInitialProfile InverseInitialClippedColumns
open CenteredMomentSectorLocalization CenteredMomentDyadicCount

def windowMass {a b:Fin 4→ℝ}(F:Finset (Windows a b))(q:Fin 4→ℝ) : ℝ :=
  ∑k∈F,∏i:Fin 4,dyadicWeight (k i).val (q i)

variable {ι:Type*}[DecidableEq ι](p:ι→Eis)
  (hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

end SevenEighths.InverseInitialDyadicAssembly

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.InverseInitialRawDictionary
open HeckeFamily HeckeDyadic HeckeDetectorDyadicBridge
open InverseInitialPoissonBridge InverseInitialConjugateEnergy
open ConcretePrimeRowBridge CompletedGauss UniqueFactorizationMonoid
local notation "O" => HeckeFamily.O

def twistedProfile (W : ℝ → ℂ) (σ freq : ℝ) (x : ℝ) : ℂ :=
  W x*(x:ℂ)^(-_root_.OAI.SevenEighths.HeckeDyadic.shift σ freq)

def fixedBase (η : Character) (m f : O) : Ideal O →* ℂ :=
  heckeIdealCharacter (idealCoeff η).toMonoidHom (m^6*f^4)

end SevenEighths.InverseInitialRawDictionary

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.InverseInitialExcludedEnergy
open HeckeFamily HeckeDyadic
open IdealMobiusDivisorSum UniqueFactorizationMonoid
local notation "O"=>HeckeFamily.O

def deletionWeight (χ:Character)(j:Ideal O):ℂ:=
  (moebius j:ℂ)*idealCoeff χ j*(j.absNorm:ℂ)^(-(1/2:ℂ))

end SevenEighths.InverseInitialExcludedEnergy

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentDivisorRows
open CenteredMomentDivisorAllocation CenteredMomentDivisorExtraction CenteredMomentDivisorTensor
open CenteredMomentDivisorRectangle CenteredMomentHeckeExpansion CenteredMomentHeckeHeight
open CenteredMomentHeckeSlots CenteredMomentRectangle HeckeFamily
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def allocatedRectangle (η : Character) (m A z : O) (t : ℝ)
    (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ)
    (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) : ℂ :=
  ∑ v : (i : ι) → S i,(∏ i,β i (v i))*
    ∑' I : Ideal O,∑' J : Ideal O,
      allocationTerm D Finset.univ (factorTuple (fun i => v i) I J) a *
        rowWeight η m A z t ((∏ i,(v i:Ideal O))*I*J)*
        idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ I J

end SevenEighths.CenteredMomentDivisorRows

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators ComplexConjugate

namespace SevenEighths.CenteredMomentDetectorDictionary
open HeckeFamily HeckeDyadic CanonicalRowCompletion
open CenteredMomentHeckeSlots
local notation "O" => HeckeFamily.O

def physicalSlotCoefficient (η : Character) (W : ℝ→ℂ) (D : ℝ) (z : ℂ) (P : Ideal O) : ℂ :=
  idealCoeff η.inverse P*conj (W ((P.absNorm:ℝ)/D)*(((P.absNorm:ℝ)/D:ℝ):ℂ)^(z-1))

end SevenEighths.CenteredMomentDetectorDictionary

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentDivisorRowEnergy
open CenteredMomentDivisorAllocation CenteredMomentDivisorRows
open CenteredMomentHeckeExpansion CenteredMomentRectangle HeckeFamily
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def maskedRectangle (η : Character) (m A z : O) (t : ℝ)
    (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (D : Ideal O)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) : ℂ :=
  ∑ v : (i : ι) → S i,(∏ i,β i (v i))*
    ∑' I : Ideal O,∑' J : Ideal O,
      (if D∣(∏ i,(v i:Ideal O))*I*J then (1:ℂ) else 0)*
        rowWeight η m A z t ((∏ i,(v i:Ideal O))*I*J)*
        idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ I J

end SevenEighths.CenteredMomentDivisorRowEnergy

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.CenteredMomentReflectionDeletion
open HeckeFamily UniqueFactorizationMonoid
open IdealMobiusDivisorSum EisensteinSchwartzPoisson ConcreteTraceCRT
local notation "O" => HeckeFamily.O
local notation "NI" => UnrestrictedIdealReindex.NonzeroIdeal

def norm (I : NI) : ℝ := I.val.absNorm
lemma norm_pos (I : NI) : 0 < norm I := CompletedGauss.nonzeroIdeal_norm_pos I

def outside (S : Finset (Ideal O)) (I : Ideal O) : Prop := ∀ P ∈ S, ¬ P ∣ I
abbrev SmoothIdeal (S : Finset (Ideal O)) := {I : NI // primeSupport I.val ⊆ S}
abbrev OutsideIdeal (S : Finset (Ideal O)) := {I : NI // outside S I.val}

def extract (S : Finset (Ideal O)) (I : Ideal O) : Ideal O :=
  ((normalizedFactors I).filter (· ∈ S)).prod
def residual (S : Finset (Ideal O)) (I : Ideal O) : Ideal O :=
  ((normalizedFactors I).filter (· ∉ S)).prod
lemma extract_factors (S : Finset (Ideal O)) (I : Ideal O) :
    normalizedFactors (extract S I) = (normalizedFactors I).filter (· ∈ S) :=
  normalizedFactors_prod_eq_self_of_subset
    (fun _ h => (Multiset.mem_filter.mp h).1)
lemma residual_factors (S : Finset (Ideal O)) (I : Ideal O) :
    normalizedFactors (residual S I) = (normalizedFactors I).filter (· ∉ S) :=
  normalizedFactors_prod_eq_self_of_subset
    (fun _ h => (Multiset.mem_filter.mp h).1)
lemma extract_ne_zero (S : Finset (Ideal O)) (I : Ideal O) : extract S I ≠ 0 :=
  prod_ne_zero_of_subset_normalizedFactors
    (fun _ h => (Multiset.mem_filter.mp h).1)
lemma residual_ne_zero (S : Finset (Ideal O)) (I : Ideal O) : residual S I ≠ 0 :=
  prod_ne_zero_of_subset_normalizedFactors
    (fun _ h => (Multiset.mem_filter.mp h).1)
lemma reconstruct (S : Finset (Ideal O)) (I : NI) :
    extract S I.val * residual S I.val = I.val := by
  rw [extract, residual, ← Multiset.prod_add, Multiset.filter_add_not]
  exact Ideal.prod_normalizedFactors_eq_self I.property
lemma extract_smooth (S : Finset (Ideal O)) (I : Ideal O) :
    primeSupport (extract S I) ⊆ S := by
  intro P hP
  have hh : P ∈ normalizedFactors I ∧ P ∈ S := by
    simpa only [primeSupport, extract_factors, Multiset.mem_toFinset, Multiset.mem_filter] using hP
  exact hh.2
lemma outside_iff_factors (S : Finset (Ideal O)) (hS : ∀ P ∈ S, Prime P) (I : NI) :
    outside S I.val ↔ ∀ P ∈ normalizedFactors I.val, P ∉ S := by
  constructor
  · intro h P hP hPS
    exact h P hPS (dvd_of_mem_normalizedFactors hP)
  · intro h P hPS hd
    exact h P ((mem_normalizedFactors_iff I.property).mpr ⟨hS P hPS, hd⟩) hPS
lemma residual_outside (S : Finset (Ideal O)) (hS : ∀ P ∈ S, Prime P) (I : Ideal O) :
    outside S (residual S I) := by
  rw [outside_iff_factors S hS ⟨_, residual_ne_zero S I⟩, residual_factors]
  intro P hP
  exact (Multiset.mem_filter.mp hP).2
lemma split_product (S : Finset (Ideal O)) (hS : ∀ P ∈ S, Prime P)
    (D : SmoothIdeal S) (J : OutsideIdeal S) :
    extract S (D.val.val * J.val.val) = D.val.val ∧
      residual S (D.val.val * J.val.val) = J.val.val := by
  have hd : (normalizedFactors D.val.val).filter (· ∈ S) = normalizedFactors D.val.val :=
    Multiset.filter_eq_self.mpr (fun P hP => D.property (Multiset.mem_toFinset.mpr hP))
  have hj : (normalizedFactors J.val.val).filter (· ∈ S) = 0 := by
    apply Multiset.filter_eq_nil.mpr
    intro P hP
    exact (outside_iff_factors S hS J.val).mp J.property P hP
  have hd' : (normalizedFactors D.val.val).filter (· ∉ S) = 0 := by
    apply Multiset.filter_eq_nil.mpr
    intro P hP
    exact not_not.mpr (D.property (Multiset.mem_toFinset.mpr hP))
  have hj' : (normalizedFactors J.val.val).filter (· ∉ S) = normalizedFactors J.val.val :=
    Multiset.filter_eq_self.mpr ((outside_iff_factors S hS J.val).mp J.property)
  simp only [extract, residual, normalizedFactors_mul D.val.property J.val.property,
    Multiset.filter_add, hd, hj, hd', hj', add_zero, zero_add,
    Ideal.prod_normalizedFactors_eq_self D.val.property,
    Ideal.prod_normalizedFactors_eq_self J.val.property, and_self]

def splitEquiv (S : Finset (Ideal O)) (hS : ∀ P ∈ S, Prime P) :
    NI ≃ SmoothIdeal S × OutsideIdeal S where
  toFun I := (⟨⟨extract S I.val, extract_ne_zero S I.val⟩, extract_smooth S I.val⟩,
    ⟨⟨residual S I.val, residual_ne_zero S I.val⟩, residual_outside S hS I.val⟩)
  invFun p := ⟨p.1.val.val * p.2.val.val, mul_ne_zero p.1.val.property p.2.val.property⟩
  left_inv I := Subtype.ext (reconstruct S I)
  right_inv p := by
    obtain ⟨hd, hj⟩ := split_product S hS p.1 p.2
    exact Prod.ext (Subtype.ext (Subtype.ext hd)) (Subtype.ext (Subtype.ext hj))

def DecayTwo (F : ℝ → ℂ) : Prop := ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 0 < x → x^2 * ‖F x‖ ≤ C

def outsideSum (η : Character) (S : Finset (Ideal O)) (F : ℝ → ℂ) (X : ℝ) : ℂ :=
  ∑' I : NI, (if outside S I.val then idealCoeff η I.val else 0) * F (norm I / X)

def reflectedTerm (η ηi : Character) (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (F : ℝ → ℂ) (X Q : ℝ)
    (D : Finset (Ideal O)) (H : SmoothIdeal S) : ℂ :=
  (moebius (∏ P ∈ D,P) : ℂ) * idealCoeff η (∏ P ∈ D,P) * idealCoeff ηi H.val.val /
    (Real.sqrt ((Ideal.absNorm (∏ P ∈ D,P) : ℝ) * norm H.val) : ℂ) *
    HeckeDyadic.polynomial (ηi.excludePrimes S hS) false F
      (Q * (Ideal.absNorm (∏ P ∈ D,P) : ℝ) / (X * norm H.val)) 0 0

end SevenEighths.CenteredMomentReflectionDeletion

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentNaturalRowSource
open HeckeFamily CompletedGauss UniqueFactorizationMonoid ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O

lemma support_prime (R P : Ideal O) (hP : P∈primeSupport R) : Prime P :=
  prime_of_normalized_factor P (Multiset.mem_toFinset.mp hP)

def excluded (χ : Character) (R : Ideal O) : Character :=
  χ.excludePrimes (primeSupport R) (support_prime R)

end SevenEighths.CenteredMomentNaturalRowSource

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentReflectedAnnuli
open Set EisensteinSchwartzPoisson CenteredMomentSectorLocalization
open LocalLogFourier

def logWindow (v : ℝ) : ℂ := (annulus (Real.exp v) : ℂ)

def annularProfile (F : ℝ→ℂ) (s x : ℝ) : ℂ := (annulus x:ℂ)*F (s*x)

def annularMass (B : ℕ) (n : ℤ) : ℝ :=
  Real.sqrt (dyadicScale n)/(1+dyadicScale n)^B

end SevenEighths.CenteredMomentReflectedAnnuli

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentFirstAnnularMajorant
open CenteredMomentSectorLocalization CenteredMomentDyadicCount

def weight (x:ℝ):ℝ:=cutoff (x/2)*(1-cutoff (4*x))

lemma weight_zero_low (x:ℝ)(hx:x≤1/8):weight x=0:=by
  rw [weight,cutoff_one (4*x) (by linarith),sub_self,mul_zero]

lemma weight_zero_high (x:ℝ)(hx:2≤x):weight x=0:=by
  rw [weight,cutoff_zero (x/2) (by linarith),zero_mul]

lemma weight_support:Function.support weight⊆Set.Icc (1/8:ℝ) 2:=by
  intro x hx
  exact ⟨(lt_of_not_ge (fun h=>hx (weight_zero_low x h))).le,
    (lt_of_not_ge (fun h=>hx (weight_zero_high x h))).le⟩

lemma weight_smooth:ContDiff ℝ ∞ weight:=by
  have hc:ContDiff ℝ ∞ cutoff:=
    Real.smoothTransition.contDiff.comp (contDiff_const.sub (contDiff_const.mul contDiff_id))
  exact (hc.comp (contDiff_id.div_const 2)).mul
    (contDiff_const.sub (hc.comp (contDiff_const.mul contDiff_id)))

def profile:𝓢(ℝ,ℂ):=
  (HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    (show Function.support (fun x:ℝ=>(weight x:ℂ))⊆Set.Icc (1/8:ℝ) 2 from by
      intro x hx
      apply weight_support
      intro hz
      apply hx
      change (weight x:ℂ)=0
      rw [hz]
      rfl)).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp weight_smooth)

def bands (H:ℝ):Finset ℤ:=indices (H/8) (2*H)

end SevenEighths.CenteredMomentFirstAnnularMajorant

end

end OAI
end

section

namespace OAI

noncomputable section

open scoped Classical BigOperators ContDiff Topology
open MeasureTheory Set Complex
namespace SevenEighths.CenteredMomentFrequencyScaleSupremum
open HeckeFamily HeckeDyadic HeckeDetectorDyadicBridge FourierBridge
open HeckeInverseAmplification (scaleProfile scaleProfile_support
  scaleSupport )
def frequencyScaleSum (χ : Character) (inv : Bool) (W : ℝ→ℂ) (freq : ℝ) (S : Finset (Ideal O)) (l : ℝ) : ℂ :=
  Complex.exp (-(l : ℂ)/2)*∑ J∈S,
    (coefficient χ inv J*logPhase (freq/(2*Real.pi)) (Real.log (J.absNorm : ℝ)))*W ((J.absNorm : ℝ)*Real.exp (-l))

end SevenEighths.CenteredMomentFrequencyScaleSupremum

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentLogDyadic
open CenteredMomentSectorLocalization CenteredMomentFirstWholeKernel

def logAnnulus (x : ℝ) : ℂ := annulus (Real.exp x)

theorem logAnnulus_smooth : ContDiff ℝ ∞ logAnnulus :=
  Complex.ofRealCLM.contDiff.comp (annulus_smooth.comp Real.contDiff_exp)

theorem logAnnulus_support : Function.support logAnnulus ⊆ Set.Icc (-Real.log 4) 0 := by
  intro x hx
  have hn : annulus (Real.exp x)≠0 := by simpa only [Function.mem_support,logAnnulus,ne_eq,Complex.ofReal_eq_zero] using hx
  have hlo : 1/4<Real.exp x := lt_of_not_ge (fun h=>hn (annulus_zero_low _ h))
  have hhi : Real.exp x<1 := lt_of_not_ge (fun h=>hn (annulus_zero_high _ h))
  constructor
  · have hh := Real.strictMonoOn_log (show 1/4∈Set.Ioi (0:ℝ) by norm_num)
      (Real.exp_pos x) hlo
    rw [Real.log_exp,Real.log_div (by norm_num) (by norm_num),Real.log_one,zero_sub] at hh
    exact hh.le
  · exact (Real.exp_lt_one_iff.mp hhi).le

theorem logAnnulus_compact : HasCompactSupport logAnnulus :=
  HasCompactSupport.intro (isCompact_Icc) (fun x hx=>by
    by_contra hn
    exact hx (logAnnulus_support hn))

end SevenEighths.CenteredMomentLogDyadic

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.CenteredMomentReflectedSeries
open HeckeFamily CenteredMomentSectorLocalization CenteredMomentReflectedAnnuli
open CenteredMomentReflectionDeletion
open EisensteinSchwartzPoisson
local notation "NI" => UnrestrictedIdealReindex.NonzeroIdeal

def dyadicIdealTerm (η : Character) (F : ℝ→ℂ) (Y : ℝ) (I : NI) (n : ℤ) : ℂ :=
  idealCoeff η I.val*(dyadicWeight n ((I.val.absNorm:ℝ)/Y):ℂ)*F ((I.val.absNorm:ℝ)/Y)

end SevenEighths.CenteredMomentReflectedSeries

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.CenteredMomentReflectedTruncation
open HeckeFamily CenteredMomentSectorLocalization CenteredMomentReflectedAnnuli
open CenteredMomentReflectionDeletion
open CenteredMomentReflectedSeries EisensteinSchwartzPoisson
local notation "NI" => UnrestrictedIdealReindex.NonzeroIdeal

def retainedAnnuli (R Y : ℝ) (hY : 0<Y) : Finset ℤ :=
  (finite_retained_above R (Y⁻¹) (inv_pos.mpr hY)).toFinset

end SevenEighths.CenteredMomentReflectedTruncation

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentZeroMeanBridge
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein EisensteinSchwartzPoisson
open CanonicalQuadraticSieve CanonicalRowCompletion ConcretePrimeRowBridge
open CenteredMomentCommonSupport
open CenteredMomentFourier CenteredMomentCorrelation
open CenteredMomentSectorLocalization CenteredMomentFirstReduced
open CenteredMomentActive
local notation "O" => ActualEisensteinCubic.O

def quotientMean (a : O) (F : Residue a → ℂ) : ℂ :=
  (normValue a : ℂ)⁻¹ * ∑' x : Residue a, F x

def dilationMask (e d : O) (F : Residue d → ℂ) (x : Residue (d*e)) : ℂ :=
  if frequencyReduction e (d*e) (dvd_mul_left e d) x = 0 then
    F (frequencyReduction d (d*e) (dvd_mul_right d e) x) else 0

@[simp] theorem dilationMask_mk (e d : O) (F : Residue d → ℂ) (z : O) :
    dilationMask e d F (Ideal.Quotient.mk _ z) =
      if e ∣ z then F (Ideal.Quotient.mk _ z) else 0 := by
  simp only [dilationMask, frequencyReduction_mk, Ideal.Quotient.eq_zero_iff_mem,
    Ideal.mem_span_singleton]

end SevenEighths.CenteredMomentZeroMeanBridge

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSecondSectorRetained
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ConcreteTraceCRT EisensteinSchwartzPoisson
open CenteredMomentHeckeColumnWindow
open CenteredMomentSecondWholeKernel CenteredMomentSectorLocalization
open CenteredMomentSourceRow
local notation "O" => ActualEisensteinCubic.O

def physicalKernel (C D : Ideal O) (W : 𝓢(ℝ,ℂ)) (K R : ℝ)
    (j : O) (I J : Ideal O) : ℂ :=
  ((K:ℂ)/((Real.sqrt (Ideal.absNorm (C*I):ℝ):ℂ)*(Real.sqrt (Ideal.absNorm (D*J):ℝ):ℂ)))*
    (retainedWeight R (normValue j):ℂ)*
      paperRadialFourier W (K*‖eisEmbedding j‖^2/
        ‖eisEmbedding (primaryGenerator (C*I)*primaryGenerator (D*J))‖^2)

end SevenEighths.CenteredMomentSecondSectorRetained

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSecondRetainedRows
open HeckeFamily CanonicalQuadraticSieve CompletedGauss ConcretePrimeRowBridge
open CenteredMomentSecondSectorRetained CenteredMomentSectorLocalization
local notation "O" => ActualEisensteinCubic.O

def retainedRows (R : ℝ) (A : O) : Finset O := rowNormDisk (Nat.ceil (4*R/normValue A))

end SevenEighths.CenteredMomentSecondRetainedRows

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSecondActiveDyadic
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSecondSectorRetained CenteredMomentSectorLocalization
open CenteredMomentSecondDyadicPartition CenteredMomentSecondWholeKernel CenteredMomentLogDyadic CenteredMomentSmooth
open CenteredMomentSourceRow CenteredMomentSecondRetainedRows
local notation "O" => ActualEisensteinCubic.O

def sourceLower (C D : Ideal O) (A : O) (K : ℝ) : Fin 4→ℝ :=
  ![secondEffectiveScale C D A K,1,1,1]

def sourceUpper (C D : Ideal O) (A : O) (K R H : ℝ) : Fin 4→ℝ :=
  ![secondEffectiveScale C D A K,max 1 (4*R/normValue A),
    max 1 (H/(Ideal.absNorm C:ℝ)),max 1 (H/(Ideal.absNorm D:ℝ))]

def dyadicKernel (C D : Ideal O) (A : O) (W : 𝓢(ℝ,ℂ)) (K R : ℝ)
    (n : Fin 4→ℤ) (h : O) (I J : Ideal O) : ℂ :=
  ((K:ℂ)/((Real.sqrt (Ideal.absNorm C:ℝ):ℂ)*(Real.sqrt (Ideal.absNorm D:ℝ):ℂ)*
    (Real.sqrt (dyadicScale (n 2)):ℂ)*(Real.sqrt (dyadicScale (n 3)):ℂ)))*
    (retainedWeight R (normValue (A*h)):ℂ)*
      wholeKernel W (fun _=>logAnnulus)
        (dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3)))
        (Real.log (secondEffectiveScale C D A K/dyadicScale (n 0)))
        (Real.log (normValue h/dyadicScale (n 1)))
        (Real.log ((Ideal.absNorm I:ℝ)/dyadicScale (n 2)))
        (Real.log ((Ideal.absNorm J:ℝ)/dyadicScale (n 3)))

end SevenEighths.CenteredMomentSecondActiveDyadic

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory

namespace SevenEighths.CenteredMomentSecondWindowBudget
open CenteredMomentLogDyadic CenteredMomentHeckeColumnWindow CenteredMomentHeckeWindowEnergy

def profileMoment (J : ℕ) : ℝ :=
  ∫ w : ℝ,(1+‖w‖)^J*‖columnDensity logAnnulus logAnnulus_compact logAnnulus_smooth w‖

def heightEnvelope (t : ℝ) : ℝ := (1+‖t‖+2*Real.pi)*(1+2*Real.pi)

def windowBudget (J : ℕ) (t E : ℝ) : ℝ := Real.sqrt E*heightEnvelope t^J*profileMoment J

end SevenEighths.CenteredMomentSecondWindowBudget

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentSecondDyadicRowSupport
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSectorLocalization
local notation "O"=>HeckeFamily.O

 def dyadicRows (rows:Finset O) (n:Fin 4→ℤ):Finset O:=
  rows.filter (fun z=>dyadicWeight (n 1) (normValue z)≠0)

end SevenEighths.CenteredMomentSecondDyadicRowSupport

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentSecondRetainedRatioScalar
open HeckeFamily CanonicalQuadraticSieve CompletedGauss RayFourExpansion
open CenteredMomentSecondWholeKernel
open CenteredMomentSectorLocalization
open CenteredMomentSecondRadicalBudget
open CenteredMomentHeckeColumnWindow
local notation "O" => HeckeFamily.O

def retainedRatio (n:Fin 4→ℤ):ℝ :=
  dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3))

end SevenEighths.CenteredMomentSecondRetainedRatioScalar

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical ComplexConjugate
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler
open CanonicalRowCompletion CanonicalQuadraticSieve CompletedGauss
local notation "O" => HeckeFamily.O

def idealUnramifiedCorrection (η : Character) (u : FreeRow) (P : PrimeIdeal) (x w z : ℂ) : ℂ :=
  unramifiedClosed P.val.absNorm (actualAPhase η (primaryGenerator P.val))
    (idealCoeff η P.val) (idealRowHom u.val P.val) x w z

end SevenEighths.ProbeHighRowFamily

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler
open CanonicalRowCompletion CompletedGauss
local notation "O" => HeckeFamily.O

def unramifiedFactor (η : Character) (u : FreeRow) (P : PrimeIdeal) (x w z : ℂ) : ℂ :=
  if P.val∣Ideal.span {u.val} then 1 else idealUnramifiedCorrection η u P x w z

def unramifiedProduct (S : Finset (Ideal O)) (η : Character) (u : FreeRow) (x w z : ℂ) : ℂ :=
  ∏' P : {P : PrimeIdeal // P.val∉S},unramifiedFactor η u P.val x w z

end SevenEighths.ProbeHighRowFamily

end

end OAI
end


