-- Prove2me | Definitions.Def_OAIHecke78B005
-- name    : OAIHecke78B005
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-08T21:38:00.423231+00:00
-- url     : https://prove2.me/theorems/fdd8a8be-26df-4977-b954-c12acf53e4b7
-- title:
--   OpenAI Hecke 7/8 split, definitions bundle 6 of 29
-- statement:
--   Definitions bundle 6 of 29 of the split of OpenAI's proof that finite-order Hecke $L$-functions over $\mathbb{Q}(\zeta_3)$ do not vanish for $\operatorname{Re} s > 7/8$: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/NumberTheory/DirichletL` (OpenAI, *The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane $\operatorname{Re} s > 7/8$*, September 30, 2026, family 003 of [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (definitions that choose witnesses of existence theorems or build structures carrying proofs need those proofs) and the instances and attribute-tagged lemmas of the same modules.
--
--   It imports the bundles `OAIHecke78B004` of this split, and through them their definitions. It also imports wurtle's published bundle `HeckeSevenEighths` (the comparator definitions of OpenAI's challenge statement: `Character`, `LFunction` and the theta-function pairs they are built from), which OpenAI's development defines identically.
--
--   Modules: `Eisenstein.PrimitiveRows`, `Poisson.PrincipalTruncation`, `Fourier.FrequencyTwists`, `CubicSieve.RowMajorants`, `CubicSieve.FrequencyBlocks`, `Eisenstein.HyperbolicSpace`, `Eisenstein.FourierCoefficients`, `QuadraticSieve.AnnularRecursion`, `CubicSieve.TwistedProfiles`, `Eisenstein.CuspIntegration`, `QuadraticSieve.DualMiddleExpansion`, `QuadraticSieve.MaskedPrincipalBounds`, `Mellin.VerticalContourShift`, `Descent.Canonical`, `Descent.SecondPass`, `Descent.FirstToSecond`, `Reflection.IdealBridge`, `Reflection.CoprimeSource`, `Reflection.SectorAggregation`, `Reflection.FixedTuples`, `Reflection.GlobalEnergy`, `Hecke.CharacterAnalytic`, `Descent.CanonicalRankExistenceInduction`, `Detector.LocalWeights`, `RayPrimeNormalizer`, `Detector.RaySlots`, `Detector.HighRowsWeights`, `Hecke.DetectorDyadicProfiles`, `Detector.CentralExponent`, `Detector.CentralDyadicWeight`, `PrimeRows.CubePrimeBound`, `PrimeRows.CubeFixedPrimes`, `Detector.CentralClassArithmetic`, `Detector.GaussianWindows`, `Detector.GaussianSlots`, `Detector.GramLatticeDecay`, `Detector.GramAnnularLattice`, `Detector.GramJointProfile`, `Hecke.DetectorRowwisePolynomial`, `Hecke.InverseAmplificationConjugation`, `Moments.PrimePool`, `Hecke.InverseAmplificationRowwise`, `Hecke.DetectorCoefficientTransfer`, `Dictionary.InverseUniformLog`, `Energy.AmplifierFamilyAdmission`, `PrimeRows.CubeFloorArithmetic`, `PrimeRows.CubeFloorGlobal`, `PrimeRows.CubeFloorGlobalIntegral`, `PrimeRows.CubeFloorNormalized`, `PrimeRows.CubeFloorSaving`, `PrimeRows.CubeFloorCollected`, `PrimeRows.NonfloorClass`, `PrimeRows.NormalizedTransport`, `PrimeRows.NormalizedTransportSaving`, `PrimeRows.NonfloorTransport`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission. Comments are removed; no statement of OpenAI's was changed.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B004

/-!
# OpenAI Hecke 7/8 split: definitions bundle OAIHecke78B005

OpenAI, *The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane
Re s > 7/8*, OpenAI Math Release, September 30, 2026, https://github.com/openai/math (family 003;
Lean in `lean/OAI/NumberTheory/DirichletL`, Apache License 2.0; vendored modules of
PrimeNumberTheoremAnd and rellich-kondrachov). Carved from the port to Lean 4.33.1 / Mathlib
0df444a, comments removed. Modules:
  Eisenstein.PrimitiveRows
  Poisson.PrincipalTruncation
  Fourier.FrequencyTwists
  CubicSieve.RowMajorants
  CubicSieve.FrequencyBlocks
  Eisenstein.HyperbolicSpace
  Eisenstein.FourierCoefficients
  QuadraticSieve.AnnularRecursion
  CubicSieve.TwistedProfiles
  Eisenstein.CuspIntegration
  QuadraticSieve.DualMiddleExpansion
  QuadraticSieve.MaskedPrincipalBounds
  Mellin.VerticalContourShift
  Descent.Canonical
  Descent.SecondPass
  Descent.FirstToSecond
  Reflection.IdealBridge
  Reflection.CoprimeSource
  Reflection.SectorAggregation
  Reflection.FixedTuples
  Reflection.GlobalEnergy
  Hecke.CharacterAnalytic
  Descent.CanonicalRankExistenceInduction
  Detector.LocalWeights
  RayPrimeNormalizer
  Detector.RaySlots
  Detector.HighRowsWeights
  Hecke.DetectorDyadicProfiles
  Detector.CentralExponent
  Detector.CentralDyadicWeight
  PrimeRows.CubePrimeBound
  PrimeRows.CubeFixedPrimes
  Detector.CentralClassArithmetic
  Detector.GaussianWindows
  Detector.GaussianSlots
  Detector.GramLatticeDecay
  Detector.GramAnnularLattice
  Detector.GramJointProfile
  Hecke.DetectorRowwisePolynomial
  Hecke.InverseAmplificationConjugation
  Moments.PrimePool
  Hecke.InverseAmplificationRowwise
  Hecke.DetectorCoefficientTransfer
  Dictionary.InverseUniformLog
  Energy.AmplifierFamilyAdmission
  PrimeRows.CubeFloorArithmetic
  PrimeRows.CubeFloorGlobal
  PrimeRows.CubeFloorGlobalIntegral
  PrimeRows.CubeFloorNormalized
  PrimeRows.CubeFloorSaving
  PrimeRows.CubeFloorCollected
  PrimeRows.NonfloorClass
  PrimeRows.NormalizedTransport
  PrimeRows.NormalizedTransportSaving
  PrimeRows.NonfloorTransport
-/

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

namespace CubicEisenstein
open scoped BigOperators Classical MatrixGroups Matrix

open ActualEisensteinCubic CubicKubota ConcreteTraceCRT

lemma levelThree_of_entries (M : SL(2,O))
    (h : ∀ i j : Fin 2, (3 : O) ∣ M i j - (if i=j then 1 else 0)) :
    M ∈ levelThree := by
  change Matrix.SpecialLinearGroup.map (n := Fin 2)
    (Ideal.Quotient.mk (Ideal.span {(3 : O)})) M = 1
  apply Subtype.ext
  funext i j
  change Ideal.Quotient.mk (Ideal.span {(3 : O)}) (M i j) =
    (1 : Matrix (Fin 2) (Fin 2) (O ⧸ Ideal.span {(3 : O)})) i j
  have hh : Ideal.Quotient.mk (Ideal.span {(3 : O)}) (M i j) =
      Ideal.Quotient.mk (Ideal.span {(3 : O)}) (if i=j then 1 else 0) :=
    (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
      (Ideal.mem_span_singleton.mpr (h i j))
  simpa only [Matrix.one_apply, apply_ite, map_one, map_zero] using hh

lemma row_coprime (M : levelThree) : IsCoprime (row M 0) (row M 1) := by
  have h : (M : SL(2,O)) 0 0*(M : SL(2,O)) 1 1 -
      (M : SL(2,O)) 0 1*(M : SL(2,O)) 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using (M : SL(2,O)).property
  refine ⟨-(M : SL(2,O)) 0 1, (M : SL(2,O)) 0 0, ?_⟩
  change -(M : SL(2,O)) 0 1*(M : SL(2,O)) 1 0 +
    (M : SL(2,O)) 0 0*(M : SL(2,O)) 1 1 = 1
  linear_combination h

lemma exists_matrix_of_primitive_row (c d : O) (hcop : IsCoprime c d)
    (hc : (3 : O) ∣ c) (hd : (3 : O) ∣ d-1) :
    ∃ M : levelThree, row M = ![c,d] := by
  obtain ⟨r,s,hrs⟩ := hcop
  let M : SL(2,O) := ⟨!![s+r*c,r*(d-1); c,d], by
    rw [Matrix.det_fin_two]
    change (s+r*c)*d-(r*(d-1))*c=1
    linear_combination hrs⟩
  have hA : s+r*c-1 = -s*(d-1) := by linear_combination hrs
  have hM : M ∈ levelThree := by
    apply levelThree_of_entries
    intro i j
    fin_cases i <;> fin_cases j
    · change (3 : O) ∣ s+r*c-1
      rw [hA]
      exact hd.mul_left (-s)
    · change (3 : O) ∣ r*(d-1)-0
      simpa only [sub_zero] using hd.mul_left r
    · change (3 : O) ∣ c-(if (1 : Fin 2)=0 then 1 else 0)
      simpa only [show (1 : Fin 2) ≠ 0 by decide, ite_false, sub_zero] using hc
    · change (3 : O) ∣ d-1
      exact hd
  exact ⟨⟨M,hM⟩, rfl⟩

def PrimitiveRow := {v : Fin 2 → O //
  IsCoprime (v 0) (v 1) ∧ (3 : O) ∣ v 0 ∧ (3 : O) ∣ v 1-1}

def cosetPrimitiveRow (x : CuspCosets) : PrimitiveRow :=
  ⟨cosetRow x, by
    induction x using Quotient.inductionOn with | _ M =>
      change IsCoprime (row M 0) (row M 1) ∧ (3 : O) ∣ row M 0 ∧ (3 : O) ∣ row M 1-1
      exact ⟨row_coprime M, levelThree_lower M, by simpa [row] using levelThree_entry M 1 1⟩⟩

lemma cosetPrimitiveRow_bijective : Function.Bijective cosetPrimitiveRow := by
  constructor
  · intro x y hxy
    exact cosetRow_injective (congrArg Subtype.val hxy)
  · intro v
    obtain ⟨M,hM⟩ := exists_matrix_of_primitive_row (v.1 0) (v.1 1)
      v.2.1 v.2.2.1 v.2.2.2
    refine ⟨cosetOf M, ?_⟩
    apply Subtype.ext
    change row M = v.1
    rw [hM]
    funext i
    fin_cases i <;> rfl

def primitiveRowEquiv : CuspCosets ≃ PrimitiveRow := Equiv.ofBijective _ cosetPrimitiveRow_bijective

open ActualEisensteinCubic CubicKubota ConcreteTraceCRT CubicJacobiGlobal

lemma inverse_character_eq_row_symbol (M : levelThree) :
    (complexCharacter M)⁻¹ = eisEmbedding (symbol (row M 0) (row M 1)) := by
  let a := (M : SL(2,O)) 0 0
  let b := (M : SL(2,O)) 0 1
  let c := (M : SL(2,O)) 1 0
  let d := (M : SL(2,O)) 1 1
  have hdet : a*d-b*c=1 := by
    simpa only [a,b,c,d,Matrix.det_fin_two] using (M : SL(2,O)).property
  have had : a*d-1=b*c := by linear_combination hdet
  have ha : lambda^2 ∣ a-1 := levelThree_primary M
  have hd3 : (3 : O) ∣ d-1 := by simpa [d] using levelThree_entry M 1 1
  have hd : lambda^2 ∣ d-1 := lambda_sq_dvd_three.trans hd3
  obtain ⟨b0,hb⟩ := levelThree_upper M
  obtain ⟨c0,hc⟩ := levelThree_lower M
  change b=3*b0 at hb
  change c=3*c0 at hc
  have h9 : (9 : O) ∣ a*d-1 := by
    refine ⟨b0*c0, ?_⟩
    rw [had,hb,hc]
    ring
  have hcd : c ∣ a*d-1 := by rw [had]; exact dvd_mul_left c b
  have hs := symbol_denominator_congr c (a*d) 1 (primary_mul a d ha hd) (by simp) h9 hcd
  rw [symbol_mul_denominator, symbol_one] at hs
  have hm : eisEmbedding (symbol c a)*eisEmbedding (symbol c d)=1 := by
    simpa only [map_mul, map_one] using congrArg eisEmbedding hs
  change (eisEmbedding (symbol c a))⁻¹ = eisEmbedding (symbol c d)
  exact inv_eq_of_mul_eq_one_right hm

lemma inverse_cosetCharacter_eq_row_symbol (x : CuspCosets) :
    (cosetCharacter x)⁻¹ = eisEmbedding (symbol (cosetRow x 0) (cosetRow x 1)) := by
  induction x using Quotient.inductionOn with | _ M => exact inverse_character_eq_row_symbol M

lemma primitiveRowEquiv_symm_row (v : PrimitiveRow) :
    cosetRow (primitiveRowEquiv.symm v) = v.1 := by
  exact congrArg Subtype.val (primitiveRowEquiv.apply_symm_apply v)

end CubicEisenstein

open scoped BigOperators Classical SchwartzMap
namespace TruncatedPrincipalPoisson

section
local notation "O" => ActualEisensteinCubic.O
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson

def radialSource (W : ℝ → ℂ) (X : ℝ) : ℂ :=
  ∑' z : O, if z = 0 then 0 else W (‖eisEmbedding z‖ ^ 2 / X)

def radialDual (W : ℝ → ℂ) (X : ℝ) : ℂ :=
  ∑' h : O, if h = 0 then 0 else paperRadialFourier W (X * ‖eisEmbedding h‖ ^ 2)

def subsetNorm {ι : Type*} (P : ι → Ideal O) (E : Finset ι) : ℝ :=
  Ideal.absNorm (∏ i ∈ E, P i)

def subsetMobius {ι : Type*} (P : ι → Ideal O) (E : Finset ι) : ℂ :=
  UniqueFactorizationMonoid.moebius (∏ i ∈ E, P i)

def smallDivisors {ι : Type*} [DecidableEq ι] (P : ι → Ideal O) (S : Finset ι) (Z : ℝ) :=
  S.powerset.filter (fun E => subsetNorm P E ≤ Z)

def largeDivisors {ι : Type*} [DecidableEq ι] (P : ι → Ideal O) (S : Finset ι) (Z : ℝ) :=
  S.powerset.filter (fun E => Z < subsetNorm P E)

end

local notation "O" => ActualEisensteinCubic.O
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson

def middleDivisors {ι : Type*} [DecidableEq ι] (P : ι → Ideal O) (S : Finset ι) (Y Z : ℝ) :=
  (smallDivisors P S Z).filter (fun E => Y < subsetNorm P E)

def dualNear (W : ℝ → ℂ) (X lengthScale : ℝ) : ℂ :=
  ∑' h : O, if ‖eisEmbedding h‖ ^ 2 ≤ lengthScale then
    (if h = 0 then 0 else paperRadialFourier W (X * ‖eisEmbedding h‖ ^ 2)) else 0

def dualFar (W : ℝ → ℂ) (X lengthScale : ℝ) : ℂ :=
  ∑' h : O, if lengthScale < ‖eisEmbedding h‖ ^ 2 then
    (if h = 0 then 0 else paperRadialFourier W (X * ‖eisEmbedding h‖ ^ 2)) else 0

end TruncatedPrincipalPoisson

open scoped BigOperators Classical SchwartzMap

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

open scoped BigOperators Classical SchwartzMap
namespace TruncatedPrincipalPoisson

local notation "O" => ActualEisensteinCubic.O
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson

def principalTruncation {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) (S : Finset ι) (W : ℝ → ℂ) (X Z : ℝ) : ℂ :=
  (X : ℂ) * paperRadialFourier W 0 * (∏ i ∈ S, (1 - (1 : ℂ) / Ideal.absNorm (P i))) -
  (X : ℂ) * paperRadialFourier W 0 *
    (∑ E ∈ largeDivisors P S Z, subsetMobius P E / (subsetNorm P E : ℂ)) -
  W 0 * (∑ E ∈ smallDivisors P S Z, subsetMobius P E)

def middleTruncation {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) (S : Finset ι) (W : ℝ → ℂ) (X Y Z lengthScale : ℝ) : ℂ :=
  (X : ℂ) * ∑ E ∈ middleDivisors P S Y Z,
    (subsetMobius P E / (subsetNorm P E : ℂ)) *
      ∑ h ∈ rowNormDisk ⌊lengthScale⌋₊, paperRadialFourier W ((X / subsetNorm P E) * ‖eisEmbedding h‖ ^ 2)

def truncationError {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) (S : Finset ι) (W : ℝ → ℂ) (X Y Z lengthScale : ℝ) : ℂ :=
  (∑' z : O, rowCoprimeMask P S z * (if z = 0 then 0 else W (‖eisEmbedding z‖ ^ 2 / X))) -
    (principalTruncation P S W X Z + middleTruncation P S W X Y Z lengthScale)

end TruncatedPrincipalPoisson

namespace JointLogSeparation

open MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform

section
open FourierBridge FirstPassCubeLabels

def profileSourceBound (g : 𝓢(ℝ, ℂ)) (J : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (J + 1),
    ((SchwartzMap.seminorm ℝ 0 i) g +
      (SchwartzMap.seminorm ℝ (volume : Measure ℝ).integrablePower i) g)

def fixedColumnTest (V : ℝ → ℂ) (t : ℝ) (x : ℝ) : ℂ := V x * logPhase t x

end

open FirstPassCubeLabels

end JointLogSeparation

open scoped BigOperators
namespace FiniteOverlapDecomposition
variable {ι : Type*} [DecidableEq ι]

abbrev Triple (ι : Type*) := Σ _ : Finset ι, Finset ι × Finset ι

def triples (F : Finset ι) : Finset (Triple ι) :=
  F.powerset.sigma fun G => ((F \ G).powerset ×ˢ (F \ G).powerset).filter fun UV => Disjoint UV.1 UV.2

def split (ST : Finset ι × Finset ι) : Triple ι :=
  ⟨ST.1 ∩ ST.2, ST.1 \ ST.2, ST.2 \ ST.1⟩

def join (GUV : Triple ι) : Finset ι × Finset ι :=
  (GUV.1 ∪ GUV.2.1, GUV.1 ∪ GUV.2.2)

end FiniteOverlapDecomposition

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

namespace JointLogSeparation

open MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform
open FourierBridge

lemma logPhase_temperate (t : ℝ) : (logPhase t).HasTemperateGrowth := by
  have hl : Function.HasTemperateGrowth (fun x : ℝ => (2 * Real.pi * t) * x) := by
    simpa [Pi.smul_def, smul_eq_mul] using (((2 * Real.pi * t) • ContinuousLinearMap.id ℝ ℝ).hasTemperateGrowth)
  exact Complex.hasTemperateGrowth_exp_mul_I.comp hl

def frequencyTwist (g : 𝓢(ℝ, ℂ)) (t : ℝ) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (logPhase t) g

@[simp] lemma frequencyTwist_apply (g : 𝓢(ℝ, ℂ)) (t x : ℝ) :
    frequencyTwist g t x = logPhase t x * g x := by
  exact SchwartzMap.smulLeftCLM_apply_apply (logPhase_temperate t) g x

@[simp] lemma frequencyTwist_norm (g : 𝓢(ℝ, ℂ)) (t x : ℝ) :
    ‖frequencyTwist g t x‖ = ‖g x‖ := by simp [logPhase_norm]

def phaseDerivative (t : ℝ) : ℂ := ((2 * Real.pi * t : ℝ) : ℂ) * Complex.I

def derivativeSeminormSum (g : 𝓢(ℝ, ℂ)) (k n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), (SchwartzMap.seminorm ℝ k i) g

def twistSourceBound (g : 𝓢(ℝ, ℂ)) (K : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (K + 1),
    ((2 : ℝ)^i * (1 + 2 * Real.pi)^i *
      (derivativeSeminormSum g 0 i + derivativeSeminormSum g (volume : Measure ℝ).integrablePower i))

end JointLogSeparation

section

open scoped BigOperators Classical SchwartzMap FourierTransform
open MeasureTheory

namespace SecondPassArithmetic
open ActualEisensteinCubic
open FirstPassCubeLabels (columnLog )
open JointLogSeparation (fixedColumnTest)
open FourierBridge (logPhase)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

def fixedSecondTest (V : ℝ → ℂ) (X t s : ℝ) (negative : Bool) (N : Finset ι) : ℂ :=
  if negative then star (fixedColumnTest V (t-s) (columnLog p X N))
  else fixedColumnTest V (t-s) (columnLog p X N)

end SecondPassArithmetic
end

open scoped BigOperators Classical

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

open scoped BigOperators Classical SchwartzMap
namespace SecondPassArithmetic

section

open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)
open RayFourExpansion (RayCharacter)

theorem exists_rowMajorant : ∃ W : 𝓢(ℝ, ℂ),
    (∀ s : ℝ, 0 ≤ (W s).re) ∧
    (∀ s : ℝ, |s| ≤ 1 → W s = 1) ∧
    (∀ s : ℝ, 2 < s → W s = 0) := by
  obtain ⟨U, hUc, hUs, hUone, hUts, hUzero⟩ :=
    FourierBridge.exists_complex_smooth_cutoff 1 (by norm_num)
  let f : ℝ → ℂ := fun s => U s * star (U s)
  have hfc : HasCompactSupport f := hUc.mul_right
  have hfs : ContDiff ℝ ∞ f := hUs.mul (Complex.conjCLE.contDiff.comp hUs)
  refine ⟨hfc.toSchwartzMap hfs, ?_, ?_, ?_⟩
  · intro s
    change 0 ≤ (U s * star (U s)).re
    simp only [Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
    nlinarith [sq_nonneg (U s).re, sq_nonneg (U s).im]
  · intro s hs
    change U s * star (U s) = 1
    rw [hUone s hs]
    norm_num
  · intro s hs
    change U s * star (U s) = 0
    have hUz : U s = 0 := by
      by_contra hne
      have hu := hUts (subset_tsupport U (by exact hne))
      norm_num at hu
      linarith [hu.2]
    simp [hUz]

def rowMajorant : 𝓢(ℝ, ℂ) := Classical.choose exists_rowMajorant

def rowMajorantBall (Y : ℝ) : Finset O := ShortDraftLatticeCount.rowNormBall (Nat.ceil (2 * Y))

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

end

open ActualEisensteinCubic
open FirstCauchyArithmetic (supportMobius)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

def secondPreKernelPair (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ)
    (m r c d e k₁ k₂ : O) (K : Finset ι → Finset ι → ℂ) : ℂ :=
  ∑ S ∈ F.powerset, ∑ T ∈ F.powerset, if Disjoint S T then
    star (secondPreColumn p hp hcop hg Ψ₁ (m * (e * r)) c d e k₁ (fun _ => 1) S) *
      secondPreColumn p hp hcop hg Ψ₂ (m * (e * r)) c d e k₂ (fun _ => 1) T * K S T else 0

def secondChildKernelPair (F V : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ)
    (m r c d e k₁ k₂ : O) (K : Finset ι → Finset ι → ℂ) : ℂ :=
  ∑ N ∈ (F \ V).powerset, ∑ M ∈ (F \ V).powerset,
    star (secondChildColumn p hp hcop hg Ψ₁ (m * r) (c * e * ∏ i ∈ V, p i)
      (d * e * k₁) (fun _ => 1) N) *
    secondChildColumn p hp hcop hg Ψ₂ (m * r) (c * e * ∏ i ∈ V, p i)
      (d * e * k₂) (fun _ => 1) M * K (V ∪ N) (V ∪ M)

def secondKernelPair (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k : O)
    (K : Finset ι → Finset ι → ℂ) : ℂ :=
  ∑ S ∈ F.powerset, ∑ T ∈ F.powerset, if Disjoint S T then
    secondGaussTerm p hp hg hinj Ψ₁ Ψ₂ m r c d e k (fun _ => 1) (fun _ => 1) S T * K S T else 0

end SecondPassArithmetic

namespace CubicEisenstein
open scoped BigOperators Classical MatrixGroups Matrix

open ActualEisensteinCubic CubicKubota ConcreteTraceCRT CubicJacobiGlobal

def denominatorCondition (c d : O) : Prop := IsCoprime c d ∧ (3 : O) ∣ d-1
abbrev AdmissibleDenominator (c : O) := {d : O // denominatorCondition c d}
abbrev LevelLower := {c : O // (3 : O) ∣ c}

lemma denominatorCondition_shift (c d n : O) :
    denominatorCondition c (d+3*c*n) ↔ denominatorCondition c d := by
  constructor
  · rintro ⟨⟨a,b,h⟩,hd⟩
    refine ⟨⟨a+b*3*n,b,by linear_combination h⟩, ?_⟩
    have h3 : (3 : O) ∣ 3*c*n := ⟨c*n,by ring⟩
    convert (preTransparency := .instances) dvd_sub hd h3 using 1 ; ring
  · rintro ⟨⟨a,b,h⟩,hd⟩
    refine ⟨⟨a-b*3*n,b,by linear_combination h⟩, ?_⟩
    have h3 : (3 : O) ∣ 3*c*n := ⟨c*n,by ring⟩
    convert (preTransparency := .instances) dvd_add hd h3 using 1 ; ring

lemma row_symbol_shift (c d n : O) (hc : (3 : O) ∣ c) (hd : (3 : O) ∣ d-1) :
    symbol c (d+3*c*n)=symbol c d := by
  have hdn : (3 : O) ∣ d+3*c*n-1 := by
    convert (preTransparency := .instances) dvd_add hd (show (3 : O) ∣ 3*c*n from ⟨c*n,by ring⟩) using 1 ; ring
  have h9 : (9 : O) ∣ d+3*c*n-d := by
    obtain ⟨c0,rfl⟩ := hc
    exact ⟨c0*n,by ring⟩
  exact symbol_denominator_congr c (d+3*c*n) d
    (lambda_sq_dvd_three.trans hdn) (lambda_sq_dvd_three.trans hd) h9
    ⟨3*n,by ring⟩

def primitiveSigmaEquiv : PrimitiveRow ≃ Σ c : LevelLower, AdmissibleDenominator c.1 where
  toFun r := ⟨⟨r.1 0,r.2.2.1⟩,⟨r.1 1,r.2.1,r.2.2.2⟩⟩
  invFun p := ⟨![p.1.1,p.2.1],p.2.2.1,p.1.2,p.2.2.2⟩
  left_inv r := by
    apply Subtype.ext
    funext i
    fin_cases i <;> rfl
  right_inv p := by rfl

abbrev DenominatorResidue (c : O) := O ⧸ Ideal.span {3*c}
def denominatorRep (c : O) (r : DenominatorResidue c) : O :=
  GaussianShiftedPartition.representative (3*c) r
lemma denominatorRep_spec (c : O) (r : DenominatorResidue c) :
    Ideal.Quotient.mk (Ideal.span {3*c}) (denominatorRep c r)=r :=
  GaussianShiftedPartition.representative_spec (3*c) r
abbrev AdmissibleResidue (c : O) :=
  {r : DenominatorResidue c // denominatorCondition c (denominatorRep c r)}

lemma finite_admissibleResidue (c : O) (hc : c ≠ 0) : Finite (AdmissibleResidue c) := by
  let : Finite (DenominatorResidue c) := finite_quotient_span (mul_ne_zero (by norm_num) hc)
  infer_instance

def residueDenominatorMap (c : O) (p : AdmissibleResidue c × O) : AdmissibleDenominator c :=
  ⟨denominatorRep c p.1.1+3*c*p.2,(denominatorCondition_shift c _ _).2 p.1.2⟩

lemma residueDenominatorMap_bijective (c : O) (hc : c ≠ 0) :
    Function.Bijective (residueDenominatorMap c) := by
  have h3c : 3*c ≠ 0 := mul_ne_zero (by norm_num) hc
  have hq (r : DenominatorResidue c) (n : O) :
      Ideal.Quotient.mk (Ideal.span {3*c}) (denominatorRep c r+3*c*n)=r := by
    have hzero : Ideal.Quotient.mk (Ideal.span {3*c}) (3*c)=0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
    rw [map_add, map_mul, hzero, zero_mul, add_zero, denominatorRep_spec]
  constructor
  · rintro ⟨r,n⟩ ⟨t,m⟩ heq
    have h := congrArg Subtype.val heq
    change denominatorRep c r.1+3*c*n=denominatorRep c t.1+3*c*m at h
    have hrt : r=t := by
      apply Subtype.ext
      simpa only [hq] using congrArg (Ideal.Quotient.mk (Ideal.span {3*c})) h
    subst t
    have hnm : n=m := mul_left_cancel₀ h3c (add_left_cancel h)
    subst m
    rfl
  · intro d
    let r : DenominatorResidue c := Ideal.Quotient.mk (Ideal.span {3*c}) d.1
    have hr : Ideal.Quotient.mk (Ideal.span {3*c}) (denominatorRep c r)=r := denominatorRep_spec c r
    have hdiv : 3*c ∣ d.1-denominatorRep c r := by
      apply Ideal.mem_span_singleton.mp
      apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp
      exact hr.symm
    obtain ⟨n,hn⟩ := hdiv
    have hd : d.1=denominatorRep c r+3*c*n := by linear_combination hn
    have hrcond : denominatorCondition c (denominatorRep c r) := by
      apply (denominatorCondition_shift c _ n).1
      rw [← hd]
      exact d.2
    refine ⟨(⟨r,hrcond⟩,n), ?_⟩
    apply Subtype.ext
    exact hd.symm

def residueDenominatorEquiv (c : O) (hc : c ≠ 0) :
    AdmissibleResidue c × O ≃ AdmissibleDenominator c :=
  Equiv.ofBijective (residueDenominatorMap c) (residueDenominatorMap_bijective c hc)

def primitiveTerm (z : ℂ) (v : ℝ) (s : ℂ) (c d : O) : ℂ :=
  eisEmbedding (symbol c d) *
    ((v/(‖eisEmbedding c*z+eisEmbedding d‖^2+‖eisEmbedding c‖^2*v^2):ℝ):ℂ)^s

theorem denominator_sum_residues (c : O) (hc : c ≠ 0) (f : O → ℂ)
    (hf : Summable (fun d : AdmissibleDenominator c => f d.1)) :
    (∑' d : AdmissibleDenominator c, f d.1)=
      ∑' r : AdmissibleResidue c, ∑' n : O, f (denominatorRep c r.1+3*c*n) := by
  have hsum := (residueDenominatorEquiv c hc).summable_iff.mpr hf
  exact ((residueDenominatorEquiv c hc).tsum_eq
    (fun d : AdmissibleDenominator c => f d.1)).symm.trans hsum.tsum_prod

lemma primitiveTerm_shift (z : ℂ) (v : ℝ) (s : ℂ) (c d n : O)
    (hc : (3 : O) ∣ c) (hd : (3 : O) ∣ d-1) :
    primitiveTerm z v s c (d+3*c*n)=
      primitiveTerm (z+3*eisEmbedding n) v s c d := by
  unfold primitiveTerm
  rw [row_symbol_shift c d n hc hd]
  have harg : eisEmbedding c*z+eisEmbedding (d+3*c*n)=
      eisEmbedding c*(z+3*eisEmbedding n)+eisEmbedding d := by
    simp only [map_add,map_mul,map_ofNat]
    ring
  rw [harg]

lemma denominator_zero_unique (d : AdmissibleDenominator 0) : d.1=1 := by
  apply A3_primary_unit_eq_one _ _ (lambda_sq_dvd_three.trans d.2.2)
  simpa only [isCoprime_zero_left] using d.2.1

end CubicEisenstein

open MeasureTheory Set Module
open scoped BigOperators Classical ENNReal

namespace CubicEisenstein
open ActualEisensteinCubic ConcreteTraceCRT EisensteinEmbedding EisensteinSchwartzPoisson
local notation "O" => ActualEisensteinCubic.O

def periodBasis : Basis (Fin 2) ℝ ℂ :=
  Complex.basisOneI.map (eisensteinLatticeMap 3 (by norm_num)).toLinearEquiv
lemma periodBasis_zero : periodBasis 0=3 := by
  simp [periodBasis,eisensteinLatticeMap,scaledBasisEquiv_apply]
lemma periodBasis_one : periodBasis 1=3*omega3 := by
  simp [periodBasis,eisensteinLatticeMap,scaledBasisEquiv_apply]

def periodLattice : Submodule ℤ ℂ := Submodule.span ℤ (Set.range periodBasis)
def periodDomain : Set ℂ := ZSpan.fundamentalDomain periodBasis

instance : Countable periodLattice := by unfold periodLattice; infer_instance
instance : VAddInvariantMeasure periodLattice ℂ volume :=
  inferInstanceAs (VAddInvariantMeasure periodLattice.toAddSubgroup ℂ volume)

lemma periodDomain_fundamental : IsAddFundamentalDomain periodLattice periodDomain volume :=
  ZSpan.isAddFundamentalDomain periodBasis volume
lemma periodDomain_measurable : MeasurableSet periodDomain :=
  ZSpan.fundamentalDomain_measurableSet periodBasis

lemma three_embedding_mem (n : O) : 3*eisEmbedding n ∈ periodLattice := by
  have hzero : periodBasis 0 ∈ periodLattice := Submodule.subset_span ⟨0,rfl⟩
  have hone : periodBasis 1 ∈ periodLattice := Submodule.subset_span ⟨1,rfl⟩
  have h := periodLattice.add_mem
    (periodLattice.smul_mem (ActualEisensteinCoordinates.coords n).1 hzero)
    (periodLattice.smul_mem (ActualEisensteinCoordinates.coords n).2 hone)
  rw [periodBasis_zero,periodBasis_one] at h
  convert (preTransparency := .instances) h using 1
  conv_lhs => rw [← ActualEisensteinCoordinates.eval_coords n,eisEmbedding_eval]
  simp only [zsmul_eq_mul,]
  ring

def periodPoint (n : O) : periodLattice := ⟨3*eisEmbedding n,three_embedding_mem n⟩
lemma periodPoint_bijective : Function.Bijective periodPoint := by
  constructor
  · intro n m h
    apply eisEmbedding_injective
    exact mul_left_cancel₀ (by norm_num : (3:ℂ)≠0) (congrArg Subtype.val h)
  · intro p
    have h := (periodBasis.mem_span_iff_repr_mem ℤ p.1).mp p.2
    obtain ⟨a,ha⟩ := h 0
    obtain ⟨b,hb⟩ := h 1
    change (a:ℝ)=_ at ha
    change (b:ℝ)=_ at hb
    refine ⟨ActualEisensteinCoordinates.eval a b, ?_⟩
    apply Subtype.ext
    change 3*eisEmbedding (ActualEisensteinCoordinates.eval a b)=p.1
    rw [← periodBasis.sum_repr p.1,Fin.sum_univ_two,← ha,← hb,
      periodBasis_zero,periodBasis_one,eisEmbedding_eval]
    simp only [Complex.real_smul,Complex.ofReal_intCast]
    ring

def periodEquiv : O ≃ periodLattice := Equiv.ofBijective _ periodPoint_bijective

theorem integral_eq_period_integrals (f : ℂ → ℂ) (hf : Integrable f) :
    (∫ z : ℂ, f z)=∑' n : O,∫ z in periodDomain,f (z+3*eisEmbedding n) := by
  rw [periodDomain_fundamental.integral_eq_tsum'' f hf]
  rw [← periodEquiv.tsum_eq]
  apply tsum_congr
  intro n
  apply setIntegral_congr_fun periodDomain_measurable
  intro z hz
  change f (3*eisEmbedding n+z)=f (z+3*eisEmbedding n)
  rw [add_comm]

theorem lintegral_eq_period_lintegrals (f : ℂ → ℝ≥0∞) :
    (∫⁻ z : ℂ, f z)=∑' n : O,∫⁻ z in periodDomain,f (z+3*eisEmbedding n) := by
  rw [periodDomain_fundamental.lintegral_eq_tsum'' f]
  rw [← periodEquiv.tsum_eq]
  apply tsum_congr
  intro n
  apply setLIntegral_congr_fun periodDomain_measurable
  intro z hz
  change f (3*eisEmbedding n+z)=f (z+3*eisEmbedding n)
  rw [add_comm]

lemma periodDomain_volume : volume periodDomain=ENNReal.ofReal (9*Real.sqrt 3/2) := by
  have hunit : volume (ZSpan.fundamentalDomain Complex.basisOneI)=1 := by
    rw [measure_congr (ZSpan.fundamentalDomain_ae_parallelepiped Complex.basisOneI volume)]
    exact Complex.orthonormalBasisOneI.volume_parallelepiped
  rw [periodDomain,ZSpan.measure_fundamentalDomain periodBasis volume Complex.basisOneI,hunit,mul_one]
  congr 1
  rw [Basis.det_apply,Matrix.det_fin_two]
  norm_num [Basis.toMatrix_apply,periodBasis_zero,periodBasis_one,
    Complex.coe_basisOneI_repr,EisensteinEmbedding.omega3_im]
  rw [abs_of_nonneg (by positivity)]
  ring

end CubicEisenstein

end

end OAI
end

section

namespace OAI

noncomputable section

namespace SecondPassArithmetic

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

section

open scoped BigOperators Classical SchwartzMap

open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)
open FirstCauchyArithmetic (supportConjugateSum supportMobius)
open RayFourExpansion (RayCharacter)

def nonzeroRowMajorantSum (P : O → ℂ) (Y : ℝ) : ℂ :=
  ∑' z : O, if z = 0 then 0 else
    rowMajorant (‖eisEmbedding z‖ ^ 2 / Y) * (↑(‖P z‖ ^ 2) : ℂ)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

end

section

open scoped BigOperators Classical

open ActualEisensteinCubic
open FirstPassCubeLabels (jLabel b0Label primeProductNorm)

@[ext] structure SecondSupportData (ι : Type*) where
  common : Finset ι
  firstDivisor : Finset ι
  secondDivisor : Finset ι
  overlap : Finset ι
  frequency : O
  deriving DecidableEq

instance {ι : Type*} : Inhabited (SecondSupportData ι) := ⟨⟨∅, ∅, ∅, ∅, 0⟩⟩

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]

end

open MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform
open ActualEisensteinCubic
open JointLogSeparation
open FirstPassCubeLabels (b0Label)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

end SecondPassArithmetic

end

end OAI
end

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

section
open scoped BigOperators Classical MatrixGroups Matrix

section
open CubicKubota

def compactSubgroup : Subgroup (SL(2,ℂ)) where
  carrier := {k | (k : Matrix (Fin 2) (Fin 2) ℂ) ∈ Matrix.unitaryGroup (Fin 2) ℂ}
  one_mem' := (Matrix.unitaryGroup (Fin 2) ℂ).one_mem
  mul_mem' := by
    intro a b ha hb
    exact (Matrix.unitaryGroup (Fin 2) ℂ).mul_mem ha hb
  inv_mem' := by
    intro k hk
    have hinv : (k⁻¹ : SL(2,ℂ)) * k = 1 := inv_mul_cancel k
    have hmat : ((k⁻¹ : SL(2,ℂ)) : Matrix (Fin 2) (Fin 2) ℂ) *
        (k : Matrix (Fin 2) (Fin 2) ℂ) = 1 := congrArg
          (fun a : SL(2,ℂ) => (a : Matrix (Fin 2) (Fin 2) ℂ)) hinv
    have he := Matrix.left_inv_eq_left_inv hmat (Matrix.mem_unitaryGroup_iff'.mp hk)
    change ((k⁻¹ : SL(2,ℂ)) : Matrix (Fin 2) (Fin 2) ℂ) ∈ Matrix.unitaryGroup (Fin 2) ℂ
    rw [he]
    exact Unitary.star_mem hk

abbrev HyperbolicSpace := SL(2,ℂ) ⧸ compactSubgroup

def hyperbolicEisenstein (s : ℂ) : HyperbolicSpace → ℂ :=
  Quotient.lift (fun g => eisenstein g s) (by
    intro g h hgh
    have hk : g⁻¹*h ∈ compactSubgroup := QuotientGroup.leftRel_apply.mp hgh
    have hh : h = g*(g⁻¹*h) := by group
    rw [hh]
    exact (eisenstein_right_unitary g (g⁻¹*h) s hk).symm)

@[simp] lemma hyperbolicEisenstein_mk (s : ℂ) (g : SL(2,ℂ)) :
    hyperbolicEisenstein s (g : HyperbolicSpace) = eisenstein g s := rfl

theorem hyperbolicEisenstein_automorphy (M : levelThree) (s : ℂ) (hs : 2 < s.re)
    (w : HyperbolicSpace) :
    hyperbolicEisenstein s (complexMatrix M • w) =
      complexCharacter M * hyperbolicEisenstein s w := by
  induction w using Quotient.inductionOn with | _ g =>
    exact eisenstein_automorphy M g s hs

def upperPoint (z : ℂ) (v : ℝ) (hv : 0 < v) : HyperbolicSpace :=
  (upperSection z v hv : HyperbolicSpace)

lemma hyperbolicEisenstein_upperPoint (s : ℂ) (z : ℂ) (v : ℝ) (hv : 0 < v) :
    hyperbolicEisenstein s (upperPoint z v hv) = upperEisenstein z v hv s := rfl

def complexBottomRow (g : SL(2,ℂ)) : Fin 2 → ℂ := g 1

lemma complexBottomRow_mul (g h : SL(2,ℂ)) :
    complexBottomRow (g*h) = rowOperator h (complexBottomRow g) := by
  funext j
  simp only [complexBottomRow, rowOperator_apply, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.mul_apply, Matrix.vecMul, dotProduct]

lemma complexBottomRow_ne_zero (g : SL(2,ℂ)) : complexBottomRow g ≠ 0 := by
  intro hz
  have hc : g 1 0 = 0 := congrFun hz 0
  have hd : g 1 1 = 0 := congrFun hz 1
  have h : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using g.property
  simp only [hc, hd, mul_zero, sub_zero] at h
  exact zero_ne_one h

def liftedHeight (g : SL(2,ℂ)) : ℝ := (rowEnergy (complexBottomRow g))⁻¹

lemma liftedHeight_pos (g : SL(2,ℂ)) : 0 < liftedHeight g :=
  inv_pos.mpr (rowEnergy_pos _ (complexBottomRow_ne_zero g))

lemma liftedHeight_right_unitary (g k : SL(2,ℂ)) (hk : k ∈ compactSubgroup) :
    liftedHeight (g*k) = liftedHeight g := by
  simp only [liftedHeight, complexBottomRow_mul, rowEnergy_unitary k hk]

def hyperbolicHeight : HyperbolicSpace → ℝ :=
  Quotient.lift liftedHeight (by
    intro g h hgh
    have hk : g⁻¹*h ∈ compactSubgroup := QuotientGroup.leftRel_apply.mp hgh
    have hh : h = g*(g⁻¹*h) := by group
    rw [hh]
    exact (liftedHeight_right_unitary g (g⁻¹*h) hk).symm)

@[simp] lemma hyperbolicHeight_mk (g : SL(2,ℂ)) :
    hyperbolicHeight (g : HyperbolicSpace) = liftedHeight g := rfl

lemma hyperbolicHeight_pos (w : HyperbolicSpace) : 0 < hyperbolicHeight w := by
  induction w using Quotient.inductionOn with | _ g => exact liftedHeight_pos g

theorem hyperbolicHeight_action_upperPoint (g : SL(2,ℂ)) (z : ℂ) (v : ℝ) (hv : 0 < v) :
    hyperbolicHeight (g • upperPoint z v hv) =
      v / (‖g 1 0*z + g 1 1‖ ^ 2 + ‖g 1 0‖ ^ 2 * v ^ 2) := by
  change liftedHeight (g * upperSection z v hv) = _
  rw [liftedHeight, complexBottomRow_mul, rowEnergy_upperSection, inv_div]
  rfl

def cosetHeight (x : CuspCosets) : HyperbolicSpace → ℝ :=
  Quotient.lift (fun g : SL(2,ℂ) => (rowEnergy (rowOperator g (embeddedRow x)))⁻¹) (by
    intro g h hgh
    have hk : g⁻¹*h ∈ compactSubgroup := QuotientGroup.leftRel_apply.mp hgh
    have hh : h = g*(g⁻¹*h) := by group
    rw [hh, ← rowOperator_mul, rowEnergy_unitary (g⁻¹*h) hk])

lemma cosetHeight_cosetOf (M : levelThree) (w : HyperbolicSpace) :
    cosetHeight (cosetOf M) w = hyperbolicHeight (complexMatrix M • w) := by
  induction w using Quotient.inductionOn with | _ g =>
    change (rowEnergy (rowOperator g (embeddedRow (cosetOf M))))⁻¹ =
      liftedHeight (complexMatrix M * g)
    rw [liftedHeight, complexBottomRow_mul]
    rfl

theorem hyperbolicEisenstein_eq_height_series (s : ℂ) (w : HyperbolicSpace) :
    hyperbolicEisenstein s w = ∑' x : CuspCosets,
      (cosetCharacter x)⁻¹ * (cosetHeight x w : ℂ) ^ s := by
  induction w using Quotient.inductionOn with | _ g =>
    apply tsum_congr
    intro x
    change (cosetCharacter x)⁻¹ *
      (rowEnergy (rowOperator g (embeddedRow x)) : ℂ) ^ (-s) =
      (cosetCharacter x)⁻¹ * ((rowEnergy (rowOperator g (embeddedRow x)))⁻¹ : ℝ) ^ s
    rw [Complex.ofReal_inv, Complex.inv_cpow_ofReal_nonneg (rowEnergy_nonneg _),
      Complex.cpow_neg]

theorem height_series_summable_norm (s : ℂ) (hs : 2 < s.re) (w : HyperbolicSpace) :
    Summable (fun x : CuspCosets =>
      ‖(cosetCharacter x)⁻¹ * (cosetHeight x w : ℂ) ^ s‖) := by
  induction w using Quotient.inductionOn with | _ g =>
    apply (summable_norm_summand g s hs).congr
    intro x
    congr 1
    change (cosetCharacter x)⁻¹ *
      (rowEnergy (rowOperator g (embeddedRow x)) : ℂ) ^ (-s) =
      (cosetCharacter x)⁻¹ * ((rowEnergy (rowOperator g (embeddedRow x)))⁻¹ : ℝ) ^ s
    rw [Complex.ofReal_inv, Complex.inv_cpow_ofReal_nonneg (rowEnergy_nonneg _),
      Complex.cpow_neg]

end

open ActualEisensteinCubic CubicKubota ConcreteTraceCRT

def upperTranslation (a : O) : levelThree := by
  let M : SL(2,O) := ⟨!![1, 3*a; 0, 1], by simp⟩
  refine ⟨M, ?_⟩
  change Matrix.SpecialLinearGroup.map (n := Fin 2)
    (Ideal.Quotient.mk (Ideal.span {(3 : O)})) M = 1
  have h3 : Ideal.Quotient.mk (Ideal.span {(3 : O)}) (3 : O) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  apply Subtype.ext
  funext i j
  change Ideal.Quotient.mk (Ideal.span {(3 : O)}) ((!![(1 : O), 3*a; 0, 1]) i j) =
    (1 : Matrix (Fin 2) (Fin 2) (O ⧸ Ideal.span {(3 : O)})) i j
  fin_cases i <;> fin_cases j <;> simp [h3, map_mul]

lemma complexCharacter_upperTranslation (a : O) : complexCharacter (upperTranslation a) = 1 := by
  change eisEmbedding (value (upperTranslation a)) = 1
  rw [value_zero_lower_left _ (by rfl), map_one]

lemma upperTranslation_section (a : O) (z : ℂ) (v : ℝ) (hv : 0 < v) :
    complexMatrix (upperTranslation a) * upperSection z v hv =
      upperSection (z + 3*eisEmbedding a) v hv := by
  apply Subtype.ext
  funext i j
  change (((!![(1 : O), 3*a; 0, 1]).map eisEmbedding) *
    !![(Real.sqrt v : ℂ), z/(Real.sqrt v : ℂ); 0, (Real.sqrt v : ℂ)⁻¹]) i j =
    (!![(Real.sqrt v : ℂ), (z+3*eisEmbedding a)/(Real.sqrt v : ℂ);
      0, (Real.sqrt v : ℂ)⁻¹]) i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, map_mul] ;
    norm_num only [map_ofNat] ; ring

end

open MeasureTheory Set Filter
open scoped BigOperators Classical

lemma integral_radial_sq (f : ℝ → ℂ) :
    (∫ z : ℂ, f (‖z‖ ^ 2)) = (Real.pi : ℂ) * ∫ t : ℝ in Set.Ioi 0, f t := by
  have hball : (volume : Measure ℂ).real (Metric.ball 0 1) = Real.pi := by
    simp [Measure.real, Complex.volume_ball]
  have hpolar := integral_fun_norm_addHaar (volume : Measure ℂ) (fun r : ℝ => f (r^2))
  have hsub := integral_comp_rpow_Ioi (E := ℂ) f (p := 2) (by norm_num)
  norm_num [Real.rpow_two, Real.rpow_one] at hsub
  simp only [Complex.finrank_real_complex, hball, Nat.reduceSub, pow_one,
    nsmul_eq_mul, Complex.real_smul, ] at hpolar hsub
  rw [hpolar]
  rw [← hsub]
  rw [show (fun x : ℝ => (2:ℂ)*x*f (x^2)) =
      (fun x : ℝ => (2:ℂ)*(x*f (x^2))) by funext x; ring, integral_const_mul]
  ring

lemma integrable_radial_sq_iff (f : ℝ → ℂ) :
    Integrable (fun z : ℂ => f (‖z‖ ^ 2)) ↔ IntegrableOn f (Set.Ioi 0) := by
  rw [integrable_fun_norm_addHaar (volume : Measure ℂ) (f := fun r : ℝ => f (r^2))]
  have h := integrableOn_Ioi_comp_rpow_iff' (E := ℂ) f (p := 2) (by norm_num)
  simpa only [Complex.finrank_real_complex, Nat.reduceSub, pow_one,
    show (2:ℝ)-1=1 by norm_num, Real.rpow_one, Real.rpow_two] using h

lemma add_one_image_Ioi : (fun x : ℝ => x+1) '' Set.Ioi 0 = Set.Ioi 1 := by
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    simp only [Set.mem_Ioi] at *
    linarith
  · intro hy
    refine ⟨y-1, ?_, by ring⟩
    simp only [Set.mem_Ioi] at *
    linarith

lemma integrable_add_one_Ioi_iff (f : ℝ → ℂ) :
    IntegrableOn (fun x : ℝ => f (x+1)) (Set.Ioi 0) ↔ IntegrableOn f (Set.Ioi 1) := by
  have h := integrableOn_image_iff_integrableOn_abs_deriv_smul
    measurableSet_Ioi
    (fun x (hx : x ∈ Set.Ioi (0:ℝ)) => (hasDerivAt_id x |>.add_const 1).hasDerivWithinAt)
    (fun x hx y hy hxy => by dsimp at hxy; linarith : InjOn (fun x : ℝ => x+1) (Set.Ioi 0)) f
  simp only [id_eq] at h
  rw [add_one_image_Ioi] at h
  simpa only [abs_one, one_smul] using h.symm

lemma integral_add_one_Ioi (f : ℝ → ℂ) :
    (∫ x : ℝ in Set.Ioi 0, f (x+1)) = ∫ x : ℝ in Set.Ioi 1, f x := by
  have h := integral_image_eq_integral_abs_deriv_smul
    measurableSet_Ioi
    (fun x (hx : x ∈ Set.Ioi (0:ℝ)) => (hasDerivAt_id x |>.add_const 1).hasDerivWithinAt)
    (fun x hx y hy hxy => by dsimp at hxy; linarith : InjOn (fun x : ℝ => x+1) (Set.Ioi 0)) f
  simp only [id_eq] at h
  rw [add_one_image_Ioi] at h
  simpa only [abs_one, one_smul] using h.symm

def hyperbolicKernel (s : ℂ) (z : ℂ) : ℂ := ((1+‖z‖^2 : ℝ) : ℂ) ^ (-s)

lemma hyperbolicKernel_integrable (s : ℂ) (hs : 1 < s.re) :
    Integrable (hyperbolicKernel s) := by
  unfold hyperbolicKernel
  rw [integrable_radial_sq_iff (fun t : ℝ => ((1+t : ℝ) : ℂ)^(-s))]
  have h := (integrable_add_one_Ioi_iff (fun x : ℝ => (x : ℂ)^(-s))).mpr
    (integrableOn_Ioi_cpow_of_lt (by simpa using neg_lt_neg hs) (by norm_num : (0:ℝ)<1))
  simpa only [add_comm] using h

theorem integral_hyperbolicKernel (s : ℂ) (hs : 1 < s.re) :
    (∫ z : ℂ, hyperbolicKernel s z) = (Real.pi : ℂ) / (s-1) := by
  unfold hyperbolicKernel
  rw [integral_radial_sq (fun t : ℝ => ((1+t : ℝ) : ℂ)^(-s))]
  simp_rw [add_comm (1:ℝ)]
  rw [integral_add_one_Ioi (fun t : ℝ => (t : ℂ)^(-s))]
  rw [integral_Ioi_cpow_of_lt (by simpa using neg_lt_neg hs) (by norm_num : (0:ℝ)<1)]
  simp only [Complex.ofReal_one, Complex.one_cpow]
  have hn : (-s+1)⁻¹ = -(s-1)⁻¹ := by
    rw [show -s+1=-(s-1) by ring, inv_neg]
  simp only [div_eq_mul_inv, hn]
  ring

open MeasureTheory Set Filter
open scoped BigOperators Classical FourierTransform RealInnerProductSpace

lemma breveE_norm (z : ℂ) : ‖ShortDraftTrace.breveE z‖ = 1 := by
  change ‖Complex.exp (2 * Real.pi * Complex.I * (z + starRingEnd ℂ z))‖ = 1
  rw [Complex.norm_exp]
  have hre : (2 * Real.pi * Complex.I * (z + starRingEnd ℂ z)).re = 0 := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [hre, Real.exp_zero]

def sourceFourierKernel (s freq : ℂ) : ℂ :=
  ∫ z : ℂ, hyperbolicKernel s z * ShortDraftTrace.breveE (-freq*z)

lemma sourceFourierKernel_integrable (s freq : ℂ) (hs : 1 < s.re) :
    Integrable (fun z : ℂ => hyperbolicKernel s z * ShortDraftTrace.breveE (-freq*z)) := by
  apply (hyperbolicKernel_integrable s hs).norm.mono'
  · have hker : Continuous (hyperbolicKernel s) := by
      unfold hyperbolicKernel
      apply Continuous.cpow
      · fun_prop
      · exact continuous_const
      · intro z
        exact Complex.ofReal_mem_slitPlane.mpr (by positivity)
    have hchar : Continuous (fun z : ℂ => ShortDraftTrace.breveE (-freq*z)) := by
      change Continuous (fun z : ℂ => Complex.exp (2*Real.pi*Complex.I*
        ((-freq*z)+starRingEnd ℂ (-freq*z))))
      fun_prop
    exact (hker.mul hchar).aestronglyMeasurable
  · exact Eventually.of_forall (fun z => by simp only [norm_mul, breveE_norm, mul_one, le_refl])

lemma sourceFourierKernel_zero (s : ℂ) (hs : 1 < s.re) :
    sourceFourierKernel s 0 = (Real.pi : ℂ)/(s-1) := by
  simpa only [sourceFourierKernel, neg_zero, zero_mul, AddChar.map_zero_eq_one, mul_one]
    using integral_hyperbolicKernel s hs

lemma sourceFrequency_inner (z freq : ℂ) : inner ℝ z (2*starRingEnd ℂ freq) = 2*(freq*z).re := by
  rw [real_inner_eq_re_inner (𝕜 := ℂ), RCLike.inner_apply]
  change ((2 * starRingEnd ℂ freq) * starRingEnd ℂ z).re = _
  simp [Complex.mul_re, Complex.mul_im]
  ring

lemma traceIntegral_eq_fourier (f : ℂ → ℂ) (freq : ℂ) :
    (∫ z : ℂ, f z * ShortDraftTrace.breveE (-freq*z)) = 𝓕 f (2*starRingEnd ℂ freq) := by
  rw [Real.fourier_eq']
  apply integral_congr_ae
  exact Eventually.of_forall (fun z => by
    dsimp only
    rw [sourceFrequency_inner]
    change f z *
      Complex.exp (2*Real.pi*Complex.I*((-freq*z)+starRingEnd ℂ (-freq*z))) = _
    simp only [smul_eq_mul]
    rw [mul_comm (f z)]
    congr 1
    congr 1
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring)

lemma hyperbolicKernel_laplace (s : ℂ) (hs : 0 < s.re) (z : ℂ) :
    hyperbolicKernel s z * Complex.Gamma s =
      ∫ t : ℝ in Set.Ioi 0, (t : ℂ)^(s-1) *
        Complex.exp (-((1+‖z‖^2 : ℝ) : ℂ) * t) := by
  have h := Complex.integral_cpow_mul_exp_neg_mul_Ioi hs
    (by positivity : 0 < 1+‖z‖^2)
  simp only [neg_mul]
  rw [h]
  congr 1
  rw [hyperbolicKernel, one_div, Complex.inv_cpow_ofReal_nonneg (by positivity),
    Complex.cpow_neg]

lemma source_gaussian_fourier (t : ℝ) (ht : 0 < t) (freq : ℂ) :
    𝓕 (fun z : ℂ => Complex.exp (-(t : ℂ)*‖z‖^2)) (2*starRingEnd ℂ freq) =
      (Real.pi : ℂ)/t * Complex.exp (-(4*Real.pi^2*‖freq‖^2 : ℝ)/t) := by
  rw [fourier_gaussian_innerProductSpace (by simpa using ht)]
  norm_num only [Complex.finrank_real_complex, Nat.cast_ofNat, div_self (by norm_num : (2:ℂ)≠0),
    Complex.cpow_one, norm_mul, Complex.norm_conj, Complex.norm_ofNat]
  congr 2
  push_cast
  ring

def gaussianMixture (s freq : ℂ) (t : ℝ) (z : ℂ) : ℂ :=
  (t : ℂ)^(s-1) * Complex.exp (-t) *
    Complex.exp (-(t : ℂ)*‖z‖^2) * ShortDraftTrace.breveE (-freq*z)

lemma norm_gaussianMixture (s freq : ℂ) (t : ℝ) (ht : 0 < t) (z : ℂ) :
    ‖gaussianMixture s freq t z‖ =
      t ^ (s.re-1) * Real.exp (-t) * Real.exp (-t*‖z‖^2) := by
  simp only [gaussianMixture, norm_mul, breveE_norm, mul_one,
    Complex.norm_cpow_eq_rpow_re_of_pos ht, Complex.sub_re, Complex.one_re,
    Complex.norm_exp, Complex.neg_re, Complex.ofReal_re, Complex.mul_re,
    Complex.ofReal_im, ← Complex.ofReal_pow, Complex.neg_im, neg_zero, zero_mul, sub_zero]

lemma gaussianMixture_slice_integrable (s freq : ℂ) (t : ℝ) (ht : 0 < t) :
    Integrable (gaussianMixture s freq t) := by
  have hg : Integrable (fun z : ℂ => Complex.exp (-(t : ℂ)*‖z‖^2)) := by
    simpa only [zero_mul, add_zero] using GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
      (by simpa using ht : 0 < (t : ℂ).re) 0 (0 : ℂ)
  apply ((hg.const_mul ((t : ℂ)^(s-1)*Complex.exp (-t))).norm).mono'
  · unfold gaussianMixture
    change AEStronglyMeasurable (fun z : ℂ => (t : ℂ)^(s-1)*Complex.exp (-t)*
      Complex.exp (-(t : ℂ)*‖z‖^2) *
      Complex.exp (2*Real.pi*Complex.I*((-freq*z)+starRingEnd ℂ (-freq*z))))
    fun_prop
  · exact Eventually.of_forall fun z => by
      simp only [gaussianMixture, norm_mul, breveE_norm, mul_one, le_refl]

lemma integral_norm_gaussianMixture (s freq : ℂ) (t : ℝ) (ht : 0 < t) :
    (∫ z : ℂ, ‖gaussianMixture s freq t z‖) =
      Real.pi * (Real.exp (-t)*t^(s.re-2)) := by
  simp_rw [norm_gaussianMixture s freq t ht]
  rw [integral_const_mul, GaussianFourier.integral_rexp_neg_mul_sq_norm ht]
  norm_num only [Complex.finrank_real_complex, Nat.cast_ofNat, div_self (by norm_num : (2:ℝ)≠0),
    Real.rpow_one]
  have hp : t^(s.re-1)/t = t^(s.re-2) := by
    calc
      t^(s.re-1)/t = t^(s.re-1)/t^(1:ℝ) := by rw [Real.rpow_one]
      _ = t^((s.re-1)-1) := (Real.rpow_sub ht _ _).symm
      _ = _ := by congr 1; ring
  calc
    t^(s.re-1)*Real.exp (-t)*(Real.pi/t) = Real.pi*(Real.exp (-t)*(t^(s.re-1)/t)) := by ring
    _ = _ := by rw [hp]

theorem gaussianMixture_integrable (s freq : ℂ) (hs : 1 < s.re) :
    Integrable (fun p : ℝ × ℂ => gaussianMixture s freq p.1 p.2)
      ((volume.restrict (Set.Ioi 0)).prod volume) := by
  have hmeas : AEStronglyMeasurable (fun p : ℝ × ℂ => gaussianMixture s freq p.1 p.2)
      ((volume.restrict (Set.Ioi 0)).prod volume) := by
    unfold gaussianMixture
    change AEStronglyMeasurable (fun p : ℝ × ℂ =>
      (p.1 : ℂ)^(s-1)*Complex.exp (-p.1)*Complex.exp (-(p.1 : ℂ)*‖p.2‖^2)*
      Complex.exp (2*Real.pi*Complex.I*((-freq*p.2)+starRingEnd ℂ (-freq*p.2)))) _
    fun_prop
  apply (integrable_prod_iff hmeas).mpr
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact gaussianMixture_slice_integrable s freq t ht
  · have hgamma := (Real.GammaIntegral_convergent (by linarith : 0 < s.re-1)).const_mul Real.pi
    apply hgamma.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [integral_norm_gaussianMixture s freq t ht]
    congr 2
    ring_nf

open MeasureTheory Set Filter
open scoped BigOperators Classical FourierTransform RealInnerProductSpace

lemma gaussianMixture_laplace_form (s freq : ℂ) (t : ℝ) (z : ℂ) :
    gaussianMixture s freq t z =
      ((t : ℂ)^(s-1) * Complex.exp (-((1+‖z‖^2 : ℝ) : ℂ)*t)) *
        ShortDraftTrace.breveE (-freq*z) := by
  have he : Complex.exp (-(t : ℂ))*Complex.exp (-(t : ℂ)*‖z‖^2) =
      Complex.exp (-((1+‖z‖^2 : ℝ) : ℂ)*t) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  calc
    _ = (t : ℂ)^(s-1) * (Complex.exp (-(t : ℂ))*Complex.exp (-(t : ℂ)*‖z‖^2)) *
        ShortDraftTrace.breveE (-freq*z) := by unfold gaussianMixture; ring
    _ = _ := by rw [he]

lemma integral_gaussianMixture_t (s freq : ℂ) (hs : 0 < s.re) (z : ℂ) :
    (∫ t : ℝ in Set.Ioi 0, gaussianMixture s freq t z) =
      (hyperbolicKernel s z * Complex.Gamma s)*ShortDraftTrace.breveE (-freq*z) := by
  simp_rw [gaussianMixture_laplace_form]
  rw [integral_mul_const, ← hyperbolicKernel_laplace s hs z]

lemma integral_gaussianMixture_z (s freq : ℂ) (t : ℝ) (ht : 0 < t) :
    (∫ z : ℂ, gaussianMixture s freq t z) =
      (Real.pi : ℂ) * ((t : ℂ)^(s-2) *
        Complex.exp (-(t : ℂ) - (4*Real.pi^2*‖freq‖^2 : ℝ)/t)) := by
  have hfac : (fun z : ℂ => gaussianMixture s freq t z) =
      (fun z : ℂ => ((t : ℂ)^(s-1)*Complex.exp (-t))*
        (Complex.exp (-(t : ℂ)*‖z‖^2)*ShortDraftTrace.breveE (-freq*z))) := by
    funext z
    unfold gaussianMixture
    ring
  rw [hfac, integral_const_mul, traceIntegral_eq_fourier, source_gaussian_fourier t ht freq]
  have hp : (t : ℂ)^(s-1)/(t : ℂ) = (t : ℂ)^(s-2) := by
    calc
      _ = (t : ℂ)^(s-1)/(t : ℂ)^(1 : ℂ) := by rw [Complex.cpow_one]
      _ = (t : ℂ)^((s-1)-1) := (Complex.cpow_sub _ _ (Complex.ofReal_ne_zero.mpr ht.ne')).symm
      _ = _ := by congr 1; ring
  calc
    _ = (Real.pi : ℂ)*(((t : ℂ)^(s-1)/t)*
        (Complex.exp (-(t : ℂ))*Complex.exp (-(4*Real.pi^2*‖freq‖^2 : ℝ)/t))) := by ring
    _ = _ := by rw [hp, ← Complex.exp_add]; congr 2; ring_nf

theorem sourceFourierKernel_gamma (s freq : ℂ) (hs : 1 < s.re) :
    sourceFourierKernel s freq * Complex.Gamma s =
      (Real.pi : ℂ) * ∫ t : ℝ in Set.Ioi 0,
        (t : ℂ)^(s-2) * Complex.exp (-(t : ℂ) - (4*Real.pi^2*‖freq‖^2 : ℝ)/t) := by
  have hmix := gaussianMixture_integrable s freq hs
  calc
    _ = ∫ z : ℂ, (hyperbolicKernel s z * Complex.Gamma s)*
        ShortDraftTrace.breveE (-freq*z) := by
      rw [sourceFourierKernel, ← integral_mul_const]
      apply integral_congr_ae
      exact Eventually.of_forall fun z => by ring
    _ = ∫ z : ℂ, ∫ t : ℝ in Set.Ioi 0, gaussianMixture s freq t z := by
      apply integral_congr_ae
      exact Eventually.of_forall fun z => (integral_gaussianMixture_t s freq (by linarith) z).symm
    _ = ∫ t : ℝ in Set.Ioi 0, ∫ z : ℂ, gaussianMixture s freq t z :=
      (integral_integral_swap hmix).symm
    _ = _ := by
      rw [← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      exact integral_gaussianMixture_z s freq t ht

def schlafliIntegral (ν : ℂ) (x : ℝ) : ℂ :=
  ∫ t : ℝ in Set.Ioi 0, (t : ℂ)^(ν-1)*
    Complex.exp (-(t : ℂ) - (x : ℂ)^2/(4*t))

lemma schlafliIntegral_integrable (ν : ℂ) (x : ℝ) (hν : 0 < ν.re) :
    IntegrableOn (fun t : ℝ => (t : ℂ)^(ν-1)*
      Complex.exp (-(t : ℂ)-(x : ℂ)^2/(4*t))) (Set.Ioi 0) := by
  apply (Real.GammaIntegral_convergent hν).mono'
  · fun_prop
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change 0 < t at ht
    have hre : (-(t : ℂ)-(x : ℂ)^2/(4*t)).re = -t-x^2/(4*t) := by
      rw [show -(t : ℂ)-(x : ℂ)^2/(4*t) = ((-t-x^2/(4*t) : ℝ) : ℂ) by push_cast; rfl]
      rfl
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht, Complex.norm_exp, hre]
    simp only [Complex.sub_re, Complex.one_re]
    have he := Real.exp_le_exp.mpr (show -t-x^2/(4*t) ≤ -t by linarith [div_nonneg (sq_nonneg x) (show 0 ≤ 4*t by positivity)])
    have hb := mul_le_mul_of_nonneg_left he (Real.rpow_nonneg ht.le (ν.re-1))
    simpa only [mul_comm] using hb

def schlafliBesselK (ν : ℂ) (x : ℝ) : ℂ :=
  (1/2 : ℂ)*(x/2 : ℂ)^(-ν)*schlafliIntegral ν x

lemma sourceFourierKernel_gamma_schlafli (s freq : ℂ) (hs : 1 < s.re) :
    sourceFourierKernel s freq * Complex.Gamma s =
      (Real.pi : ℂ)*schlafliIntegral (s-1) (4*Real.pi*‖freq‖) := by
  rw [sourceFourierKernel_gamma s freq hs]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  rw [show s-2=(s-1)-1 by ring]
  apply congrArg (fun w : ℂ => (t : ℂ)^((s-1)-1)*Complex.exp w)
  push_cast
  ring

theorem sourceFourierKernel_bessel (s freq : ℂ) (hs : 1 < s.re) (hf : freq ≠ 0) :
    sourceFourierKernel s freq =
      (2*Real.pi : ℂ)/Complex.Gamma s *
        (2*Real.pi*‖freq‖ : ℂ)^(s-1) *
        schlafliBesselK (s-1) (4*Real.pi*‖freq‖) := by
  have hg := Complex.Gamma_ne_zero_of_re_pos (show 0 < s.re by linarith)
  have hz : (2*Real.pi*‖freq‖ : ℂ) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hf))
  have hp : (2*Real.pi*‖freq‖ : ℂ)^(s-1) * (2*Real.pi*‖freq‖ : ℂ)^(-(s-1)) = 1 := by
    rw [← Complex.cpow_add _ _ hz, add_neg_cancel, Complex.cpow_zero]
  have hreorder : (2*Real.pi : ℂ)/Complex.Gamma s *
      (2*Real.pi*‖freq‖ : ℂ)^(s-1) * schlafliBesselK (s-1) (4*Real.pi*‖freq‖) =
      ((2*Real.pi : ℂ)*(2*Real.pi*‖freq‖ : ℂ)^(s-1)*
        schlafliBesselK (s-1) (4*Real.pi*‖freq‖))/Complex.Gamma s := by ring
  rw [hreorder]
  apply (eq_div_iff hg).mpr
  rw [sourceFourierKernel_gamma_schlafli s freq hs]
  unfold schlafliBesselK
  push_cast
  have hhalf : (4*(Real.pi : ℂ)*‖freq‖)/2 = 2*Real.pi*‖freq‖ := by ring
  rw [hhalf]
  linear_combination -((Real.pi : ℂ)*schlafliIntegral (s-1) (4*Real.pi*‖freq‖))*hp

theorem sourceFourierKernel_four_thirds (freq : ℂ) (hf : freq ≠ 0) :
    sourceFourierKernel (4/3 : ℂ) freq =
      (2*Real.pi : ℂ)/Complex.Gamma (4/3) *
        (2*Real.pi*‖freq‖ : ℂ)^(1/3 : ℂ) *
        schlafliBesselK (1/3) (4*Real.pi*‖freq‖) := by
  convert (preTransparency := .instances) sourceFourierKernel_bessel (4/3) freq (by norm_num) hf using 1 ; norm_num

end CubicEisenstein

end

end OAI
end

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

section
open MeasureTheory Set Filter
open scoped BigOperators Classical ENNReal

open ActualEisensteinCubic ConcreteTraceCRT

lemma breveE_embedding_div_traceLambda (n : O) :
    ShortDraftTrace.breveE (eisEmbedding n/eisLam)=1 := by
  rw [← ActualEisensteinCoordinates.eval_coords n,eisEmbedding_eval]
  exact ConcreteBreveE.breveE_period_coordinates _ _

def cuspFrequency (h : O) : ℂ := eisEmbedding h/(3*eisLam)

lemma cuspFrequency_period (h n : O) :
    ShortDraftTrace.breveE (cuspFrequency h*(3*eisEmbedding n))=1 := by
  have heq : cuspFrequency h*(3*eisEmbedding n)=eisEmbedding (h*n)/eisLam := by
    rw [cuspFrequency,map_mul]
    field_simp
  rw [heq]
  exact breveE_embedding_div_traceLambda (h*n)

lemma cuspFrequency_negative_period (h n : O) (z : ℂ) :
    ShortDraftTrace.breveE (-cuspFrequency h*(z+3*eisEmbedding n))=
      ShortDraftTrace.breveE (-cuspFrequency h*z) := by
  rw [mul_add,AddChar.map_add_eq_mul]
  have hp : ShortDraftTrace.breveE (-cuspFrequency h*(3*eisEmbedding n))=1 := by
    rw [neg_mul,AddChar.map_neg_eq_inv,cuspFrequency_period,inv_one]
  rw [hp,mul_one]

lemma trace_mul_integrable (f : ℂ → ℂ) (hf : Integrable f) (freq : ℂ) :
    Integrable (fun z => f z*ShortDraftTrace.breveE (-freq*z)) := by
  have hchar : Continuous (fun z : ℂ => ShortDraftTrace.breveE (-freq*z)) := by
    change Continuous (fun z : ℂ => Complex.exp (2*Real.pi*Complex.I*
      ((-freq*z)+starRingEnd ℂ (-freq*z))))
    fun_prop
  refine hf.norm.mono' (hf.aestronglyMeasurable.mul hchar.aestronglyMeasurable) ?_
  exact Eventually.of_forall fun z => by simp only [norm_mul,breveE_norm,mul_one,le_refl]

end

section
open MeasureTheory Set Filter Module
open scoped BigOperators Classical ENNReal MatrixGroups Matrix

open ActualEisensteinCubic ConcreteTraceCRT

lemma continuous_inverse_upper_operator (v : ℝ) (hv : 0 < v) :
    Continuous (fun z : ℂ => rowOperator (upperSection z v hv)⁻¹) := by
  apply continuous_clm_apply.mpr
  intro u
  apply continuous_pi
  intro i
  simp only [rowOperator_apply,upperSection,
    Matrix.vecMul,dotProduct,Fin.sum_univ_two]
  fin_cases i <;> simp only [] <;> fun_prop

lemma continuous_upper_rowBound (v : ℝ) (hv : 0 < v) :
    Continuous (fun z : ℂ => rowBound (upperSection z v hv)) :=
  continuous_const.mul (continuous_const.add (continuous_inverse_upper_operator v hv).norm)

lemma norm_mem_periodDomain (z : ℂ) (hz : z ∈ periodDomain) :
    ‖z‖ ≤ ∑ i : Fin 2, ‖periodBasis i‖ := by
  have heq := (ZSpan.fract_eq_self (b := periodBasis)).mpr hz
  simpa only [heq] using ZSpan.norm_fract_le periodBasis z

lemma exists_upper_rowBound (v : ℝ) (hv : 0 < v) :
    ∃ C : ℝ, 0 < C ∧ ∀ z ∈ periodDomain, rowBound (upperSection z v hv) ≤ C := by
  let R : ℝ := ∑ i : Fin 2, ‖periodBasis i‖
  obtain ⟨C,hC⟩ := (isCompact_closedBall (0:ℂ) R).bddAbove_image
    (continuous_upper_rowBound v hv).continuousOn
  refine ⟨max 1 C,lt_of_lt_of_le (by norm_num) (le_max_left _ _),?_⟩
  intro z hz
  apply (hC ?_).trans (le_max_right _ _)
  exact ⟨z,by simpa only [Metric.mem_closedBall,dist_zero_right] using norm_mem_periodDomain z hz,rfl⟩

lemma continuous_upper_summand (v : ℝ) (hv : 0 < v) (s : ℂ) (x : CuspCosets) :
    Continuous (fun z : ℂ => summand (upperSection z v hv) s x) := by
  simp_rw [summand_upperSection]
  apply continuous_const.mul
  apply Continuous.cpow
  · apply Complex.continuous_ofReal.comp
    apply continuous_const.div
    · unfold heightDenominator
      fun_prop
    · intro z
      exact (heightDenominator_pos z v hv _ (embeddedRow_ne_zero x)).ne'
  · exact continuous_const
  · intro z
    apply Complex.ofReal_mem_slitPlane.mpr
    exact div_pos hv (heightDenominator_pos z v hv _ (embeddedRow_ne_zero x))

lemma upper_summable_majorant (v : ℝ) (hv : 0 < v) (s : ℂ) (hs : 2 < s.re) :
    ∃ M : CuspCosets → ℝ, Summable M ∧ (∀ x,0 ≤ M x) ∧
      ∀ z ∈ periodDomain, ∀ x, ‖summand (upperSection z v hv) s x‖ ≤ M x := by
  obtain ⟨C,hC,hbound⟩ := exists_upper_rowBound v hv
  refine ⟨fun x => C ^(2*s.re)*‖rowCoordinates (cosetRow x)‖^(-(2*s.re)),?_,?_,?_⟩
  · have hsumm := summable_integer_four_rpow (2*s.re) (by linarith)
    have hinj : Function.Injective (fun x : CuspCosets => rowCoordinates (cosetRow x)) :=
      rowCoordinates_injective.comp cosetRow_injective
    exact (hsumm.comp_injective hinj).mul_left _
  · intro x
    positivity
  · intro z hz x
    apply (norm_summand_bound (upperSection z v hv) s (by linarith) x).trans
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow (rowBound_pos _).le (hbound z hz) (by linarith)) (by positivity)

lemma periodDomain_finiteMeasure : IsFiniteMeasure (volume.restrict periodDomain) := by
  constructor
  rw [Measure.restrict_apply_univ,periodDomain_volume]
  exact ENNReal.ofReal_lt_top

theorem hasSum_integral_upperEisenstein (v : ℝ) (hv : 0 < v) (s freq : ℂ) (hs : 2 < s.re) :
    HasSum (fun x : CuspCosets => ∫ z in periodDomain,
      summand (upperSection z v hv) s x*ShortDraftTrace.breveE (-freq*z))
      (∫ z in periodDomain,upperEisenstein z v hv s*ShortDraftTrace.breveE (-freq*z)) := by
  let : Countable CuspCosets :=
    (rowCoordinates_injective.comp cosetRow_injective).countable
  let := periodDomain_finiteMeasure
  obtain ⟨M,hM,hMnonneg,hbound⟩ := upper_summable_majorant v hv s hs
  have hchar : Continuous (fun z : ℂ => ShortDraftTrace.breveE (-freq*z)) := by
    change Continuous (fun z : ℂ => Complex.exp (2*Real.pi*Complex.I*
      ((-freq*z)+starRingEnd ℂ (-freq*z))))
    fun_prop
  have hsum := hasSum_integral_of_dominated_convergence
    («μ» := volume.restrict periodDomain)
    (fun (x : CuspCosets) (_ : ℂ) => M x)
    (fun x => ((continuous_upper_summand v hv s x).mul hchar).aestronglyMeasurable.restrict)
    (fun x => (ae_restrict_mem periodDomain_measurable).mono fun z hz => by
      simpa only [Pi.mul_apply,norm_mul,breveE_norm,mul_one] using hbound z hz x)
    (Eventually.of_forall fun _ => hM)
    (integrable_const (∑' x,M x))
    (Eventually.of_forall fun z => (summable_summand (upperSection z v hv) s hs).hasSum.mul_right
      (ShortDraftTrace.breveE (-freq*z)))
  exact hsum

end

section
open MeasureTheory Set Filter
open scoped BigOperators Classical

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal

def shiftedHeightKernel (v : ℝ) (s b z : ℂ) : ℂ :=
  (v:ℂ)^(-s)*hyperbolicKernel s ((z+b)/(v:ℂ))

lemma shiftedHeightKernel_integrable (v : ℝ) (hv : 0 < v) (s b : ℂ) (hs : 1 < s.re) :
    Integrable (shiftedHeightKernel v s b) := by
  have h := ((hyperbolicKernel_integrable s hs).comp_smul (inv_ne_zero hv.ne')).comp_add_right b
  apply (h.const_mul ((v:ℂ)^(-s))).congr
  exact Eventually.of_forall fun z => by
    simp only [shiftedHeightKernel,Complex.real_smul,Complex.ofReal_inv,div_eq_mul_inv,mul_comm]

lemma primitiveTerm_eq_shiftedHeightKernel (z : ℂ) (v : ℝ) (hv : 0 < v)
    (s : ℂ) (c d : O) (hc : c ≠ 0) :
    primitiveTerm z v s c d =
      (eisEmbedding (symbol c d)*(‖eisEmbedding c‖^2:ℝ) ^ (-s:ℂ))*
        shiftedHeightKernel v s (eisEmbedding d/eisEmbedding c) z := by
  have hc' := eisEmbedding_ne_zero hc
  have hnorm : 0 < ‖eisEmbedding c‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hc')
  have hfac : eisEmbedding c*z+eisEmbedding d =
      eisEmbedding c*(z+eisEmbedding d/eisEmbedding c) := by field_simp
  have heq : v/(‖eisEmbedding c*z+eisEmbedding d‖^2+‖eisEmbedding c‖^2*v^2) =
      ((‖eisEmbedding c‖^2*v)*(1+‖(z+eisEmbedding d/eisEmbedding c)/(v:ℂ)‖^2))⁻¹ := by
    rw [hfac,norm_mul,mul_pow,norm_div,Complex.norm_real,Real.norm_of_nonneg hv.le]
    field_simp
    ; ring
  unfold primitiveTerm shiftedHeightKernel hyperbolicKernel
  rw [heq,Complex.ofReal_inv,Complex.inv_cpow_ofReal_nonneg (by positivity),← Complex.cpow_neg]
  rw [Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg (mul_nonneg hnorm.le hv.le) (by positivity),
    Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg hnorm.le hv.le]
  ring

lemma primitiveTerm_integrable (v : ℝ) (hv : 0 < v) (s : ℂ) (hs : 1 < s.re)
    (c d : O) (hc : c ≠ 0) : Integrable (fun z => primitiveTerm z v s c d) := by
  simp_rw [primitiveTerm_eq_shiftedHeightKernel _ v hv s c d hc]
  exact (shiftedHeightKernel_integrable v hv s _ hs).const_mul _

lemma traceIntegral_translate (f : ℂ → ℂ) (b freq : ℂ) :
    (∫ z : ℂ,f (z+b)*ShortDraftTrace.breveE (-freq*z))=
      ShortDraftTrace.breveE (freq*b)*(∫ z : ℂ,f z*ShortDraftTrace.breveE (-freq*z)) := by
  have heq (z : ℂ) : f (z+b)*ShortDraftTrace.breveE (-freq*z)=
      ShortDraftTrace.breveE (freq*b)*(f (z+b)*ShortDraftTrace.breveE (-freq*(z+b))) := by
    rw [mul_left_comm (ShortDraftTrace.breveE (freq*b)),
      ← AddChar.map_add_eq_mul]
    congr 2
    ring
  simp_rw [heq]
  rw [integral_const_mul,integral_add_right_eq_self (fun z => f z*ShortDraftTrace.breveE (-freq*z)) b]

lemma traceIntegral_scale (v : ℝ) (hv : 0 < v) (s freq : ℂ) :
    (∫ z : ℂ,hyperbolicKernel s (z/(v:ℂ))*ShortDraftTrace.breveE (-freq*z))=
      (v:ℂ)^2*sourceFourierKernel s (freq*v) := by
  have heq (z : ℂ) : hyperbolicKernel s (z/(v:ℂ))*ShortDraftTrace.breveE (-freq*z)=
      (fun w : ℂ => hyperbolicKernel s w*ShortDraftTrace.breveE (-(freq*v)*w)) (v⁻¹ • z) := by
    simp only [Complex.real_smul,Complex.ofReal_inv]
    congr 2
    · ring
    · field_simp [Complex.ofReal_ne_zero.mpr hv.ne']
  simp_rw [heq]
  have h := Measure.integral_comp_inv_smul_of_nonneg (volume : Measure ℂ)
    (fun w : ℂ => hyperbolicKernel s w*ShortDraftTrace.breveE (-(freq*v)*w)) hv.le
  simpa only [Complex.finrank_real_complex,Complex.real_smul,Complex.ofReal_pow,sourceFourierKernel] using h

lemma traceIntegral_shiftedHeightKernel (v : ℝ) (hv : 0 < v) (s b freq : ℂ) :
    (∫ z : ℂ,shiftedHeightKernel v s b z*ShortDraftTrace.breveE (-freq*z))=
      (v:ℂ)^(2-s)*ShortDraftTrace.breveE (freq*b)*sourceFourierKernel s (freq*v) := by
  simp only [shiftedHeightKernel,mul_assoc]
  rw [integral_const_mul,traceIntegral_translate (fun z => hyperbolicKernel s (z/(v:ℂ))) b freq,
    traceIntegral_scale v hv s freq]
  have hp : (v:ℂ)^(-s)*(v:ℂ)^2=(v:ℂ)^(2-s) := by
    rw [← Complex.cpow_natCast,← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hv.ne')]
    congr 1
    ring
  calc
    _ = ((v:ℂ)^(-s)*(v:ℂ)^2)*ShortDraftTrace.breveE (freq*b)*sourceFourierKernel s (freq*v) := by ring
    _ = _ := by rw [hp]; ring

end

section
open MeasureTheory Set Filter
open scoped BigOperators Classical ENNReal Pointwise

open ActualEisensteinCubic ConcreteTraceCRT

lemma period_integral_translation (f : ℂ → ℂ)
    (hperiod : ∀ (n : O) (z : ℂ), f (z+3*eisEmbedding n)=f z) (b : ℂ) :
    (∫ z in periodDomain,f (b+z))=∫ z in periodDomain,f z := by
  have hperiod' (n : periodLattice) (z : ℂ) : f (n+ᵥz)=f z := by
    obtain ⟨m,rfl⟩ := periodEquiv.surjective n
    change f (3*eisEmbedding m+z)=f z
    simpa only [add_comm] using hperiod m z
  have hD := periodDomain_fundamental.vadd_of_comm b
  have heq := periodDomain_fundamental.setIntegral_eq hD hperiod'
  have hchange := (measurePreserving_add_left volume b).setIntegral_image_emb
    (measurableEmbedding_const_vadd b) f periodDomain
  exact hchange.symm.trans heq.symm

lemma breveE_quarter_eq_neg_one : ShortDraftTrace.breveE (1/4:ℂ)=-1 := by
  change Complex.exp (2*Real.pi*Complex.I*((1/4:ℂ)+starRingEnd ℂ (1/4:ℂ)))=-1
  norm_num only [map_div₀,map_one,map_ofNat]
  convert (preTransparency := .instances) Complex.exp_pi_mul_I using 1 ; congr 1 ; ring

lemma cuspFrequency_ne_zero (h : O) (hh : h ≠ 0) : cuspFrequency h ≠ 0 :=
  div_ne_zero (eisEmbedding_ne_zero hh) (mul_ne_zero (by norm_num) eisLam_ne_zero)

theorem integral_cusp_character (h : O) :
    (∫ z in periodDomain,ShortDraftTrace.breveE (-cuspFrequency h*z))=
      if h=0 then ((9*Real.sqrt 3/2:ℝ):ℂ) else 0 := by
  by_cases hh : h=0
  · subst h
    simp only [cuspFrequency,map_zero,zero_div,neg_zero,zero_mul,
      AddChar.map_zero_eq_one,ite_true,setIntegral_const,measureReal_def,periodDomain_volume,
      ENNReal.toReal_ofReal (by positivity : (0:ℝ) ≤ 9*Real.sqrt 3/2),Complex.real_smul,mul_one]
  · rw [if_neg hh]
    let freq := cuspFrequency h
    let b : ℂ := -(4*freq)⁻¹
    have hfreq : freq ≠ 0 := cuspFrequency_ne_zero h hh
    have harg : -freq*b=(1/4:ℂ) := by dsimp [b]; field_simp
    have hphase : ShortDraftTrace.breveE (-freq*b)=-1 := by rw [harg,breveE_quarter_eq_neg_one]
    have heq := period_integral_translation
      (fun z => ShortDraftTrace.breveE (-freq*z))
      (fun n z => cuspFrequency_negative_period h n z) b
    have hpoint (z : ℂ) : ShortDraftTrace.breveE (-freq*(b+z))=
        -ShortDraftTrace.breveE (-freq*z) := by
      rw [mul_add,AddChar.map_add_eq_mul,hphase,neg_one_mul]
    simp_rw [hpoint,integral_neg] at heq
    linear_combination (-1/2:ℂ)*heq

end

section
open MeasureTheory Set Filter
open scoped BigOperators Classical ENNReal

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal

def primitiveRowIntegral (v : ℝ) (s freq : ℂ) (c d : O) : ℂ :=
  ∫ z in periodDomain,primitiveTerm z v s c d*ShortDraftTrace.breveE (-freq*z)

lemma integral_summand_eq_primitiveRowIntegral (v : ℝ) (hv : 0 < v)
    (s freq : ℂ) (x : CuspCosets) :
    (∫ z in periodDomain,summand (upperSection z v hv) s x*ShortDraftTrace.breveE (-freq*z))=
      primitiveRowIntegral v s freq (cosetRow x 0) (cosetRow x 1) := by
  apply integral_congr_ae
  exact Eventually.of_forall fun z => by
    dsimp only
    rw [summand_upperSection,inverse_cosetCharacter_eq_row_symbol]
    rfl

lemma hasSum_primitiveRowIntegrals (v : ℝ) (hv : 0 < v) (s freq : ℂ) (hs : 2 < s.re) :
    HasSum (fun p : Σ c : LevelLower,AdmissibleDenominator c.1 =>
      primitiveRowIntegral v s freq p.1.1 p.2.1)
      (∫ z in periodDomain,upperEisenstein z v hv s*ShortDraftTrace.breveE (-freq*z)) := by
  apply primitiveSigmaEquiv.hasSum_iff.mp
  apply primitiveRowEquiv.hasSum_iff.mp
  exact (hasSum_integral_upperEisenstein v hv s freq hs).congr_fun
    fun x => (integral_summand_eq_primitiveRowIntegral v hv s freq x).symm

lemma primitiveRowIntegral_sum_translate (v : ℝ) (hv : 0 < v) (s : ℂ) (hs : 1 < s.re)
    (h c d : O) (hc : c ≠ 0) (hlevel : (3:O) ∣ c) (hd : (3:O) ∣ d-1) :
    (∑' n : O,primitiveRowIntegral v s (cuspFrequency h) c (d+3*c*n))=
      ∫ z : ℂ,primitiveTerm z v s c d*ShortDraftTrace.breveE (-cuspFrequency h*z) := by
  have hint := trace_mul_integrable (fun z => primitiveTerm z v s c d)
    (primitiveTerm_integrable v hv s hs c d hc) (cuspFrequency h)
  rw [integral_eq_period_integrals _ hint]
  apply tsum_congr
  intro n
  apply integral_congr_ae
  exact Eventually.of_forall fun z => by
    dsimp only
    rw [primitiveTerm_shift z v s c d n hlevel hd,cuspFrequency_negative_period]

lemma primitiveTerm_fourier_integral (v : ℝ) (hv : 0 < v) (s freq : ℂ)
    (c d : O) (hc : c ≠ 0) :
    (∫ z : ℂ,primitiveTerm z v s c d*ShortDraftTrace.breveE (-freq*z))=
      ((v:ℂ)^(2-s)*sourceFourierKernel s (freq*v))*
        ((‖eisEmbedding c‖^2:ℝ):ℂ)^(-s)*
        (eisEmbedding (symbol c d)*ShortDraftTrace.breveE (freq*eisEmbedding d/eisEmbedding c)) := by
  simp_rw [primitiveTerm_eq_shiftedHeightKernel _ v hv s c d hc,mul_assoc]
  rw [integral_const_mul,integral_const_mul,traceIntegral_shiftedHeightKernel v hv s (eisEmbedding d/eisEmbedding c) freq]
  ring_nf

def arithmeticResidueSum (h c : O) : ℂ :=
  ∑' r : AdmissibleResidue c,eisEmbedding (symbol c (denominatorRep c r.1))*
    ShortDraftTrace.breveE (cuspFrequency h*eisEmbedding (denominatorRep c r.1)/eisEmbedding c)

lemma denominator_integral_formula (v : ℝ) (hv : 0 < v) (s : ℂ) (hs : 2 < s.re)
    (h : O) (c : LevelLower) (hc : c.1 ≠ 0) :
    (∑' d : AdmissibleDenominator c.1,primitiveRowIntegral v s (cuspFrequency h) c.1 d.1)=
      ((v:ℂ)^(2-s)*sourceFourierKernel s (cuspFrequency h*v))*
        ((‖eisEmbedding c.1‖^2:ℝ):ℂ)^(-s)*arithmeticResidueSum h c.1 := by
  have hsum : Summable (fun d : AdmissibleDenominator c.1 =>
      primitiveRowIntegral v s (cuspFrequency h) c.1 d.1) :=
    (hasSum_primitiveRowIntegrals v hv s (cuspFrequency h) hs).summable.sigma_factor c
  rw [denominator_sum_residues c.1 hc
    (fun d : O => primitiveRowIntegral v s (cuspFrequency h) c.1 d) hsum]
  calc
    _ = ∑' r : AdmissibleResidue c.1, ∫ z : ℂ,
        primitiveTerm z v s c.1 (denominatorRep c.1 r.1)*
          ShortDraftTrace.breveE (-cuspFrequency h*z) := by
      apply tsum_congr
      intro r
      exact primitiveRowIntegral_sum_translate v hv s (by linarith) h c.1
        (denominatorRep c.1 r.1) hc c.2 r.2.2
    _ = _ := by
      simp_rw [primitiveTerm_fourier_integral v hv s (cuspFrequency h) c.1 _ hc]
      exact tsum_mul_left

end

section
open MeasureTheory Set Filter
open scoped BigOperators Classical ENNReal Matrix

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal

instance : DiscreteTopology periodLattice := by unfold periodLattice; infer_instance
instance : IsZLattice ℝ periodLattice := by unfold periodLattice; infer_instance

lemma summable_embedding_rpow (k : ℝ) (hk : k < -2) :
    Summable (fun n : O => ‖eisEmbedding n‖^k) := by
  have hrank : Module.finrank ℤ periodLattice=2 := by
    rw [ZLattice.rank ℝ periodLattice,Complex.finrank_real_complex]
  have hs := ZLattice.summable_norm_rpow periodLattice k (by rw [hrank]; norm_num; exact hk)
  have hcomp := periodEquiv.summable_iff.mpr hs
  have hscale := hcomp.mul_left (((3:ℝ)^k)⁻¹)
  apply hscale.congr
  intro n
  change ((3:ℝ)^k)⁻¹*‖(3:ℂ)*eisEmbedding n‖^k=‖eisEmbedding n‖^k
  rw [norm_mul,show ‖(3:ℂ)‖=(3:ℝ) by norm_num,
    Real.mul_rpow (by norm_num) (norm_nonneg _)]
  rw [← mul_assoc,inv_mul_cancel₀ (Real.rpow_pos_of_pos (by norm_num) k).ne',one_mul]

lemma norm_row_symbol (c d : O) (hc : (3:O) ∣ c) (hd : denominatorCondition c d) :
    ‖eisEmbedding (symbol c d)‖=1 := by
  let r : PrimitiveRow := ⟨![c,d],hd.1,hc,hd.2⟩
  let x := primitiveRowEquiv.symm r
  have heq : (cosetCharacter x)⁻¹=eisEmbedding (symbol c d) := by
    rw [inverse_cosetCharacter_eq_row_symbol]
    change eisEmbedding (symbol (cosetRow (primitiveRowEquiv.symm r) 0)
      (cosetRow (primitiveRowEquiv.symm r) 1))=eisEmbedding (symbol c d)
    rw [primitiveRowEquiv_symm_row r]
    rfl
  rw [← heq,norm_inv,norm_cosetCharacter,inv_one]

lemma norm_arithmeticResidueSum_le (h c : O) (hc : c ≠ 0) (hlevel : (3:O) ∣ c) :
    ‖arithmeticResidueSum h c‖ ≤ 9*‖eisEmbedding c‖^2 := by
  let : Finite (DenominatorResidue c) := finite_quotient_span (mul_ne_zero (by norm_num) hc)
  let : Fintype (DenominatorResidue c) := Fintype.ofFinite _
  let : Fintype (AdmissibleResidue c) := Fintype.ofFinite _
  have hcard : (Fintype.card (DenominatorResidue c):ℝ)=9*‖eisEmbedding c‖^2 := by
    have hh := eisEmbedding_norm_sq_eq_absNorm_span (3*c)
    simp only [Ideal.absNorm_apply,Submodule.cardQuot_apply,Nat.card_eq_fintype_card] at hh
    rw [← hh,map_mul,map_ofNat,norm_mul,mul_pow]
    norm_num
  rw [arithmeticResidueSum,tsum_fintype]
  calc
    _ ≤ ∑ r : AdmissibleResidue c, ‖eisEmbedding (symbol c (denominatorRep c r.1))*
        ShortDraftTrace.breveE (cuspFrequency h*eisEmbedding (denominatorRep c r.1)/eisEmbedding c)‖ :=
      norm_sum_le _ _
    _ = (Fintype.card (AdmissibleResidue c):ℝ) := by
      have hr (r : AdmissibleResidue c) :
          ‖eisEmbedding (symbol c (denominatorRep c r.1))‖=1 :=
        norm_row_symbol c (denominatorRep c r.1) hlevel r.2
      simp only [norm_mul,hr,breveE_norm,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one]
    _ ≤ (Fintype.card (DenominatorResidue c):ℝ) := by
      exact_mod_cast Fintype.card_subtype_le (fun r => denominatorCondition c (denominatorRep c r))
    _ = _ := hcard

def arithmeticDirichletTerm (s : ℂ) (h : O) (c : LevelLower) : ℂ :=
  if c.1=0 then 0 else ((‖eisEmbedding c.1‖^2:ℝ):ℂ)^(-s)*arithmeticResidueSum h c.1

lemma norm_arithmeticDirichletTerm_le (s : ℂ) (h : O) (c : LevelLower) :
    ‖arithmeticDirichletTerm s h c‖ ≤ 9*‖eisEmbedding c.1‖^(2-2*s.re) := by
  unfold arithmeticDirichletTerm
  split_ifs with hc
  · simp only [norm_zero]
    positivity
  · have hn : 0 < ‖eisEmbedding c.1‖ := norm_pos_iff.mpr (eisEmbedding_ne_zero hc)
    rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos (sq_pos_of_pos hn)]
    change (‖eisEmbedding c.1‖^2)^(-s.re)*‖arithmeticResidueSum h c.1‖ ≤ _
    calc
      _ ≤ (‖eisEmbedding c.1‖^2)^(-s.re)*(9*‖eisEmbedding c.1‖^2) :=
        mul_le_mul_of_nonneg_left (norm_arithmeticResidueSum_le h c.1 hc c.2) (by positivity)
      _ = _ := by
        rw [← Real.rpow_natCast_mul hn.le 2 (-s.re)]
        rw [show 2-2*s.re=2+2*(-s.re) by ring,Real.rpow_add hn]
        norm_num only [Nat.cast_ofNat,Real.rpow_two]
        ring

theorem arithmeticDirichletTerm_summable_norm (s : ℂ) (hs : 2 < s.re) (h : O) :
    Summable (fun c : LevelLower => ‖arithmeticDirichletTerm s h c‖) := by
  have hbase := (summable_embedding_rpow (2-2*s.re) (by linarith)).subtype
    (fun c : O => (3:O) ∣ c)
  exact (hbase.mul_left 9).of_nonneg_of_le (fun _ => norm_nonneg _)
    (norm_arithmeticDirichletTerm_le s h)

def arithmeticDirichletSeries (s : ℂ) (h : O) : ℂ :=
  ∑' c : LevelLower,arithmeticDirichletTerm s h c

def scatteringCoefficient (s : ℂ) (h : O) : ℂ :=
  arithmeticDirichletSeries s h/((9*Real.sqrt 3/2:ℝ):ℂ)

end

open MeasureTheory Set Filter
open scoped BigOperators Classical

open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal

lemma zero_lower_integral (v : ℝ) (s : ℂ) (h : O) :
    (∑' d : AdmissibleDenominator 0,primitiveRowIntegral v s (cuspFrequency h) 0 d.1)=
      (v:ℂ)^s*(if h=0 then ((9*Real.sqrt 3/2:ℝ):ℂ) else 0) := by
  let d0 : AdmissibleDenominator 0 := ⟨1,isCoprime_one_right,by simp⟩
  rw [tsum_eq_single d0]
  · simp only [d0,primitiveRowIntegral,primitiveTerm,map_zero,map_one,zero_mul,zero_add,
      norm_one,norm_zero,one_pow,zero_pow (by decide : (2:ℕ) ≠ 0),add_zero,
      div_one,symbol_one,map_one]
    rw [integral_const_mul,integral_cusp_character,one_mul]
  · intro d hd
    exact False.elim (hd (Subtype.ext (denominator_zero_unique d)))

lemma integral_upperEisenstein_arithmetic (v : ℝ) (hv : 0 < v) (s : ℂ) (hs : 2 < s.re) (h : O) :
    (∫ z in periodDomain,upperEisenstein z v hv s*ShortDraftTrace.breveE (-cuspFrequency h*z))=
      (v:ℂ)^s*(if h=0 then ((9*Real.sqrt 3/2:ℝ):ℂ) else 0)+
        ((v:ℂ)^(2-s)*sourceFourierKernel s (cuspFrequency h*v))*arithmeticDirichletSeries s h := by
  let c0 : LevelLower := ⟨0,dvd_zero _⟩
  let F (c : LevelLower) := ∑' d : AdmissibleDenominator c.1,
    primitiveRowIntegral v s (cuspFrequency h) c.1 d.1
  have hsum := hasSum_primitiveRowIntegrals v hv s (cuspFrequency h) hs
  have hF : Summable F := hsum.summable.sigma
  have hzero : F c0=(v:ℂ)^s*(if h=0 then ((9*Real.sqrt 3/2:ℝ):ℂ) else 0) :=
    zero_lower_integral v s h
  calc
    _ = ∑' c : LevelLower,F c := hsum.tsum_eq.symm.trans hsum.summable.tsum_sigma
    _ = F c0+∑' c : LevelLower,if c=c0 then 0 else F c := hF.tsum_eq_add_tsum_ite c0
    _ = _ := by
      rw [hzero]
      congr 1
      rw [arithmeticDirichletSeries,← tsum_mul_left]
      apply tsum_congr
      intro c
      by_cases hc : c.1=0
      · have heq : c=c0 := Subtype.ext hc
        simp only [heq,ite_true,arithmeticDirichletTerm,c0,mul_zero]
      · have heq : c ≠ c0 := fun heq => hc (congrArg Subtype.val heq)
        rw [if_neg heq]
        change (∑' d : AdmissibleDenominator c.1,
          primitiveRowIntegral v s (cuspFrequency h) c.1 d.1)=_
        rw [denominator_integral_formula v hv s hs h c hc]
        simp only [arithmeticDirichletTerm,if_neg hc]
        ring

def eisensteinFourierCoefficient (v : ℝ) (hv : 0 < v) (s : ℂ) (h : O) : ℂ :=
  (∫ z in periodDomain,upperEisenstein z v hv s*ShortDraftTrace.breveE (-cuspFrequency h*z))/
    ((9*Real.sqrt 3/2:ℝ):ℂ)

theorem eisensteinFourierCoefficient_formula (v : ℝ) (hv : 0 < v) (s : ℂ) (hs : 2 < s.re) (h : O) :
    eisensteinFourierCoefficient v hv s h=(if h=0 then (v:ℂ)^s else 0)+
      (v:ℂ)^(2-s)*sourceFourierKernel s (cuspFrequency h*v)*scatteringCoefficient s h := by
  rw [eisensteinFourierCoefficient,integral_upperEisenstein_arithmetic v hv s hs h,scatteringCoefficient]
  have hvol : ((9*Real.sqrt 3/2:ℝ):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
  split_ifs <;> field_simp ; ring

theorem eisensteinConstantCoefficient_formula (v : ℝ) (hv : 0 < v) (s : ℂ) (hs : 2 < s.re) :
    eisensteinFourierCoefficient v hv s 0=(v:ℂ)^s+
      (v:ℂ)^(2-s)*((Real.pi:ℂ)/(s-1))*scatteringCoefficient s 0 := by
  rw [eisensteinFourierCoefficient_formula v hv s hs 0]
  simp only [ite_true,cuspFrequency,map_zero,zero_div,zero_mul]
  rw [sourceFourierKernel_zero s (by linarith)]

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

open scoped BigOperators Classical
namespace CanonicalQuadraticSieve

section
open ActualEisensteinCubic CompletedGauss FiniteSieveRestriction
open QuadraticSquarefreeKernel

def rayPairValue (N : ℝ) (D : Ideal O) (c : EisensteinEPrimaryPhase.Coord)
    (a : idealRange N → ℂ) (I : Ideal O) : ℂ :=
  ∑ J : idealRange N, ∑ lengthScale : idealRange N,
    gcdTerm D (fun _ : Unit => I) (fun J : idealRange N => J.val)
      (sectorCoefficient (fun J : idealRange N => columnRay J.val) c a) () J lengthScale

end

open ActualEisensteinCubic CompletedGauss FiniteSieveOperator

theorem exists_dyadic_shell (n lengthScale : ℕ) (hn : 1 ≤ n) (hL : (n : ℝ) ≤ (2 : ℝ) ^ lengthScale) :
    ∃ j ∈ Finset.range (lengthScale + 1), (2 : ℝ) ^ j / 2 < n ∧ (n : ℝ) ≤ (2 : ℝ) ^ j := by
  have hex : ∃ j : ℕ, (n : ℝ) ≤ (2 : ℝ) ^ j := ⟨lengthScale, hL⟩
  let j := Nat.find hex
  have hj : (n : ℝ) ≤ (2 : ℝ) ^ j := Nat.find_spec hex
  have hjL : j ≤ lengthScale := Nat.find_min' hex hL
  refine ⟨j, Finset.mem_range.mpr (by omega), ?_, hj⟩
  have hjfind : j = Nat.find hex := rfl
  rcases j with _ | j
  · have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    norm_num
    linarith
  · have hprev : ¬ (n : ℝ) ≤ (2 : ℝ) ^ j := Nat.find_min hex (by omega)
    have hp := lt_of_not_ge hprev
    simpa only [pow_succ, mul_div_cancel_right₀ _ (by norm_num : (2 : ℝ) ≠ 0)] using hp

end CanonicalQuadraticSieve

open scoped SchwartzMap ContDiff
namespace QuadraticInitialBound

def annularSieveBump : ContDiffBump (3 / 4 : ℝ) where
  rIn := 1 / 4
  rOut := 1 / 2
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

def annularSieveCutoff : 𝓢(ℝ, ℂ) := by
  have hc : HasCompactSupport (fun t : ℝ => (annularSieveBump t : ℂ)) :=
    annularSieveBump.hasCompactSupport.comp_left Complex.ofReal_zero
  have hs : ContDiff ℝ ∞ (fun t : ℝ => (annularSieveBump t : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp annularSieveBump.contDiff
  exact hc.toSchwartzMap hs

@[simp] theorem annularSieveCutoff_apply (t : ℝ) : annularSieveCutoff t = (annularSieveBump t : ℂ) := rfl

end QuadraticInitialBound

open scoped BigOperators Classical
namespace CanonicalQuadraticSieve

section
open ActualEisensteinCubic CompletedGauss IdealCoprimeSieveOperator DivisorBlockCauchy

def annularHighWeight (M : ℝ) (I : Ideal O) : ℝ :=
  QuadraticInitialBound.annularSieveBump ((Ideal.absNorm I : ℝ) / M)

def annularHighEnergy (M N K : ℝ) (a : idealRange N → ℂ) : ℝ :=
  ∑ I : highKernelRange (2 * M) K, annularHighWeight M I.val *
    ‖∑ J : idealRange N, quadraticRow J.val (primaryGenerator I.val) * a J‖ ^ 2

def annularRayGcdBlock (M N K : ℝ) (D : Ideal O) (c : EisensteinEPrimaryPhase.Coord)
    (a : idealRange N → ℂ) : ℂ :=
  weightedRayGcdBlock D c (fun I : highKernelRange (2 * M) K => I.val)
    (fun J : idealRange N => J.val) (fun I => annularHighWeight M I.val) a

end

open ActualEisensteinCubic CompletedGauss FiniteSieveRestriction
open QuadraticSquarefreeKernel

end CanonicalQuadraticSieve

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

open scoped BigOperators Classical SchwartzMap ContDiff

namespace CubicEisenstein
open Filter
open scoped BigOperators Classical MatrixGroups Matrix Topology

open ActualEisensteinCubic CubicKubota ConcreteTraceCRT

abbrev UpperCoordinates := {p : ℂ × ℝ // 0 < p.2}

def coordinateSection (w : UpperCoordinates) : SL(2,ℂ) :=
  upperSection w.1.1 w.1.2 w.2

lemma continuous_coordinate_inverse_operator :
    Continuous (fun w : UpperCoordinates => rowOperator (coordinateSection w)⁻¹) := by
  have hroot : Continuous (fun w : UpperCoordinates => (Real.sqrt w.1.2 : ℂ)) :=
    Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp
      (continuous_snd.comp continuous_subtype_val))
  have hne : ∀ w : UpperCoordinates, (Real.sqrt w.1.2 : ℂ) ≠ 0 := fun w =>
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr w.2).ne'
  apply continuous_clm_apply.mpr
  intro u
  apply continuous_pi
  intro i
  change Continuous (fun w : UpperCoordinates =>
    Matrix.vecMul u (Matrix.adjugate (coordinateSection w : Matrix (Fin 2) (Fin 2) ℂ)) i)
  simp only [Matrix.vecMul,dotProduct,Fin.sum_univ_two,coordinateSection,upperSection,
    Matrix.SpecialLinearGroup.coe_mk,Matrix.adjugate_fin_two]
  fin_cases i
  · change Continuous (fun w : UpperCoordinates =>
      u 0 * (Real.sqrt w.1.2 : ℂ)⁻¹ + u 1 * (-0))
    exact (continuous_const.mul (hroot.inv₀ hne)).add
      (continuous_const.mul continuous_const)
  · change Continuous (fun w : UpperCoordinates =>
      u 0 * (-(w.1.1 / (Real.sqrt w.1.2 : ℂ))) + u 1 * (Real.sqrt w.1.2 : ℂ))
    exact (continuous_const.mul ((continuous_fst.comp continuous_subtype_val).div hroot hne).neg).add
      (continuous_const.mul hroot)

lemma continuous_coordinate_rowBound :
    Continuous (fun w : UpperCoordinates => rowBound (coordinateSection w)) :=
  continuous_const.mul (continuous_const.add continuous_coordinate_inverse_operator.norm)

lemma continuous_coordinate_summand (x : CuspCosets) :
    Continuous (fun p : UpperCoordinates × ℂ => summand (coordinateSection p.1) p.2 x) := by
  have hv : Continuous (fun p : UpperCoordinates × ℂ => p.1.1.2) :=
    (continuous_snd.comp continuous_subtype_val).comp continuous_fst
  have hz : Continuous (fun p : UpperCoordinates × ℂ => p.1.1.1) :=
    (continuous_fst.comp continuous_subtype_val).comp continuous_fst
  simp only [coordinateSection,summand_upperSection]
  apply continuous_const.mul
  apply Continuous.cpow
  · apply Complex.continuous_ofReal.comp
    apply hv.div
    · unfold heightDenominator
      exact ((continuous_const.mul hz).add continuous_const).norm.pow 2 |>.add
        (continuous_const.mul (hv.pow 2))
    · intro p
      exact (heightDenominator_pos _ _ p.1.2 _ (embeddedRow_ne_zero x)).ne'
  · exact continuous_snd
  · intro p
    exact Complex.ofReal_mem_slitPlane.mpr (div_pos p.1.2
      (heightDenominator_pos _ _ p.1.2 _ (embeddedRow_ne_zero x)))

lemma coordinate_summable_majorant (C a b : ℝ) (hC : 0 < C)
    (ha : 2 < a) (hb : 2 < b) :
    ∃ M : CuspCosets → ℝ, Summable M ∧ (∀ x,0 ≤ M x) ∧
      ∀ p : UpperCoordinates × ℂ,
        rowBound (coordinateSection p.1) ≤ C → a ≤ p.2.re → p.2.re ≤ b →
        ∀ x, ‖summand (coordinateSection p.1) p.2 x‖ ≤ M x := by
  let weight (t : ℝ) (x : CuspCosets) :=
    C ^(2*t)*‖rowCoordinates (cosetRow x)‖^(-(2*t))
  have hsum (t : ℝ) (ht : 2<t) : Summable (weight t) := by
    have hinj : Function.Injective (fun x : CuspCosets => rowCoordinates (cosetRow x)) :=
      rowCoordinates_injective.comp cosetRow_injective
    exact ((summable_integer_four_rpow (2*t) (by linarith)).comp_injective hinj).mul_left _
  refine ⟨fun x => weight a x + weight b x,(hsum a ha).add (hsum b hb),?_,?_⟩
  · intro x
    dsimp [weight]
    positivity
  · intro p hbound hpa hpb x
    apply (norm_summand_strip (coordinateSection p.1) a b p.2 hpa hpb x).trans
    apply add_le_add
    · apply (norm_summand_bound (coordinateSection p.1) (a:ℂ) (by simpa using lt_trans (by norm_num) ha) x).trans
      exact mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow (rowBound_pos _).le hbound (by simpa only [Complex.ofReal_re] using (show 0 ≤ 2*a by linarith))) (by positivity)
    · apply (norm_summand_bound (coordinateSection p.1) (b:ℂ) (by simpa using lt_trans (by norm_num) hb) x).trans
      exact mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow (rowBound_pos _).le hbound (by simpa only [Complex.ofReal_re] using (show 0 ≤ 2*b by linarith))) (by positivity)

theorem coordinate_eisenstein_continuousAt (p : UpperCoordinates × ℂ) (hp : 2 < p.2.re) :
    ContinuousAt (fun q : UpperCoordinates × ℂ => eisenstein (coordinateSection q.1) q.2) p := by
  let a : ℝ := (2+p.2.re)/2
  let b : ℝ := p.2.re+1
  let C : ℝ := rowBound (coordinateSection p.1)+1
  let region : Set (UpperCoordinates × ℂ) := {q |
    rowBound (coordinateSection q.1) < C ∧ a < q.2.re ∧ q.2.re < b}
  have ha : 2<a := by dsimp [a]; linarith
  have hb : 2<b := by dsimp [b]; linarith
  have hC : 0<C := by dsimp [C]; linarith [rowBound_pos (coordinateSection p.1)]
  obtain ⟨M,hM,hMnonneg,hbound⟩ := coordinate_summable_majorant C a b hC ha hb
  have hopen : IsOpen region := by
    exact (isOpen_lt (continuous_coordinate_rowBound.comp continuous_fst) continuous_const).inter
      ((isOpen_lt continuous_const (Complex.continuous_re.comp continuous_snd)).inter
        (isOpen_lt (Complex.continuous_re.comp continuous_snd) continuous_const))
  have hmem : p ∈ region := by
    dsimp [region,a,b,C]
    constructor
    · linarith
    · constructor <;> linarith
  have hcont : ContinuousOn (fun q : UpperCoordinates × ℂ =>
      ∑' x : CuspCosets, summand (coordinateSection q.1) q.2 x) region := by
    apply continuousOn_tsum (fun x => (continuous_coordinate_summand x).continuousOn) hM
    intro x q hq
    exact hbound q hq.1.le hq.2.1.le hq.2.2.le x
  exact (hcont p hmem).continuousAt (hopen.mem_nhds hmem)

theorem upperEisenstein_joint_continuousAt (p : UpperCoordinates × ℂ)
    (hp : 2 < p.2.re) :
    ContinuousAt (fun q : UpperCoordinates × ℂ =>
      upperEisenstein q.1.1.1 q.1.1.2 q.1.2 q.2) p :=
  coordinate_eisenstein_continuousAt p hp

end CubicEisenstein

open Filter
open scoped BigOperators Classical Topology

namespace CubicEisenstein

def logRatioPower (s : ℂ) (v q : ℝ) : ℂ :=
  Complex.exp (s * ((Real.log v - Real.log q : ℝ) : ℂ))

lemma logRatioPower_eq_cpow (s : ℂ) {v q : ℝ} (hv : 0<v) (hq : 0<q) :
    logRatioPower s v q = ((v/q : ℝ):ℂ)^s := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (div_pos hv hq).ne'),
    ← Complex.ofReal_log (div_pos hv hq).le, Real.log_div hv.ne' hq.ne']
  unfold logRatioPower
  congr 1
  ring

lemma hasDerivAt_logRatioPower (s : ℂ) {f g : ℝ → ℝ} {x f' g' : ℝ}
    (hf : HasDerivAt f f' x) (hg : HasDerivAt g g' x)
    (hf0 : f x ≠ 0) (hg0 : g x ≠ 0) :
    HasDerivAt (fun t => logRatioPower s (f t) (g t))
      (logRatioPower s (f x) (g x) * s * ((f'/f x-g'/g x : ℝ):ℂ)) x := by
  convert (preTransparency := .instances) (((hf.log hf0).sub (hg.log hg0)).ofReal_comp.const_mul s).cexp using 1 <;>
    dsimp [logRatioPower] ; ring

lemma hasDerivAt_deriv_logRatioPower (s : ℂ) (f g df dg : ℝ → ℝ) (x ddf ddg : ℝ)
    (hf : ∀t, HasDerivAt f (df t) t) (hg : ∀t, HasDerivAt g (dg t) t)
    (hdf : HasDerivAt df ddf x) (hdg : HasDerivAt dg ddg x)
    (hf0 : f x ≠ 0) (hg0 : g x ≠ 0) :
    HasDerivAt (deriv (fun t => logRatioPower s (f t) (g t)))
      (logRatioPower s (f x) (g x) *
        (s^2 * ((df x/f x-dg x/g x : ℝ):ℂ)^2 +
         s * (((ddf*f x-df x*df x)/(f x)^2 -
           (ddg*g x-dg x*dg x)/(g x)^2 : ℝ):ℂ))) x := by
  have hnear : ∀ᶠ t in 𝓝 x, f t ≠ 0 ∧ g t ≠ 0 :=
    ((hf x).continuousAt.eventually_ne hf0).and ((hg x).continuousAt.eventually_ne hg0)
  have heq : (deriv (fun t => logRatioPower s (f t) (g t))) =ᶠ[𝓝 x]
      (fun t => logRatioPower s (f t) (g t) * s * ((df t/f t-dg t/g t : ℝ):ℂ)) := by
    filter_upwards [hnear] with t ht
    exact (hasDerivAt_logRatioPower s (hf t) (hg t) ht.1 ht.2).deriv
  have hfirst := hasDerivAt_logRatioPower s (hf x) (hg x) hf0 hg0
  have hsecond := ((hdf.div (hf x) hf0).sub (hdg.div (hg x) hg0)).ofReal_comp
  apply HasDerivAt.congr_of_eventuallyEq _ heq
  convert (preTransparency := .instances) (hfirst.mul_const s).mul hsecond using 1 ;
    simp only [Pi.sub_apply,Pi.div_apply] ; ring

def quadraticHeightDenominator (A B C D x y v : ℝ) : ℝ :=
  A*(x^2+y^2+v^2)+2*(B*x+C*y)+D

lemma quadraticHeightDenominator_hasDerivAt_x (A B C D x y v : ℝ) :
    HasDerivAt (fun t => quadraticHeightDenominator A B C D t y v)
      (2*(A*x+B)) x := by
  convert (preTransparency := .instances) (((((hasDerivAt_id x).pow 2).add_const (y^2)).add_const (v^2)).const_mul A).add
    ((((hasDerivAt_id x).const_mul B).add_const (C*y)).const_mul 2) |>.add_const D using 1 <;>
    dsimp [quadraticHeightDenominator] ; ring

lemma quadraticHeightDenominator_hasDerivAt_y (A B C D x y v : ℝ) :
    HasDerivAt (fun t => quadraticHeightDenominator A B C D x t v)
      (2*(A*y+C)) y := by
  convert (preTransparency := .instances) (((((hasDerivAt_id y).pow 2).const_add (x^2)).add_const (v^2)).const_mul A).add
    ((((hasDerivAt_id y).const_mul C).const_add (B*x)).const_mul 2) |>.add_const D using 1 <;>
    dsimp [quadraticHeightDenominator] ; ring

lemma quadraticHeightDenominator_hasDerivAt_v (A B C D x y v : ℝ) :
    HasDerivAt (fun t => quadraticHeightDenominator A B C D x y t)
      (2*A*v) v := by
  convert (preTransparency := .instances) ((((hasDerivAt_id v).pow 2).const_add (x^2+y^2)).const_mul A).add_const
    (2*(B*x+C*y)+D) using 1 <;> dsimp [quadraticHeightDenominator] <;> ring_nf

def spatialHeightPower (s : ℂ) (A B C D x y v : ℝ) : ℂ :=
  logRatioPower s v (quadraticHeightDenominator A B C D x y v)

def heightLogDx (A B C D x y v : ℝ) : ℝ :=
  -(2*(A*x+B)/quadraticHeightDenominator A B C D x y v)
def heightLogDy (A B C D x y v : ℝ) : ℝ :=
  -(2*(A*y+C)/quadraticHeightDenominator A B C D x y v)
def heightLogDv (A B C D x y v : ℝ) : ℝ :=
  1/v - 2*A*v/quadraticHeightDenominator A B C D x y v

def heightLogDxx (A B C D x y v : ℝ) : ℝ :=
  -((2*A*quadraticHeightDenominator A B C D x y v -
    (2*(A*x+B))*(2*(A*x+B)))/(quadraticHeightDenominator A B C D x y v)^2)
def heightLogDyy (A B C D x y v : ℝ) : ℝ :=
  -((2*A*quadraticHeightDenominator A B C D x y v -
    (2*(A*y+C))*(2*(A*y+C)))/(quadraticHeightDenominator A B C D x y v)^2)
def heightLogDvv (A B C D x y v : ℝ) : ℝ :=
  -(1/v^2) - ((2*A*quadraticHeightDenominator A B C D x y v -
    (2*A*v)*(2*A*v))/(quadraticHeightDenominator A B C D x y v)^2)

lemma deriv_spatialHeightPower_v (s : ℂ) (A B C D x y v : ℝ)
    (hv : v≠0) (hq : quadraticHeightDenominator A B C D x y v≠0) :
    deriv (spatialHeightPower s A B C D x y) v =
      spatialHeightPower s A B C D x y v * s * (heightLogDv A B C D x y v : ℂ) := by
  exact (hasDerivAt_logRatioPower s (hasDerivAt_id v)
    (quadraticHeightDenominator_hasDerivAt_v A B C D x y v) hv hq).deriv

lemma deriv2_spatialHeightPower_x (s : ℂ) (A B C D x y v : ℝ)
    (hv : v≠0) (hq : quadraticHeightDenominator A B C D x y v≠0) :
    deriv (deriv (fun t => spatialHeightPower s A B C D t y v)) x =
      spatialHeightPower s A B C D x y v *
        (s^2*(heightLogDx A B C D x y v : ℂ)^2 +
          s*(heightLogDxx A B C D x y v : ℂ)) := by
  have h := hasDerivAt_deriv_logRatioPower s (fun _ => v)
    (fun t => quadraticHeightDenominator A B C D t y v) (fun _ => 0)
    (fun t => 2*(A*t+B)) x 0 (2*A)
    (fun t => hasDerivAt_const t v)
    (fun t => quadraticHeightDenominator_hasDerivAt_x A B C D t y v)
    (hasDerivAt_const x 0) (by simpa only [id_eq,mul_one] using ((hasDerivAt_id x).const_mul A |>.add_const B).const_mul 2)
    hv hq
  simpa only [spatialHeightPower,heightLogDx,heightLogDxx,zero_div,zero_sub,zero_mul,sub_zero] using h.deriv

lemma deriv2_spatialHeightPower_y (s : ℂ) (A B C D x y v : ℝ)
    (hv : v≠0) (hq : quadraticHeightDenominator A B C D x y v≠0) :
    deriv (deriv (fun t => spatialHeightPower s A B C D x t v)) y =
      spatialHeightPower s A B C D x y v *
        (s^2*(heightLogDy A B C D x y v : ℂ)^2 +
          s*(heightLogDyy A B C D x y v : ℂ)) := by
  have h := hasDerivAt_deriv_logRatioPower s (fun _ => v)
    (fun t => quadraticHeightDenominator A B C D x t v) (fun _ => 0)
    (fun t => 2*(A*t+C)) y 0 (2*A)
    (fun t => hasDerivAt_const t v)
    (fun t => quadraticHeightDenominator_hasDerivAt_y A B C D x t v)
    (hasDerivAt_const y 0) (by simpa only [id_eq,mul_one] using ((hasDerivAt_id y).const_mul A |>.add_const C).const_mul 2)
    hv hq
  simpa only [spatialHeightPower,heightLogDy,heightLogDyy,zero_div,zero_sub,zero_mul,sub_zero] using h.deriv

lemma deriv2_spatialHeightPower_v (s : ℂ) (A B C D x y v : ℝ)
    (hv : v≠0) (hq : quadraticHeightDenominator A B C D x y v≠0) :
    deriv (deriv (spatialHeightPower s A B C D x y)) v =
      spatialHeightPower s A B C D x y v *
        (s^2*(heightLogDv A B C D x y v : ℂ)^2 +
          s*(heightLogDvv A B C D x y v : ℂ)) := by
  change deriv (deriv (fun t => logRatioPower s t
    (quadraticHeightDenominator A B C D x y t))) v = _
  have h := hasDerivAt_deriv_logRatioPower s (fun t => t)
    (fun t => quadraticHeightDenominator A B C D x y t) (fun _ => 1)
    (fun t => 2*A*t) v 0 (2*A)
    (fun t => hasDerivAt_id t)
    (fun t => quadraticHeightDenominator_hasDerivAt_v A B C D x y t)
    (hasDerivAt_const v 1) (by simpa only [id_eq,mul_one] using (hasDerivAt_id v).const_mul (2*A))
    hv hq
  simpa only [spatialHeightPower,heightLogDv,heightLogDvv,zero_mul,zero_sub,one_mul,neg_div] using h.deriv

lemma quadraticHeight_gradient_square (A B C D x y v : ℝ)
    (hrel : A*D=B^2+C ^2) :
    (A*x+B)^2 + (A*y+C)^2 + (A*v)^2 =
      A*quadraticHeightDenominator A B C D x y v := by
  unfold quadraticHeightDenominator
  nlinarith [hrel]

lemma heightLog_eikonal (A B C D x y v : ℝ)
    (hrel : A*D=B^2+C ^2) (hv : v≠0)
    (hq : quadraticHeightDenominator A B C D x y v≠0) :
    v^2 * ((heightLogDx A B C D x y v)^2 +
      (heightLogDy A B C D x y v)^2 + (heightLogDv A B C D x y v)^2) = 1 := by
  calc
    _ = 1 + 4*v^2/(quadraticHeightDenominator A B C D x y v)^2 *
        ((A*x+B)^2+(A*y+C)^2+(A*v)^2 - A*quadraticHeightDenominator A B C D x y v) := by
      unfold heightLogDx heightLogDy heightLogDv
      field_simp [hv,hq]
      ; ring
    _ = 1 := by rw [quadraticHeight_gradient_square A B C D x y v hrel]; ring

lemma heightLog_laplacian (A B C D x y v : ℝ)
    (hrel : A*D=B^2+C ^2) (hv : v≠0)
    (hq : quadraticHeightDenominator A B C D x y v≠0) :
    v^2 * (heightLogDxx A B C D x y v +
      heightLogDyy A B C D x y v + heightLogDvv A B C D x y v) -
      v*heightLogDv A B C D x y v = -2 := by
  calc
    _ = -2 + 4*v^2/(quadraticHeightDenominator A B C D x y v)^2 *
        ((A*x+B)^2+(A*y+C)^2+(A*v)^2 - A*quadraticHeightDenominator A B C D x y v) := by
      unfold heightLogDxx heightLogDyy heightLogDvv heightLogDv
      field_simp [hv,hq]
      ; ring
    _ = -2 := by rw [quadraticHeight_gradient_square A B C D x y v hrel]; ring

def hyperbolicLaplacian (f : ℝ → ℝ → ℝ → ℂ) (x y v : ℝ) : ℂ :=
  (v:ℂ)^2 * (deriv (deriv (fun t => f t y v)) x +
    deriv (deriv (fun t => f x t v)) y + deriv (deriv (f x y)) v) -
    (v:ℂ)*deriv (f x y) v

theorem spatialHeightPower_eigenfunction (s : ℂ) (A B C D x y v : ℝ)
    (hrel : A*D=B^2+C ^2) (hv : v≠0)
    (hq : quadraticHeightDenominator A B C D x y v≠0) :
    hyperbolicLaplacian (spatialHeightPower s A B C D) x y v =
      s*(s-2)*spatialHeightPower s A B C D x y v := by
  have he : (v:ℂ)^2 * ((heightLogDx A B C D x y v : ℂ)^2 +
      (heightLogDy A B C D x y v : ℂ)^2 + (heightLogDv A B C D x y v : ℂ)^2) = 1 := by
    exact_mod_cast heightLog_eikonal A B C D x y v hrel hv hq
  have hl : (v:ℂ)^2 * ((heightLogDxx A B C D x y v : ℂ) +
      (heightLogDyy A B C D x y v : ℂ) + (heightLogDvv A B C D x y v : ℂ)) -
      (v:ℂ)*(heightLogDv A B C D x y v : ℂ) = -2 := by
    exact_mod_cast heightLog_laplacian A B C D x y v hrel hv hq
  unfold hyperbolicLaplacian
  rw [deriv2_spatialHeightPower_x s A B C D x y v hv hq,
    deriv2_spatialHeightPower_y s A B C D x y v hv hq,
    deriv2_spatialHeightPower_v s A B C D x y v hv hq,
    deriv_spatialHeightPower_v s A B C D x y v hv hq]
  calc
    _ = spatialHeightPower s A B C D x y v *
        (s^2*((v:ℂ)^2*((heightLogDx A B C D x y v : ℂ)^2 +
          (heightLogDy A B C D x y v : ℂ)^2 + (heightLogDv A B C D x y v : ℂ)^2)) +
        s*((v:ℂ)^2*((heightLogDxx A B C D x y v : ℂ) +
          (heightLogDyy A B C D x y v : ℂ) + (heightLogDvv A B C D x y v : ℂ)) -
          (v:ℂ)*(heightLogDv A B C D x y v : ℂ))) := by ring
    _ = _ := by rw [he,hl]; ring

lemma complex_row_quadratic_relation (c d : ℂ) :
    Complex.normSq c * Complex.normSq d = (c*star d).re^2 + (-(c*star d).im)^2 := by
  simp only [Complex.normSq_apply,Complex.mul_re,Complex.mul_im,Complex.star_def,
    Complex.conj_re,Complex.conj_im]
  ring

lemma heightDenominator_eq_quadratic (u : Fin 2 → ℂ) (x y v : ℝ) :
    heightDenominator ((x:ℂ)+(y:ℂ)*Complex.I) v u =
      quadraticHeightDenominator (Complex.normSq (u 0)) ((u 0*star (u 1)).re)
        (-(u 0*star (u 1)).im) (Complex.normSq (u 1)) x y v := by
  unfold heightDenominator quadraticHeightDenominator
  simp only [← Complex.normSq_eq_norm_sq,Complex.normSq_apply,Complex.add_re,Complex.add_im,
    Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,
    Complex.I_im,Complex.star_def,Complex.conj_re,Complex.conj_im]
  ring

def actualHeightPower (s : ℂ) (u : Fin 2 → ℂ) (x y v : ℝ) : ℂ :=
  ((transformedHeight ((x:ℂ)+(y:ℂ)*Complex.I) v u : ℝ) : ℂ)^s

lemma actualHeightPower_eq_spatial (s : ℂ) (u : Fin 2 → ℂ) (hu : u≠0)
    (x y v : ℝ) (hv : 0<v) :
    actualHeightPower s u x y v =
      spatialHeightPower s (Complex.normSq (u 0)) ((u 0*star (u 1)).re)
        (-(u 0*star (u 1)).im) (Complex.normSq (u 1)) x y v := by
  rw [actualHeightPower,spatialHeightPower,logRatioPower_eq_cpow s hv]
  · rw [transformedHeight,heightDenominator_eq_quadratic]
  · rw [← heightDenominator_eq_quadratic]
    exact heightDenominator_pos _ _ hv u hu

lemma hyperbolicLaplacian_const_mul (c : ℂ) (f : ℝ → ℝ → ℝ → ℂ) (x y v : ℝ) :
    hyperbolicLaplacian (fun x y v => c*f x y v) x y v =
      c*hyperbolicLaplacian f x y v := by
  unfold hyperbolicLaplacian
  simp only [deriv_const_mul_field',deriv_const_mul_field]
  ring

lemma eigenfunction_summand_eq_actual_series (s : ℂ) (r : CuspCosets)
    (x y v : ℝ) (hv : 0<v) :
    (cosetCharacter r)⁻¹ * actualHeightPower s (embeddedRow r) x y v =
      summand (upperSection ((x:ℂ)+(y:ℂ)*Complex.I) v hv) s r := by
  rw [summand_upperSection]
  rfl

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

open scoped BigOperators Classical SchwartzMap
namespace CanonicalQuadraticSieve

open ActualEisensteinCubic

open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson
open TruncatedPrincipalPoisson IdealMobiusDivisorSum

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

def originalTruncatedMiddle (W : 𝓢(ℝ, ℂ))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M : ℝ) (Y Z : m → ℝ) (lengthScale : ℝ) : ℂ :=
  ∑ i, ∑ j, ∑ k, originalTerm rows left right a b 1 1 i j k *
    middleTruncation (fun P : primePool {left j * right k} => P.val) Finset.univ W
      (Real.sqrt (M / (Ideal.absNorm (rows i) : ℝ))) (Y i) (Z i) lengthScale

end CanonicalQuadraticSieve

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

open scoped BigOperators Classical SchwartzMap
namespace CanonicalQuadraticSieve
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson
open TruncatedPrincipalPoisson IdealMobiusDivisorSum

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

def dualTruncatedMiddle (W : 𝓢(ℝ, ℂ))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M F : ℝ) (Y Z : m → ℝ) (lengthScale : ℝ) : ℂ :=
  ∑ i, ∑ j, ∑ k, originalTerm rows left right a b 1 1 i j k *
    (((M / (Real.sqrt ((Ideal.absNorm (left j) : ℝ) * (Ideal.absNorm (right k) : ℝ)) * F) : ℝ) : ℂ) *
      middleTruncation (fun P : primePool {left j * right k} => P.val) Finset.univ W
        (Real.sqrt (F * (Ideal.absNorm (left j) : ℝ) * (Ideal.absNorm (right k) : ℝ) /
          (M * (Ideal.absNorm (rows i) : ℝ)))) (Y i) (Z i) lengthScale)

end CanonicalQuadraticSieve

open scoped BigOperators Classical

open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory

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

open scoped BigOperators Classical SchwartzMap
namespace CanonicalQuadraticSieve

section
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson
open TruncatedPrincipalPoisson IdealMobiusDivisorSum

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

def originalMaskedTruncatedMiddle (G : Ideal O) (W : 𝓢(ℝ, ℂ))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M : ℝ) (Y Z : m → ℝ) (lengthScale : ℝ) : ℂ :=
  ∑ i, ∑ j, ∑ k, originalTerm rows left right a b 1 1 i j k *
    middleTruncation (fun P : primePool {G * (left j * right k)} => P.val) Finset.univ W
      (Real.sqrt (M / (Ideal.absNorm (rows i) : ℝ))) (Y i) (Z i) lengthScale

end

open ActualEisensteinCubic IdealMobiusDivisorSum IdealCoprimeSieveOperator

end CanonicalQuadraticSieve

open scoped BigOperators Classical
namespace CanonicalQuadraticSieve

section
open ActualEisensteinCubic FourierBridge

def halfShellFactor (N q : ℝ) : ℝ := Real.sqrt (N/2) / Real.sqrt q

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

def smallPrincipalCorrection (S T : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M F : ℝ) : ℝ :=
  ∑ D ∈ S, ∑ E ∈ T, ∑ i,
    ‖∑ j, ∑ k, originalTerm rows left right a b D E i j k *
      ((M/(Real.sqrt ((Ideal.absNorm (left j) : ℝ)*(Ideal.absNorm (right k) : ℝ))*F) : ℝ) : ℂ)‖

end

open ActualEisensteinCubic

open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson
open TruncatedPrincipalPoisson IdealCoprimeSieveOperator

open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson
open TruncatedPrincipalPoisson IdealCoprimeSieveOperator

end CanonicalQuadraticSieve

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

namespace VerticalContourShift
open Filter MeasureTheory
open scoped Classical Topology

def gaussianRegulatorSequence (n : ℕ) : ℝ := 1/((n:ℝ)+1)

end VerticalContourShift

open Filter MeasureTheory
open scoped Classical BigOperators Topology

open Filter MeasureTheory
open scoped Classical BigOperators Topology

namespace CubicEisenstein

def radialBesselProfile {α : Type*} (r : α→ℝ) (a : α→ℂ) (q v : ℝ) : ℂ :=
  ∑'i,(a i*(r i:ℂ))*(v:ℂ)*
    schlafliBesselK (1/3) (4*Real.pi*q*Real.sqrt (r i)*v)

end CubicEisenstein

end

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic CompletedGauss FirstPassCubeLabels SecondPassArithmetic
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

def finiteCanonicalMarkedRow (pool : Finset ι) (Ψ : Eis →* ℂ) (m f k : Eis)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (W : ℝ → ℂ) (X : ℝ) : ℂ :=
  fixedChildRow p hp hcop hg pool Ψ m
    (fun U => primeMark slots lists a U * W (primeProductNorm p U / X)) f k

end
end SevenEighths.InverseMoment

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

def canonicalMarkedSplit (F V A : Finset ι) (Ψ : Eis →* ℂ) (m r c d e k : Eis)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (W : ℝ → ℂ) (X : ℝ) : ℂ :=
  ∑ J ∈ slots.powerset, primeMark J lists a (A ∪ V) *
    finiteCanonicalMarkedRow p hp hcop hg F Ψ (m * r)
      (c * e * ∏ i ∈ V, p i) (d * e * k)
      (slots \ J) (fun i => lists i \ A) a W (X / primeProductNorm p V)

end
end SevenEighths.InverseMoment

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic RayFourExpansion
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]
  (p : ι → Eis) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

def firstFreshSecondPoisson
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (F D B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (χ : RayCharacter) (Ψ : Eis →* ℂ) (m : Eis)
    (H : Finset ι → ℂ) (ω : ℝ → ℂ) (X : ℝ) (c d : Eis)
    (r : FirstCoreIndex) (t Y : ℝ) : ℂ :=
  ∑ G ∈ (F\D).powerset, ∑ U ∈ ((F\D)\G).powerset, ∑ V ∈ ((F\D)\G).powerset,
    if Disjoint U V then overlapPairWeight p hg (firstCoreTwist negative χ Ψ r)
      (m*b0Label p B v ε₁ ε₂) (c*jLabel p B v ε₁ ε₂) d
      (firstCoreTest H (fun u => ω (Real.exp u))
        (columnLog p (primeProductNorm p D*X)) negative (-t) D) G U V *
      maskedSecondDual p hg hp hinj G U V rowMajorant Y else 0

end
end SevenEighths.InverseMoment

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss LocalReflectionBrackets
open CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
noncomputable local instance idealBridgeFinite (P : Ideal Eis) [P.IsMaximal] : Fintype (Eis ⧸ P) := Fintype.ofFinite _

theorem admissible_primeIndex_product (K : Ideal Eis) (hK : Admissible K) :
    (∏ P : PrimeIndex K, P.val) = K := by
  have hn := (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hK.1).mp hK.2.1
  have hv : (CompletedGauss.primeSupport K).val = UniqueFactorizationMonoid.normalizedFactors K := by
    simpa only [CompletedGauss.primeSupport, Multiset.toFinset_val] using hn.dedup
  calc
    _ = ∏ P ∈ CompletedGauss.primeSupport K, P := Finset.prod_coe_sort _ _
    _ = (CompletedGauss.primeSupport K).val.prod := (Finset.prod_val _).symm
    _ = K := by rw [hv]; exact Ideal.prod_normalizedFactors_eq_self hK.1

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {φ σ : Type*} [Fintype φ] [Fintype σ] {N a c : Eis} {mode : Bool}

abbrev CoprimeSourceIndex (K : Ideal Eis) (Pset nset bset : Finset (Ideal Eis)) :=
  {P : Pset // IsCoprime K P.val} × (nset × bset)

instance (K : Ideal Eis) (Pset nset bset : Finset (Ideal Eis)) :
    Fintype (CoprimeSourceIndex K Pset nset bset) := inferInstanceAs
      (Fintype ({P : Pset // IsCoprime K P.val} × (nset × bset)))

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

def fullRaySector (N : Eis) (rows : Finset (Ideal Eis)) (r : Eis⧸Ideal.span {N^2}) : Finset (Ideal Eis) :=
  rows.filter (fun K => Ideal.Quotient.mk (Ideal.span {N^2}) (primaryGenerator K)=r)

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {σ φ : Type*} [Fintype σ] [DecidableEq σ]

def fixedSlotTupleSet (L : σ→Finset (Ideal Eis)) (F : φ→Ideal Eis) : Finset (σ→Ideal Eis) :=
  (Fintype.piFinset L).filter fun p => ∀ j i,p i≠F j

lemma mem_fixedSlotTupleSet (L : σ→Finset (Ideal Eis)) (F : φ→Ideal Eis) (p : σ→Ideal Eis) :
    p∈fixedSlotTupleSet L F ↔ (∀ i,p i∈L i) ∧ ∀ j i,p i≠F j := by
  simp only [fixedSlotTupleSet,Finset.mem_filter,Fintype.mem_piFinset]

def supportedSlotTupleEquiv (L : σ→Finset (Ideal Eis)) (F : φ→Ideal Eis) (K : Ideal Eis) :
    supportedSlotChoices L F K ≃ {p : fixedSlotTupleSet L F // IsCoprime K (slotTupleProduct p.val)} where
  toFun p := ⟨⟨fun i => (p.val i).val,(mem_fixedSlotTupleSet L F _).mpr ⟨fun i => (p.val i).property,p.property.2⟩⟩,p.property.1⟩
  invFun p := ⟨fun i => ⟨p.val.val i,((mem_fixedSlotTupleSet L F _).mp p.val.property).1 i⟩,
    ⟨p.property,((mem_fixedSlotTupleSet L F _).mp p.val.property).2⟩⟩
  left_inv p := by
    apply Subtype.ext
    funext i
    rfl
  right_inv p := rfl

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {φ σ : Type*} [Fintype φ] [Fintype σ] {N a c : Eis} {mode : Bool}

lemma fullRaySector_subset (N : Eis) (rows : Finset (Ideal Eis)) (r : Eis⧸Ideal.span {N^2}) :
    fullRaySector N rows r⊆rows := Finset.filter_subset _ _

end
end SevenEighths.InverseReflectedPhase

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators
namespace SevenEighths.HeckeCharacterAnalytic

def additiveFiberEquiv {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (π : A →+ B) (hπ : Function.Surjective π) : A ≃ B × π.ker := by
  classical
  let r : B → A := fun b => (hπ b).choose
  have hr : ∀ b, π (r b) = b := fun b => (hπ b).choose_spec
  exact {
    toFun := fun a => (π a, ⟨a - r (π a), by simp [AddMonoidHom.mem_ker, hr]⟩)
    invFun := fun p => p.2 + r p.1
    left_inv := by intro a; simp
    right_inv := by
      rintro ⟨b, k⟩
      have hk : π k = 0 := k.property
      apply Prod.ext
      · simp [hr, hk]
      · apply Subtype.ext
        simp [hr, hk] }

theorem sum_comp_additiveHom {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    [Fintype A] [Fintype B] (π : A →+ B) (hπ : Function.Surjective π) (f : B → ℂ) :
    (∑ a, f (π a)) = (Nat.card π.ker : ℂ) * ∑ b, f b := by
  classical
  let : Fintype π.ker := Fintype.ofFinite _
  have hid (a : A) : f (π a) = (fun p : B × π.ker => f p.1) (additiveFiberEquiv π hπ a) := rfl
  simp_rw [hid]
  rw [(additiveFiberEquiv π hπ).bijective.sum_comp (fun p : B × π.ker => f p.1)]
  simp only [Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, ← Finset.mul_sum, Nat.card_eq_fintype_card]

theorem sum_residue_pullback_eq_zero {A R : Type*} [AddCommGroup A] [Fintype A]
    [CommRing R] [Fintype R] (π : A →+ R) (hπ : Function.Surjective π)
    (χ : MulChar R ℂ) (hχ : χ ≠ 1) : (∑ a, χ (π a)) = 0 := by
  rw [sum_comp_additiveHom π hπ, MulChar.sum_eq_zero_of_ne_one hχ, mul_zero]

def finCastEquiv (N : ℕ) [NeZero N] : Fin N ≃ ZMod N where
  toFun a := (a : ℕ)
  invFun z := ⟨z.val, ZMod.val_lt z⟩
  left_inv a := Fin.ext (ZMod.val_natCast_of_lt a.isLt)
  right_inv z := ZMod.natCast_zmod_val z

theorem coefficients_sum_eq_zero (χ : HeckeFamily.Character) (hχ : χ.residue ≠ 1) :
    (∑ a, HeckeFamily.coefficients χ a) = 0 := by
  classical
  let : Finite (HeckeFamily.O ⧸ χ.modulus) :=
    Ring.HasFiniteQuotients.finiteQuotient χ.modulus_ne_bot
  let : Fintype (HeckeFamily.O ⧸ χ.modulus) := Fintype.ofFinite _
  let e := Equiv.prodCongr (finCastEquiv χ.period) (finCastEquiv χ.period)
  calc
    (∑ a, HeckeFamily.coefficients χ a) =
        ∑ a, χ.residue (HeckeCoordinates.coordinateQuotientHom χ (e a)) := by
      apply Finset.sum_congr rfl
      intro a _
      exact HeckeCoordinates.coefficients_eq_quotient_character χ a
    _ = ∑ a : ZMod χ.period × ZMod χ.period,
        χ.residue (HeckeCoordinates.coordinateQuotientHom χ a) :=
      e.bijective.sum_comp (fun a => χ.residue (HeckeCoordinates.coordinateQuotientHom χ a))
    _ = 0 := sum_residue_pullback_eq_zero
      (HeckeCoordinates.coordinateQuotientHom χ)
      (HeckeCoordinates.coordinateQuotientHom_surjective χ) χ.residue hχ

theorem residue_zero_of_nonprincipal (χ : HeckeFamily.Character) (hχ : χ.residue ≠ 1) :
    χ.residue 0 = 0 := by
  rcases subsingleton_or_nontrivial (HeckeFamily.O ⧸ χ.modulus) with h | h
  · let := h
    exfalso
    apply hχ
    apply MulChar.ext'
    intro a
    have ha : a = 1 := Subsingleton.elim _ _
    simp [ha]
  · let := h
    exact χ.residue.map_zero

theorem coefficients_zero_of_nonprincipal (χ : HeckeFamily.Character) (hχ : χ.residue ≠ 1) :
    HeckeFamily.coefficients χ (0, 0) = 0 := by
  simpa only [HeckeFamily.coefficients, HeckeFamily.elementCoeff,
    HeckeFamily.coordinateElement, Fin.val_zero, Int.natCast_zero, Int.cast_zero,
    zero_mul, zero_add, map_zero] using residue_zero_of_nonprincipal χ hχ

theorem completed_entire_nonprincipal (χ : HeckeFamily.Character) (hχ : χ.residue ≠ 1) :
    Differentiable ℂ (HeckeTheta.completed (HeckeFamily.coefficients χ)) := by
  intro s
  exact (HeckeTheta.pair (HeckeFamily.coefficients χ)).differentiableAt_Λ
    (Or.inr (by rw [HeckeTheta.pair_f₀, coefficients_zero_of_nonprincipal χ hχ]))
    (Or.inr (HeckeTheta.pair_g₀_eq_zero _ (coefficients_sum_eq_zero χ hχ)))

theorem continuedLattice_entire_nonprincipal (χ : HeckeFamily.Character)
    (hχ : χ.residue ≠ 1) : Differentiable ℂ (HeckeFamily.continuedLattice χ) := by
  exact ((differentiable_id.const_cpow (Or.inl
    (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))).mul
      Complex.differentiable_one_div_Gamma).mul (completed_entire_nonprincipal χ hχ)

end SevenEighths.HeckeCharacterAnalytic

end

end OAI
end

section

namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseMoment
open CanonicalCubeSeparation

def RankReferenceCutoffs:Prop :=
  ∀lo hi:ℝ,0<lo→0≤hi→∃(Vlog:𝓢(ℝ,ℂ))(Alog:ℝ),
    (∀x,Vlog x≠0→|x|≤Alog) ∧
    (∀x,|x|≤ columnWindowRadius lo hi→Vlog x=1)

def RankReferenceThresholds:Prop :=
  ∀eta:ℝ,0<eta→∀hi Alog window:ℝ,∃Zt:ℝ,1<Zt ∧ ∀Z:ℝ,Zt≤Z→
    2≤Z ∧ 2≤Z^eta ∧ Real.exp 1≤Z^eta ∧ 1≤eta*Real.log Z ∧
    hi≤Z^eta ∧ Real.exp Alog≤Z^eta ∧ Real.exp window≤Z^eta

end SevenEighths.InverseMoment

end

end OAI
end

section

namespace OAI

noncomputable section
namespace SevenEighths.ProbeEuler

def localCubePhase (C omega : ℂ) (e l k : ℕ) : ℂ :=
  C ^l * omega^((e+3*l)*k+e*l+l.choose 2)

def weightedScalar (Q eta a G1 C omega X W V scalar : ℂ) (e l k m : ℕ) : ℂ :=
  (-eta*X/G1)^e * (a*X^3/Q)^l * localCubePhase C omega e l k * scalar * W^k * V^m

def evenRatio (Q a X V : ℂ) : ℂ := a^2*Q^4*X^6*V

end SevenEighths.ProbeEuler
end

end OAI
end

section

namespace OAI

noncomputable section
open Filter MeasureTheory
open scoped Classical Topology ContDiff
namespace SevenEighths.RayPrimeNormalizer
open HeckeFamily
variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
def normalizer (S : Finset (Ideal O)) (W : ℝ → ℝ) (x : ℝ) : ℝ :=
  PNT.AnnularPrimeMass.weightedPrimeSumDeleted (RayQuotient.identityClass M H) S W x

include hH

end SevenEighths.RayPrimeNormalizer

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter
namespace SevenEighths.ProbeRaySlots
open HeckeFamily ProbePhysical PNT.AnnularPrimeMass
open ProbePrincipalResidueActual
local notation "Id" => Ideal HeckeFamily.O

def pool (C : Set Id) (S : Finset Id) (a b x : ℝ) : Finset PrimeIdeal :=
  (annularPrimeIdeals C a b x \ S).subtype (fun P=>Prime P)

@[simp] theorem mem_pool (C : Set Id) (S : Finset Id) (a b x : ℝ) (P : PrimeIdeal) :
    P∈pool C S a b x ↔ P.val∈C ∧ ⌊x*a⌋₊<Ideal.absNorm P.val ∧
      Ideal.absNorm P.val≤⌊x*b⌋₊ ∧ P.val∉S := by
  simp only [pool,Finset.mem_subtype,Finset.mem_sdiff,mem_annularPrimeIdeals,P.property]
  tauto

variable (M : Id) [NeZero M]
variable (H : Subgroup (HeckeFamily.O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

include hH

end SevenEighths.ProbeRaySlots
end

end OAI
end

section

namespace OAI

noncomputable section
namespace SevenEighths.ProbeEuler

def rowWeightedScalar (Q eta a G1 C omega X W V rho scalar : ℂ) (e l k m : ℕ) : ℂ :=
  (rho^k/rho^(e+3*l))*weightedScalar Q eta a G1 C omega X W V scalar e l k m

end SevenEighths.ProbeEuler
end

end OAI
end

section

namespace OAI

noncomputable section

open scoped Classical FourierTransform SchwartzMap ContDiff Topology
open MeasureTheory Filter Set
namespace SevenEighths.HeckeDetectorDyadicProfiles
open CubicReflectionKernel

def ratioProfile (V W : ℝ→ℂ) (R x : ℝ) : ℂ := V (R*x)*W x

def logFamily (V W : ℝ→ℂ) (p : ℝ×ℝ) (y : ℝ) : ℂ :=
  Real.exp (-p.2*y) • ratioProfile V W p.1 (Real.exp (-y))

lemma ratioProfile_support (V W : ℝ→ℂ) (R : ℝ) :
    Function.support (ratioProfile V W R)⊆Function.support W := by
  intro x hx
  exact (mul_ne_zero_iff.mp hx).2

end SevenEighths.HeckeDetectorDyadicProfiles

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators
namespace SevenEighths.ProbeCentralExponent

def sourceExponent (a d R q : ℝ) : ℝ :=
  (17/48)*(1/2-17/50)+a+17/50-1-a*(23/48)-d*(17/50)+d*R+
    d*(a-1/2)+(1/6)*(17/50-1/2+q)

def relativeExponent (δ d R q : ℝ) : ℝ :=
  -1/48+(2/3)*δ+q/6-(13/16)*(1-R)+(d-13/16)*(R+δ/2-17/50)

def realLoss (N : ℕ) (d e eps heightLoss mesh : ℝ) : ℝ :=
  (105/8)*e+12*d*e+d*eps*(N+8)+heightLoss+mesh/6

end SevenEighths.ProbeCentralExponent

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical

def mixedSourceExponent (a v d R q : ℝ) : ℝ :=
  ProbeCentralExponent.sourceExponent a v R q+(d-v)*R

end SevenEighths.ProbeHighRowFamily

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
open ProbeRaySlots HeckePrimeAmplitudeBins
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

omit [NeZero M] in
theorem poolOutside (S : Finset (Ideal O)) (N : ℕ) (c b : ℝ) (Y : Fin N→ℝ) :
    ∀j P,P∈pool (RayQuotient.identityClass M H) S c b (Y j) → P.val∉S :=
  fun j P hP=>(mem_pool _ S c b (Y j) P).mp hP |>.2.2.2

end SevenEighths.ProbeHighRowFamily

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
open ProbeRaySlots HeckePrimeAmplitudeBins
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

omit [NeZero M] in
theorem fixedPoolOutside (S : Finset (Ideal O)) (N : ℕ) (c b : ℝ) (Y : Fin N→ℝ) :
    ∀j P,P∈pool (RayQuotient.identityClass M H) S c b (Y j) → P.val∉S :=
  fun j P hP=>(mem_pool _ S c b (Y j) P).mp hP |>.2.2.2

end SevenEighths.ProbeHighRowFamily

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
open ProbeRaySlots
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

omit [NeZero M] in
theorem classPoolOutside (S : Finset (Ideal O)) (N : ℕ) (c b : ℝ) (Y : Fin N→ℝ) :
    ∀j P,P∈pool (RayQuotient.identityClass M H) S c b (Y j) → P.val∉S :=
  fun j P hP=>(mem_pool _ S c b (Y j) P).mp hP |>.2.2.2

end SevenEighths.ProbeHighRowFamily

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical Topology ContDiff
open Filter
namespace SevenEighths.ProbePhysical
open CompletedGauss

def gaussianDyadicProfile (Z : ℝ) (j : ℕ) (y : ℝ) : ℂ :=
  gaussianAnnulus y*gaussianMellinProfile ((2:ℝ)^j*y/Z)/(Real.sqrt y:ℂ)

end SevenEighths.ProbePhysical
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical ContDiff Topology SchwartzMap FourierTransform
open MeasureTheory Filter Set FourierBridge CompletedGauss
namespace SevenEighths.ProbePhysical

def gaussianSlotWindow {ι : Type*} (W : ι→ℝ→ℂ) : Option ι→ℝ→ℂ
  | none => fun y=>gaussianAnnulus (Real.exp y)
  | some i => fun y=>W i (Real.exp y)
def gaussianSlotSlope {ι : Type*} : Option ι→ℝ
  | none => 1
  | some _ => -1
def gaussianSlotPoint {ι : Type*} (x : ℝ) (q : ι→ℝ) : Option ι→ℝ
  | none => Real.log x
  | some i => Real.log (q i)

end SevenEighths.ProbePhysical
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical FourierTransform SchwartzMap RealInnerProductSpace

namespace ProbeGramLatticeDecay
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson
local notation "O" => ActualEisensteinCubic.O

abbrev Joint := WithLp 2 (ℂ × ℂ)

def point (x y : ℂ) : Joint := WithLp.toLp 2 (x,y)

def sourceControl (S : Finset (ℕ × ℕ)) (W : 𝓢(Joint, ℂ)) : ℝ :=
  S.sup (schwartzSeminormFamily ℝ Joint ℂ) W

@[simp] theorem norm_point_sq (x y : ℂ) :
    ‖point x y‖^2 = ‖x‖^2 + ‖y‖^2 := WithLp.prod_norm_sq_eq_of_L2 _

def physicalPoint (N : ℝ) (m : O × O) : Joint :=
  point (eisEmbedding m.1 / (Real.sqrt N : ℂ))
    (eisEmbedding m.2 / (Real.sqrt N : ℂ))

abbrev DualIndex := (ℤ × ℤ) × (ℤ × ℤ)

def dualPoint (p : DualIndex) : Joint :=
  point (explicitDualFrequency 1 p.1) (explicitDualFrequency 1 p.2)

def dualRow (p : DualIndex) : Fin 2 → O :=
  ![dualFrequencyEquiv p.1, dualFrequencyEquiv p.2]

def dualCoordinates (p : DualIndex) : (Fin 2 × Fin 2) → ℤ :=
  CubicEisenstein.rowCoordinates (dualRow p)

@[simp] theorem dualCoordinates_zero : dualCoordinates 0 = 0 := by
  have hzero : ActualEisensteinCoordinates.coords (0 : O) = (0,0) := by
    simpa [ActualEisensteinCoordinates.eval] using ShortDraftLatticeCount.coords_eval 0 0
  ext ⟨i,j⟩
  fin_cases i <;> fin_cases j <;>
    simp [dualCoordinates, CubicEisenstein.rowCoordinates, dualRow,
      dualFrequencyEquiv, ActualEisensteinCoordinates.eval, hzero]

def scaledDualPoint (L : ℝ) (u : ℂ) (p : DualIndex) : Joint :=
  point (u*(L:ℂ)*explicitDualFrequency 1 p.1)
    (u*(L:ℂ)*explicitDualFrequency 1 p.2)

end ProbeGramLatticeDecay

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical FourierTransform SchwartzMap RealInnerProductSpace

namespace ProbeGramAnnularLattice
open ProbeGramLatticeDecay ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson
local notation "O" => ActualEisensteinCubic.O

def AnnularSupport (a b : ℝ) (W : 𝓢(Joint, ℂ)) : Prop :=
  Function.support W ⊆ {z : Joint | a ≤ ‖z.fst‖^2 ∧ ‖z.fst‖^2 ≤ b ∧
    a ≤ ‖z.snd‖^2 ∧ ‖z.snd‖^2 ≤ b}

def cauchyWeight (m : O) : ℝ := ((1+‖eisEmbedding m‖^2)^2)⁻¹

end ProbeGramAnnularLattice

end

end OAI
end

section

namespace OAI

noncomputable section

open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set FourierBridge
namespace ProbeGramJointProfile
open ProbeGramLatticeDecay EisensteinSchwartzPoisson

def rayControl (B n : ℕ) (g : 𝓢(ℝ, ℂ)) : ℝ :=
  (Finset.Iic (2*B+n,n)).sup (schwartzSeminormFamily ℝ ℝ ℂ) g

def amplitudeControl (n : ℕ) (A : 𝓢(Joint, ℂ)) : ℝ :=
  (Finset.Iic (0,n)).sup (schwartzSeminormFamily ℝ Joint ℂ) A

def heightOrder (H : Finset (ℕ × ℕ)) : ℕ := H.sup Prod.snd

end ProbeGramJointProfile

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical ContDiff Topology
open Set Complex
namespace SevenEighths.HeckeDetectorRowwisePolynomial
open HeckeFamily HeckeDetectorDyadicBridge

def logProfile (W : ℝ→ℂ) (x : ℝ) : ℂ := (Real.log x : ℂ)*W x

theorem logProfile_support (W : ℝ→ℂ) :
    Function.support (logProfile W)⊆Function.support W := by
  intro x hx hw
  exact hx (by simp [logProfile,hw])

theorem logProfile_smooth (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W) :
    ContDiff ℝ ∞ (logProfile W) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x=0
  · subst x
    have he : logProfile W =ᶠ[nhds (0 : ℝ)] (fun _ => 0) := by
      filter_upwards [isOpen_Iio.mem_nhds ha] with y hy
      have hw : W y=0 := by
        by_contra hn
        exact (not_le_of_gt hy) (hs hn).1
      simp [logProfile,hw]
    exact contDiffAt_const.congr_of_eventuallyEq he
  · exact (Complex.ofRealCLM.contDiff.contDiffAt.comp x
      (Real.contDiffAt_log.mpr hx)).mul hW.contDiffAt

end SevenEighths.HeckeDetectorRowwisePolynomial

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical ComplexConjugate ContDiff
open Complex
namespace SevenEighths.HeckeInverseAmplification
open HeckeFamily

theorem conjugate_profile_support (W : ℝ→ℂ) :
    Function.support (fun x => conj (W x))=Function.support W := by
  ext x
  simp

theorem conjugate_profile_smooth (W : ℝ→ℂ) (hW : ContDiff ℝ ∞ W) :
    ContDiff ℝ ∞ (fun x => conj (W x)) := by
  exact Complex.conjCLE.contDiff.comp hW

end SevenEighths.HeckeInverseAmplification

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical Topology ContDiff
open Filter
namespace SevenEighths.CenteredMomentPrimePool
open HeckeFamily PNT.AnnularPrimeMass

def primePool (M : Ideal O) [NeZero M]
    (H : Subgroup (O ⧸ M)ˣ) (S : Finset (Ideal O)) (a b x : ℝ) : Finset (Ideal O) :=
  annularPrimeIdeals (RayQuotient.identityClass M H) a b x \ S

def eligiblePool (P : Finset (Ideal O)) (R : Ideal O) : Finset (Ideal O) :=
  P.filter (fun Q => ¬Q ∣ R)

end SevenEighths.CenteredMomentPrimePool

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
open Set Filter
namespace SevenEighths.HeckeInverseAmplification
open HeckeFamily HeckeDetectorRowwisePolynomial

def logTest (W : ℝ→ℂ) : ℕ→ℝ→ℂ
  | 0 => W
  | n+1 => logProfile (logTest W n)

theorem logTest_support (W : ℝ→ℂ) (n : ℕ) :
    Function.support (logTest W n)⊆Function.support W := by
  induction n with
  | zero => exact subset_rfl
  | succ n ih => exact (logProfile_support (logTest W n)).trans ih

theorem logTest_smooth (W : ℝ→ℂ) (n : ℕ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W) :
    ContDiff ℝ ∞ (logTest W n) := by
  induction n with
  | zero => exact hW
  | succ n ih => exact logProfile_smooth (logTest W n) a b ha ((logTest_support W n).trans hs) ih

end SevenEighths.HeckeInverseAmplification

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical ComplexConjugate
open Complex
namespace SevenEighths.HeckeDetectorCoefficientTransfer
open HeckeFamily HeckeInverseAmplification

def orientedProfile (reverse : Bool) (W : ℝ→ℂ) : ℝ→ℂ :=
  if reverse then fun x => conj (W x) else W

def orientedFrequency (reverse : Bool) (freq : ℝ) : ℝ := if reverse then -freq else freq

end SevenEighths.HeckeDetectorCoefficientTransfer

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff ComplexConjugate
open Set

namespace SevenEighths.DetectorDictionaryInverseUniform
open HeckeInverseAmplification HeckeDetectorCoefficientTransfer HeckeDetectorDyadicProfiles
open HeckeDetectorRowwisePolynomial

def baseProfile (reverse : Bool) (n : ℕ) (V W : ℝ→ℂ) (R : ℝ) : ℝ→ℂ :=
  logTest (orientedProfile reverse (ratioProfile V W R)) n

lemma baseProfile_support (reverse : Bool) (n : ℕ) (V W : ℝ→ℂ) (R : ℝ) :
    Function.support (baseProfile reverse n V W R)⊆Function.support W := by
  apply (logTest_support _ _).trans
  cases reverse
  · exact ratioProfile_support V W R
  · rw [orientedProfile,if_pos rfl,conjugate_profile_support]
    exact ratioProfile_support V W R

lemma baseProfile_smooth (reverse : Bool) (n : ℕ) (V W : ℝ→ℂ) (R a b : ℝ)
    (ha : 0<a) (hV : ContDiff ℝ ∞ V) (hW : ContDiff ℝ ∞ W)
    (hs : Function.support W⊆Icc a b) : ContDiff ℝ ∞ (baseProfile reverse n V W R) := by
  apply logTest_smooth _ n a b ha
  · cases reverse
    · exact (ratioProfile_support V W R).trans hs
    · rw [orientedProfile,if_pos rfl,conjugate_profile_support]
      exact (ratioProfile_support V W R).trans hs
  · have hv : ContDiff ℝ ∞ (ratioProfile V W R) :=
      (hV.comp (by fun_prop)).mul hW
    cases reverse
    · exact hv
    · exact conjugate_profile_smooth _ hv

def inverseLogFamily (reverse : Bool) (n : ℕ) (V W : ℝ→ℂ) (p : ℝ×ℝ) (x : ℝ) : ℂ :=
  Real.exp (-p.1*x) • ((x:ℂ)^n*
    (orientedProfile reverse V (p.2*Real.exp x)*orientedProfile reverse W (Real.exp x)))

end SevenEighths.DetectorDictionaryInverseUniform

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyAmplifierFamilyAdmission
open HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT ActualEisensteinCubic
open CenteredMomentFirstSourceConductorCaps CenteredMomentAmplificationRadicalFamily
open CenteredMomentAmplificationActiveFactor
open CenteredMomentFirstPhysicalSource CenteredMomentSecondHeightFamily
local notation "O"=>HeckeFamily.O

local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _
def referenceCost : ℝ := max 1 rayCost

end SevenEighths.CenteredMomentEnergyAmplifierFamilyAdmission

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
open ProbeRaySlots
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

omit [NeZero M] in
theorem floorPoolOutside (S : Finset (Ideal O)) (N : ℕ) (c b : ℝ) (Y : Fin N→ℝ) :
    ∀j P,P∈pool (RayQuotient.identityClass M H) S c b (Y j) → P.val∉S :=
  fun j P hP=>(mem_pool _ S c b (Y j) P).mp hP |>.2.2.2

end SevenEighths.ProbeHighRowFamily

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
open ProbeRaySlots
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

omit [NeZero M] in
theorem globalFloorPoolOutside (S : Finset (Ideal O)) (N : ℕ) (c b : ℝ) (Y : Fin N→ℝ) :
    ∀j P,P∈pool (RayQuotient.identityClass M H) S c b (Y j) → P.val∉S :=
  fun j P hP=>(mem_pool _ S c b (Y j) P).mp hP |>.2.2.2

end SevenEighths.ProbeHighRowFamily

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
open ProbeRaySlots
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

omit [NeZero M] in
theorem globalFloorIntegralPoolOutside (S : Finset (Ideal O)) (N : ℕ) (c b : ℝ) (Y : Fin N→ℝ) :
    ∀j P,P∈pool (RayQuotient.identityClass M H) S c b (Y j) → P.val∉S :=
  fun j P hP=>(mem_pool _ S c b (Y j) P).mp hP |>.2.2.2

end SevenEighths.ProbeHighRowFamily

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
open ProbeRaySlots
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

omit [NeZero M] in
theorem normalizedFloorPoolOutside (S : Finset (Ideal O)) (N : ℕ) (c b : ℝ) (Y : Fin N→ℝ) :
    ∀j P,P∈pool (RayQuotient.identityClass M H) S c b (Y j) → P.val∉S :=
  fun j P hP=>(mem_pool _ S c b (Y j) P).mp hP |>.2.2.2

end SevenEighths.ProbeHighRowFamily

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
open ProbeRaySlots
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

omit [NeZero M] in
theorem savingFloorPoolOutside (S : Finset (Ideal O)) (N : ℕ) (c b : ℝ) (Y : Fin N→ℝ) :
    ∀j P,P∈pool (RayQuotient.identityClass M H) S c b (Y j) → P.val∉S :=
  fun j P hP=>(mem_pool _ S c b (Y j) P).mp hP |>.2.2.2

end SevenEighths.ProbeHighRowFamily

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
open ProbeRaySlots
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

omit [NeZero M] in
theorem collectedFloorPoolOutside (S : Finset (Ideal O)) (N : ℕ) (c b : ℝ) (Y : Fin N→ℝ) :
    ∀j P,P∈pool (RayQuotient.identityClass M H) S c b (Y j) → P.val∉S :=
  fun j P hP=>(mem_pool _ S c b (Y j) P).mp hP |>.2.2.2

end SevenEighths.ProbeHighRowFamily

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
open ProbeRaySlots
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
omit [NeZero M] in
lemma nonfloorPoolOutside (S : Finset (Ideal O)) (N : ℕ) (c b : ℝ) (Y : Fin N→ℝ) :
    ∀j P,P∈pool (RayQuotient.identityClass M H) S c b (Y j) → P.val∉S :=
  fun j P hP=>(mem_pool _ S c b (Y j) P).mp hP |>.2.2.2

end SevenEighths.ProbeHighRowFamily

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary CompletedGauss
open ProbeRaySlots ProbePrincipalResidueActual
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

omit [NeZero M] in
theorem transportPoolOutside (S : Finset (Ideal O)) (K : ℕ) (a b : ℝ) (Y : Fin K→ℝ) :
    ∀j P,P∈pool (RayQuotient.identityClass M H) S a b (Y j) → P.val∉S :=
  fun j P hP=>(mem_pool _ S a b (Y j) P).mp hP |>.2.2.2

end SevenEighths.ProbeHighRowFamily

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary CompletedGauss
open ProbeRaySlots ProbePrincipalResidueActual
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

omit [NeZero M] in
theorem transportSavingPoolOutside (S : Finset (Ideal O)) (K : ℕ) (a b : ℝ) (Y : Fin K→ℝ) :
    ∀j P,P∈pool (RayQuotient.identityClass M H) S a b (Y j) → P.val∉S :=
  fun j P hP=>(mem_pool _ S a b (Y j) P).mp hP |>.2.2.2

end SevenEighths.ProbeHighRowFamily

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary CompletedGauss
open ProbeRaySlots ProbePrincipalResidueActual
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

omit [NeZero M] in
theorem nonfloorTransportPoolOutside (S : Finset (Ideal O)) (K : ℕ) (a b : ℝ) (Y : Fin K→ℝ) :
    ∀j P,P∈pool (RayQuotient.identityClass M H) S a b (Y j) → P.val∉S :=
  fun j P hP=>(mem_pool _ S a b (Y j) P).mp hP |>.2.2.2

end SevenEighths.ProbeHighRowFamily

end

end OAI
end


