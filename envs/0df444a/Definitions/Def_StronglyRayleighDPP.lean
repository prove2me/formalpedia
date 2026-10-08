-- Prove2me | Definitions.Def_StronglyRayleighDPP
-- name    : StronglyRayleighDPP
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:33:07.983974+00:00
-- url     : https://prove2.me/theorems/9f3329cb-f069-401d-a187-5017bddab992
-- statement:
--   For a group Γ, leftTranslate(g,a) is the shifted configuration h ↦ a(g⁻¹h), and iidUnitLabels(Γ) is the infinite product of Lebesgue measure on the unit interval [0,1] over the coordinates in Γ. A probability measure μ on {0,1}-valued configurations Γ → Bool is an InvariantBinaryLaw if it is preserved by every left translation, and it HasEquivariantIIDFactor if some measurable map Phi from [0,1]-labelings of Γ to Bool-configurations commutes with left translation and pushes iidUnitLabels(Γ) forward to μ. For a finite index set F, finiteGeneratingValue(μ,z) is the generating polynomial Σₓ μ({x}) ∏_{i: x i = true} z_i over Boolean configurations x, and StronglyRayleighFinite(μ) says it is nonzero whenever every z_i has strictly positive imaginary part. For a general index set I, marginalMass gives the μ-mass of the cylinder fixing the coordinates in a finite set S to a pattern x, marginalGeneratingValue is the corresponding generating polynomial over S, and StronglyRayleighCountable(μ) requires nonvanishing for every finite S and every z with all imaginary parts positive. For finite F, the exponential tilt by a real vector h has partition function tiltPartition = Σₓ exp(Σⱼ h_j·[x_j]) μ({x}), with boolReal(true)=1 and boolReal(false)=0; tiltMean, tiltSecondMoment and tiltCovariance are the resulting first moments, pairwise moments, and covariance (second moment minus product of means), and coordinatePerturb(h,j,r) adds r to coordinate j of h. PositiveContractionFinite(K) says a complex matrix K is Hermitian and that for every complex vector c, 0 ≤ Re Σ conj(c_i)K_ij c_j ≤ Σ|c_i|²; PositiveContractionKernel is the same for a kernel on any index set, tested on all finite subsets S. IsFiniteDeterminantalLaw(μ,K) and IsDeterminantalLaw(μ,K) say that for every finite set A of indices, the probability that all coordinates in A are true equals det(K restricted to A×A). Finally, TranslationInvariantKernel(K) on a group means K(gh,gk)=K(h,k) for all g,h,k. These are definitions only, with no theorem asserted.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/StronglyRayleighDPP.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/StronglyRayleighDPP.lean; bytes 16..4970
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12
universe u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal Topology ComplexConjugate

namespace Problem336AdditiveD139

abbrev UnitLabel := Set.Icc (0 : ℝ) 1

def leftTranslate {Γ : Type u_1} {α : Type u_2} [Group Γ] (g : Γ) (a : Γ → α) : Γ → α :=
  fun h => a (g⁻¹ * h)

def iidUnitLabels (Γ : Type u_3) [MeasurableSpace Γ] : Measure (Γ → UnitLabel) :=
  Measure.infinitePi (fun _ : Γ => (volume : Measure UnitLabel))

def InvariantBinaryLaw {Γ : Type u_4} [Group Γ]
    (μ : ProbabilityMeasure (Γ → Bool)) : Prop :=
  ∀ g : Γ,
    Measure.map (leftTranslate g) (μ : Measure (Γ → Bool)) =
      (μ : Measure (Γ → Bool))

def HasEquivariantIIDFactor {Γ : Type u_5} [Group Γ] [MeasurableSpace Γ]
    (μ : ProbabilityMeasure (Γ → Bool)) : Prop :=
  ∃ Phi : (Γ → UnitLabel) → (Γ → Bool),
    Measurable Phi ∧
    (∀ (g : Γ) (u : Γ → UnitLabel),
      Phi (leftTranslate g u) = leftTranslate g (Phi u)) ∧
    Measure.map Phi (iidUnitLabels Γ) = (μ : Measure (Γ → Bool))

def finiteGeneratingValue {F : Type u_6} [Fintype F]
    (μ : ProbabilityMeasure (F → Bool)) (z : F → ℂ) : ℂ := by
  classical
  exact ∑ x : F → Bool,
    (((μ : Measure (F → Bool)) {x}).toReal : ℂ) *
      ∏ i : F, if x i = true then z i else 1

def StronglyRayleighFinite {F : Type u_7} [Fintype F]
    (μ : ProbabilityMeasure (F → Bool)) : Prop :=
  ∀ z : F → ℂ, (∀ i : F, 0 < (z i).im) → finiteGeneratingValue μ z ≠ 0

def marginalMass {I : Type u_8} (μ : ProbabilityMeasure (I → Bool))
    (S : Finset I) (x : S → Bool) : ℝ :=
  ((μ : Measure (I → Bool)) {a | ∀ i : S, a i.1 = x i}).toReal

def marginalGeneratingValue {I : Type u_9} (μ : ProbabilityMeasure (I → Bool))
    (S : Finset I) (z : S → ℂ) : ℂ := by
  classical
  exact ∑ x : S → Bool,
    (marginalMass μ S x : ℂ) *
      ∏ i : S, if x i = true then z i else 1

def StronglyRayleighCountable {I : Type u_10}
    (μ : ProbabilityMeasure (I → Bool)) : Prop :=
  ∀ S : Finset I, ∀ z : S → ℂ,
    (∀ i : S, 0 < (z i).im) → marginalGeneratingValue μ S z ≠ 0

def boolReal (b : Bool) : ℝ := if b = true then 1 else 0

def tiltPartition {F : Type u_11} [Fintype F]
    (μ : ProbabilityMeasure (F → Bool)) (h : F → ℝ) : ℝ := by
  classical
  exact ∑ x : F → Bool,
    Real.exp (∑ j : F, h j * boolReal (x j)) *
      ((μ : Measure (F → Bool)) {x}).toReal

def tiltMean {F : Type u_12} [Fintype F]
    (μ : ProbabilityMeasure (F → Bool)) (h : F → ℝ) (i : F) : ℝ := by
  classical
  exact (∑ x : F → Bool,
      Real.exp (∑ j : F, h j * boolReal (x j)) *
        ((μ : Measure (F → Bool)) {x}).toReal * boolReal (x i)) /
    tiltPartition μ h

def tiltSecondMoment {F : Type u_13} [Fintype F]
    (μ : ProbabilityMeasure (F → Bool)) (h : F → ℝ) (i j : F) : ℝ := by
  classical
  exact (∑ x : F → Bool,
      Real.exp (∑ k : F, h k * boolReal (x k)) *
        ((μ : Measure (F → Bool)) {x}).toReal *
        boolReal (x i) * boolReal (x j)) /
    tiltPartition μ h

def tiltCovariance {F : Type u_14} [Fintype F]
    (μ : ProbabilityMeasure (F → Bool)) (h : F → ℝ) (i j : F) : ℝ :=
  tiltSecondMoment μ h i j - tiltMean μ h i * tiltMean μ h j

def coordinatePerturb {F : Type u_15} (h : F → ℝ) (j : F) (r : ℝ) : F → ℝ := by
  classical
  exact fun k => h k + if k = j then r else 0

def PositiveContractionFinite {F : Type u_16} [Fintype F]
    (K : F → F → ℂ) : Prop :=
  (∀ i j, K i j = conj (K j i)) ∧
  ∀ c : F → ℂ,
    0 ≤ (∑ i : F, ∑ j : F, conj (c i) * K i j * c j).re ∧
    (∑ i : F, ∑ j : F, conj (c i) * K i j * c j).re ≤
      ∑ i : F, Complex.normSq (c i)

def IsFiniteDeterminantalLaw {F : Type u_17} [Fintype F]
    (μ : ProbabilityMeasure (F → Bool)) (K : F → F → ℂ) : Prop := by
  classical
  exact ∀ A : Finset F,
    (((μ : Measure (F → Bool)) {x | ∀ i ∈ A, x i = true}).toReal : ℂ) =
      Matrix.det (fun i j : A => K i.1 j.1)

def PositiveContractionKernel {I : Type u_18}
    (K : I → I → ℂ) : Prop :=
  (∀ i j, K i j = conj (K j i)) ∧
  ∀ (S : Finset I) (c : S → ℂ),
    0 ≤ (∑ i : S, ∑ j : S, conj (c i) * K i.1 j.1 * c j).re ∧
    (∑ i : S, ∑ j : S, conj (c i) * K i.1 j.1 * c j).re ≤
      ∑ i : S, Complex.normSq (c i)

def IsDeterminantalLaw {I : Type u_19}
    (μ : ProbabilityMeasure (I → Bool)) (K : I → I → ℂ) : Prop := by
  classical
  exact ∀ A : Finset I,
    (((μ : Measure (I → Bool)) {x | ∀ i ∈ A, x i = true}).toReal : ℂ) =
      Matrix.det (fun i j : A => K i.1 j.1)

def TranslationInvariantKernel {Γ : Type u_20} [Group Γ]
    (K : Γ → Γ → ℂ) : Prop :=
  ∀ g h k : Γ, K (g * h) (g * k) = K h k



end Problem336AdditiveD139
end
end OAI


