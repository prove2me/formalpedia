-- Prove2me | Definitions.Def_SmoothObstruction
-- name    : SmoothObstruction
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:33:23.016336+00:00
-- url     : https://prove2.me/theorems/e72ce3ab-959c-4059-828d-a98c20b512d9
-- statement:
--   entropyTerm(p) is the Shannon entropy contribution −p·log p / log 2 of a mass p, in bits, equal to zero at p=0. For a measure μ, a map T and a partition P with labels in Fin q, blockEntropy(μ,T,P,n) is the sum, over all label words w of length n, of entropyTerm applied to the μ-measure of the set of points x with P(Tʲx)=w(j) for every j<n; this is the entropy of the n-fold join of the partition. FiniteKSEntropy(μ,T) says there is one real bound C such that, for every q and every measurable partition P into q+1 labelled pieces (empty pieces allowed), the sequence blockEntropy(μ,T,P,n)/n converges to some real limit h with h ≤ C; so all finite-partition entropy rates exist and are uniformly bounded. ConullIsomorphic(μ,ν) means there are measurable sets A and B with null complements and a measurable equivalence A≃B carrying the restricted measure on A to that on B. StandardNonatomic(μ) means μ is conull-isomorphic to Lebesgue measure on [0,1]. ConullConjugate(μ,T,ν,S) means there are measurable conull sets A and B, invariant under T and S respectively (T⁻¹A=A, S⁻¹B=B), and a measure-preserving measurable equivalence e:A≃B with e(Tx)=S(e x); it is a measurable conjugacy, not a continuous one and not just a factor map. SmoothPositiveDensity(I,ν) says that on a charted manifold modelled by I over ℝᵈ, in each extended chart the pushforward of ν restricted to the chart source equals Lebesgue measure on the chart target weighted by a positive density that is C^∞ on the target (including up to the boundary for half-space charts); no orientation or volume form is assumed. HasModelWith(μ,T,I) says there exist a compact, Hausdorff, second-countable Borel manifold M, smooth with respect to I, with a probability measure ν having smooth positive density, and a C^∞ diffeomorphism S of M preserving ν, such that (μ,T) is conull-conjugate to (ν,S). HasSmoothPositiveVolumeModel(μ,T) holds when this is true for some dimension d with the model ℝᵈ (a closed manifold, d=0 allowed), or for some positive dimension d with the half-space model (a manifold with boundary); nonorientable manifolds are allowed.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/SmoothObstruction.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/SmoothObstruction.lean; bytes 16..4364
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI


open MeasureTheory Set Filter
open scoped ENNReal Topology Manifold ContDiff

namespace SmoothObstruction

/-- Shannon entropy in bits; the value at mass zero is zero. -/
noncomputable def entropyTerm (p : ℝ) : ℝ := -(p * Real.log p) / Real.log 2

/-- The entropy of the length-`n` join of the partition with labels in `Fin q`. -/
noncomputable def blockEntropy {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (T : X → X) {q : ℕ} (P : X → Fin q) (n : ℕ) : ℝ :=
  ∑ w : Fin n → Fin q,
    entropyTerm ((μ {x | ∀ j : Fin n, P ((T^[j.val]) x) = w j}).toReal)

/-- All finite-partition entropy rates exist and have one finite real upper
bound. This spells out `sup_P lim_n H(join_{j<n} T^{-j}P)/n < ∞` without
choosing a value for limits of nonconvergent sequences. Empty atoms are allowed. -/
def FiniteKSEntropy {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (T : X → X) : Prop :=
  ∃ C : ℝ, ∀ (q : ℕ) (P : X → Fin (q + 1)), Measurable P →
    ∃ h : ℝ, h ≤ C ∧
      Tendsto (fun n : ℕ => blockEntropy μ T P n / (n : ℝ)) atTop (𝓝 h)

/-- Measure-space isomorphism after removing measurable null sets. -/
def ConullIsomorphic {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) : Prop :=
  ∃ (A : Set X) (B : Set Y), MeasurableSet A ∧ MeasurableSet B ∧
    μ Aᶜ = 0 ∧ ν Bᶜ = 0 ∧
    ∃ e : A ≃ᵐ B,
      MeasurePreserving e (μ.comap (Subtype.val : A → X))
        (ν.comap (Subtype.val : B → Y))

/-- Standard nonatomic in the source's explicit modulo-null-set sense. -/
def StandardNonatomic {X : Type*} [MeasurableSpace X] (μ : Measure X) : Prop :=
  ConullIsomorphic μ
    (volume.comap (Subtype.val : Set.Icc (0 : ℝ) 1 → ℝ))

/-- Measurable conjugacy on invariant conull measurable subsets, not a
continuous conjugacy and not merely a factor map. -/
def ConullConjugate {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (T : X → X) (ν : Measure Y) (S : Y → Y) : Prop :=
  ∃ (A : Set X) (B : Set Y), MeasurableSet A ∧ MeasurableSet B ∧
    μ Aᶜ = 0 ∧ ν Bᶜ = 0 ∧ T ⁻¹' A = A ∧ S ⁻¹' B = B ∧
    ∃ e : A ≃ᵐ B,
      MeasurePreserving e (μ.comap (Subtype.val : A → X))
        (ν.comap (Subtype.val : B → Y)) ∧
      ∀ (x y : A), T x = y → (e y : Y) = S (e x)

/-- Positive smooth local coordinate densities. In a half-space chart,
`ContDiffOn` includes smoothness up to the boundary. Absolute Lebesgue density
is used; no orientation or volume form is part of the data. -/
def SmoothPositiveDensity {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [MeasurableSpace M]
    (ν : Measure M) : Prop :=
  ∀ x : M, ∃ f : EuclideanSpace ℝ (Fin d) → ℝ,
    ContDiffOn ℝ ∞ f (extChartAt I x).target ∧
    (∀ y ∈ (extChartAt I x).target, 0 < f y) ∧
    Measure.map (extChartAt I x) (ν.restrict (extChartAt I x).source) =
      (volume.withDensity (fun y => ENNReal.ofReal (f y))).restrict
        (extChartAt I x).target

/-- A smooth positive-volume model with a specified Euclidean or half-space
manifold model. All model dimensions will be quantified below. -/
def HasModelWith {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (T : X → X) {d : ℕ} {H : Type} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H) : Prop :=
  ∃ (M : Type) (_ : TopologicalSpace M) (_ : MeasurableSpace M)
      (_ : BorelSpace M) (_ : T2Space M) (_ : SecondCountableTopology M)
      (_ : CompactSpace M) (_ : ChartedSpace H M) (_ : IsManifold I ∞ M)
      (ν : Measure M) (_ : IsProbabilityMeasure ν)
      (S : Diffeomorph I I M M ∞),
    SmoothPositiveDensity I ν ∧ MeasurePreserving S ν ν ∧
      ConullConjugate μ T ν S

/-- Closed manifolds of all dimensions (including zero), and smooth manifolds
with boundary of every positive finite dimension. Nonorientable manifolds
are included: no orientability hypothesis occurs. -/
def HasSmoothPositiveVolumeModel {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (T : X → X) : Prop :=
  (∃ d : ℕ, HasModelWith μ T (𝓡 d)) ∨
    (∃ d : ℕ, ∃ _ : NeZero d, HasModelWith μ T (𝓡∂ d))



end SmoothObstruction
end OAI


