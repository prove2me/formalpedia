-- Prove2me | Definitions.Def_CoveringDensity
-- name    : CoveringDensity
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:06.013409+00:00
-- url     : https://prove2.me/theorems/3ba488f1-2eb6-4461-b06a-8b7a8e02bdfe
-- statement:
--   For each nonnegative integer n, the ambient space is n-dimensional real Euclidean space. A lattice covering of a set K consists of a discrete, full-rank integer lattice L such that every point y satisfies y−ℓ ∈ K for some ℓ ∈ L. Euclidean volume is defined by transporting product Lebesgue measure to this space; the lattice covering density is volume(K) divided by the covolume of L, and θL(K) is the infimum of this density over all lattice coverings. A set X of translation centers is locally finite when its intersection with every bounded set is finite, and it covers by K when every y belongs to K+x for some x ∈ X. Its upper center intensity is limsup as R → ∞ of #(X ∩ [−R,R]ⁿ)/(2R)ⁿ. The translative covering density θT(K) is the infimum of volume(K) times this intensity over all locally finite covering center sets. A convex body is a compact convex set with nonempty interior; it is centrally symmetric if reflection x ↦ 2z−x preserves membership for some center z. Four extremal quantities are defined by taking the supremum of θT or θL over all convex bodies or over centrally symmetric convex bodies. All densities and extrema take values in the extended nonnegative reals. OptimalOrder is the defined proposition that there exist absolute positive real constants c and C and a natural threshold n₀ such that, for every n ≥ n₀, each of these four extrema lies between cn log n and Cn log n, with these real bounds embedded into the extended nonnegative reals by truncating negative values to zero. In particular, the asserted upper bounds require the extrema to be finite.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/CoveringDensity.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/CoveringDensity.lean; bytes 16..4134
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

namespace CoveringOrder
open Set MeasureTheory
open scoped ENNReal

abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- Actual discrete full-rank lattice coverings; no assumed density theorem. -/
structure LatticeCover {n : ℕ} (K : Set (Space n)) where
  lattice : Submodule ℤ (Space n)
  discrete : DiscreteTopology lattice
  fullrank : IsZLattice ℝ lattice
  covers : ∀ y, ∃ l : lattice, y - l.val ∈ K

noncomputable def euclideanVolume (n : ℕ) :
    @Measure (EuclideanSpace ℝ (Fin n))
      (@WithLp.measurableSpace 2 (Fin n → ℝ)
        (@MeasurableSpace.pi (Fin n) (fun _ => ℝ) (fun _ => Real.measurableSpace))) :=
  @Measure.map (Fin n → ℝ) (EuclideanSpace ℝ (Fin n))
    (@MeasurableSpace.pi (Fin n) (fun _ => ℝ) (fun _ => Real.measurableSpace))
    (@WithLp.measurableSpace 2 (Fin n → ℝ)
      (@MeasurableSpace.pi (Fin n) (fun _ => ℝ) (fun _ => Real.measurableSpace)))
    (@WithLp.toLp 2 (Fin n → ℝ))
    (Measure.pi (fun _ : Fin n => @volume ℝ Real.measureSpace))

noncomputable def euclideanCovolume {n : ℕ}
    (lattice : Submodule ℤ (EuclideanSpace ℝ (Fin n))) : ℝ≥0∞ :=
  addCovolume lattice (EuclideanSpace ℝ (Fin n)) (euclideanVolume n)

noncomputable def latticeDensity {n : ℕ} {K : Set (Space n)}
    (cover : LatticeCover K) : ℝ≥0∞ :=
  euclideanVolume n K / euclideanCovolume cover.lattice

noncomputable def thetaL {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) : ℝ≥0∞ :=
  ⨅ cover : LatticeCover K, latticeDensity cover

end CoveringOrder

namespace TranslativeCovering

open Set Filter MeasureTheory
open scoped ENNReal

abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n)

def cube (n : ℕ) (R : ℝ) : Set (Space n) :=
  {x | ∀ i, -R ≤ x i ∧ x i ≤ R}

def LocallyFiniteCenters {n : ℕ} (X : Set (Space n)) : Prop :=
  ∀ B : Set (Space n), Bornology.IsBounded B → (X ∩ B).Finite

def Covers {n : ℕ} (K X : Set (Space n)) : Prop :=
  ∀ y, ∃ x ∈ X, y - x ∈ K

def ConvexBody {n : ℕ} (K : Set (Space n)) : Prop :=
  IsCompact K ∧ Convex ℝ K ∧ (interior K).Nonempty

def CentrallySymmetric {n : ℕ} (K : Set (Space n)) : Prop :=
  ∃ z, ∀ x, x ∈ K ↔ (2 : ℝ) • z - x ∈ K

noncomputable def upperCenterIntensity {n : ℕ} (X : Set (Space n)) : ℝ≥0∞ :=
  Filter.limsup (fun R : ℝ =>
    (↑(X ∩ cube n R).ncard : ℝ≥0∞) / ENNReal.ofReal ((2 * R) ^ n)) atTop

noncomputable def thetaT {n : ℕ} (K : Set (Space n)) : ℝ≥0∞ :=
  ⨅ X : {X : Set (Space n) // LocallyFiniteCenters X ∧ Covers K X},
    volume K * upperCenterIntensity X.val

end TranslativeCovering

namespace CoveringOrder
open Set MeasureTheory
open scoped ENNReal

abbrev Body (n : ℕ) := {K : Set (Space n) // TranslativeCovering.ConvexBody K}
abbrev SymmetricBody (n : ℕ) :=
  {K : Body n // TranslativeCovering.CentrallySymmetric K.val}

noncomputable def translativeSup (n : ℕ) : ℝ≥0∞ :=
  ⨆ K : Body n, TranslativeCovering.thetaT K.val

noncomputable def symmetricTranslativeSup (n : ℕ) : ℝ≥0∞ :=
  ⨆ K : SymmetricBody n, TranslativeCovering.thetaT K.val.val

noncomputable def latticeSup (n : ℕ) : ℝ≥0∞ :=
  ⨆ K : Body n, thetaL K.val

noncomputable def symmetricLatticeSup (n : ℕ) : ℝ≥0∞ :=
  ⨆ K : SymmetricBody n, thetaL K.val.val

/-- The finite real comparison scale, viewed in extended nonnegative reals. -/
def orderBounds (c C : ℝ) (n : ℕ) (a : ℝ≥0∞) : Prop :=
  ENNReal.ofReal (c * (n : ℝ) * Real.log (n : ℝ)) ≤ a ∧
    a ≤ ENNReal.ofReal (C * (n : ℝ) * Real.log (n : ℝ))

/-- All four extremal quantities have common
absolute positive comparison constants. ENNReal bounds imply finiteness rather
than mapping a potentially infinite density to zero through `toReal`. -/
def OptimalOrder : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
    orderBounds c C n (translativeSup n) ∧
    orderBounds c C n (symmetricTranslativeSup n) ∧
    orderBounds c C n (latticeSup n) ∧
    orderBounds c C n (symmetricLatticeSup n)

end CoveringOrder



end OAI


