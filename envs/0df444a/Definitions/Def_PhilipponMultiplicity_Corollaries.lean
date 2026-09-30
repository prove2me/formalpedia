-- Prove2me | Definitions.Def_PhilipponMultiplicity_Corollaries
-- name    : PhilipponMultiplicity_Corollaries
-- status  : Definition
-- author  : @tomasz
-- created : 2026-09-23T20:18:55.386341+00:00
-- url     : https://prove2.me/theorems/04f71018-a3ae-469f-8f92-ae18e5ee4de3
-- title:
--   Mixed indices, disjoint factors, sampling grids and minima
-- statement:
--   Actual mixed-codimension indices, factor projections, the disjoint-factor condition, real-bound integer sampling grids, quotient ranks, and infima over obstruction subgroups. Empty infima are zero; the source audit records the trivial analytic-subgroup boundary.
--
--   Compiled, admission-free definition bundle. Theorems asserting its substantive properties remain open targets in the full-paper goal.
-- source:
--   Philippon 1986, §§2–5; 1987 corrections/addenda. https://numdam.org/articles/10.24033/bsmf.2060/

import Definitions.Def_PhilipponMultiplicity_Analytic
import Definitions.Def_PhilipponMultiplicity_Degree

set_option autoImplicit false
open scoped BigOperators
noncomputable section

namespace PhilipponMultiplicity

universe u
variable {K : Type u} [NontriviallyNormedField K]

structure SourceMixedCodimensionIndex (G : EmbeddedGroupProduct K)
    (H : AlgebraicSubgroup G) where
  exponent : G.FactorIndex → ℕ
  bounded : ∀ i, exponent i ≤ (G.factor i).dimension
  sum_eq : (∑ i, exponent i) + varietyDimension G H.carrier = G.dimension

def SourceMixedCodimensionIndex.complementIndex {G : EmbeddedGroupProduct K}
    {H : AlgebraicSubgroup G} (r : SourceMixedCodimensionIndex G H) : G.FactorIndex → ℕ :=
  fun i => (G.factor i).dimension - r.exponent i

def SourceMixedCodimensionIndex.degreeMonomial {G : EmbeddedGroupProduct K}
    {H : AlgebraicSubgroup G} (r : SourceMixedCodimensionIndex G H)
    (D : G.FactorIndex → ℕ) : ℝ :=
  ∏ i, (D i : ℝ) ^ r.exponent i

def factorProjection (G : EmbeddedGroupProduct K) (H : AlgebraicSubgroup G)
    (i : G.FactorIndex) : Set (G.factor i).Point :=
  (fun x : G.Point => x i) '' H.carrier

def factorTopology (E : EmbeddedCommutativeGroup K) : TopologicalSpace E.Point :=
  TopologicalSpace.induced (fun x _ => x.val) (projectiveSpace K E.ambientDimension).zariskiTopology

/-- Every algebraic subgroup is a product of algebraic subgroups of the factors. -/
def HasDisjointFactors (G : EmbeddedGroupProduct K) : Prop :=
  ∀ H : AlgebraicSubgroup G,
    (∀ x : G.Point, x ∈ H.carrier ↔ ∀ i, x i ∈ factorProjection G H i) ∧
    (∀ i, @IsClosed _ (factorTopology (G.factor i)) (factorProjection G H i))

def factorCodimension (G : EmbeddedGroupProduct K) (H : AlgebraicSubgroup G)
    (i : G.FactorIndex) : ℕ :=
  (G.factor i).dimension -
    (Hilbert.hilbertPolynomial K 1 (fun _ => (G.factor i).ambientDimension)
      ((projectiveSpace K (G.factor i).ambientDimension).vanishingIdeal
        ((fun x : (G.factor i).Point => fun _ => x.val) '' factorProjection G H i))).totalDegree

def samplingGrid {G : EmbeddedGroupProduct K} {l : ℕ}
    (γ : Fin l → G.Point) (S : ℝ) : Set G.Point :=
  {x | ∃ a : Fin l → ℕ, (∀ i, (a i : ℝ) ≤ S) ∧ x = ∑ i, a i • γ i}

def samplingQuotientRank {G : EmbeddedGroupProduct K} {l : ℕ}
    (γ : Fin l → G.Point) (H : AlgebraicSubgroup G) : ℕ :=
  Module.finrank ℤ (Submodule.span ℤ
    (Set.range (fun i => QuotientAddGroup.mk' H.toAddSubgroup (γ i))))

def IsCorollary23Obstruction {G : EmbeddedGroupProduct K} (A : AnalyticSubgroup G)
    (r : G.FactorIndex → ℕ) (H : AlgebraicSubgroup G) : Prop :=
  (¬ A.carrier ⊆ H.carrier) ∧ ∀ i, r i ≤ factorCodimension G H i

/-- The source minimum, using the natural-number infimum (zero on an empty
family). Nonempty-family and zero-dimensional-image cases need separate audit. -/
def analyticCodimensionMinimum {G : EmbeddedGroupProduct K} (A : AnalyticSubgroup G)
    (r : G.FactorIndex → ℕ) : ℕ :=
  sInf {k | ∃ H : AlgebraicSubgroup G,
    IsCorollary23Obstruction A r H ∧ k = analyticCodimension A H.carrier}

def samplingRankMinimum {G : EmbeddedGroupProduct K} (A : AnalyticSubgroup G)
    {l : ℕ} (γ : Fin l → G.Point) (r : G.FactorIndex → ℕ) : ℕ :=
  sInf {k | ∃ H : AlgebraicSubgroup G,
    IsCorollary23Obstruction A r H ∧ k = samplingQuotientRank γ H}

end PhilipponMultiplicity


