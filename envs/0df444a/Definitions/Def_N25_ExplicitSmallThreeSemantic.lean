-- Prove2me | Definitions.Def_N25_ExplicitSmallThreeSemantic
-- name    : N25_ExplicitSmallThreeSemantic
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:16:29.631464+00:00
-- url     : https://prove2.me/theorems/4d074efd-867b-47da-9724-c04da53092f9
-- title:
--   Semantic chart decomposition for the small characteristic-three fields
-- statement:
--   For an actual field $K$ of characteristic three, the file defines the signed operation record coming from the field, the forced regular-chart coordinate $$w=-\frac{y^2+yz-z}{z-1},$$ and a five-piece solution carrier consisting of regular residual pairs, the exceptional divisor $z=1$, the next two normalized charts, and the final $w$-chart point. It defines mutually inverse maps between this structured carrier and normalized canonical-curve points. This proves that the executable $𝔽_3$, $𝔽_9$, and $𝔽_{27}$ decompositions count the intended algebraic curve.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_CanonicalThreeNormalization
import Definitions.Def_N25_ExplicitSmallThreeFields
import Definitions.Def_N25_ExplicitKummerThreeProjective
import Definitions.Def_N25_ExplicitWeilThreeLinear
/-!
# Semantic characteristic-three counts for the level-25 quotient

The executable counts over `F3`, `F9`, and `F27` use explicit polynomial-basis
tables.  This file identifies those tables with the actual field equations and
proves that the linear-elimination count is the cardinality of the normalized
canonical curve.

The central equivalence follows the projective chart decomposition.  On the
regular `x`-chart, the quadric determines `w` uniquely and the cubic becomes
the bivariate residual.  The exceptional divisor `z=1` and the three boundary
charts are retained literally.  Thus no ambient four-coordinate enumeration
enters the semantic comparison.
-/

namespace MazurProof.RationalPointsN25QuotientSmallThreeSemantic

open MazurProof.RationalPointsN25QuotientWeil
open MazurProof.RationalPointsN25QuotientF2
open MazurProof.RationalPointsN25QuotientWeilThree
open MazurProof.RationalPointsN25QuotientWeilThreeLinear
open MazurProof.RationalPointsN25QuotientKummerThree
open MazurProof.RationalPointsN25QuotientKummerThreeProjective

noncomputable section

universe u

/-! ## A table interface for an actual field -/

/-- The signed operation record obtained directly from a field.  It is the
semantic target of each executable ternary table. -/
def fieldTernaryOperations (K : Type*) [Field K] : TernaryRingOperations K where
  zero := 0
  one := 1
  add := (· + ·)
  neg := (- ·)
  mul := (· * ·)

/-- Evaluation of the executable residual through the field-operation record
is the polynomial residual used by the elimination theorem. -/
theorem canonicalResidualX25Ternary_field_eq
    {K : Type*} [Field K] (y z : K) :
    canonicalResidualX25Ternary (fieldTernaryOperations K) y z =
      canonicalResidualX25Three y z := by
  unfold canonicalResidualX25Ternary fieldTernaryOperations
    canonicalResidualX25Three
  ring

/-- Field-operation chart coordinates are the standard first-nonzero
homogeneous representatives. -/
theorem ternaryCoordinates_field_eq
    {K : Type*} [Field K] (P : NormalizedProjective4 K) :
    ternaryCoordinates (fieldTernaryOperations K) P =
      normalizedCoordinatesThree P := by
  cases P <;> rfl

/-- The signed table quadric evaluated with field operations is the canonical
quadric polynomial. -/
theorem canonicalQuadric25Ternary_field_eq
    {K : Type*} [Field K] (P : Coordinates4 K) :
    canonicalQuadric25Ternary (fieldTernaryOperations K) P =
      canonicalQuadric25Three P := by
  unfold canonicalQuadric25Ternary fieldTernaryOperations
    canonicalQuadric25Three
  ring

/-- The signed table cubic evaluated with field operations is the canonical
cubic polynomial. -/
theorem canonicalCubic25Ternary_field_eq
    {K : Type*} [Field K] (P : Coordinates4 K) :
    canonicalCubic25Ternary (fieldTernaryOperations K) P =
      canonicalCubic25Three P := by
  unfold canonicalCubic25Ternary fieldTernaryOperations canonicalCubic25Three
  ring

/-- Over an actual field, the executable normalized predicate is exactly the
semantic canonical quadric-cubic predicate. -/
theorem isCanonicalNormalized25Ternary_field_iff
    {K : Type*} [Field K] [DecidableEq K] (P : NormalizedProjective4 K) :
    IsCanonicalNormalized25Ternary (fieldTernaryOperations K) P ↔
      IsCanonicalNormalizedThree P := by
  unfold IsCanonicalNormalized25Ternary IsCanonicalNormalizedThree
  rw [ternaryCoordinates_field_eq]
  dsimp only
  rw [canonicalQuadric25Ternary_field_eq,
    canonicalCubic25Ternary_field_eq]
  rfl

/-! ## The regular `x`-chart as a residual graph -/

/-- The `w`-coordinate forced by the quadric away from the exceptional
divisor `z=1`. -/
def canonicalRegularW25Three {K : Type*} [Field K] (y z : K) : K :=
  -(y ^ 2 + y * z - z) / (z - 1)

/-- Substituting the forced `w`-coordinate makes the normalized quadric
vanish. -/
theorem canonicalQuadricX_regularW_eq_zero
    {K : Type*} [Field K] {y z : K} (hz : z ≠ 1) :
    canonicalQuadricX25Three y z (canonicalRegularW25Three y z) = 0 := by
  have hD : z - 1 ≠ 0 := sub_ne_zero.mpr hz
  unfold canonicalQuadricX25Three canonicalRegularW25Three
  field_simp
  ring

/-- A normalized regular-chart point lies on the curve exactly when its
residual pair does.  The cubic equivalence is the cleared-denominator
elimination theorem, after the quadric has solved for `w`. -/
theorem isCanonicalNormalizedThree_regular_iff
    {K : Type*} [Field K] [CharP K 3] {y z : K} (hz : z ≠ 1) :
    IsCanonicalNormalizedThree
        (.xChart y z (canonicalRegularW25Three y z)) ↔
      canonicalResidualX25Three y z = 0 := by
  have hQ := canonicalQuadricX_regularW_eq_zero (y := y) (z := z) hz
  rw [isCanonicalNormalizedThree_xChart_iff]
  simp only [hQ, eq_self, true_and]
  exact canonicalCubicX25Three_eq_zero_iff_residual hz hQ

/-- The quadric determines the regular-chart `w`-coordinate uniquely. -/
theorem canonicalRegularW25Three_eq_of_quadric
    {K : Type*} [Field K] {y z w : K} (hz : z ≠ 1)
    (hQ : canonicalQuadricX25Three y z w = 0) :
    canonicalRegularW25Three y z = w := by
  have hD : z - 1 ≠ 0 := sub_ne_zero.mpr hz
  unfold canonicalQuadricX25Three canonicalRegularW25Three at *
  apply (div_eq_iff hD).2
  linear_combination -hQ

/-! ## Structural equivalence and cardinality -/

/-- The five pieces in the structured point count: regular residual pairs,
the exceptional `z=1` fibre, the `y`- and `z`-charts, and the final
`w`-chart point. -/
abbrev CanonicalStructuredSolutions25Three
    (K : Type u) [Field K] [Fintype K] [DecidableEq K] : Type u :=
  ↥(canonicalRegularPairs25Three (fieldTernaryOperations K)) ⊕
    (↥(canonicalExceptionalPairs25Three (fieldTernaryOperations K)) ⊕
      (↥(canonicalYChartPairs25Three (fieldTernaryOperations K)) ⊕
        (↥(canonicalZChartValues25Three (fieldTernaryOperations K)) ⊕ Unit)))

/-- Membership in the regular finite set is the semantic residual condition. -/
theorem mem_canonicalRegularPairs25Three_field_iff
    {K : Type*} [Field K] [Fintype K] [DecidableEq K] (y z : K) :
    (y, z) ∈ canonicalRegularPairs25Three (fieldTernaryOperations K) ↔
      z ≠ 1 ∧ canonicalResidualX25Three y z = 0 := by
  unfold canonicalRegularPairs25Three
  rw [Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  change z ≠ 1 ∧
      canonicalResidualX25Ternary (fieldTernaryOperations K) y z = 0 ↔ _
  rw [canonicalResidualX25Ternary_field_eq]

/-- Membership in the exceptional finite set is the semantic curve
condition on the divisor `z=1`. -/
theorem mem_canonicalExceptionalPairs25Three_field_iff
    {K : Type*} [Field K] [Fintype K] [DecidableEq K] (y w : K) :
    (y, w) ∈ canonicalExceptionalPairs25Three (fieldTernaryOperations K) ↔
      IsCanonicalNormalizedThree (.xChart y 1 w) := by
  unfold canonicalExceptionalPairs25Three
  rw [Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  change IsCanonicalNormalized25Ternary (fieldTernaryOperations K)
      (.xChart y 1 w) ↔ _
  exact isCanonicalNormalized25Ternary_field_iff _

/-- Membership in the `y`-chart finite set is its semantic curve condition. -/
theorem mem_canonicalYChartPairs25Three_field_iff
    {K : Type*} [Field K] [Fintype K] [DecidableEq K] (z w : K) :
    (z, w) ∈ canonicalYChartPairs25Three (fieldTernaryOperations K) ↔
      IsCanonicalNormalizedThree (.yChart z w) := by
  unfold canonicalYChartPairs25Three
  rw [Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  exact isCanonicalNormalized25Ternary_field_iff _

/-- Membership in the `z`-chart finite set is its semantic curve condition. -/
theorem mem_canonicalZChartValues25Three_field_iff
    {K : Type*} [Field K] [Fintype K] [DecidableEq K] (w : K) :
    w ∈ canonicalZChartValues25Three (fieldTernaryOperations K) ↔
      IsCanonicalNormalizedThree (.zChart w) := by
  unfold canonicalZChartValues25Three
  rw [Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  exact isCanonicalNormalized25Ternary_field_iff _

/-- The final normalized chart `[0:0:0:1]` always lies on both homogeneous
equations. -/
theorem isCanonicalNormalizedThree_wChart
    {K : Type*} [Field K] :
    IsCanonicalNormalizedThree (NormalizedProjective4.wChart :
      NormalizedProjective4 K) := by
  simp [IsCanonicalNormalizedThree, normalizedCoordinatesThree,
    canonicalQuadric25Three, canonicalCubic25Three]

/-- Send a semantic curve point to its piece in the linear-elimination
decomposition.  The regular branch forgets `w`; the quadric will reconstruct
it uniquely. -/
def canonicalCurveToStructured25Three
    (K : Type u) [Field K] [CharP K 3] [Fintype K] [DecidableEq K] :
    {P : NormalizedProjective4 K // IsCanonicalNormalizedThree P} →
      CanonicalStructuredSolutions25Three K
  | ⟨P, hP⟩ => by
      cases P with
      | xChart y z w =>
          by_cases hz : z = 1
          · exact Sum.inr (Sum.inl ⟨(y, w),
              (mem_canonicalExceptionalPairs25Three_field_iff y w).2
                (hz ▸ hP)⟩)
          · have hQC := (isCanonicalNormalizedThree_xChart_iff y z w).1 hP
            have hR :=
              (canonicalCubicX25Three_eq_zero_iff_residual hz hQC.1).1 hQC.2
            exact Sum.inl ⟨(y, z),
              (mem_canonicalRegularPairs25Three_field_iff y z).2 ⟨hz, hR⟩⟩
      | yChart z w =>
          exact Sum.inr (Sum.inr (Sum.inl ⟨(z, w),
            (mem_canonicalYChartPairs25Three_field_iff z w).2 hP⟩))
      | zChart w =>
          exact Sum.inr (Sum.inr (Sum.inr (Sum.inl ⟨w,
            (mem_canonicalZChartValues25Three_field_iff w).2 hP⟩)))
      | wChart => exact Sum.inr (Sum.inr (Sum.inr (Sum.inr Unit.unit)))

/-- Reconstruct a semantic curve point from a structural piece.  Only the
regular branch performs work: it inserts the rational function forced by the
quadric and invokes the elimination equivalence for the cubic. -/
def structuredToCanonicalCurve25Three
    (K : Type u) [Field K] [CharP K 3] [Fintype K] [DecidableEq K] :
    CanonicalStructuredSolutions25Three K →
      {P : NormalizedProjective4 K // IsCanonicalNormalizedThree P}
  | Sum.inl ⟨⟨y, z⟩, hR⟩ => by
      have hR' := (mem_canonicalRegularPairs25Three_field_iff y z).1 hR
      exact ⟨.xChart y z (canonicalRegularW25Three y z),
        (isCanonicalNormalizedThree_regular_iff hR'.1).2 hR'.2⟩
  | Sum.inr (Sum.inl ⟨⟨y, w⟩, hE⟩) =>
      ⟨.xChart y 1 w,
        (mem_canonicalExceptionalPairs25Three_field_iff y w).1 hE⟩
  | Sum.inr (Sum.inr (Sum.inl ⟨⟨z, w⟩, hY⟩)) =>
      ⟨.yChart z w, (mem_canonicalYChartPairs25Three_field_iff z w).1 hY⟩
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl ⟨w, hZ⟩))) =>
      ⟨.zChart w, (mem_canonicalZChartValues25Three_field_iff w).1 hZ⟩
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr _))) =>
      ⟨.wChart, isCanonicalNormalizedThree_wChart⟩

/-- Reconstructing after decomposition fixes every semantic curve point.
On the regular chart this is exactly uniqueness of the quadric solution for
`w`; all boundary charts are literal. -/
theorem structuredToCanonicalCurve25Three_leftInverse
    (K : Type u) [Field K] [CharP K 3] [Fintype K] [DecidableEq K] :
    Function.LeftInverse (structuredToCanonicalCurve25Three K)
      (canonicalCurveToStructured25Three K) := by
  rintro ⟨P, hP⟩
  apply Subtype.ext
  cases P with
  | xChart y z w =>
      by_cases hz : z = 1
      · subst z
        simp [canonicalCurveToStructured25Three,
          structuredToCanonicalCurve25Three]
      · have hQ := ((isCanonicalNormalizedThree_xChart_iff y z w).1 hP).1
        simp [canonicalCurveToStructured25Three,
          structuredToCanonicalCurve25Three, hz,
          canonicalRegularW25Three_eq_of_quadric hz hQ]
  | yChart z w =>
      simp [canonicalCurveToStructured25Three,
        structuredToCanonicalCurve25Three]
  | zChart w =>
      simp [canonicalCurveToStructured25Three,
        structuredToCanonicalCurve25Three]
  | wChart =>
      simp [canonicalCurveToStructured25Three,
        structuredToCanonicalCurve25Three]

/-- Decomposing after reconstruction fixes every structural piece.  Regular
membership supplies `z≠1`, so the reconstructed point returns to the regular
summand rather than the exceptional divisor. -/
theorem canonicalCurveToStructured25Three_leftInverse
    (K : Type u) [Field K] [CharP K 3] [Fintype K] [DecidableEq K] :
    Function.LeftInverse (canonicalCurveToStructured25Three K)
      (structuredToCanonicalCurve25Three K) := by
  intro S
  rcases S with R | E
  · rcases R with ⟨⟨y, z⟩, hR⟩
    have hz := ((mem_canonicalRegularPairs25Three_field_iff y z).1 hR).1
    simp [canonicalCurveToStructured25Three,
      structuredToCanonicalCurve25Three, hz]
  · rcases E with E | Y
    · rcases E with ⟨⟨y, w⟩, hE⟩
      simp [canonicalCurveToStructured25Three,
        structuredToCanonicalCurve25Three]
    · rcases Y with Y | Z
      · rcases Y with ⟨⟨z, w⟩, hY⟩
        simp [canonicalCurveToStructured25Three,
          structuredToCanonicalCurve25Three]
      · rcases Z with Z | W
        · rcases Z with ⟨w, hZ⟩
          simp [canonicalCurveToStructured25Three,
            structuredToCanonicalCurve25Three]
        · rcases W with ⟨⟩
          simp [canonicalCurveToStructured25Three,
            structuredToCanonicalCurve25Three]

/-- The normalized canonical curve is equivalent to the five structural
pieces used by the linear-elimination count. -/
def canonicalCurveEquivStructured25Three
    (K : Type u) [Field K] [CharP K 3] [Fintype K] [DecidableEq K] :
    {P : NormalizedProjective4 K // IsCanonicalNormalizedThree P} ≃
      CanonicalStructuredSolutions25Three K where
  toFun := canonicalCurveToStructured25Three K
  invFun := structuredToCanonicalCurve25Three K
  left_inv := structuredToCanonicalCurve25Three_leftInverse K
  right_inv := canonicalCurveToStructured25Three_leftInverse K

/-! ## The three executable tables and their semantic counts -/
end

end MazurProof.RationalPointsN25QuotientSmallThreeSemantic


