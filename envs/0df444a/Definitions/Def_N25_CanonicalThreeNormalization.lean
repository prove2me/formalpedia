-- Prove2me | Definitions.Def_N25_CanonicalThreeNormalization
-- name    : N25_CanonicalThreeNormalization
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:05:43.465207+00:00
-- url     : https://prove2.me/theorems/e8ff8ff5-fea2-40d0-8b0a-8a16a39511a0
-- title:
--   Characteristic-three elimination and normalization on the canonical curve
-- statement:
--   This certificate module records the characteristic-$3$ elimination identity $$(z-1)^2C=AQ-R,$$ where $Q$ and $C$ are the normalized canonical equations and $R$ is the bivariate residual. It also packages the equivalence between $C=0$ and $R=0$ when $z≠1$, the affine equations on the normalized $x$-chart, and the nonzero rescaling used for projective normalization. These objects reduce point enumeration in characteristic $3$ to a controlled residual count.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_CanonicalChartJacobian
/-! Characteristic-three normalization of canonical points: the linear elimination identity, the
normalized x-chart equations and the rescaling property of `normalizeCoordinatesThree`. The explicit
characteristic-three point enumerations use these lemmas inside their definitions. -/

namespace MazurProof.RationalPointsN25QuotientWeilThreeLinear

open MazurProof.RationalPointsN25QuotientF2
open MazurProof.RationalPointsN25QuotientWeil

variable {K : Type*} [Field K] [CharP K 3]

/-- Clearing the linear denominator `z-1` gives the exact identity

`(z-1)^2 C = A Q - R`

in every field of characteristic three.  This is the structural reason the
three-variable point enumeration reduces to a bivariate residual count. -/
theorem canonical_elimination_identity25Three (y z w : K) :
    (z - 1) ^ 2 * canonicalCubicX25Three y z w =
      canonicalEliminationMultiplierX25Three y z w *
        canonicalQuadricX25Three y z w -
      canonicalResidualX25Three y z := by
  unfold canonicalCubicX25Three canonicalEliminationMultiplierX25Three
    canonicalQuadricX25Three canonicalResidualX25Three
  linear_combination
    (-y ^ 3 * z ^ 2 - y ^ 2 * z ^ 3 + y ^ 3 * z + y ^ 2 * z ^ 2 +
      y * z ^ 3 - z ^ 3 * w - y ^ 2 * z - 2 * y * z ^ 2 +
      z ^ 2 * w + y * z + z ^ 2) * CharP.cast_eq_zero K 3

/-- On `z ≠ 1`, a point satisfying the quadric satisfies the cubic exactly
when its bivariate elimination residual vanishes.

The nonzero factor `(z-1)^2` can be cancelled because the ambient type is a
field.  This theorem formally justifies counting one candidate `w` for each
residual pair `(y,z)`. -/
theorem canonicalCubicX25Three_eq_zero_iff_residual
    {y z w : K} (hz : z ≠ 1)
    (hQ : canonicalQuadricX25Three y z w = 0) :
    canonicalCubicX25Three y z w = 0 ↔
      canonicalResidualX25Three y z = 0 := by
  have hD : z - 1 ≠ 0 := sub_ne_zero.mpr hz
  have hid := canonical_elimination_identity25Three y z w
  rw [hQ, mul_zero] at hid
  constructor
  · intro hC
    have hneg : -canonicalResidualX25Three y z = 0 := by
      simpa [hC] using hid.symm
    exact neg_eq_zero.mp hneg
  · intro hR
    have hprod : (z - 1) ^ 2 * canonicalCubicX25Three y z w = 0 := by
      simpa [hR] using hid
    exact (mul_eq_zero.mp hprod).resolve_left (pow_ne_zero 2 hD)


end MazurProof.RationalPointsN25QuotientWeilThreeLinear
namespace MazurProof.RationalPointsN25QuotientSmallThreeSemantic

open MazurProof.RationalPointsN25QuotientF2
open MazurProof.RationalPointsN25QuotientWeil
open MazurProof.RationalPointsN25QuotientWeilThreeLinear
open MazurProof.RationalPointsN25QuotientKummerThree
open MazurProof.RationalPointsN25QuotientKummerThreeProjective

/-- On the normalized `x`-chart, the homogeneous canonical equations are the
two affine polynomials used by linear elimination. -/
theorem isCanonicalNormalizedThree_xChart_iff
    {K : Type*} [Field K] (y z w : K) :
    IsCanonicalNormalizedThree (.xChart y z w) ↔
      canonicalQuadricX25Three y z w = 0 ∧
        canonicalCubicX25Three y z w = 0 := by
  change canonicalQuadric25Three ⟨1, y, z, w⟩ = 0 ∧
      canonicalCubic25Three ⟨1, y, z, w⟩ = 0 ↔ _
  have hQ : canonicalQuadric25Three ⟨1, y, z, w⟩ =
      canonicalQuadricX25Three y z w := by
    unfold canonicalQuadric25Three canonicalQuadricX25Three
    ring
  have hC : canonicalCubic25Three ⟨1, y, z, w⟩ =
      canonicalCubicX25Three y z w := by
    unfold canonicalCubic25Three canonicalCubicX25Three
    ring
  rw [hQ, hC]


end MazurProof.RationalPointsN25QuotientSmallThreeSemantic
namespace MazurProof.RationalPointsN25QuotientKummerThreeProjective

open MazurProof.RationalPointsN25QuotientF2
open MazurProof.RationalPointsN25QuotientWeil

/-- Normalization rescales every nonzero homogeneous vector by a nonzero
field element. -/
theorem normalizeCoordinatesThree_spec
    {K : Type*} [Field K] [DecidableEq K] {P : Coordinates4 K}
    (hP : P ≠ zeroCoordinatesThree) :
    ∃ a : K, a ≠ 0 ∧
      normalizedCoordinatesThree (normalizeCoordinatesThree P) =
        scaleCoordinatesThree a P := by
  by_cases hx : P.x ≠ 0
  · refine ⟨P.x⁻¹, inv_ne_zero hx, ?_⟩
    simp [normalizeCoordinatesThree, hx, normalizedCoordinatesThree,
      scaleCoordinatesThree, div_eq_mul_inv, mul_comm]
  · by_cases hy : P.y ≠ 0
    · have hx0 : P.x = 0 := not_ne_iff.mp hx
      refine ⟨P.y⁻¹, inv_ne_zero hy, ?_⟩
      simp [normalizeCoordinatesThree, hy, normalizedCoordinatesThree,
        scaleCoordinatesThree, hx0, div_eq_mul_inv, mul_comm]
    · by_cases hz : P.z ≠ 0
      · have hx0 : P.x = 0 := not_ne_iff.mp hx
        have hy0 : P.y = 0 := not_ne_iff.mp hy
        refine ⟨P.z⁻¹, inv_ne_zero hz, ?_⟩
        simp [normalizeCoordinatesThree, hz, normalizedCoordinatesThree,
          scaleCoordinatesThree, hx0, hy0, div_eq_mul_inv, mul_comm]
      · have hw : P.w ≠ 0 := by
          have hx0 : P.x = 0 := not_ne_iff.mp hx
          have hy0 : P.y = 0 := not_ne_iff.mp hy
          have hz0 : P.z = 0 := not_ne_iff.mp hz
          intro hw
          apply hP
          rcases P with ⟨x, y, z, w⟩
          simp only at hx0 hy0 hz0 hw
          subst x
          subst y
          subst z
          subst w
          rfl
        have hx0 : P.x = 0 := not_ne_iff.mp hx
        have hy0 : P.y = 0 := not_ne_iff.mp hy
        have hz0 : P.z = 0 := not_ne_iff.mp hz
        refine ⟨P.w⁻¹, inv_ne_zero hw, ?_⟩
        simp [normalizeCoordinatesThree, normalizedCoordinatesThree,
          scaleCoordinatesThree, hx0, hy0, hz0, hw]

end MazurProof.RationalPointsN25QuotientKummerThreeProjective


