-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13GaussianNormalizedSquareclassSeam_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13GaussianNormalizedSquareclassSeam_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-08T00:22:51.503386+00:00
-- url     : https://prove2.me/theorems/f242bb58-d953-4d35-99b9-3d2f7d851384
-- title:
--   FLT.Assumptions.MazurProof.N13GaussianNormalizedSquareclassSeam source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13GaussianNormalizedSquareclassSeam

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13GaussianNormalizedSquareclassSeam
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13GaussianNormalizationOrderTransport_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13GlobalKummerSimpleRootParity_p0

set_option autoImplicit false




/-!
# The normalized and actual N13 fake squareclasses

The integral Kummer representative differs from the actual Mumford value by
a nonzero rational scalar.  The fake squareclass quotient kills precisely
such scalars, so the two values have the same fake squareclass.

The only technical seam is that the Gaussian--sextic equivalence and the
current sextic field presentation were compiled under definitionally
different rational algebra instances.  Uniqueness of a ring homomorphism out
of `ℚ` identifies the two scalar maps without unfolding either presentation.
-/

namespace MazurProof.N13GaussianNormalizedSquareclassSeam

noncomputable section

open N13GaussianNormalizationOrderTransport

abbrev LowRep := N13LowDegreeKummerHom.LowRep
abbrev Ls := N13SexticSquareclass.SexticAlgebra

/-- The normalized integral representative, transported to the sextic field
and packaged as a unit. -/
def normalizedIntegralUnit (D : LowRep) : Lsˣ :=
  unitOfNonzero
    (N13GlobalKummerNormalization.normalizedKummerInteger D)
    (N13GlobalKummerSimpleRootParity.normalizedKummerInteger_ne_zero D)

@[simp] theorem coe_normalizedIntegralUnit
    (D : LowRep) :
    (normalizedIntegralUnit D : Ls) =
      normalizationOrderToSextic
        (N13GlobalKummerNormalization.normalizedKummerInteger D) :=
  rfl

/-- The normalized integral unit is the actual Mumford Kummer unit times one
rational scalar unit. -/
theorem exists_normalizedIntegralUnit_eq_uThetaUnit_mul_scalar
    (D : LowRep) :
    ∃ q : ℚˣ,
      normalizedIntegralUnit D =
        N13MumfordKummerValue.uThetaUnit
            (N13LowDegreeKummerHom.asMumford D) *
          FakeSquareClass.scalarUnitsMap
            (algebraMap ℚ Ls) q := by
  obtain ⟨c, hc, hspec⟩ :=
    N13GlobalKummerNormalization.normalizedKummerInteger_spec D
  let q : ℚˣ := Units.mk0 c hc
  have hscalar :
      N13GaussianFieldEquiv.sexticEquivGaussian.symm
          (algebraMap ℚ N13GaussianCubicField.L c) =
        algebraMap ℚ Ls c := by
    let φ : ℚ →+* Ls :=
      N13GaussianFieldEquiv.sexticEquivGaussian.symm.toRingEquiv.toRingHom.comp
        (algebraMap ℚ N13GaussianCubicField.L)
    have hφ : φ = algebraMap ℚ Ls :=
      RingHom.ext_rat _ _
    exact DFunLike.congr_fun hφ c
  have hvalue :
      normalizationOrderToSextic
          (N13GlobalKummerNormalization.normalizedKummerInteger D) =
        algebraMap ℚ Ls c *
          N13MumfordKummerValue.uTheta
            (N13LowDegreeKummerHom.asMumford D) := by
    calc
      normalizationOrderToSextic
          (N13GlobalKummerNormalization.normalizedKummerInteger D) =
          N13GaussianFieldEquiv.sexticEquivGaussian.symm
            ((N13GlobalKummerNormalization.normalizedKummerInteger D :
              N13GlobalKummerIdealSquare.O) :
              N13GaussianCubicField.L) :=
        normalizationOrderToSextic_apply _
      _ =
          N13GaussianFieldEquiv.sexticEquivGaussian.symm
            (algebraMap ℚ N13GaussianCubicField.L c *
              N13GaussianFieldEquiv.sexticEquivGaussian
                (N13MumfordKummerValue.uTheta
                  (N13LowDegreeKummerHom.asMumford D))) := by
        rw [hspec]
      _ =
          N13GaussianFieldEquiv.sexticEquivGaussian.symm
              (algebraMap ℚ N13GaussianCubicField.L c) *
            N13MumfordKummerValue.uTheta
              (N13LowDegreeKummerHom.asMumford D) := by
        rw [map_mul,
          N13GaussianFieldEquiv.sexticEquivGaussian.symm_apply_apply]
      _ =
          algebraMap ℚ Ls c *
            N13MumfordKummerValue.uTheta
              (N13LowDegreeKummerHom.asMumford D) := by
        rw [hscalar]
  refine ⟨q, ?_⟩
  apply Units.ext
  change
    normalizationOrderToSextic
        (N13GlobalKummerNormalization.normalizedKummerInteger D) =
      N13MumfordKummerValue.uTheta
          (N13LowDegreeKummerHom.asMumford D) *
        algebraMap ℚ Ls c
  simpa [mul_comm] using hvalue

/-- Rational normalization does not alter the fake squareclass. -/
theorem normalizedIntegralUnit_fakeClass_eq_uThetaUnit
    (D : LowRep) :
    ((normalizedIntegralUnit D : Lsˣ) :
        FakeSquareClass.Target (algebraMap ℚ Ls)) =
      ((N13MumfordKummerValue.uThetaUnit
          (N13LowDegreeKummerHom.asMumford D) : Lsˣ) :
        FakeSquareClass.Target (algebraMap ℚ Ls)) := by
  obtain ⟨q, hq⟩ :=
    exists_normalizedIntegralUnit_eq_uThetaUnit_mul_scalar D
  rw [hq]
  change
    ((N13MumfordKummerValue.uThetaUnit
          (N13LowDegreeKummerHom.asMumford D) : Lsˣ) :
        FakeSquareClass.Target (algebraMap ℚ Ls)) *
        ((FakeSquareClass.scalarUnitsMap
            (algebraMap ℚ Ls) q : Lsˣ) :
          FakeSquareClass.Target (algebraMap ℚ Ls)) =
      ((N13MumfordKummerValue.uThetaUnit
          (N13LowDegreeKummerHom.asMumford D) : Lsˣ) :
        FakeSquareClass.Target (algebraMap ℚ Ls))
  rw [FakeSquareClass.scalar_eq_one, mul_one]

/-- Any zero-carrier candidate theorem for the normalized unit transfers
unchanged to the actual Mumford Kummer value. -/
theorem uThetaUnit_candidateClass_of_normalized
    (D : LowRep)
    (hCandidate :
      ∃ i j k : ZMod 2,
        ((normalizedIntegralUnit D : Lsˣ) :
          FakeSquareClass.Target (algebraMap ℚ Ls)) =
          N13CandidateCollapse.candidateClass i j k 0) :
    ∃ i j k : ZMod 2,
      ((N13MumfordKummerValue.uThetaUnit
          (N13LowDegreeKummerHom.asMumford D) : Lsˣ) :
        FakeSquareClass.Target (algebraMap ℚ Ls)) =
        N13CandidateCollapse.candidateClass i j k 0 := by
  obtain ⟨i, j, k, h⟩ := hCandidate
  exact
    ⟨i, j, k,
      (normalizedIntegralUnit_fakeClass_eq_uThetaUnit D).symm.trans h⟩

end

end MazurProof.N13GaussianNormalizedSquareclassSeam


