-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13MumfordKummerKernelForward_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13MumfordKummerKernelForward_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-08T00:25:01.350556+00:00
-- url     : https://prove2.me/theorems/a2c940a3-7098-48ec-a109-c9467169aa9e
-- title:
--   FLT.Assumptions.MazurProof.N13MumfordKummerKernelForward source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13MumfordKummerKernelForward

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13MumfordKummerKernelForward
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13MumfordKummerHom_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13LowDegreeKummerHom_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13KummerKernelAssembly_p0

set_option autoImplicit false




/-!
# The forward N13 fake-Kummer kernel inclusions

The actual fake-Kummer homomorphism has an exponent-two target, so it kills
every double.  The even-sextic infinity class is represented by the balanced
Mumford datum with `u = 1`; its raw value `u(θ)` is therefore one, so that
class is killed as well.

These are only the forward inclusions in the standard even-sextic kernel
description.  No converse half-divisor theorem is assumed here.
-/

namespace MazurProof.N13MumfordKummerKernelForward

noncomputable section

open SexticMumford

abbrev M : SexticMumford.Model ℚ :=
  N13MumfordKummerHom.M

abbrev O : SexticMumford.InfinityOrder M :=
  N13MumfordKummerHom.O

abbrev G : Type :=
  N13MumfordKummerHom.G

abbrev Target : Type :=
  N13MumfordKummerHom.Target

abbrev infinityClass : G :=
  N13KummerKernelAssembly.infinityClass

/-- The balanced negative-infinity representative has raw fake value zero:
its Mumford polynomial is `u = 1`. -/
theorem mumfordFakeClass_infinityMinus :
    N13MumfordKummerValue.mumfordFakeClass
        (infinityMinusMumford M) = 0 := by
  have hu :
      N13MumfordKummerValue.uThetaUnit
          (infinityMinusMumford M) = 1 := by
    apply Units.ext
    simp [N13MumfordKummerValue.uThetaUnit,
      N13MumfordKummerValue.uTheta,
      infinityMinusMumford]
  change
    Additive.ofMul
        (((N13MumfordKummerValue.uThetaUnit
          (infinityMinusMumford M) :
          N13MumfordKummerValue.Lˣ)) :
          FakeSquareClass.Target
            (algebraMap ℚ N13MumfordKummerValue.L)) =
      Additive.ofMul 1
  simp only [hu, QuotientGroup.mk_one]

/-- The descended Kummer homomorphism kills the difference of the two
points at infinity. -/
theorem mumfordKummer_infinityClass
    (hrep : Function.Surjective (classOf M O)) :
    N13MumfordKummerHom.mumfordKummer hrep infinityClass = 0 := by
  change
    N13MumfordKummerHom.mumfordKummer hrep
        (classOf M O (infinityMinusMumford M)) = 0
  rw [N13MumfordKummerHom.mumfordKummer_classOf]
  exact mumfordFakeClass_infinityMinus

/-- Every double belongs to the kernel of the actual Kummer homomorphism. -/
theorem mumfordKummer_two_nsmul
    (hrep : Function.Surjective (classOf M O))
    (Q : G) :
    N13MumfordKummerHom.mumfordKummer hrep (2 • Q) = 0 := by
  rw [map_nsmul, N13MumfordKummerHom.mumfordKummer_apply]
  exact
    N13MumfordKummerValue.two_nsmul_mumfordFakeClass
      (N13MumfordKummerHom.representative hrep Q)

/-- The second standard even-sextic branch is also contained in the
kernel: a double plus the infinity class has trivial fake value. -/
theorem mumfordKummer_two_nsmul_add_infinityClass
    (hrep : Function.Surjective (classOf M O))
    (Q : G) :
    N13MumfordKummerHom.mumfordKummer hrep
        (2 • Q + infinityClass) = 0 := by
  rw [map_add, mumfordKummer_two_nsmul,
    mumfordKummer_infinityClass, zero_add]

/-! ## Unconditional low-degree Kummer homomorphism -/

abbrev structuralKummer : G →+ Target :=
  N13LowDegreeKummerHom.mumfordKummer

def infinityMinusLow :
    N13LowDegreeKummerHom.LowRep where
  toSemi := (infinityMinusMumford M).toSemi
  degree_le_two := (infinityMinusMumford M).deg_u

@[simp] theorem lowClass_infinityMinusLow :
    N13LowDegreeKummerHom.lowClass infinityMinusLow =
      infinityClass := by
  rfl

@[simp] theorem lowFakeClass_infinityMinusLow :
    N13LowDegreeKummerHom.lowFakeClass infinityMinusLow = 0 := by
  have hu :
      N13MumfordKummerValue.uThetaUnit
          (N13LowDegreeKummerHom.asMumford infinityMinusLow) = 1 := by
    apply Units.ext
    simp [N13MumfordKummerValue.uThetaUnit,
      N13MumfordKummerValue.uTheta,
      N13LowDegreeKummerHom.asMumford, infinityMinusLow,
      infinityMinusMumford]
  change
    Additive.ofMul
        (((N13MumfordKummerValue.uThetaUnit
          (N13LowDegreeKummerHom.asMumford infinityMinusLow) :
          N13MumfordKummerValue.Lˣ)) :
          FakeSquareClass.Target
            (algebraMap ℚ N13MumfordKummerValue.L)) =
      Additive.ofMul 1
  simp only [hu, QuotientGroup.mk_one]

/-- The unconditional structural Kummer homomorphism kills the difference
of the two infinity points. -/
theorem structuralKummer_infinityClass :
    structuralKummer infinityClass = 0 := by
  rw [← lowClass_infinityMinusLow,
    N13LowDegreeKummerHom.mumfordKummer_lowClass,
    lowFakeClass_infinityMinusLow]

/-- The unconditional structural Kummer homomorphism kills every double. -/
theorem structuralKummer_two_nsmul (Q : G) :
    structuralKummer (2 • Q) = 0 := by
  rw [map_nsmul, N13LowDegreeKummerHom.mumfordKummer_apply]
  exact
    N13MumfordKummerValue.two_nsmul_mumfordFakeClass
      (N13LowDegreeKummerHom.asMumford
        (N13LowDegreeKummerHom.representative Q))

/-- It also kills a double translated by the infinity class. -/
theorem structuralKummer_two_nsmul_add_infinityClass (Q : G) :
    structuralKummer (2 • Q + infinityClass) = 0 := by
  rw [map_add, structuralKummer_two_nsmul,
    structuralKummer_infinityClass, zero_add]

end

end MazurProof.N13MumfordKummerKernelForward


