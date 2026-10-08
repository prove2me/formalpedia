-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13GaussianCandidateUnitAssembly_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13GaussianCandidateUnitAssembly_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T22:33:17.015512+00:00
-- url     : https://prove2.me/theorems/974f63e0-b09b-4b87-a0fa-5a852bd9986a
-- title:
--   FLT.Assumptions.MazurProof.N13GaussianCandidateUnitAssembly source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13GaussianCandidateUnitAssembly

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13GaussianCandidateUnitAssembly
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13GaussianNamedUnitTransport_p0

set_option autoImplicit false




/-!
# Assembly of the N13 Gaussian candidate units

This file closes the final group-theoretic seam after the arithmetic descent
has produced one common ramified carrier bit.  A maximal-order unit is
transported to the sextic field and decomposed in the three named unit
generators.  The remaining common carrier is exactly the fourth generator,
up to a square.

No finite enumeration is used: the argument is an identity in the unit group,
followed by passage to the squareclass quotient.
-/

namespace MazurProof.N13GaussianCandidateUnitAssembly

noncomputable section

open N13GaussianNamedUnitTransport

abbrev O :=
  N13GaussianNamedUnitTransport.O

abbrev Ls :=
  N13GaussianNamedUnitTransport.Ls

/-- A maximal-order unit, one common ramified carrier bit, and a field
square assemble into exactly the existing four-generator candidate word
times a square. -/
theorem exists_candidateUnit_mul_sq
    (x : Lsˣ) (ε : Oˣ)
    (d : ZMod 2) (s : Lsˣ)
    (h :
      x =
        orderUnitsToSextic ε *
          (N13CandidateCollapse.primeAUnit *
            N13CandidateCollapse.primeQUnit) ^ d.val *
          s ^ 2) :
    ∃ i j k : ZMod 2, ∃ t : Lsˣ,
      x =
        N13CandidateCollapse.candidateUnit
          i j k d * t ^ 2 := by
  obtain ⟨i, j, k, η, hη⟩ :=
    orderUnitsToSextic_decompose_named ε
  refine ⟨i, j, k, η * s, ?_⟩
  rw [h, hη]
  simp only [N13CandidateCollapse.candidateUnit,
    mul_pow]
  ac_rfl

/-- Passing the preceding identity to fake squareclasses gives one of the
named N13 candidate classes. -/
theorem fakeClass_eq_candidateClass
    (x : Lsˣ) (ε : Oˣ)
    (d : ZMod 2) (s : Lsˣ)
    (h :
      x =
        orderUnitsToSextic ε *
          (N13CandidateCollapse.primeAUnit *
            N13CandidateCollapse.primeQUnit) ^ d.val *
          s ^ 2) :
    ∃ i j k : ZMod 2,
      (x :
        FakeSquareClass.Target
          (algebraMap ℚ Ls)) =
        N13CandidateCollapse.candidateClass
          i j k d := by
  obtain ⟨i, j, k, t, ht⟩ :=
    exists_candidateUnit_mul_sq x ε d s h
  refine ⟨i, j, k, ?_⟩
  rw [ht]
  change
    ((N13CandidateCollapse.candidateUnit
        i j k d * t ^ 2 : Lsˣ) :
      FakeSquareClass.Target (algebraMap ℚ Ls)) =
      ((N13CandidateCollapse.candidateUnit
        i j k d : Lsˣ) :
      FakeSquareClass.Target (algebraMap ℚ Ls))
  simp

end

end MazurProof.N13GaussianCandidateUnitAssembly


