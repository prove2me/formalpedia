-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13MumfordFullKummerTwoSurjective_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13MumfordFullKummerTwoSurjective_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-08T10:13:13.4509+00:00
-- url     : https://prove2.me/theorems/1faa895b-085d-45db-890e-b7304a72baea
-- title:
--   FLT.Assumptions.MazurProof.N13MumfordFullKummerTwoSurjective source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13MumfordFullKummerTwoSurjective

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13MumfordFullKummerTwoSurjective
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13MumfordFullKummerIdentityFiber_p0

set_option autoImplicit false




/-!
# Surjectivity of doubling for the N13 concrete Picard group

The global zero-carrier calculation proves that the actual Mumford Kummer
homomorphism is identically zero.  The structural identity-fibre theorem
identifies its kernel with the subgroup of doubles.  Their composition is
exactly surjectivity of multiplication by two.
-/

namespace MazurProof.N13MumfordFullKummerTwoSurjective

noncomputable section

abbrev G : Type :=
  N13LowDegreeKummerHom.G

/-- The generic Padé square root and the exact half selected by the current
Kummer proof, retained instead of immediately erasing them behind
surjectivity.  This still makes no claim that the generic ideal root extends
to a normalized two-adic graph lattice. -/
structure ConstructedHalfData (P : G) where
  representative : N13LowDegreeKummerHom.LowRep
  representative_spec :
    N13LowDegreeKummerHom.lowClass representative = P
  finite :
    N13MumfordFullKummerIdentityFiber.FiniteIdealHalfData representative
  double_eq :
    P = 2 • finite.half


end
end MazurProof.N13MumfordFullKummerTwoSurjective


