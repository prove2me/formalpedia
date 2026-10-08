-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_SexticMumfordNormalForm_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_SexticMumfordNormalForm_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T21:50:47.462259+00:00
-- url     : https://prove2.me/theorems/7d649aad-a2ca-4301-8202-02ea72646379
-- title:
--   FLT.Assumptions.MazurProof.SexticMumfordNormalForm source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.SexticMumfordNormalForm

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.SexticMumfordNormalForm
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_SexticMumfordBasis_p0

set_option autoImplicit false




/-!
# First normalization step for sextic Mumford ideals

Before choosing a two-generator `K[X]`-basis, a fractional ideal may be
cleared of denominators by a single nonzero element of the coordinate ring.
This is the first, representation-independent step in the normal-form
argument.
-/

open scoped nonZeroDivisors

namespace MazurProof.SexticMumford

noncomputable section

universe u

variable {K : Type u} [Field K]

/-- Every invertible fractional ideal of the sextic coordinate ring becomes
an integral ideal after multiplication by one nonzero principal factor. -/
theorem invFrac_exists_integral_scaling (M : Model K) (I : InvFrac M) :
    ∃ (a : CoordinateRing M) (J : Ideal (CoordinateRing M)), a ≠ 0 ∧
      (I : FractionalIdeal (CoordinateRing M)⁰ (FunctionField M)) =
        FractionalIdeal.spanSingleton (CoordinateRing M)⁰
          (algebraMap (CoordinateRing M) (FunctionField M) a)⁻¹ * J := by
  exact FractionalIdeal.exists_eq_spanSingleton_mul
    (I : FractionalIdeal (CoordinateRing M)⁰ (FunctionField M))

end

end MazurProof.SexticMumford


