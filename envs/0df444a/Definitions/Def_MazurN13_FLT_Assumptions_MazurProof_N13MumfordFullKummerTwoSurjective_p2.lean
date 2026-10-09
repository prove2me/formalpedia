-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13MumfordFullKummerTwoSurjective_p2
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13MumfordFullKummerTwoSurjective_p2
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-08T17:30:10.658045+00:00
-- url     : https://prove2.me/theorems/fc13ed9e-cf52-409e-82dd-f2e3d6e60aba
-- title:
--   FLT.Assumptions.MazurProof.N13MumfordFullKummerTwoSurjective source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13MumfordFullKummerTwoSurjective

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13MumfordFullKummerTwoSurjective
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13GaussianGlobalZeroCarrierDlog_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13MumfordFullKummerIdentityFiber_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13MumfordFullKummerTwoSurjective_p1

set_option autoImplicit false

namespace MazurProof.N13MumfordFullKummerTwoSurjective
noncomputable section
/-- Multiplication by two is surjective on the concrete N13 Picard group. -/
theorem twoSurjective :
    N13TwoAdicEndgame.TwoSurjective G := by
  intro P
  let D := constructedHalfData P
  exact ⟨D.finite.half, D.double_eq⟩

/-- For the actual image quotient, no special-fibre group law or
exponent-nineteen argument is needed.  Finiteness of the quotient and a
separated reduction kernel already force injectivity. -/
theorem reduction_injective_of_finite_image
    {J₂ : Type*} [AddCommGroup J₂] [Finite J₂]
    (red : G →+ J₂)
    (red_surjective : Function.Surjective red)
    (separated :
      N18RouteC.Separated.NSeparated red.ker 2) :
    Function.Injective red :=
  N13TwoAdicEndgame.reduction_injective_of_finite_target
    red red_surjective twoSurjective separated

/-- Assemble the remaining geometric reduction data with the now-proved
doubling surjectivity. -/
def endgameData
    {J₂ : Type*} [AddCommGroup J₂] [Finite J₂]
    (abelFibres :
      N13SymmetricSquareTwo.AbelFiberData J₂)
    (red : G →+ J₂)
    (formalKernel :
      N13TwoAdicEndgame.FormalKernelData red.ker) :
    N13TwoAdicEndgame.Data G J₂ where
  abelFibres := abelFibres
  red := red
  twoSurjective := twoSurjective
  formalKernel := formalKernel

/-- Once the genuine special-fibre Abel data, reduction map, and formal
kernel are constructed, reduction injectivity is immediate. -/
theorem reduction_injective
    {J₂ : Type*} [AddCommGroup J₂] [Finite J₂]
    (abelFibres :
      N13SymmetricSquareTwo.AbelFiberData J₂)
    (red : G →+ J₂)
    (formalKernel :
      N13TwoAdicEndgame.FormalKernelData red.ker) :
    Function.Injective red :=
  (endgameData abelFibres red formalKernel).reduction_injective

end

end MazurProof.N13MumfordFullKummerTwoSurjective


