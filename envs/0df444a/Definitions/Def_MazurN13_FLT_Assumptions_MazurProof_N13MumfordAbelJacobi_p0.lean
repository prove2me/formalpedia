-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13MumfordAbelJacobi_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13MumfordAbelJacobi_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T22:23:51.886028+00:00
-- url     : https://prove2.me/theorems/c62df462-2629-46c3-9e74-a7feb71c5b84
-- title:
--   FLT.Assumptions.MazurProof.N13MumfordAbelJacobi source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13MumfordAbelJacobi

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13MumfordAbelJacobi
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13SmallMumfordRigidity_p0

set_option autoImplicit false




/-!
# The N13 Abel--Jacobi embedding in oriented Mumford coordinates

The chosen positive infinity is the base point.  A curve point is first sent
to its balanced Mumford representative and then to its oriented Picard class.
-/

namespace MazurProof.N13MumfordAbelJacobi

noncomputable section

universe u

variable (K : Type u) [Field K] [CharZero K]

abbrev ConcretePic : Type u :=
  SexticMumford.ConcretePic (N13Mumford.model K)
    (N13Infinity.positiveInfinityOrder K)

def abelJacobi :
    SexticMumford.CurvePoint (N13Mumford.model K) → ConcretePic K :=
  fun P => SexticMumford.classOf (N13Mumford.model K)
    (N13Infinity.positiveInfinityOrder K)
    (SexticMumford.pointMumford (N13Mumford.model K) P)

theorem abelJacobi_injective
    : Function.Injective (abelJacobi K) := by
  exact N13SmallMumfordRigidity.point_class_injective K

abbrev Cusp13 := N13Mumford.Cusp13

def cuspPoint : Cusp13 →
    SexticMumford.CurvePoint (N13Mumford.model ℚ) :=
  N13Mumford.cuspPoint

def cuspAbelJacobi : Cusp13 → ConcretePic ℚ :=
  (abelJacobi ℚ).comp cuspPoint

theorem cuspAbelJacobi_injective
    : Function.Injective cuspAbelJacobi := by
  exact (abelJacobi_injective ℚ).comp N13Mumford.cuspPoint_injective

theorem cuspAbelJacobi_ne
    {c d : Cusp13} (hcd : c ≠ d) :
    cuspAbelJacobi c ≠ cuspAbelJacobi d := by
  exact fun h => hcd (cuspAbelJacobi_injective h)

end

end MazurProof.N13MumfordAbelJacobi


