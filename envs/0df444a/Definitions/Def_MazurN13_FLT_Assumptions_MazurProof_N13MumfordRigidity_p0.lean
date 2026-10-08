-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13MumfordRigidity_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13MumfordRigidity_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T22:05:49.670067+00:00
-- url     : https://prove2.me/theorems/f867fd91-ac50-4db2-bb4a-4ae8a9640eaa
-- title:
--   FLT.Assumptions.MazurProof.N13MumfordRigidity source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13MumfordRigidity

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13MumfordRigidity
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_SexticMumfordRecover_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_SexticMumfordUnit_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13InfinityAPI_p0

set_option autoImplicit false




/-!
# Constant-principal rigidity for balanced `X₁(13)` Mumford data

Once a principal multiplier between two balanced representatives is known to
be constant, its fractional ideal and its order at the positive infinity are
both trivial.  The generic ideal-kernel calculation then recovers `u`, `v`,
and the infinity coordinate.

The remaining normal-form uniqueness problem is therefore geometric: prove
that a function with the relevant small pole bounds is constant.
-/

open scoped nonZeroDivisors

namespace MazurProof.N13Mumford

open SexticMumford

noncomputable section

universe u

variable (K : Type u) [Field K] [CharZero K]

theorem principal_between_balanced_of_constant
    {D₁ D₂ : Mumford K} {α : (FunctionField K)ˣ}
    (c : Kˣ)
    (hα : α = N13Infinity.functionConstUnit K c)
    (hIdeal :
      mumfordIdealUnit (model K) D₁.toSemi *
          toPrincipalIdeal (CoordinateRing K) (FunctionField K) α =
        mumfordIdealUnit (model K) D₂.toSemi)
    (hInf :
      Multiplicative.ofAdd ((D₁.nInf : ℤ) - 1) *
          (N13Infinity.positiveInfinityOrder K).ordPlus α =
        Multiplicative.ofAdd ((D₂.nInf : ℤ) - 1)) :
    D₁ = D₂ := by
  subst α
  have hUnits :
      mumfordIdealUnit (model K) D₁.toSemi =
        mumfordIdealUnit (model K) D₂.toSemi := by
    simpa only [N13Infinity.principalIdeal_functionConstUnit, mul_one] using
      hIdeal
  have hFrac := congrArg
    (fun I : InvFrac (model K) ↦
      (I : FractionalIdeal (CoordinateRing K)⁰ (FunctionField K))) hUnits
  simp only [coe_mumfordIdealUnit] at hFrac
  have hIdeal' :
      mumfordIdeal (model K) D₁.u D₁.v =
        mumfordIdeal (model K) D₂.u D₂.v :=
    FractionalIdeal.coeIdeal_inj.mp hFrac
  have hInf' :
      Multiplicative.ofAdd ((D₁.nInf : ℤ) - 1) =
        Multiplicative.ofAdd ((D₂.nInf : ℤ) - 1) := by
    simpa only [N13Infinity.ordPlus_functionConstUnit, mul_one] using hInf
  have hz : ((D₁.nInf : ℤ) - 1) = ((D₂.nInf : ℤ) - 1) :=
    Multiplicative.ofAdd.injective hInf'
  have hn : D₁.nInf = D₂.nInf := by omega
  exact mumford_eq_of_ideal_eq_of_nInf_eq (model K) hIdeal' hn

end

end MazurProof.N13Mumford


