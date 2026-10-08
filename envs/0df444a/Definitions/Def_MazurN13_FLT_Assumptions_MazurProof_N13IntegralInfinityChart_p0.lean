-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13IntegralInfinityChart_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13IntegralInfinityChart_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T22:44:44.069846+00:00
-- url     : https://prove2.me/theorems/0586b19f-305f-4be0-a409-6328f7a7079c
-- title:
--   FLT.Assumptions.MazurProof.N13IntegralInfinityChart source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13IntegralInfinityChart

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13IntegralInfinityChart
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13FormalInfinityChart_p0

set_option autoImplicit false




/-!
# The ordinary integral infinity chart of N13

This algebraic chart precedes completion.  It is the quadratic algebra over
`ℤ₂[t]` cut out by

`v² + (1+t²+t³)v = t+t²`.

The coefficientwise map `ℤ₂[t] → ℤ₂[[t]]` induces the canonical completion
map to the already constructed formal infinity chart.
-/

open Polynomial

namespace MazurProof.N13IntegralInfinityChart

noncomputable section

local instance instFactPrimeOfNatNat_fLT : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

abbrev R₂ : Type :=
  N13FormalInfinityChart.R₂

abbrev Base : Type :=
  R₂[X]

abbrev Power : Type :=
  N13FormalInfinityChart.Power

abbrev FormalInfinityCurve : Type :=
  N13FormalInfinityChart.InfinityCurve

/-- Coefficient of `v` on the ordinary infinity chart. -/
def hBase : Base :=
  1 + X ^ 2 + X ^ 3

/-- Right-hand side on the ordinary infinity chart. -/
def rhsBase : Base :=
  X + X ^ 2

/-- The ordinary quadratic infinity-chart equation. -/
def infinityCurvePoly : Base[X] :=
  X ^ 2 + C hBase * X - C rhsBase

theorem infinityCurvePoly_monic :
    infinityCurvePoly.Monic := by
  unfold infinityCurvePoly
  monicity <;> norm_num

theorem infinityCurvePoly_natDegree :
    infinityCurvePoly.natDegree = 2 := by
  unfold infinityCurvePoly
  compute_degree <;> norm_num

/-- The actual algebraic infinity-chart coordinate ring before completion. -/
abbrev InfinityCurve : Type :=
  AdjoinRoot infinityCurvePoly

/-- The ordinary infinity chart is finite free of rank two over
`ℤ₂[t]`; its power basis is `1,v`. -/
def powerBasis : PowerBasis Base InfinityCurve :=
  AdjoinRoot.powerBasis' infinityCurvePoly_monic

noncomputable instance infinityCurveModuleFree :
    Module.Free Base InfinityCurve :=
  Module.Free.of_basis powerBasis.basis

noncomputable instance infinityCurveModuleFinite :
    Module.Finite Base InfinityCurve :=
  powerBasis.finite

@[simp] theorem powerBasis_dim :
    powerBasis.dim = 2 := by
  exact infinityCurvePoly_natDegree

/-- The ordinary coordinates `t` and `v`. -/
def tClass : InfinityCurve :=
  algebraMap Base InfinityCurve X

def vClass : InfinityCurve :=
  AdjoinRoot.root infinityCurvePoly

/-- Send an ordinary polynomial in `t` to the corresponding power series. -/
def baseToPower : Base →+* Power :=
  Polynomial.eval₂RingHom
    (algebraMap R₂ Power) PowerSeries.X

@[simp] theorem baseToPower_X :
    baseToPower X = PowerSeries.X := by
  simp [baseToPower]

@[simp] theorem baseToPower_hBase :
    baseToPower hBase =
      N13FormalInfinityChart.hPower := by
  simp [baseToPower, hBase, N13FormalInfinityChart.hPower]

@[simp] theorem baseToPower_rhsBase :
    baseToPower rhsBase =
      N13FormalInfinityChart.rhsPower := by
  simp [baseToPower, rhsBase, N13FormalInfinityChart.rhsPower]

theorem formal_v_relation :
    infinityCurvePoly.eval₂
        ((algebraMap Power FormalInfinityCurve).comp baseToPower)
        N13FormalInfinityChart.vClass = 0 := by
  simp only [infinityCurvePoly, eval₂_sub, eval₂_add,
    eval₂_pow, eval₂_X, eval₂_C, eval₂_mul,
    RingHom.comp_apply, baseToPower_hBase,
    baseToPower_rhsBase]
  change
    AdjoinRoot.mk
      N13FormalInfinityChart.infinityCurvePoly
      N13FormalInfinityChart.infinityCurvePoly = 0
  exact
    AdjoinRoot.mk_self

/-- Completion of the ordinary infinity chart at the parameter `t`. -/
def toFormalInfinity :
    InfinityCurve →+* FormalInfinityCurve :=
  AdjoinRoot.lift
    ((algebraMap Power FormalInfinityCurve).comp baseToPower)
    N13FormalInfinityChart.vClass formal_v_relation

@[simp] theorem toFormalInfinity_tClass :
    toFormalInfinity tClass =
      algebraMap Power FormalInfinityCurve PowerSeries.X := by
  simp [toFormalInfinity, tClass, baseToPower]

@[simp] theorem toFormalInfinity_vClass :
    toFormalInfinity vClass =
      N13FormalInfinityChart.vClass := by
  exact AdjoinRoot.lift_root formal_v_relation

end

end MazurProof.N13IntegralInfinityChart


