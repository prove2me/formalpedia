-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13MumfordFormalTransition_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13MumfordFormalTransition_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-08T00:31:01.179259+00:00
-- url     : https://prove2.me/theorems/cb8566cb-4d45-4fbb-b061-6928ed016a0a
-- title:
--   FLT.Assumptions.MazurProof.N13MumfordFormalTransition source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13MumfordFormalTransition

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13MumfordFormalTransition
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13TwoAdicAbelChartRecover_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13FormalInfinityChart_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13AbelChartBase_p0
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.RingTheory.PowerSeries.Inverse

set_option autoImplicit false




/-!
# The formal transition of a near-base N13 Mumford graph

The affine graph ideal of integral Mumford data contains its monic polynomial
`u(x)`.  On the punctured formal neighbourhood of infinity this polynomial
is a unit: after factoring its pole `t⁻ᵈ`, the remaining power series is the
reversal of `u`, whose constant coefficient is the leading coefficient `1`.

For data reducing to the selected base graph, the ratio between `u` and the
base polynomial is therefore a genuine unit of the integral quadratic formal
overlap.  Its coefficientwise reduction is one, so it supplies the actual
`NearIdentityTransition` required by the twisted Čech complex.  No Laurent
coefficient enumeration or global generator of the affine ideal is used.
-/

open Polynomial
open scoped LaurentSeries PowerSeries

namespace MazurProof.N13MumfordFormalTransition

noncomputable section

local instance instFactPrimeOfNatNat_fLT : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

abbrev R₂ : Type :=
  N13FormalCurveOverlap.R₂

abbrev K : Type :=
  N13FormalLineBundleCech.K

abbrev Laurent : Type :=
  N13FormalCurveOverlap.Laurent

abbrev LaurentBar : Type :=
  N13FormalLineBundleCech.LaurentBar

abbrev FormalCurve : Type :=
  N13FormalCurveOverlap.FormalCurve

abbrev Overlap : Type :=
  N13FormalCurveOverlap.Overlap

/-- Every Laurent monomial is a unit, with the opposite monomial as
inverse. -/
def tPowUnit (n : ℤ) : Laurentˣ where
  val := N13FormalCurveOverlap.tPow n
  inv := N13FormalCurveOverlap.tPow (-n)
  val_inv := by
    rw [N13FormalCurveOverlap.tPow_mul]
    simp
  inv_val := by
    rw [N13FormalCurveOverlap.tPow_mul]
    simp

@[simp] theorem coe_tPowUnit (n : ℤ) :
    (tPowUnit n : Laurent) =
      N13FormalCurveOverlap.tPow n :=
  rfl

/-- Evaluation of an ordinary polynomial at `t` agrees with first viewing
it as a power series and then including it into Laurent series. -/
theorem eval₂_tPow_one_eq_includePower
    (p : R₂[X]) :
    p.eval₂ (algebraMap R₂ Laurent)
        (N13FormalCurveOverlap.tPow 1) =
      N13FormalInfinityChart.includePowerRing
        (p : PowerSeries R₂) := by
  have h :
      Polynomial.eval₂RingHom
          (algebraMap R₂ Laurent)
          (N13FormalCurveOverlap.tPow 1) =
        N13FormalInfinityChart.includePowerRing.comp
          Polynomial.coeToPowerSeries.ringHom := by
    apply Polynomial.ringHom_ext
    · intro a
      simp [N13FormalInfinityChart.includePowerRing,
        N13FormalCurveOverlap.tPow,
        HahnSeries.algebraMap_apply']
    · simp [N13FormalInfinityChart.includePowerRing_X]
  exact congrArg (fun f : R₂[X] →+* Laurent => f p) h

@[implicit_reducible] private def tInvInvertible :
    Invertible (N13FormalCurveOverlap.tPow (-1)) where
  invOf := N13FormalCurveOverlap.tPow 1
  invOf_mul_self := by
    rw [N13FormalCurveOverlap.tPow_mul]
    norm_num
  mul_invOf_self := by
    rw [N13FormalCurveOverlap.tPow_mul]
    norm_num

attribute [local instance] tInvInvertible

/-- Reversal factors a polynomial at infinity into its pole monomial and a
power series with the coefficients in the opposite order. -/
theorem polyAtTInv_eq_reverse
    (p : R₂[X]) :
    N13FormalCurveOverlap.polyAtTInv p =
      N13FormalInfinityChart.includePowerRing
          (p.reverse : PowerSeries R₂) *
        N13FormalCurveOverlap.tPow
          (-(p.natDegree : ℤ)) := by
  have h :=
    Polynomial.eval₂_reverse_mul_pow
      (algebraMap R₂ Laurent)
      (N13FormalCurveOverlap.tPow (-1)) p
  have hpow :
      N13FormalCurveOverlap.tPow (-1) ^ p.natDegree =
        N13FormalCurveOverlap.tPow
          (-(p.natDegree : ℤ)) := by
    simp [N13FormalCurveOverlap.tPow,
      HahnSeries.single_pow]
  change
    p.reverse.eval₂ (algebraMap R₂ Laurent)
          (N13FormalCurveOverlap.tPow 1) *
        N13FormalCurveOverlap.tPow (-1) ^ p.natDegree =
      N13FormalCurveOverlap.polyAtTInv p at h
  rw [eval₂_tPow_one_eq_includePower, hpow] at h
  exact h.symm

/-- The reversal of a monic polynomial is a power-series unit because its
constant coefficient is one. -/
theorem reverse_powerSeries_isUnit
    (p : R₂[X]) (hp : p.Monic) :
    IsUnit (p.reverse : PowerSeries R₂) := by
  rw [PowerSeries.isUnit_iff_constantCoeff,
    Polynomial.constantCoeff_coe,
    Polynomial.coeff_zero_reverse,
    hp.leadingCoeff]
  exact isUnit_one

/-- A monic affine polynomial becomes a unit on the integral Laurent
overlap. -/
theorem polyAtTInv_isUnit
    (p : R₂[X]) (hp : p.Monic) :
    IsUnit (N13FormalCurveOverlap.polyAtTInv p) := by
  rw [polyAtTInv_eq_reverse]
  exact
    (reverse_powerSeries_isUnit p hp).map
        N13FormalInfinityChart.includePowerRing
      |>.mul (tPowUnit (-(p.natDegree : ℤ))).isUnit

/-! ## Reduction of polynomial restrictions -/

/-- Coefficientwise reduction as a ring homomorphism. -/
def reduceLaurentHom : Laurent →+* LaurentBar where
  toFun := N13FormalLineBundleCech.reduceLaurent
  map_zero' := N13FormalLineBundleCech.reduceLaurent_zero
  map_one' := N13FormalLineBundleCech.reduceLaurent_one
  map_add' := N13FormalLineBundleCech.reduceLaurent_add
  map_mul' := N13FormalLineBundleCech.reduceLaurent_mul

@[simp] theorem reduceLaurentHom_apply
    (f : Laurent) :
    reduceLaurentHom f =
      N13FormalLineBundleCech.reduceLaurent f :=
  rfl

@[simp] theorem reduceLaurent_algebraMap
    (a : R₂) :
    N13FormalLineBundleCech.reduceLaurent
        (algebraMap R₂ Laurent a) =
      algebraMap K LaurentBar
        (N13GeneralizedMumfordReduction.reduceBase a) := by
  rw [HahnSeries.algebraMap_apply',
    HahnSeries.algebraMap_apply',
    PowerSeries.algebraMap_apply,
    PowerSeries.algebraMap_apply,
    HahnSeries.ofPowerSeries_C,
    HahnSeries.ofPowerSeries_C]
  ext n
  by_cases hn : n = 0
  · subst n
    simp [N13FormalLineBundleCech.reduceLaurent,
      N13FormalLineBundleCech.reduceBase,
      N13GeneralizedMumfordReduction.reduceBase]
  · simp [N13FormalLineBundleCech.reduceLaurent,
      N13FormalLineBundleCech.reduceBase,
      N13GeneralizedMumfordReduction.reduceBase, hn]

/-- Evaluate a special-fibre polynomial at `t⁻¹`. -/
def specialPolyAtTInv : K[X] →+* LaurentBar :=
  Polynomial.eval₂RingHom
    (algebraMap K LaurentBar)
    (N13FormalLineBundleCech.tPow (R := K) (-1))

/-- Restriction to infinity commutes with coefficientwise reduction. -/
theorem reduceLaurent_polyAtTInv
    (p : R₂[X]) :
    N13FormalLineBundleCech.reduceLaurent
        (N13FormalCurveOverlap.polyAtTInv p) =
      specialPolyAtTInv
        (N13GeneralizedMumfordReduction.reducePoly p) := by
  have h :
      reduceLaurentHom.comp
          N13FormalCurveOverlap.polyAtTInv =
        specialPolyAtTInv.comp
          N13GeneralizedMumfordReduction.reducePoly := by
    apply Polynomial.ringHom_ext
    · intro a
      simp [specialPolyAtTInv,
        N13GeneralizedMumfordReduction.reducePoly]
    · simp [specialPolyAtTInv,
        N13FormalCurveOverlap.polyAtTInv_X,
        N13GeneralizedMumfordReduction.reducePoly]
      change
        N13FormalLineBundleCech.reduceLaurent
            (N13FormalLineBundleCech.tPow (R := R₂) (-1)) =
          N13FormalLineBundleCech.tPow (R := K) (-1)
      exact N13FormalLineBundleCech.reduceLaurent_tPow (-1)
  exact congrArg (fun f : R₂[X] →+* LaurentBar => f p) h

/-! ## The near-base transition -/

/-- The scalar formal-curve unit represented by a monic affine
polynomial. -/
def formalPolyUnit
    (p : R₂[X]) (hp : p.Monic) :
    FormalCurveˣ :=
  ((polyAtTInv_isUnit p hp).map
    (algebraMap Laurent FormalCurve)).unit

@[simp] theorem coe_formalPolyUnit
    (p : R₂[X]) (hp : p.Monic) :
    (formalPolyUnit p hp : FormalCurve) =
      algebraMap Laurent FormalCurve
        (N13FormalCurveOverlap.polyAtTInv p) :=
  IsUnit.unit_spec
    ((polyAtTInv_isUnit p hp).map
      (algebraMap Laurent FormalCurve))

theorem reduceOverlap_formalPolyUnit
    (p : R₂[X]) (hp : p.Monic) :
    N13FormalLineBundleCech.reduceOverlap
        (N13FormalCurveOverlap.toOverlap
          (formalPolyUnit p hp : FormalCurve)) =
      (specialPolyAtTInv
          (N13GeneralizedMumfordReduction.reducePoly p), 0) := by
  rw [coe_formalPolyUnit,
    N13FormalCurveOverlap.toOverlap_algebraMap]
  apply Prod.ext
  · change
      N13FormalLineBundleCech.reduceLaurent
          (N13FormalCurveOverlap.polyAtTInv p) =
        specialPolyAtTInv
          (N13GeneralizedMumfordReduction.reducePoly p)
    exact reduceLaurent_polyAtTInv p
  · change N13FormalLineBundleCech.reduceLaurent 0 = 0
    exact N13FormalLineBundleCech.reduceLaurent_zero

abbrev NearBaseMumford : Type :=
  N13TwoAdicAbelChartRecover.NearBaseMumford

/-- The base graph's monic polynomial, as a formal-overlap unit. -/
def baseFormalPolyUnit : FormalCurveˣ :=
  formalPolyUnit
    N13AbelChartBase.baseSmoothMumford.u
    N13AbelChartBase.baseSmoothMumford.u_monic

/-- Ratio of the monic polynomial trivializations for a near-base graph
and the selected base graph. -/
def transitionUnit
    (D : NearBaseMumford) :
    FormalCurveˣ :=
  formalPolyUnit D.u D.u_monic *
    baseFormalPolyUnit⁻¹

theorem reducePoly_eq_base
    (D : NearBaseMumford) :
    N13GeneralizedMumfordReduction.reducePoly D.u =
      N13GeneralizedMumfordReduction.reducePoly
        N13AbelChartBase.baseSmoothMumford.u := by
  rw [D.reduce_u]
  exact N13AbelChartBase.reduce_baseSmoothMumford_u.symm

/-- The ratio transition of a near-base graph has identity special
fibre. -/
theorem reduce_transitionUnit
    (D : NearBaseMumford) :
    N13FormalLineBundleCech.reduceOverlap
        (N13FormalCurveOverlap.toOverlap
          (transitionUnit D : FormalCurve)) =
      N13FormalLineBundleCech.oneOverlap (R := K) := by
  change
    N13FormalLineBundleCech.reduceOverlap
        (N13FormalCurveOverlap.toOverlap
          ((formalPolyUnit D.u D.u_monic : FormalCurve) *
            (baseFormalPolyUnit⁻¹ : FormalCurveˣ))) =
      N13FormalLineBundleCech.oneOverlap (R := K)
  rw [N13FormalCurveOverlap.toOverlap_mul,
    N13FormalLineBundleCech.reduceOverlap_mul]
  have hred :
      N13FormalLineBundleCech.reduceOverlap
          (N13FormalCurveOverlap.toOverlap
            (formalPolyUnit D.u D.u_monic : FormalCurve)) =
        N13FormalLineBundleCech.reduceOverlap
          (N13FormalCurveOverlap.toOverlap
            (baseFormalPolyUnit : FormalCurve)) := by
    rw [reduceOverlap_formalPolyUnit,
      show baseFormalPolyUnit =
          formalPolyUnit
            N13AbelChartBase.baseSmoothMumford.u
            N13AbelChartBase.baseSmoothMumford.u_monic from rfl,
      reduceOverlap_formalPolyUnit,
      reducePoly_eq_base D]
  rw [hred, ← N13FormalLineBundleCech.reduceOverlap_mul,
    ← N13FormalCurveOverlap.toOverlap_mul]
  simp [N13FormalLineBundleCech.reduceOverlap_one]

/-- Every smooth integral graph reducing to the selected base graph supplies
the genuine near-identity transition used by the actual twisted Čech
complex. -/
def nearIdentityTransition
    (D : NearBaseMumford) :
    N13FormalLineBundleCech.NearIdentityTransition :=
  N13FormalCurveOverlap.transitionOfUnit
    (transitionUnit D) (reduce_transitionUnit D)

@[simp] theorem nearIdentityTransition_transition
    (D : NearBaseMumford) :
    (nearIdentityTransition D).transition =
      N13FormalCurveOverlap.toOverlap
        (transitionUnit D : FormalCurve) :=
  rfl

end

end MazurProof.N13MumfordFormalTransition


