-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13TwoAdicInfinityCompatibility_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13TwoAdicInfinityCompatibility_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T22:52:31.441605+00:00
-- url     : https://prove2.me/theorems/b6bdb6ce-7ce2-4373-914f-51f79424abc6
-- title:
--   FLT.Assumptions.MazurProof.N13TwoAdicInfinityCompatibility source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13TwoAdicInfinityCompatibility

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13TwoAdicInfinityCompatibility
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13FormalOverlapSplit_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13TwoAdicCoordinateBaseChange_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13TwoInfinityRestriction_p0

set_option autoImplicit false




/-!
# Compatibility of the integral and rational N13 infinity branches

The two branches obtained by X-adic Hensel lifting over `ℤ₂` are the same
branches as the positive and negative Laurent expansions of the sextic
function field after extension to `ℚ₂`.  This identifies the integral
complete-chart lattices with the rational branch pair used to restrict
fractional ideals.
-/

open Polynomial
open scoped LaurentSeries PowerSeries

namespace MazurProof.N13TwoAdicInfinityCompatibility

noncomputable section

local instance instFactPrimeOfNatNat_fLT : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

abbrev R₂ : Type :=
  N13TwoAdicCoordinateBaseChange.R₂

abbrev Q₂ : Type :=
  N13TwoAdicCoordinateBaseChange.Q₂

abbrev IntegralPower : Type :=
  PowerSeries R₂

abbrev IntegralLaurent : Type :=
  LaurentSeries R₂

abbrev RationalPower : Type :=
  PowerSeries Q₂

abbrev RationalLaurent : Type :=
  LaurentSeries Q₂

def coeffMap : R₂ →+* Q₂ :=
  N13TwoAdicCoordinateBaseChange.coeffMap

theorem coeffMap_injective :
    Function.Injective coeffMap :=
  IsFractionRing.injective R₂ Q₂

/-- Coefficientwise extension of integral power series. -/
def powerMap : IntegralPower →+* RationalPower :=
  PowerSeries.map coeffMap

/-- Coefficientwise extension of integral Laurent series. -/
def laurentMap : IntegralLaurent →+* RationalLaurent where
  toFun z := z.map coeffMap
  map_zero' := HahnSeries.map_zero coeffMap.toZeroHom
  map_one' := HahnSeries.map_one coeffMap.toMonoidWithZeroHom
  map_add' _ _ := HahnSeries.map_add coeffMap.toAddMonoidHom
  map_mul' _ _ := HahnSeries.map_mul coeffMap.toNonUnitalRingHom

@[simp] theorem powerMap_coeff
    (f : IntegralPower) (n : ℕ) :
    PowerSeries.coeff n (powerMap f) =
      coeffMap (PowerSeries.coeff n f) :=
  rfl

@[simp] theorem laurentMap_coeff
    (f : IntegralLaurent) (n : ℤ) :
    (laurentMap f).coeff n = coeffMap (f.coeff n) :=
  rfl

theorem powerMap_injective :
    Function.Injective powerMap :=
  PowerSeries.map_injective coeffMap coeffMap_injective

theorem laurentMap_injective :
    Function.Injective laurentMap := by
  intro f g h
  apply HahnSeries.coeff_injective
  funext n
  apply coeffMap_injective
  simpa only [laurentMap_coeff] using
    congrArg (fun z : RationalLaurent => z.coeff n) h

/-- Extension commutes with the inclusion of power series into Laurent
series. -/
theorem laurentMap_includePower
    (f : IntegralPower) :
    laurentMap
        (N13FormalInfinityChart.includePowerRing f) =
      (HahnSeries.ofPowerSeries ℤ Q₂) (powerMap f) := by
  ext n
  rw [laurentMap_coeff]
  by_cases hn : n < 0
  · simp [N13FormalInfinityChart.includePowerRing,
      PowerSeries.coeff_coe, hn]
  · simp [N13FormalInfinityChart.includePowerRing,
      PowerSeries.coeff_coe, hn]

/-- Laurent monomials over `ℚ₂`. -/
def tPowQ (n : ℤ) : RationalLaurent :=
  HahnSeries.single n 1

@[simp] theorem laurentMap_tPow
    (n : ℤ) :
    laurentMap (N13FormalCurveOverlap.tPow n) =
      tPowQ n := by
  ext m
  rw [laurentMap_coeff]
  by_cases hmn : m = n
  · subst m
    simp [N13FormalCurveOverlap.tPow, tPowQ]
  · simp [N13FormalCurveOverlap.tPow, tPowQ,
      hmn]

@[simp] theorem laurentMap_cechTPow
    (n : ℤ) :
    laurentMap (N13FormalLineBundleCech.tPow n) =
      tPowQ n := by
  ext m
  rw [laurentMap_coeff]
  by_cases hmn : m = n
  · subst m
    simp [N13FormalLineBundleCech.tPow, tPowQ]
  · simp [N13FormalLineBundleCech.tPow, tPowQ,
      hmn]

@[simp] theorem tPowQ_mul
    (m n : ℤ) :
    tPowQ m * tPowQ n = tPowQ (m + n) := by
  simp [tPowQ]

@[simp] theorem tPowQ_zero :
    tPowQ 0 = 1 := rfl

def hInfinityQ : RationalLaurent :=
  tPowQ 0 + tPowQ 2 + tPowQ 3

def rhsInfinityQ : RationalLaurent :=
  tPowQ 1 + tPowQ 2

@[simp] theorem laurentMap_hInfinity :
    laurentMap
        (N13FormalLineBundleCech.hInfinity (R := R₂)) =
      hInfinityQ := by
  simp [N13FormalLineBundleCech.hInfinity,
    hInfinityQ]

@[simp] theorem laurentMap_rhsInfinity :
    laurentMap
        (N13FormalLineBundleCech.rhsInfinity (R := R₂)) =
      rhsInfinityQ := by
  simp [N13FormalLineBundleCech.rhsInfinity,
    rhsInfinityQ]

@[simp] theorem powerMap_branchZero_constantCoeff :
    PowerSeries.constantCoeff
        (powerMap N13FormalInfinityBranches.branchZero) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    powerMap_coeff,
    PowerSeries.coeff_zero_eq_constantCoeff_apply,
    N13FormalInfinityBranches.branchZero_constantCoeff]
  exact map_zero coeffMap

theorem wSeries_coeff_zero :
    (N13Infinity.wSeries Q₂).coeff (0 : ℤ) = 1 := by
  change
    (HahnSeries.ofPowerSeries ℤ Q₂
      (N13Infinity.sqrtReverseF Q₂)).coeff (0 : ℕ) = 1
  rw [HahnSeries.ofPowerSeries_apply_coeff,
    PowerSeries.coeff_zero_eq_constantCoeff,
    N13Infinity.sqrtReverseF_constantCoeff]

@[simp] theorem hInfinityQ_coeff_zero :
    hInfinityQ.coeff (0 : ℤ) = 1 := by
  simp [hInfinityQ, tPowQ]

theorem wSeries_sq_eq_h_sq_add_four_rhs :
    N13Infinity.wSeries Q₂ ^ 2 =
      hInfinityQ ^ 2 + 4 * rhsInfinityQ := by
  rw [N13Infinity.wSeries_sq]
  have ht0 :
      tPowQ 0 = (1 : RationalLaurent) := rfl
  have ht1 :
      tPowQ 1 = N13Infinity.parameter Q₂ := rfl
  have ht2 :
      tPowQ 2 = N13Infinity.parameter Q₂ ^ 2 := by
    simp [tPowQ, N13Infinity.parameter,
      HahnSeries.single_pow]
  have ht3 :
      tPowQ 3 = N13Infinity.parameter Q₂ ^ 3 := by
    simp [tPowQ, N13Infinity.parameter,
      HahnSeries.single_pow]
  rw [hInfinityQ, rhsInfinityQ, ht0, ht1, ht2, ht3]
  ring

/-- The rational branch of the good coordinate `v=t³y` reducing to zero. -/
def rationalBranchZero : RationalLaurent :=
  algebraMap Q₂ RationalLaurent (1 / 2) *
    (N13Infinity.wSeries Q₂ - hInfinityQ)

/-- Its quadratic conjugate. -/
def rationalBranchOne : RationalLaurent :=
  -hInfinityQ - rationalBranchZero

theorem tPowQ_three_mul_ySeries :
    tPowQ 3 * N13Infinity.ySeries Q₂ =
      N13Infinity.wSeries Q₂ := by
  have ht3 :
      tPowQ 3 = N13Infinity.parameter Q₂ ^ 3 := by
    simp [tPowQ, N13Infinity.parameter,
      HahnSeries.single_pow]
  rw [ht3, N13Infinity.ySeries, ← mul_assoc,
    ← mul_pow]
  simp [N13Infinity.parameter_ne_zero]

theorem tPowQ_three_mul_ySeriesMinus :
    tPowQ 3 * N13InfinityMinus.ySeriesMinus Q₂ =
      -N13Infinity.wSeries Q₂ := by
  rw [N13InfinityMinus.ySeriesMinus_eq_neg]
  calc
    tPowQ 3 * -N13Infinity.ySeries Q₂ =
        -(tPowQ 3 * N13Infinity.ySeries Q₂) := by ring
    _ = -N13Infinity.wSeries Q₂ :=
      congrArg Neg.neg tPowQ_three_mul_ySeries

/-- The zero Hensel branch is the positive sextic Laurent branch after the
good-model change of coordinates. -/
theorem rationalBranchZero_eq_positive :
    rationalBranchZero =
      algebraMap Q₂ RationalLaurent (1 / 2) *
        (tPowQ 3 * N13Infinity.ySeries Q₂ -
          hInfinityQ) := by
  rw [tPowQ_three_mul_ySeries]
  rfl

/-- The conjugate Hensel branch is the negative sextic Laurent branch after
the same coordinate change. -/
theorem rationalBranchOne_eq_negative :
    rationalBranchOne =
      algebraMap Q₂ RationalLaurent (1 / 2) *
        (tPowQ 3 *
            N13InfinityMinus.ySeriesMinus Q₂ -
          hInfinityQ) := by
  rw [tPowQ_three_mul_ySeriesMinus]
  have htwo :
      (2 : RationalLaurent) *
          algebraMap Q₂ RationalLaurent (1 / 2) = 1 := by
    rw [← map_ofNat
        (algebraMap Q₂ RationalLaurent) 2,
      ← map_mul]
    norm_num
  unfold rationalBranchOne rationalBranchZero
  linear_combination hInfinityQ * htwo

@[simp] theorem rationalBranchZero_coeff_zero :
    rationalBranchZero.coeff (0 : ℤ) = 0 := by
  unfold rationalBranchZero
  rw [HahnSeries.algebraMap_apply',
    PowerSeries.algebraMap_apply,
    HahnSeries.ofPowerSeries_C]
  change
    ((HahnSeries.single 0 (1 / 2 : Q₂)) *
      (N13Infinity.wSeries Q₂ - hInfinityQ)).coeff
        (0 : ℤ) = 0
  rw [HahnSeries.coeff_single_zero_mul]
  simp [wSeries_coeff_zero, hInfinityQ_coeff_zero]

@[simp] theorem rationalBranchOne_coeff_zero :
    rationalBranchOne.coeff (0 : ℤ) = -1 := by
  simp [rationalBranchOne, rationalBranchZero_coeff_zero,
    hInfinityQ_coeff_zero]

theorem rationalBranchZero_relation :
    rationalBranchZero ^ 2 +
        hInfinityQ * rationalBranchZero -
      rhsInfinityQ = 0 := by
  have hsq := wSeries_sq_eq_h_sq_add_four_rhs
  unfold rationalBranchZero
  have htwo :
      (2 : RationalLaurent) *
          algebraMap Q₂ RationalLaurent (1 / 2) = 1 := by
    rw [← map_ofNat
        (algebraMap Q₂ RationalLaurent) 2,
      ← map_mul]
    norm_num
  linear_combination
    algebraMap Q₂ RationalLaurent (1 / 2) ^ 2 * hsq +
      (-algebraMap Q₂ RationalLaurent (1 / 2) *
          N13Infinity.wSeries Q₂ * hInfinityQ +
        algebraMap Q₂ RationalLaurent (1 / 2) *
            hInfinityQ ^ 2 +
        (2 * algebraMap Q₂ RationalLaurent (1 / 2) + 1) *
            rhsInfinityQ) * htwo

theorem mappedBranchZero_relation :
    laurentMap
          N13FormalOverlapSplit.branchZeroLaurent ^ 2 +
        hInfinityQ *
          laurentMap
            N13FormalOverlapSplit.branchZeroLaurent -
      rhsInfinityQ = 0 := by
  have h := congrArg laurentMap
    N13FormalOverlapSplit.branchZeroLaurent_relation
  simp only [map_sub, map_add, map_pow, map_mul, map_zero] at h
  simpa using h

@[simp] theorem mappedBranchZero_coeff_zero :
    (laurentMap
      N13FormalOverlapSplit.branchZeroLaurent).coeff
        (0 : ℤ) = 0 := by
  rw [N13FormalOverlapSplit.branchZeroLaurent,
    laurentMap_includePower]
  rw [show (0 : ℤ) = (0 : ℕ) by rfl,
    HahnSeries.ofPowerSeries_apply_coeff]
  simpa only [PowerSeries.coeff_zero_eq_constantCoeff] using
    powerMap_branchZero_constantCoeff

/-- A root of the rational formal equation with constant coefficient zero
is the distinguished positive branch. -/
theorem root_eq_rationalBranchZero
    (r : RationalLaurent)
    (hr :
      r ^ 2 + hInfinityQ * r - rhsInfinityQ = 0)
    (hr0 : r.coeff (0 : ℤ) = 0) :
    r = rationalBranchZero := by
  have hprod :
      (r - rationalBranchZero) *
          (r + rationalBranchZero + hInfinityQ) = 0 := by
    linear_combination hr - rationalBranchZero_relation
  rcases mul_eq_zero.mp hprod with h | h
  · exact sub_eq_zero.mp h
  · have hcoeff :=
      congrArg
        (fun z : RationalLaurent => z.coeff (0 : ℤ)) h
    simp [hr0, rationalBranchZero_coeff_zero,
      hInfinityQ_coeff_zero] at hcoeff

@[simp] theorem laurentMap_branchZero :
    laurentMap N13FormalOverlapSplit.branchZeroLaurent =
      rationalBranchZero :=
  root_eq_rationalBranchZero _
    mappedBranchZero_relation mappedBranchZero_coeff_zero

@[simp] theorem laurentMap_branchOne :
    laurentMap N13FormalOverlapSplit.branchOneLaurent =
      rationalBranchOne := by
  calc
    laurentMap N13FormalOverlapSplit.branchOneLaurent =
        laurentMap
          (N13FormalInfinityChart.includePowerRing
            (-N13FormalInfinityChart.hPower -
              N13FormalInfinityBranches.branchZero)) := by
          rw [N13FormalOverlapSplit.branchOneLaurent,
            N13FormalInfinityBranches.branchOne]
    _ =
        -laurentMap
            (N13FormalInfinityChart.includePowerRing
              N13FormalInfinityChart.hPower) -
          laurentMap
            N13FormalOverlapSplit.branchZeroLaurent := by
          simp [N13FormalOverlapSplit.branchZeroLaurent]
    _ = -hInfinityQ - rationalBranchZero := by
      rw [N13FormalInfinityChart.includePowerRing_hPower,
        laurentMap_hInfinity, laurentMap_branchZero]
    _ = rationalBranchOne := rfl

end

end MazurProof.N13TwoAdicInfinityCompatibility


