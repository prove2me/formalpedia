-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13IntegralFiberDetection_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13IntegralFiberDetection_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T22:28:03.198981+00:00
-- url     : https://prove2.me/theorems/cf75ed02-77bc-493e-b9a6-e28a9d7162aa
-- title:
--   FLT.Assumptions.MazurProof.N13IntegralFiberDetection source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13IntegralFiberDetection

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13IntegralFiberDetection
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13IntegralFractionalHull_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13GeneralizedMumfordReduction_p0
import Mathlib.Algebra.Ring.GeomSum

set_option autoImplicit false




open Polynomial
open scoped BigOperators nonZeroDivisors

namespace MazurProof.N13IntegralFiberDetection

noncomputable section

local instance instFactPrimeOfNatNat_fLT : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

abbrev R₂ : Type :=
  N13IntegralModelContraction.R₂

abbrev IntegralRing : Type :=
  N13IntegralModelContraction.IntegralRing

abbrev RationalRing : Type :=
  N13IntegralModelContraction.RationalRing

abbrev SpecialRing : Type :=
  N13GeneralizedMumfordReduction.SpecialRing

abbrev FunctionField : Type :=
  N13IntegralFractionalHull.FunctionField

abbrev IntegralFractionalIdeal : Type :=
  N13IntegralFractionalHull.IntegralFractionalIdeal

abbrev RationalFractionalIdeal : Type :=
  N13IntegralFractionalHull.RationalFractionalIdeal

def integralToRational : IntegralRing →+* RationalRing :=
  N13IntegralFractionalHull.integralToRational

local instance integralRationalAlgebra :
    Algebra IntegralRing RationalRing :=
  N13IntegralFractionalHull.integralToRational.toAlgebra

local instance integralRingDomain : IsDomain IntegralRing :=
  N13IntegralFractionalHull.integralToRational_injective.isDomain
    N13IntegralFractionalHull.integralToRational

local instance rationalRingLocalization :
    IsLocalization
      N13IntegralModelContraction.verticalScalars
      RationalRing :=
  N13IntegralModelContraction.rationalRing_isLocalization

local instance integralFunctionFieldFractionRing :
    IsFractionRing IntegralRing FunctionField :=
  N13IntegralFractionalHull.functionField_isFractionRing

def reduceCoordinate : IntegralRing →+* SpecialRing :=
  N13GeneralizedMumfordReduction.reduceCoordinate

/-- An integral ideal is the unit ideal as soon as both its vertical generic
fibre and its special fibre are the unit ideal.  A generic unit supplies one
nonzero two-adic scalar in the ideal; the DVR structure replaces it by a
power of two.  A special unit lifts to an element congruent to one modulo
two, and a finite geometric series combines the two witnesses. -/
theorem eq_top_of_generic_and_special_eq_top
    (I : Ideal IntegralRing)
    (hGeneric :
      Ideal.map integralToRational I = ⊤)
    (hSpecial :
      Ideal.map reduceCoordinate I = ⊤) :
    I = ⊤ := by
  have hGenericOne :
      algebraMap IntegralRing RationalRing 1 ∈
        Ideal.map (algebraMap IntegralRing RationalRing) I := by
    change integralToRational 1 ∈
      Ideal.map integralToRational I
    rw [hGeneric]
    simp
  rw [IsLocalization.algebraMap_mem_map_algebraMap_iff
    N13IntegralModelContraction.verticalScalars] at hGenericOne
  obtain ⟨m, hm, hmI⟩ := hGenericOne
  simp only [mul_one] at hmI
  change
    ∃ r : R₂, r ∈ nonZeroDivisors R₂ ∧
      algebraMap R₂ IntegralRing r = m at hm
  obtain ⟨r, hr, rfl⟩ := hm
  have hr0 : r ≠ 0 :=
    mem_nonZeroDivisors_iff_ne_zero.mp hr
  obtain ⟨n, hn⟩ :=
    PadicInt.ideal_eq_span_pow_p
      (s := Ideal.span ({r} : Set R₂))
      (by
        rw [Ne, Ideal.span_singleton_eq_bot]
        exact hr0)
  have hpowSpan :
      (2 : R₂) ^ n ∈
        Ideal.span ({r} : Set R₂) := by
    rw [hn]
    exact Ideal.subset_span (by simp)
  rw [Ideal.mem_span_singleton] at hpowSpan
  obtain ⟨c, hc⟩ := hpowSpan
  have htwoPow :
      algebraMap R₂ IntegralRing ((2 : R₂) ^ n) ∈ I := by
    rw [hc, map_mul]
    exact I.mul_mem_right _ hmI
  have hSpecialOne :
      (1 : SpecialRing) ∈
        Ideal.map reduceCoordinate I := by
    rw [hSpecial]
    simp
  rw [Ideal.mem_map_iff_of_surjective
    reduceCoordinate
    N13GeneralizedMumfordReduction.reduceCoordinate_surjective] at hSpecialOne
  obtain ⟨q, hqI, hqOne⟩ := hSpecialOne
  have hqSub :
      q - 1 ∈ RingHom.ker reduceCoordinate := by
    rw [RingHom.mem_ker, map_sub, hqOne, map_one, sub_self]
  change
    q - 1 ∈
      RingHom.ker
        N13GeneralizedMumfordReduction.reduceCoordinate at hqSub
  rw [N13GeneralizedMumfordReduction.ker_reduceCoordinate,
    Ideal.mem_span_singleton] at hqSub
  obtain ⟨a, ha⟩ := hqSub
  have hq :
      q =
        1 + algebraMap R₂ IntegralRing (2 : R₂) * a := by
    calc
      q = (q - 1) + 1 := by ring
      _ = algebraMap R₂ IntegralRing (2 : R₂) * a + 1 := by
        rw [ha]
      _ = 1 + algebraMap R₂ IntegralRing (2 : R₂) * a := by
        ring
  let x : IntegralRing :=
    -(algebraMap R₂ IntegralRing (2 : R₂) * a)
  have hxPow : x ^ n ∈ I := by
    have hbase :
        (algebraMap R₂ IntegralRing (2 : R₂)) ^ n ∈ I := by
      simpa only [map_pow] using htwoPow
    have hmul :=
      I.mul_mem_right ((-a) ^ n) hbase
    change
      (-(algebraMap R₂ IntegralRing (2 : R₂) * a)) ^ n ∈ I
    rw [show
      -(algebraMap R₂ IntegralRing (2 : R₂) * a) =
        algebraMap R₂ IntegralRing (2 : R₂) * (-a) by ring,
      mul_pow]
    exact hmul
  have hqAs :
      1 - x = q := by
    dsimp only [x]
    rw [hq]
    ring
  have hOneSub : 1 - x ^ n ∈ I := by
    rw [← geom_sum_mul_neg x n, hqAs]
    exact I.mul_mem_left _ hqI
  rw [Ideal.eq_top_iff_one]
  have hadd := I.add_mem hOneSub hxPow
  simpa using hadd

/-- The remaining obstruction to invertibility is purely special-fibre:
once the defect ideal maps onto the special ring, generic invertibility and
the fibre-detection theorem force it to be the unit ideal. -/
theorem isUnit_of_map_defectIdeal_eq_top
    {H : N13IntegralFractionalHull.IntegralFractionalIdeal}
    (hH : H ≠ 0)
    (hGeneric :
      IsUnit
        (N13IntegralFractionalHull.extendFractional H))
    (hSpecial :
      Ideal.map reduceCoordinate
        (N13IntegralFractionalHull.defectIdeal H) = ⊤) :
    IsUnit H := by
  have hDefect :
      N13IntegralFractionalHull.defectIdeal H = ⊤ :=
    eq_top_of_generic_and_special_eq_top
      (N13IntegralFractionalHull.defectIdeal H)
      (N13IntegralFractionalHull.map_defectIdeal_eq_top
        hH hGeneric)
      hSpecial
  exact
    N13IntegralFractionalHull.isUnit_of_defectIdeal_eq_top
      hDefect

/-- The special-fibre condition is equivalent to one concrete integral
trace witness: an element of the defect ideal reducing to one. -/
theorem map_defectIdeal_eq_top_iff_exists
    (H : N13IntegralFractionalHull.IntegralFractionalIdeal) :
    Ideal.map reduceCoordinate
          (N13IntegralFractionalHull.defectIdeal H) = ⊤ ↔
      ∃ z : IntegralRing,
        z ∈ N13IntegralFractionalHull.defectIdeal H ∧
          reduceCoordinate z = 1 := by
  constructor
  · intro htop
    have hone :
        (1 : SpecialRing) ∈
          Ideal.map reduceCoordinate
            (N13IntegralFractionalHull.defectIdeal H) := by
      rw [htop]
      simp
    rw [Ideal.mem_map_iff_of_surjective
      reduceCoordinate
      N13GeneralizedMumfordReduction.reduceCoordinate_surjective] at hone
    exact hone
  · rintro ⟨z, hz, hred⟩
    rw [Ideal.eq_top_iff_one]
    rw [← hred]
    exact Ideal.mem_map_of_mem reduceCoordinate hz

/-- A finite dual frame for a fractional ideal, with integral evaluation
trace reducing to one.  The primal vectors lie in `H`, the dual vectors lie
in the multiplier inverse `H⁻¹`, and their evaluation sum is represented by
one integral affine function.  This is the exact algebraic output expected
from the module-valued Čech construction. -/
structure DefectDualFrame
    (H : IntegralFractionalIdeal) where
  rank : ℕ
  primal : Fin rank → FunctionField
  dual : Fin rank → FunctionField
  primal_mem : ∀ i, primal i ∈ H
  dual_mem : ∀ i, dual i ∈ H⁻¹
  trace : IntegralRing
  algebraMap_trace :
    algebraMap IntegralRing FunctionField trace =
      ∑ i, primal i * dual i
  reduce_trace :
    reduceCoordinate trace = 1

namespace DefectDualFrame

variable {H : IntegralFractionalIdeal}

/-- The evaluation trace of a finite dual frame belongs to the integral
defect ideal. -/
theorem trace_mem_defect
    (F : DefectDualFrame H) :
    F.trace ∈ N13IntegralFractionalHull.defectIdeal H := by
  have hsum :
      (∑ i, F.primal i * F.dual i) ∈ H * H⁻¹ := by
    apply Submodule.sum_mem
    intro i _
    exact
      FractionalIdeal.mul_mem_mul
        (F.primal_mem i) (F.dual_mem i)
  have htrace :
      algebraMap IntegralRing FunctionField F.trace ∈
        (N13IntegralFractionalHull.defectIdeal H :
          IntegralFractionalIdeal) := by
    rw [N13IntegralFractionalHull.coe_defectIdeal,
      F.algebraMap_trace]
    exact hsum
  obtain ⟨z, hz, hzTrace⟩ :=
    (FractionalIdeal.mem_coeIdeal
      (nonZeroDivisors IntegralRing)).mp htrace
  have hzt : z = F.trace :=
    (IsFractionRing.injective IntegralRing FunctionField)
      hzTrace
  simpa [hzt] using hz

/-- A finite dual frame supplies exactly the concrete special trace witness
required by the generic--special fibre criterion. -/
theorem exists_defect_reduces_one
    (F : DefectDualFrame H) :
    ∃ z : IntegralRing,
      z ∈ N13IntegralFractionalHull.defectIdeal H ∧
        reduceCoordinate z = 1 :=
  ⟨F.trace, F.trace_mem_defect, F.reduce_trace⟩

end DefectDualFrame

/-- A finite dual frame stated before reflexive hull: primal vectors lie in
the contracted generic ideal and dual vectors lie in its multiplier inverse.
Triple-inverse stability transports this frame verbatim to the divisorial
hull and its inverse. -/
structure ContractedDualFrame
    (J : Ideal RationalRing) where
  rank : ℕ
  primal : Fin rank → FunctionField
  dual : Fin rank → FunctionField
  primal_mem :
    ∀ i, primal i ∈
      N13IntegralFractionalHull.contractedFractional J
  dual_mem :
    ∀ i, dual i ∈
      (N13IntegralFractionalHull.contractedFractional J)⁻¹
  trace : IntegralRing
  algebraMap_trace :
    algebraMap IntegralRing FunctionField trace =
      ∑ i, primal i * dual i
  reduce_trace :
    reduceCoordinate trace = 1

namespace ContractedDualFrame

variable {J : Ideal RationalRing}

/-- Build the contracted dual frame from finitely many affine primal and
multiplier-inverse lifts together with integral representatives of their
products.  The factors need not extend individually as global sections of
the proper curve. -/
noncomputable def ofProductLifts
    {n : ℕ}
    (primal dual : Fin n → FunctionField)
    (primal_mem :
      ∀ i, primal i ∈
        N13IntegralFractionalHull.contractedFractional J)
    (dual_mem :
      ∀ i, dual i ∈
        (N13IntegralFractionalHull.contractedFractional J)⁻¹)
    (product : Fin n → IntegralRing)
    (algebraMap_product :
      ∀ i,
        algebraMap IntegralRing FunctionField (product i) =
          primal i * dual i)
    (reduce_sum :
      (∑ i, reduceCoordinate (product i)) = 1) :
    ContractedDualFrame J where
  rank := n
  primal := primal
  dual := dual
  primal_mem := primal_mem
  dual_mem := dual_mem
  trace := ∑ i, product i
  algebraMap_trace := by
    rw [map_sum]
    exact Finset.sum_congr rfl
      (fun i _ ↦ algebraMap_product i)
  reduce_trace := by
    rw [map_sum]
    exact reduce_sum

end ContractedDualFrame

/-- Product-level special-fibre detection.  It is enough to lift finitely
many special evaluations into `L * L⁻¹`; no choice of primal and dual
factors is needed on the integral model.  When the generic fibre is
invertible and the reductions sum to one, these witnesses constitute the
entire missing trace-ideal unit certificate; they do not follow from
vertical contraction alone. -/
theorem isUnit_divisorialHull_of_productWitnesses
    {J : Ideal RationalRing}
    (hJ : J ≠ ⊥)
    (hGeneric : IsUnit (J : RationalFractionalIdeal))
    {n : ℕ}
    (product : Fin n → IntegralRing)
    (product_mem :
      ∀ i,
        algebraMap IntegralRing FunctionField (product i) ∈
          N13IntegralFractionalHull.contractedFractional J *
            (N13IntegralFractionalHull.contractedFractional J)⁻¹)
    (reduce_sum :
      (∑ i, reduceCoordinate (product i)) = 1) :
    IsUnit
      (N13IntegralFractionalHull.divisorialHull J) := by
  let H :=
    N13IntegralFractionalHull.divisorialHull J
  have hH : H ≠ 0 := by
    intro hzero
    have hle :=
      N13IntegralFractionalHull.contractedFractional_le_divisorialHull
        hJ
    change
      N13IntegralFractionalHull.contractedFractional J ≤ H at hle
    rw [hzero] at hle
    exact
      N13IntegralFractionalHull.contractedFractional_ne_zero hJ
        (bot_unique hle)
  have hGenericH :
      IsUnit
        (N13IntegralFractionalHull.extendFractional H) := by
    change
      IsUnit
        (N13IntegralFractionalHull.extendFractional
          (N13IntegralFractionalHull.divisorialHull J))
    rw [N13IntegralFractionalHull.extendFractional_divisorialHull_eq
      hJ hGeneric]
    exact hGeneric
  apply isUnit_of_map_defectIdeal_eq_top hH hGenericH
  apply (map_defectIdeal_eq_top_iff_exists H).2
  refine ⟨∑ i, product i, ?_, ?_⟩
  · have hmul_le :
        N13IntegralFractionalHull.contractedFractional J *
              (N13IntegralFractionalHull.contractedFractional J)⁻¹ ≤
            H * H⁻¹ := by
      change
        N13IntegralFractionalHull.contractedFractional J *
              (N13IntegralFractionalHull.contractedFractional J)⁻¹ ≤
            N13IntegralFractionalHull.divisorialHull J *
              (N13IntegralFractionalHull.divisorialHull J)⁻¹
      rw [N13IntegralFractionalHull.divisorialHull_inv hJ]
      exact mul_le_mul'
        (N13IntegralFractionalHull.contractedFractional_le_divisorialHull
          hJ)
        le_rfl
    have htrace :
        algebraMap IntegralRing FunctionField (∑ i, product i) ∈
          (N13IntegralFractionalHull.defectIdeal H :
            IntegralFractionalIdeal) := by
      rw [N13IntegralFractionalHull.coe_defectIdeal, map_sum]
      apply Submodule.sum_mem
      intro i _
      exact hmul_le (product_mem i)
    obtain ⟨z, hz, hzTrace⟩ :=
      (FractionalIdeal.mem_coeIdeal
        (nonZeroDivisors IntegralRing)).mp htrace
    have hzt : z = ∑ i, product i :=
      (IsFractionRing.injective IntegralRing FunctionField)
        hzTrace
    simpa [hzt] using hz
  · rw [map_sum]
    exact reduce_sum

namespace ContractedDualFrame

variable {J : Ideal RationalRing}

/-- A contracted dual frame is already a defect dual frame for the
divisorial hull; no local-freeness theorem is used. -/
def toDefectDualFrame
    (F : ContractedDualFrame J)
    (hJ : J ≠ ⊥) :
    DefectDualFrame
      (N13IntegralFractionalHull.divisorialHull J) where
  rank := F.rank
  primal := F.primal
  dual := F.dual
  primal_mem i :=
    N13IntegralFractionalHull.contractedFractional_le_divisorialHull
      hJ (F.primal_mem i)
  dual_mem i := by
    rw [N13IntegralFractionalHull.divisorialHull_inv hJ]
    exact F.dual_mem i
  trace := F.trace
  algebraMap_trace := F.algebraMap_trace
  reduce_trace := F.reduce_trace

end ContractedDualFrame

/-- Concrete capstone for the affine invertibility problem.  It avoids all
local-factoriality infrastructure: generic invertibility plus one integral
evaluation element reducing to one already make `H` a unit fractional
ideal. -/
theorem isUnit_of_exists_defect_reduces_one
    {H : N13IntegralFractionalHull.IntegralFractionalIdeal}
    (hH : H ≠ 0)
    (hGeneric :
      IsUnit
        (N13IntegralFractionalHull.extendFractional H))
    (hSpecial :
      ∃ z : IntegralRing,
        z ∈ N13IntegralFractionalHull.defectIdeal H ∧
          reduceCoordinate z = 1) :
    IsUnit H :=
  isUnit_of_map_defectIdeal_eq_top
    hH hGeneric
    ((map_defectIdeal_eq_top_iff_exists H).2 hSpecial)

/-- Structural capstone in the form used by Čech duality: a generically
invertible fractional ideal with one finite dual frame reducing to the
identity is already an integral unit fractional ideal. -/
theorem isUnit_of_defectDualFrame
    {H : IntegralFractionalIdeal}
    (hH : H ≠ 0)
    (hGeneric :
      IsUnit
        (N13IntegralFractionalHull.extendFractional H))
    (F : DefectDualFrame H) :
    IsUnit H :=
  isUnit_of_exists_defect_reduces_one
    hH hGeneric F.exists_defect_reduces_one

/-- Final affine-hull criterion in the form needed upstream: an invertible
generic ideal and one contracted dual frame with trace `1 mod 2` make its
divisorial hull an invertible integral fractional ideal. -/
theorem isUnit_divisorialHull_of_contractedDualFrame
    {J : Ideal RationalRing}
    (hJ : J ≠ ⊥)
    (hGeneric :
      IsUnit (J : RationalFractionalIdeal))
    (F : ContractedDualFrame J) :
    IsUnit
      (N13IntegralFractionalHull.divisorialHull J) := by
  have hHull :
      N13IntegralFractionalHull.divisorialHull J ≠ 0 := by
    intro hzero
    have hle :=
      N13IntegralFractionalHull.contractedFractional_le_divisorialHull
        hJ
    rw [hzero] at hle
    exact
      N13IntegralFractionalHull.contractedFractional_ne_zero hJ
        (bot_unique hle)
  have hExtended :
      IsUnit
        (N13IntegralFractionalHull.extendFractional
          (N13IntegralFractionalHull.divisorialHull J)) := by
    rw [N13IntegralFractionalHull.extendFractional_divisorialHull_eq
      hJ hGeneric]
    exact hGeneric
  exact
    isUnit_of_defectDualFrame
      hHull hExtended (F.toDefectDualFrame hJ)

end

end MazurProof.N13IntegralFiberDetection


