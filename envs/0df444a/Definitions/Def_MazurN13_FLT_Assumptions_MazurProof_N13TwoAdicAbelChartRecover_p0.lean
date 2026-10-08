-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13TwoAdicAbelChartRecover_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13TwoAdicAbelChartRecover_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T23:15:04.499374+00:00
-- url     : https://prove2.me/theorems/e7bae953-5ae1-4173-8295-5fa28d9747f7
-- title:
--   FLT.Assumptions.MazurProof.N13TwoAdicAbelChartRecover source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13TwoAdicAbelChartRecover

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13TwoAdicAbelChartRecover
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13TwoAdicAbelChartData_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13TwoAdicAbelChartPic_p0
import Mathlib.RingTheory.Henselian

set_option autoImplicit false




/-!
# Recovering the N13 two-disk divisor from an integral Mumford graph

Suppose a smooth integral generalized Mumford graph reduces to the fixed
nonspecial graph `(X² + X, 0)`.  Hensel lifting splits its monic quadratic
into one root in each of the residue disks of `0` and `-1`.  Evaluating the
curve relation at those roots and using uniqueness in the vertical Hensel
fibres identifies the graph values with the canonical disk lifts.

Consequently every such integral graph comes from a unique `DiskPair`, up
to the harmless operation of changing its graph polynomial by a multiple
of `u`.  This is the algebraic reverse of
`N13TwoAdicAbelChartData.DiskPair.smoothMumford`; no divisor enumeration or
properness shortcut is used.
-/

open Polynomial
open scoped nonZeroDivisors

namespace MazurProof.N13TwoAdicAbelChartRecover

noncomputable section

local instance instFactPrimeOfNatNat_fLT : Fact (Nat.Prime 2) :=
  ⟨Nat.prime_two⟩

abbrev R₂ : Type :=
  ℤ_[2]

abbrev K : Type :=
  N13GoodCoordinateRingTwo.K

abbrev Q₂ : Type :=
  ℚ_[2]

abbrev Pic : Type :=
  N13TwoAdicAbelChartPic.Pic

abbrev maximal : Ideal R₂ :=
  IsLocalRing.maximalIdeal R₂

/-- Smooth integral Mumford data whose graph has the selected nonspecial
special fibre. -/
structure NearBaseMumford
    extends N13GeneralizedMumfordReduction.SmoothMumford₂ where
  reduce_u :
    N13GeneralizedMumfordReduction.reducePoly u =
      (X ^ 2 + X : K[X])
  reduce_v :
    N13GeneralizedMumfordReduction.reducePoly v = 0

namespace NearBaseMumford

variable (D : NearBaseMumford)

/-- Every two-disk divisor gives near-base integral data. -/
def ofDiskPair
    (P : N13TwoAdicAbelChartData.DiskPair) :
    NearBaseMumford where
  toSmoothMumford₂ := P.smoothMumford
  reduce_u := P.reducePoly_u
  reduce_v := P.reducePoly_v

@[simp] theorem ofDiskPair_u
    (P : N13TwoAdicAbelChartData.DiskPair) :
    (ofDiskPair P).u = P.u := rfl

@[simp] theorem ofDiskPair_v
    (P : N13TwoAdicAbelChartData.DiskPair) :
    (ofDiskPair P).v = P.v := rfl

theorem mem_maximal_iff_reduceBase_eq_zero
    (a : R₂) :
    a ∈ maximal ↔
      N13GeneralizedMumfordReduction.reduceBase a = 0 := by
  constructor
  · intro ha
    have hker :
        a ∈ RingHom.ker (PadicInt.toZMod : R₂ →+* K) := by
      rw [PadicInt.ker_toZMod]
      exact ha
    exact RingHom.mem_ker.mp hker
  · intro ha
    have hker :
        a ∈ RingHom.ker (PadicInt.toZMod : R₂ →+* K) :=
      RingHom.mem_ker.mpr ha
    rw [PadicInt.ker_toZMod] at hker
    exact hker

theorem isUnit_of_reduceBase_eq_one
    {a : R₂}
    (ha :
      N13GeneralizedMumfordReduction.reduceBase a = 1) :
    IsUnit a := by
  apply N13TwoAdicDisks.isUnit_of_sub_mem_maximal isUnit_one
  apply (mem_maximal_iff_reduceBase_eq_zero (a - 1)).2
  rw [map_sub, ha, map_one, sub_self]

theorem reduceBase_eval
    (p : R₂[X]) (a : R₂) :
    N13GeneralizedMumfordReduction.reduceBase (p.eval a) =
      (N13GeneralizedMumfordReduction.reducePoly p).eval
        (N13GeneralizedMumfordReduction.reduceBase a) := by
  rw [N13GeneralizedMumfordReduction.reducePoly_apply,
    Polynomial.eval_map_apply]

theorem reduceBase_derivative_eval
    (p : R₂[X]) (a : R₂) :
    N13GeneralizedMumfordReduction.reduceBase
        (p.derivative.eval a) =
      (N13GeneralizedMumfordReduction.reducePoly p).derivative.eval
        (N13GeneralizedMumfordReduction.reduceBase a) := by
  rw [N13GeneralizedMumfordReduction.reducePoly_apply,
    Polynomial.derivative_map, Polynomial.eval_map_apply]

theorem u_eval_zero_mem :
    D.u.eval 0 ∈ maximal := by
  apply (mem_maximal_iff_reduceBase_eq_zero _).2
  rw [reduceBase_eval, D.reduce_u]
  have htwo : (2 : K) = 0 := CharP.cast_eq_zero K 2
  norm_num [N13GeneralizedMumfordReduction.reduceBase, htwo]

theorem u_eval_negOne_mem :
    D.u.eval (-1) ∈ maximal := by
  apply (mem_maximal_iff_reduceBase_eq_zero _).2
  rw [reduceBase_eval, D.reduce_u]
  have htwo : (2 : K) = 0 := CharP.cast_eq_zero K 2
  norm_num [N13GeneralizedMumfordReduction.reduceBase, htwo]
  exact htwo

theorem derivative_eval_zero_isUnit :
    IsUnit (D.u.derivative.eval 0) := by
  apply isUnit_of_reduceBase_eq_one
  rw [reduceBase_derivative_eval, D.reduce_u]
  have htwo : (2 : K) = 0 := CharP.cast_eq_zero K 2
  norm_num [N13GeneralizedMumfordReduction.reduceBase, htwo]

theorem derivative_eval_negOne_isUnit :
    IsUnit (D.u.derivative.eval (-1)) := by
  apply isUnit_of_reduceBase_eq_one
  rw [reduceBase_derivative_eval, D.reduce_u]
  have htwo : (2 : K) = 0 := CharP.cast_eq_zero K 2
  norm_num [N13GeneralizedMumfordReduction.reduceBase, htwo]
  linear_combination htwo

/-- The root of `u` in the residue disk of zero. -/
theorem exists_root_zeroDisk :
    ∃ x : R₂, D.u.eval x = 0 ∧ x ∈ maximal := by
  obtain ⟨x, hx, hxmem⟩ :=
    HenselianRing.is_henselian
      D.u D.u_monic 0 D.u_eval_zero_mem
      (D.derivative_eval_zero_isUnit.map
        (Ideal.Quotient.mk maximal))
  refine ⟨x, ?_, by simpa using hxmem⟩
  exact hx

/-- The root of `u` in the residue disk of `-1`. -/
theorem exists_root_negOneDisk :
    ∃ x : R₂, D.u.eval x = 0 ∧ x + 1 ∈ maximal := by
  obtain ⟨x, hx, hxmem⟩ :=
    HenselianRing.is_henselian
      D.u D.u_monic (-1) D.u_eval_negOne_mem
      (D.derivative_eval_negOne_isUnit.map
        (Ideal.Quotient.mk maximal))
  refine ⟨x, ?_, by simpa using hxmem⟩
  exact hx

/-- The two Hensel roots, selected in their distinct residue disks. -/
def x₀ : R₂ :=
  Classical.choose D.exists_root_zeroDisk

def x₁ : R₂ :=
  Classical.choose D.exists_root_negOneDisk

theorem x₀_spec :
    D.u.eval D.x₀ = 0 ∧ D.x₀ ∈ maximal :=
  Classical.choose_spec D.exists_root_zeroDisk

theorem x₁_spec :
    D.u.eval D.x₁ = 0 ∧ D.x₁ + 1 ∈ maximal :=
  Classical.choose_spec D.exists_root_negOneDisk

/-- The disk pair cut out by the two Hensel factors of `u`. -/
def diskPair :
    N13TwoAdicAbelChartData.DiskPair where
  x₀ := D.x₀
  x₁ := D.x₁
  x₀_mem := D.x₀_spec.2
  x₁_add_one_mem := D.x₁_spec.2

@[simp] theorem diskPair_x₀ :
    D.diskPair.x₀ = D.x₀ := rfl

@[simp] theorem diskPair_x₁ :
    D.diskPair.x₁ = D.x₁ := rfl

theorem u_natDegree :
    D.u.natDegree = 2 := by
  calc
    D.u.natDegree =
        (D.u.map
          N13GeneralizedMumfordReduction.reduceBase).natDegree :=
      (D.u_monic.natDegree_map
        N13GeneralizedMumfordReduction.reduceBase).symm
    _ =
        (N13GeneralizedMumfordReduction.reducePoly D.u).natDegree := rfl
    _ = (X ^ 2 + X : K[X]).natDegree := by rw [D.reduce_u]
    _ = 2 := by
      compute_degree
      norm_num [K, N13GoodCoordinateRingTwo.K,
        N13GoodModelTwo.F2]

theorem diskPair_u_natDegree :
    D.diskPair.u.natDegree = 2 := by
  rw [N13TwoAdicAbelChartData.DiskPair.u,
    Polynomial.natDegree_mul
      (monic_X_sub_C D.diskPair.x₀).ne_zero
      (monic_X_sub_C D.diskPair.x₁).ne_zero]
  simp

theorem diskPair_u_dvd :
    D.diskPair.u ∣ D.u := by
  have h₀ : X - C D.diskPair.x₀ ∣ D.u := by
    rw [dvd_iff_isRoot, IsRoot, D.diskPair_x₀]
    exact D.x₀_spec.1
  have h₁ : X - C D.diskPair.x₁ ∣ D.u := by
    rw [dvd_iff_isRoot, IsRoot, D.diskPair_x₁]
    exact D.x₁_spec.1
  have hprod :=
    (isCoprime_X_sub_C_of_isUnit_sub
      D.diskPair.x₁_sub_x₀_isUnit).mul_dvd h₁ h₀
  simpa [N13TwoAdicAbelChartData.DiskPair.u, mul_comm] using hprod

/-- The recovered disk pair has exactly the original monic quadratic. -/
theorem diskPair_u :
    D.diskPair.u = D.u := by
  exact
    (Polynomial.eq_of_monic_of_dvd_of_natDegree_le
      D.diskPair.u_monic D.u_monic D.diskPair_u_dvd
      (by rw [D.u_natDegree, D.diskPair_u_natDegree])).symm

theorem v_eval_mem_maximal
    (x : R₂) :
    D.v.eval x ∈ maximal := by
  apply (mem_maximal_iff_reduceBase_eq_zero _).2
  rw [reduceBase_eval, D.reduce_v]
  simp

theorem v_eval_on_curve
    {x : R₂} (hx : D.u.eval x = 0) :
    N13GoodModelTwo.AffineEquation x (D.v.eval x) := by
  have h :=
    congrArg (fun p : R₂[X] => p.eval x) D.curve_eq
  simp only [eval_sub, eval_add, eval_pow, eval_mul] at h
  rw [hx, zero_mul] at h
  rw [N13GoodModelTwo.affineEquation_iff_residual]
  simpa [N13GoodModelTwo.affineResidual,
    N13GoodModelTwo.h, N13GoodModelTwo.rhs,
    N13GeneralizedMumfordIntegral.hPoly,
    N13GeneralizedMumfordIntegral.rhsPoly] using h

theorem v_eval_x₀ :
    D.v.eval D.diskPair.x₀ = D.diskPair.y₀ := by
  exact
    N13TwoAdicDisks.y_eq_zeroDiskY
      D.diskPair.x₀ D.diskPair.x₀_mem
      (D.v_eval_on_curve (by
        rw [D.diskPair_x₀]
        exact D.x₀_spec.1))
      (D.v_eval_mem_maximal D.diskPair.x₀)

theorem v_eval_x₁ :
    D.v.eval D.diskPair.x₁ = D.diskPair.y₁ := by
  exact
    N13TwoAdicDisks.y_eq_negOneDiskY
      D.diskPair.x₁ D.diskPair.x₁_add_one_mem
      (D.v_eval_on_curve (by
        rw [D.diskPair_x₁]
        exact D.x₁_spec.1))
      (D.v_eval_mem_maximal D.diskPair.x₁)

/-- The original graph polynomial and the recovered interpolant agree
modulo the recovered quadratic. -/
theorem diskPair_u_dvd_v_sub :
    D.diskPair.u ∣ D.v - D.diskPair.v := by
  have h₀ :
      X - C D.diskPair.x₀ ∣ D.v - D.diskPair.v := by
    rw [dvd_iff_isRoot, IsRoot, eval_sub,
      D.v_eval_x₀,
      N13TwoAdicAbelChartData.DiskPair.v_eval_x₀,
      sub_self]
  have h₁ :
      X - C D.diskPair.x₁ ∣ D.v - D.diskPair.v := by
    rw [dvd_iff_isRoot, IsRoot, eval_sub,
      D.v_eval_x₁,
      N13TwoAdicAbelChartData.DiskPair.v_eval_x₁,
      sub_self]
  have hprod :=
    (isCoprime_X_sub_C_of_isUnit_sub
      D.diskPair.x₁_sub_x₀_isUnit).mul_dvd h₁ h₀
  simpa [N13TwoAdicAbelChartData.DiskPair.u, mul_comm] using hprod

theorem u_dvd_v_sub_diskPair_v :
    D.u ∣ D.v - D.diskPair.v := by
  rw [← D.diskPair_u]
  exact D.diskPair_u_dvd_v_sub

/-- Generalized Mumford graph ideals only depend on `v` modulo `u`. -/
theorem mumfordIdeal_eq_of_dvd_sub
    (u v w : R₂[X]) (hvw : u ∣ v - w) :
    N13GeneralizedMumfordIntegral.mumfordIdeal u v =
      N13GeneralizedMumfordIntegral.mumfordIdeal u w := by
  obtain ⟨q, hq⟩ := hvw
  have hmultiple :
      N13GeneralizedMumfordIntegral.xClass (v - w) =
        N13GeneralizedMumfordIntegral.xClass u *
          N13GeneralizedMumfordIntegral.xClass q := by
    rw [hq, N13GeneralizedMumfordIntegral.xClass_mul]
  have hyw :
      N13GeneralizedMumfordIntegral.ySubClass w =
        N13GeneralizedMumfordIntegral.ySubClass v +
          N13GeneralizedMumfordIntegral.xClass (v - w) := by
    simp [N13GeneralizedMumfordIntegral.ySubClass]
  have hyv :
      N13GeneralizedMumfordIntegral.ySubClass v =
        N13GeneralizedMumfordIntegral.ySubClass w -
          N13GeneralizedMumfordIntegral.xClass (v - w) := by
    rw [hyw]
    ring
  apply le_antisymm
  · apply Ideal.span_le.2
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact
        N13GeneralizedMumfordIntegral.xClass_mem_mumfordIdeal u w
    · rw [hyv, hmultiple]
      exact Ideal.sub_mem _
        (N13GeneralizedMumfordIntegral.ySubClass_mem_mumfordIdeal u w)
        (by
          simpa only [mul_comm] using
            Ideal.mul_mem_left
              (N13GeneralizedMumfordIntegral.mumfordIdeal u w)
              (N13GeneralizedMumfordIntegral.xClass q)
              (N13GeneralizedMumfordIntegral.xClass_mem_mumfordIdeal u w))
  · apply Ideal.span_le.2
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact
        N13GeneralizedMumfordIntegral.xClass_mem_mumfordIdeal u v
    · rw [hyw, hmultiple]
      exact Ideal.add_mem _
        (N13GeneralizedMumfordIntegral.ySubClass_mem_mumfordIdeal u v)
        (by
          simpa only [mul_comm] using
            Ideal.mul_mem_left
              (N13GeneralizedMumfordIntegral.mumfordIdeal u v)
              (N13GeneralizedMumfordIntegral.xClass q)
              (N13GeneralizedMumfordIntegral.xClass_mem_mumfordIdeal u v))

/-- The recovered disk pair cuts out exactly the original integral graph
ideal. -/
theorem mumfordIdeal_diskPair :
    N13GeneralizedMumfordIntegral.mumfordIdeal D.u D.v =
      N13GeneralizedMumfordIntegral.mumfordIdeal
        D.diskPair.u D.diskPair.v := by
  rw [D.diskPair_u]
  exact mumfordIdeal_eq_of_dvd_sub
    D.u D.v D.diskPair.v D.u_dvd_v_sub_diskPair_v

/-- Completion of the square carries the original graph and the recovered
disk graph to the same standard sextic Mumford ideal. -/
theorem sextic_mumfordIdeal_diskPair :
    SexticMumford.mumfordIdeal
        (N13Mumford.model Q₂)
        (N13TwoAdicMumfordTransport.sexticSemi
          D.toSmoothMumford₂ 0).u
        (N13TwoAdicMumfordTransport.sexticSemi
          D.toSmoothMumford₂ 0).v =
      SexticMumford.mumfordIdeal
        (N13Mumford.model Q₂)
        (N13TwoAdicMumfordTransport.sexticSemi
          D.diskPair.smoothMumford 0).u
        (N13TwoAdicMumfordTransport.sexticSemi
          D.diskPair.smoothMumford 0).v := by
  rw [
    ← N13TwoAdicCoordinateBaseChange.map_mumfordIdeal_sexticSemi
      D.toSmoothMumford₂ 0,
    ← N13TwoAdicCoordinateBaseChange.map_mumfordIdeal_sexticSemi
      D.diskPair.smoothMumford 0]
  exact congrArg
    (Ideal.map N13TwoAdicCoordinateBaseChange.integralToSextic)
    D.mumfordIdeal_diskPair

theorem sextic_mumfordIdealUnit_diskPair :
    SexticMumford.mumfordIdealUnit
        (N13Mumford.model Q₂)
        (N13TwoAdicMumfordTransport.sexticSemi
          D.toSmoothMumford₂ 0) =
      SexticMumford.mumfordIdealUnit
        (N13Mumford.model Q₂)
        (N13TwoAdicMumfordTransport.sexticSemi
          D.diskPair.smoothMumford 0) := by
  apply Units.ext
  change
    (SexticMumford.mumfordIdeal
        (N13Mumford.model Q₂)
        (N13TwoAdicMumfordTransport.sexticSemi
          D.toSmoothMumford₂ 0).u
        (N13TwoAdicMumfordTransport.sexticSemi
          D.toSmoothMumford₂ 0).v :
      FractionalIdeal
        (N13Mumford.CoordinateRing Q₂)⁰
        (N13Mumford.FunctionField Q₂)) =
      SexticMumford.mumfordIdeal
        (N13Mumford.model Q₂)
        (N13TwoAdicMumfordTransport.sexticSemi
          D.diskPair.smoothMumford 0).u
        (N13TwoAdicMumfordTransport.sexticSemi
          D.diskPair.smoothMumford 0).v
  rw [D.sextic_mumfordIdeal_diskPair]

/-- The oriented two-adic Picard class carried by a near-base integral
graph. -/
def pic : Pic :=
  SexticMumford.semiMumfordClass
    (N13Mumford.model Q₂)
    (N13Infinity.positiveInfinityOrder Q₂)
    (N13TwoAdicMumfordTransport.sexticSemi
      D.toSmoothMumford₂ 0)

/-- Recovery is compatible with the actual oriented Picard class. -/
theorem pic_eq_diskPair_pic :
    D.pic =
      N13TwoAdicAbelChartPic.DiskPair.pic D.diskPair := by
  change
    SexticMumford.semiMumfordClass
        (N13Mumford.model Q₂)
        (N13Infinity.positiveInfinityOrder Q₂)
        (N13TwoAdicMumfordTransport.sexticSemi
          D.toSmoothMumford₂ 0) =
      SexticMumford.classOf
        (N13Mumford.model Q₂)
        (N13Infinity.positiveInfinityOrder Q₂)
        (N13TwoAdicAbelChartPic.DiskPair.mumford D.diskPair)
  rw [← SexticMumford.semiMumfordClass_toSemi]
  change
    SexticMumford.semiMumfordClass
        (N13Mumford.model Q₂)
        (N13Infinity.positiveInfinityOrder Q₂)
        (N13TwoAdicMumfordTransport.sexticSemi
          D.toSmoothMumford₂ 0) =
      SexticMumford.semiMumfordClass
        (N13Mumford.model Q₂)
        (N13Infinity.positiveInfinityOrder Q₂)
        (N13TwoAdicMumfordTransport.sexticSemi
          D.diskPair.smoothMumford 0)
  unfold SexticMumford.semiMumfordClass
  congr 2
  apply Prod.ext
  · exact D.sextic_mumfordIdealUnit_diskPair
  · rfl

/-- Centre the integral graph class at the selected base divisor. -/
def centeredPic : Pic :=
  D.pic -
    N13TwoAdicAbelChartPic.DiskPair.pic
      N13TwoAdicAbelChartData.basePair

theorem centeredPic_eq_diskPair_centeredPic :
    D.centeredPic =
      N13TwoAdicAbelChartPic.DiskPair.centeredPic D.diskPair := by
  rw [centeredPic,
    N13TwoAdicAbelChartPic.DiskPair.centeredPic,
    D.pic_eq_diskPair_pic]

/-- The disk pair associated with a near-base graph is unique. -/
theorem existsUnique_diskPair :
    ∃! P : N13TwoAdicAbelChartData.DiskPair,
      P.u = D.u ∧ D.u ∣ D.v - P.v := by
  refine
    ⟨D.diskPair,
      ⟨D.diskPair_u, D.u_dvd_v_sub_diskPair_v⟩, ?_⟩
  intro P hP
  apply N13TwoAdicAbelChartData.DiskPair.u_injective
  exact hP.1.trans D.diskPair_u.symm

@[simp] theorem diskPair_ofDiskPair
    (P : N13TwoAdicAbelChartData.DiskPair) :
    (ofDiskPair P).diskPair = P := by
  apply N13TwoAdicAbelChartData.DiskPair.u_injective
  rw [(ofDiskPair P).diskPair_u]
  rfl

@[simp] theorem pic_ofDiskPair
    (P : N13TwoAdicAbelChartData.DiskPair) :
    (ofDiskPair P).pic =
      N13TwoAdicAbelChartPic.DiskPair.pic P := by
  rw [(ofDiskPair P).pic_eq_diskPair_pic, diskPair_ofDiskPair]

@[simp] theorem centeredPic_ofDiskPair
    (P : N13TwoAdicAbelChartData.DiskPair) :
    (ofDiskPair P).centeredPic =
      N13TwoAdicAbelChartPic.DiskPair.centeredPic P := by
  rw [(ofDiskPair P).centeredPic_eq_diskPair_centeredPic,
    diskPair_ofDiskPair]

end NearBaseMumford

end

end MazurProof.N13TwoAdicAbelChartRecover


