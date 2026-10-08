-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_GraphJacobianDualFrame_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_GraphJacobianDualFrame_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T21:45:15.857651+00:00
-- url     : https://prove2.me/theorems/0d11c63d-6813-40d7-90e0-e4c7d0549749
-- title:
--   FLT.Assumptions.MazurProof.GraphJacobianDualFrame source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.GraphJacobianDualFrame

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.GraphJacobianDualFrame
Original leading source comments and nonproject imports are retained below. -/
import Mathlib.RingTheory.FractionalIdeal.Inverse
import Mathlib.RingTheory.Ideal.Span
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

set_option autoImplicit false




/-!
# A Jacobian dual frame for a graph ideal

For a graph ideal `(U,G)`, the factorization

`G * Gbar = -(U * W)`

places `-Gbar/U` in the multiplier inverse.  If two Jacobian rows generate
one, their graph decompositions then give an explicit two-term dual frame.
This proves invertibility without Noetherian, regular-local, divisor-class,
or special-fibre arguments.
-/

open scoped nonZeroDivisors

namespace MazurProof.GraphJacobianDualFrame

noncomputable section

variable {A K : Type*}
variable [CommRing A] [IsDomain A]
variable [Field K] [Algebra A K] [IsFractionRing A K]

/-- A graph factorization and a global Jacobian Bézout identity produce an
explicit dual frame, hence an invertible graph fractional ideal. -/
theorem graphJacobian_isUnit
    (U G Gbar W Fy Fx Ux Wx Vx hx a b : A)
    (hU : U ≠ 0)
    (hGGbar : G * Gbar = -(U * W))
    (hFy : Fy = G + Gbar)
    (hFx :
      Fx =
        Ux * W + U * Wx - Vx * Gbar +
          (hx + Vx) * G)
    (hBez : a * Fx + b * Fy = 1) :
    IsUnit
      ((Ideal.span ({U, G} : Set A) : Ideal A) :
        FractionalIdeal A⁰ K) := by
  let M : Ideal A :=
    Ideal.span ({U, G} : Set A)
  let I : FractionalIdeal A⁰ K :=
    (M : FractionalIdeal A⁰ K)
  have hU_M : U ∈ M := by
    dsimp only [M]
    exact Ideal.subset_span (by simp)
  have hG_M : G ∈ M := by
    dsimp only [M]
    exact Ideal.subset_span (by simp)
  have hU_I : algebraMap A K U ∈ I := by
    simpa only [I] using
      (FractionalIdeal.mem_coeIdeal_of_mem A⁰ hU_M)
  have hG_I : algebraMap A K G ∈ I := by
    simpa only [I] using
      (FractionalIdeal.mem_coeIdeal_of_mem A⁰ hG_M)
  have hI_le_one : I ≤ 1 := by
    dsimp only [I]
    exact FractionalIdeal.coeIdeal_le_one
  have hI_ne : I ≠ 0 := by
    intro hI0
    have hmapU0 : algebraMap A K U = 0 :=
      (FractionalIdeal.eq_zero_iff.mp hI0)
        (algebraMap A K U) hU_I
    exact hU
      (IsFractionRing.to_map_eq_zero_iff.mp hmapU0)
  have hmapU_ne : algebraMap A K U ≠ 0 := by
    intro hmapU0
    exact hU
      (IsFractionRing.to_map_eq_zero_iff.mp hmapU0)
  have hGGbarK :
      algebraMap A K G * algebraMap A K Gbar =
        -(algebraMap A K U * algebraMap A K W) := by
    simpa only [map_mul, map_neg] using
      congrArg (algebraMap A K) hGGbar
  let z : K :=
    -algebraMap A K Gbar / algebraMap A K U
  have hzU :
      z * algebraMap A K U =
        -algebraMap A K Gbar := by
    dsimp only [z]
    field_simp [hmapU_ne]
  have hzG :
      z * algebraMap A K G =
        algebraMap A K W := by
    calc
      z * algebraMap A K G =
          -(algebraMap A K Gbar *
              algebraMap A K G) /
            algebraMap A K U := by
              dsimp only [z]
              ring
      _ =
          -(algebraMap A K G *
              algebraMap A K Gbar) /
            algebraMap A K U := by
              ring
      _ =
          -(-(algebraMap A K U *
              algebraMap A K W)) /
            algebraMap A K U := by
              rw [hGGbarK]
      _ = algebraMap A K W := by
            field_simp [hmapU_ne]
  have hz_mem : z ∈ I⁻¹ := by
    rw [FractionalIdeal.mem_inv_iff hI_ne]
    intro y hy
    change
      y ∈ (M : FractionalIdeal A⁰ K) at hy
    rw [FractionalIdeal.mem_coeIdeal A⁰] at hy
    obtain ⟨yA, hyA, hyEq⟩ := hy
    subst y
    obtain ⟨c, d, hcd⟩ :=
      Ideal.mem_span_pair.mp
        (by simpa only [M] using hyA)
    rw [FractionalIdeal.mem_one_iff A⁰]
    refine ⟨-c * Gbar + d * W, ?_⟩
    calc
      algebraMap A K (-c * Gbar + d * W) =
          algebraMap A K c *
              (-algebraMap A K Gbar) +
            algebraMap A K d *
              algebraMap A K W := by
                simp only [map_add, map_mul, map_neg]
                ring
      _ =
          algebraMap A K c *
              (z * algebraMap A K U) +
            algebraMap A K d *
              (z * algebraMap A K G) := by
                rw [← hzU, ← hzG]
      _ =
          z * algebraMap A K
            (c * U + d * G) := by
              simp only [map_add, map_mul]
              ring
      _ = z * algebraMap A K yA := by
            rw [hcd]
  have hone_inv : (1 : K) ∈ I⁻¹ := by
    rw [FractionalIdeal.mem_inv_iff hI_ne]
    intro y hy
    simpa only [one_mul] using hI_le_one hy
  have hIntegral (r : A) :
      algebraMap A K r ∈ I⁻¹ := by
    have hr :=
      (((I⁻¹ : FractionalIdeal A⁰ K) :
        Submodule A K).smul_mem r hone_inv)
    simpa only [FractionalIdeal.mem_coe,
      Algebra.smul_def, mul_one] using hr
  have hScalarZ (r : A) :
      algebraMap A K r * z ∈ I⁻¹ := by
    have hr :=
      (((I⁻¹ : FractionalIdeal A⁰ K) :
        Submodule A K).smul_mem r hz_mem)
    simpa only [FractionalIdeal.mem_coe,
      Algebra.smul_def] using hr
  let tU : K :=
    algebraMap A K a *
        (algebraMap A K Wx +
          algebraMap A K Vx * z) -
      algebraMap A K b * z
  let tG : K :=
    algebraMap A K a *
        (algebraMap A K Ux * z +
          algebraMap A K hx +
          algebraMap A K Vx) +
      algebraMap A K b
  have htU : tU ∈ I⁻¹ := by
    have hinner :
        algebraMap A K Wx +
            algebraMap A K Vx * z ∈ I⁻¹ :=
      (((I⁻¹ : FractionalIdeal A⁰ K) :
        Submodule A K).add_mem
        (hIntegral Wx) (hScalarZ Vx))
    have hscaled :
        algebraMap A K a *
            (algebraMap A K Wx +
              algebraMap A K Vx * z) ∈ I⁻¹ := by
      simpa only [FractionalIdeal.mem_coe,
        Algebra.smul_def] using
        (((I⁻¹ : FractionalIdeal A⁰ K) :
          Submodule A K).smul_mem a hinner)
    simpa only [FractionalIdeal.mem_coe, tU] using
      (((I⁻¹ : FractionalIdeal A⁰ K) :
        Submodule A K).sub_mem
        hscaled (hScalarZ b))
  have htG : tG ∈ I⁻¹ := by
    have hinner :
        algebraMap A K Ux * z +
            algebraMap A K hx +
            algebraMap A K Vx ∈ I⁻¹ :=
      (((I⁻¹ : FractionalIdeal A⁰ K) :
        Submodule A K).add_mem
        (((I⁻¹ : FractionalIdeal A⁰ K) :
          Submodule A K).add_mem
          (hScalarZ Ux) (hIntegral hx))
        (hIntegral Vx))
    have hscaled :
        algebraMap A K a *
            (algebraMap A K Ux * z +
              algebraMap A K hx +
              algebraMap A K Vx) ∈ I⁻¹ := by
      simpa only [FractionalIdeal.mem_coe,
        Algebra.smul_def] using
        (((I⁻¹ : FractionalIdeal A⁰ K) :
          Submodule A K).smul_mem a hinner)
    simpa only [FractionalIdeal.mem_coe, tG] using
      (((I⁻¹ : FractionalIdeal A⁰ K) :
        Submodule A K).add_mem
        hscaled (hIntegral b))
  have hGbarK :
      algebraMap A K Gbar =
        -(z * algebraMap A K U) := by
    rw [hzU]
    ring
  have hWK :
      algebraMap A K W =
        z * algebraMap A K G :=
    hzG.symm
  have hFxK :
      algebraMap A K Fx =
        algebraMap A K Ux * algebraMap A K W +
          algebraMap A K U * algebraMap A K Wx -
          algebraMap A K Vx *
            algebraMap A K Gbar +
          (algebraMap A K hx +
              algebraMap A K Vx) *
            algebraMap A K G := by
    simpa only [map_add, map_sub, map_mul] using
      congrArg (algebraMap A K) hFx
  have hFx_decomp :
      algebraMap A K Fx =
        algebraMap A K U *
            (algebraMap A K Wx +
              algebraMap A K Vx * z) +
          algebraMap A K G *
            (algebraMap A K Ux * z +
              algebraMap A K hx +
              algebraMap A K Vx) := by
    calc
      algebraMap A K Fx =
          algebraMap A K Ux *
              algebraMap A K W +
            algebraMap A K U *
              algebraMap A K Wx -
            algebraMap A K Vx *
              algebraMap A K Gbar +
            (algebraMap A K hx +
                algebraMap A K Vx) *
              algebraMap A K G :=
        hFxK
      _ =
          algebraMap A K U *
              (algebraMap A K Wx +
                algebraMap A K Vx * z) +
            algebraMap A K G *
              (algebraMap A K Ux * z +
                algebraMap A K hx +
                algebraMap A K Vx) := by
              rw [hWK, hGbarK]
              ring
  have hFyK :
      algebraMap A K Fy =
        algebraMap A K G +
          algebraMap A K Gbar := by
    simpa only [map_add] using
      congrArg (algebraMap A K) hFy
  have hFy_decomp :
      algebraMap A K Fy =
        algebraMap A K U * (-z) +
          algebraMap A K G := by
    calc
      algebraMap A K Fy =
          algebraMap A K G +
            algebraMap A K Gbar :=
        hFyK
      _ =
          algebraMap A K U * (-z) +
            algebraMap A K G := by
              rw [hGbarK]
              ring
  have hBezK :
      algebraMap A K a *
            algebraMap A K Fx +
          algebraMap A K b *
            algebraMap A K Fy = 1 := by
    simpa only [map_add, map_mul, map_one] using
      congrArg (algebraMap A K) hBez
  have hframe :
      algebraMap A K U * tU +
          algebraMap A K G * tG = 1 := by
    calc
      algebraMap A K U * tU +
            algebraMap A K G * tG =
          algebraMap A K a *
              (algebraMap A K U *
                  (algebraMap A K Wx +
                    algebraMap A K Vx * z) +
                algebraMap A K G *
                  (algebraMap A K Ux * z +
                    algebraMap A K hx +
                    algebraMap A K Vx)) +
            algebraMap A K b *
              (algebraMap A K U * (-z) +
                algebraMap A K G) := by
                dsimp only [tU, tG]
                ring
      _ =
          algebraMap A K a *
              algebraMap A K Fx +
            algebraMap A K b *
              algebraMap A K Fy := by
                rw [← hFx_decomp, ← hFy_decomp]
      _ = 1 := hBezK
  have hmul_le : I * I⁻¹ ≤ 1 := by
    rw [FractionalIdeal.mul_le]
    intro x hx y hy
    have hxy :=
      (FractionalIdeal.mem_inv_iff hI_ne).mp
        hy x hx
    simpa only [mul_comm] using hxy
  have hone_le : 1 ≤ I * I⁻¹ := by
    rw [FractionalIdeal.one_le, ← hframe]
    simpa only [FractionalIdeal.mem_coe] using
      (((I * I⁻¹ : FractionalIdeal A⁰ K) :
        Submodule A K).add_mem
          (FractionalIdeal.mul_mem_mul hU_I htU)
          (FractionalIdeal.mul_mem_mul hG_I htG))
  have hmul_eq : I * I⁻¹ = 1 :=
    le_antisymm hmul_le hone_le
  have hunitI : IsUnit I :=
    (FractionalIdeal.mul_inv_cancel_iff_isUnit K).mp
      hmul_eq
  simpa only [I, M] using hunitI

end

end MazurProof.GraphJacobianDualFrame


