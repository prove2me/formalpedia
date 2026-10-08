-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_GraphJacobianDecompositionFrame_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_GraphJacobianDecompositionFrame_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T21:45:37.668121+00:00
-- url     : https://prove2.me/theorems/2bd0dc8d-6c3b-498e-87c2-6b654a40ac38
-- title:
--   FLT.Assumptions.MazurProof.GraphJacobianDecompositionFrame source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.GraphJacobianDecompositionFrame

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.GraphJacobianDecompositionFrame
Original leading source comments and nonproject imports are retained below. -/
import Mathlib.RingTheory.FractionalIdeal.Inverse
import Mathlib.RingTheory.Ideal.Span
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

set_option autoImplicit false




open scoped nonZeroDivisors

/-!
# A decomposition form of the graph-Jacobian dual frame

For a two-generated ideal `(U,G)`, a complementary factorization
`G H = -U W` puts both integral scalars and integral multiples of
`-H/U` in the inverse ideal.  Arbitrary decompositions of two Jacobian
rows in the four elements `U,G,H,W`, together with a global Bézout
identity, therefore give an explicit dual frame.
-/

namespace MazurProof.GraphJacobianDecompositionFrame

noncomputable section

variable {A K : Type*}
variable [CommRing A] [IsDomain A]
variable [Field K] [Algebra A K] [IsFractionRing A K]

theorem graphJacobian_isUnit_of_decompositions
    (U G H W Fx Fy
      αx βx γx δx αy βy γy δy a b : A)
    (hU : U ≠ 0)
    (hGH : G * H = -(U * W))
    (hFx :
      Fx = U * αx + G * βx + H * γx + W * δx)
    (hFy :
      Fy = U * αy + G * βy + H * γy + W * δy)
    (hBez : a * Fx + b * Fy = 1) :
    IsUnit
      ((Ideal.span ({U, G} : Set A) : Ideal A) :
        FractionalIdeal A⁰ K) := by
  let M : Ideal A :=
    Ideal.span ({U, G} : Set A)
  let I : FractionalIdeal A⁰ K :=
    (M : FractionalIdeal A⁰ K)
  have hU_M : U ∈ M := by
    exact Ideal.subset_span (by simp)
  have hG_M : G ∈ M := by
    exact Ideal.subset_span (by simp)
  have hU_I : algebraMap A K U ∈ I := by
    simpa only [I] using
      (FractionalIdeal.mem_coeIdeal_of_mem A⁰ hU_M)
  have hG_I : algebraMap A K G ∈ I := by
    simpa only [I] using
      (FractionalIdeal.mem_coeIdeal_of_mem A⁰ hG_M)
  have hI_le_one : I ≤ 1 := by
    exact FractionalIdeal.coeIdeal_le_one
  have hI_ne : I ≠ 0 := by
    intro hI0
    have hmapU0 : algebraMap A K U = 0 :=
      (FractionalIdeal.eq_zero_iff.mp hI0)
        (algebraMap A K U) hU_I
    exact hU
      (IsFractionRing.to_map_eq_zero_iff.mp hmapU0)
  have hmapU_ne : algebraMap A K U ≠ 0 := by
    simpa only [map_zero] using
      (IsFractionRing.injective A K).ne hU
  have hGHK :
      algebraMap A K G * algebraMap A K H =
        -(algebraMap A K U * algebraMap A K W) := by
    simpa only [map_mul, map_neg] using
      congrArg (algebraMap A K) hGH
  let z : K :=
    -algebraMap A K H / algebraMap A K U
  have hzU :
      z * algebraMap A K U =
        -algebraMap A K H := by
    dsimp only [z]
    field_simp [hmapU_ne]
  have hzG :
      z * algebraMap A K G =
        algebraMap A K W := by
    calc
      z * algebraMap A K G =
          -(algebraMap A K H *
              algebraMap A K G) /
            algebraMap A K U := by
              dsimp only [z]
              ring
      _ =
          -(algebraMap A K G *
              algebraMap A K H) /
            algebraMap A K U := by ring
      _ =
          -(-(algebraMap A K U *
              algebraMap A K W)) /
            algebraMap A K U := by rw [hGHK]
      _ = algebraMap A K W := by
            field_simp [hmapU_ne]
  have hz_mem : z ∈ I⁻¹ := by
    rw [FractionalIdeal.mem_inv_iff hI_ne]
    intro y hy
    change y ∈ (M : FractionalIdeal A⁰ K) at hy
    rw [FractionalIdeal.mem_coeIdeal A⁰] at hy
    obtain ⟨yA, hyA, hyEq⟩ := hy
    subst y
    obtain ⟨c, d, hcd⟩ :=
      Ideal.mem_span_pair.mp
        (by simpa only [M] using hyA)
    rw [FractionalIdeal.mem_one_iff A⁰]
    refine ⟨-c * H + d * W, ?_⟩
    calc
      algebraMap A K (-c * H + d * W) =
          algebraMap A K c *
              (-algebraMap A K H) +
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
      _ = z * algebraMap A K yA := by rw [hcd]
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
  let ux : K :=
    algebraMap A K αx - algebraMap A K γx * z
  let gx : K :=
    algebraMap A K βx + algebraMap A K δx * z
  let uy : K :=
    algebraMap A K αy - algebraMap A K γy * z
  let gy : K :=
    algebraMap A K βy + algebraMap A K δy * z
  have hux : ux ∈ I⁻¹ := by
    exact
      (((I⁻¹ : FractionalIdeal A⁰ K) :
        Submodule A K).sub_mem
          (hIntegral αx) (hScalarZ γx))
  have hgx : gx ∈ I⁻¹ := by
    exact
      (((I⁻¹ : FractionalIdeal A⁰ K) :
        Submodule A K).add_mem
          (hIntegral βx) (hScalarZ δx))
  have huy : uy ∈ I⁻¹ := by
    exact
      (((I⁻¹ : FractionalIdeal A⁰ K) :
        Submodule A K).sub_mem
          (hIntegral αy) (hScalarZ γy))
  have hgy : gy ∈ I⁻¹ := by
    exact
      (((I⁻¹ : FractionalIdeal A⁰ K) :
        Submodule A K).add_mem
          (hIntegral βy) (hScalarZ δy))
  have hHK :
      algebraMap A K H =
        -(z * algebraMap A K U) := by
    rw [hzU]
    ring
  have hWK :
      algebraMap A K W =
        z * algebraMap A K G :=
    hzG.symm
  have hFxK :
      algebraMap A K Fx =
        algebraMap A K U * ux +
          algebraMap A K G * gx := by
    rw [hFx]
    simp only [map_add, map_mul, ux, gx]
    rw [hHK, hWK]
    ring
  have hFyK :
      algebraMap A K Fy =
        algebraMap A K U * uy +
          algebraMap A K G * gy := by
    rw [hFy]
    simp only [map_add, map_mul, uy, gy]
    rw [hHK, hWK]
    ring
  let tU : K :=
    algebraMap A K a * ux +
      algebraMap A K b * uy
  let tG : K :=
    algebraMap A K a * gx +
      algebraMap A K b * gy
  have htU : tU ∈ I⁻¹ := by
    simpa only [FractionalIdeal.mem_coe,
      Algebra.smul_def, tU] using
      (((I⁻¹ : FractionalIdeal A⁰ K) :
        Submodule A K).add_mem
          (((I⁻¹ : FractionalIdeal A⁰ K) :
            Submodule A K).smul_mem a hux)
          (((I⁻¹ : FractionalIdeal A⁰ K) :
            Submodule A K).smul_mem b huy))
  have htG : tG ∈ I⁻¹ := by
    simpa only [FractionalIdeal.mem_coe,
      Algebra.smul_def, tG] using
      (((I⁻¹ : FractionalIdeal A⁰ K) :
        Submodule A K).add_mem
          (((I⁻¹ : FractionalIdeal A⁰ K) :
            Submodule A K).smul_mem a hgx)
          (((I⁻¹ : FractionalIdeal A⁰ K) :
            Submodule A K).smul_mem b hgy))
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
              (algebraMap A K U * ux +
                algebraMap A K G * gx) +
            algebraMap A K b *
              (algebraMap A K U * uy +
                algebraMap A K G * gy) := by
          dsimp only [tU, tG]
          ring
      _ =
          algebraMap A K a * algebraMap A K Fx +
            algebraMap A K b * algebraMap A K Fy := by
        rw [← hFxK, ← hFyK]
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
  exact
    (FractionalIdeal.mul_inv_cancel_iff_isUnit K).mp hmul_eq

end

end MazurProof.GraphJacobianDecompositionFrame


