-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13SpecialDualFrame_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13SpecialDualFrame_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T22:04:24.872103+00:00
-- url     : https://prove2.me/theorems/6a0c8471-f059-46e9-8f10-677cb87be71e
-- title:
--   FLT.Assumptions.MazurProof.N13SpecialDualFrame source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13SpecialDualFrame

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13SpecialDualFrame
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13AbelChartBase_p0

set_option autoImplicit false




/-!
# The explicit special-fibre dual frame

For the selected nonspecial graph ideal `(X²+X,Y)`, three explicit primal
and multiplier-dual elements have evaluation sum one.  The only
denominator is `(Y+h)/(X²+X)`; its inverse-ideal membership follows
directly from the curve equation.

This is a symbolic certificate in the special affine coordinate ring.  It
does not use invertibility of the graph ideal and is therefore suitable as
the input relation for the two-chart lifting argument.
-/

open Polynomial
open scoped nonZeroDivisors

namespace MazurProof.N13SpecialDualFrame

noncomputable section

abbrev k : Type := N13GoodCoordinateRingTwo.K
abbrev A : Type := N13GoodCoordinateRingTwo.CoordinateRing
abbrev F : Type := N13GoodCoordinateRingTwo.FunctionField
abbrev Frac : Type := FractionalIdeal A⁰ F

def u : k[X] := X ^ 2 + X
def c : k[X] := X ^ 2 + X + 1

theorem u_monic : u.Monic := by
  unfold u
  (monicity; norm_num)

def I : Ideal A :=
  N13GoodCoordinateRingTwo.mumfordIdeal u 0

def IFrac : Frac :=
  (I : Frac)

def uF : F :=
  algebraMap A F (N13GoodCoordinateRingTwo.xClass u)

def cF : F :=
  algebraMap A F (N13GoodCoordinateRingTwo.xClass c)

def x3F : F :=
  algebraMap A F (N13GoodCoordinateRingTwo.xClass (X ^ 3))

def yF : F :=
  algebraMap A F N13GoodCoordinateRingTwo.yClass

def hF : F :=
  algebraMap A F
    (N13GoodCoordinateRingTwo.xClass
      N13GoodCoordinateRingTwo.hPoly)

def quotientDual : F :=
  (yF + hF) / uF

theorem u_ne_zero : uF ≠ 0 := by
  change
    algebraMap A F (N13GoodCoordinateRingTwo.xClass u) ≠ 0
  simpa only [map_zero] using
    (IsFractionRing.injective A F).ne
      (N13GoodCoordinateRingTwo.xClass_ne_zero
        (p := u) u_monic.ne_zero)

theorem polynomial_identity :
    u * X ^ 3 + c * N13GoodCoordinateRingTwo.hPoly = 1 := by
  simp [u, c, N13GoodCoordinateRingTwo.hPoly]
  ring_nf
  rw [show (2 : k[X]) = 0 by
    exact CharP.cast_eq_zero (k[X]) 2]
  simp

theorem coordinate_identity :
    N13GoodCoordinateRingTwo.xClass u *
          N13GoodCoordinateRingTwo.xClass (X ^ 3) +
        N13GoodCoordinateRingTwo.xClass c *
          (N13GoodCoordinateRingTwo.yClass +
            N13GoodCoordinateRingTwo.xClass
              N13GoodCoordinateRingTwo.hPoly) +
        N13GoodCoordinateRingTwo.yClass *
          N13GoodCoordinateRingTwo.xClass c =
      1 := by
  have htwoPoly : (2 : k[X]) = 0 :=
    CharP.cast_eq_zero (k[X]) 2
  have htwoCoord : (2 : A) = 0 := by
    calc
      (2 : A) =
          N13GoodCoordinateRingTwo.xClass (2 : k[X]) :=
        (N13GoodCoordinateRingTwo.xClass_natCast 2).symm
      _ = N13GoodCoordinateRingTwo.xClass 0 := by
        rw [htwoPoly]
      _ = 0 :=
        N13GoodCoordinateRingTwo.xClass_zero
  have htwo :
      N13GoodCoordinateRingTwo.yClass *
            N13GoodCoordinateRingTwo.xClass c +
          N13GoodCoordinateRingTwo.yClass *
            N13GoodCoordinateRingTwo.xClass c = 0 := by
    rw [← two_mul, htwoCoord, zero_mul]
  calc
    N13GoodCoordinateRingTwo.xClass u *
            N13GoodCoordinateRingTwo.xClass (X ^ 3) +
          N13GoodCoordinateRingTwo.xClass c *
            (N13GoodCoordinateRingTwo.yClass +
              N13GoodCoordinateRingTwo.xClass
                N13GoodCoordinateRingTwo.hPoly) +
          N13GoodCoordinateRingTwo.yClass *
            N13GoodCoordinateRingTwo.xClass c =
        N13GoodCoordinateRingTwo.xClass u *
              N13GoodCoordinateRingTwo.xClass (X ^ 3) +
            N13GoodCoordinateRingTwo.xClass c *
              N13GoodCoordinateRingTwo.xClass
                N13GoodCoordinateRingTwo.hPoly +
            (N13GoodCoordinateRingTwo.yClass *
                N13GoodCoordinateRingTwo.xClass c +
              N13GoodCoordinateRingTwo.yClass *
                N13GoodCoordinateRingTwo.xClass c) := by
      ring
    _ =
        N13GoodCoordinateRingTwo.xClass u *
              N13GoodCoordinateRingTwo.xClass (X ^ 3) +
            N13GoodCoordinateRingTwo.xClass c *
              N13GoodCoordinateRingTwo.xClass
                N13GoodCoordinateRingTwo.hPoly := by
      rw [htwo, add_zero]
    _ =
        N13GoodCoordinateRingTwo.xClass
          (u * X ^ 3 +
            c * N13GoodCoordinateRingTwo.hPoly) := by
      rw [N13GoodCoordinateRingTwo.xClass_add,
        N13GoodCoordinateRingTwo.xClass_mul,
        N13GoodCoordinateRingTwo.xClass_mul]
    _ = 1 := by
      rw [polynomial_identity,
        N13GoodCoordinateRingTwo.xClass_one]

theorem rhs_eq_u_mul_x3 :
    N13GoodCoordinateRingTwo.rhsPoly = u * X ^ 3 := by
  simp [N13GoodCoordinateRingTwo.rhsPoly, u]
  ring

theorem y_mul_y_add_h :
    N13GoodCoordinateRingTwo.yClass *
          (N13GoodCoordinateRingTwo.yClass +
            N13GoodCoordinateRingTwo.xClass
              N13GoodCoordinateRingTwo.hPoly) =
      N13GoodCoordinateRingTwo.xClass u *
        N13GoodCoordinateRingTwo.xClass (X ^ 3) := by
  calc
    N13GoodCoordinateRingTwo.yClass *
          (N13GoodCoordinateRingTwo.yClass +
            N13GoodCoordinateRingTwo.xClass
              N13GoodCoordinateRingTwo.hPoly) =
        N13GoodCoordinateRingTwo.yClass ^ 2 +
          N13GoodCoordinateRingTwo.xClass
            N13GoodCoordinateRingTwo.hPoly *
              N13GoodCoordinateRingTwo.yClass := by
      ring
    _ =
        N13GoodCoordinateRingTwo.xClass
          N13GoodCoordinateRingTwo.rhsPoly :=
      N13GoodCoordinateRingTwo.yClass_relation
    _ =
        N13GoodCoordinateRingTwo.xClass (u * X ^ 3) := by
      rw [rhs_eq_u_mul_x3]
    _ =
        N13GoodCoordinateRingTwo.xClass u *
          N13GoodCoordinateRingTwo.xClass (X ^ 3) :=
      N13GoodCoordinateRingTwo.xClass_mul _ _

theorem algebraMap_mem_IFrac
    {z : A} (hz : z ∈ I) :
    algebraMap A F z ∈ IFrac := by
  exact
    (FractionalIdeal.mem_coeIdeal
      (nonZeroDivisors A)).2
      ⟨z, hz, rfl⟩

theorem uF_mem : uF ∈ IFrac := by
  apply algebraMap_mem_IFrac
  exact
    N13GoodCoordinateRingTwo.xClass_mem_mumfordIdeal u 0

theorem cF_mul_uF_mem : cF * uF ∈ IFrac := by
  change
    algebraMap A F (N13GoodCoordinateRingTwo.xClass c) *
        algebraMap A F (N13GoodCoordinateRingTwo.xClass u) ∈
      IFrac
  rw [← map_mul]
  apply algebraMap_mem_IFrac
  exact
    Ideal.mul_mem_left I
      (N13GoodCoordinateRingTwo.xClass c)
      (N13GoodCoordinateRingTwo.xClass_mem_mumfordIdeal u 0)

theorem yF_mem : yF ∈ IFrac := by
  change algebraMap A F N13GoodCoordinateRingTwo.yClass ∈ IFrac
  apply algebraMap_mem_IFrac
  change
    N13GoodCoordinateRingTwo.yClass ∈
      N13GoodCoordinateRingTwo.mumfordIdeal u 0
  simpa [N13GoodCoordinateRingTwo.ySubClass] using
    (N13GoodCoordinateRingTwo.ySubClass_mem_mumfordIdeal u 0)

theorem IFrac_ne_zero : IFrac ≠ 0 := by
  intro hzero
  have hu := uF_mem
  rw [hzero] at hu
  exact u_ne_zero (by simpa using hu)

theorem integral_mem_inv (z : A) :
    algebraMap A F z ∈ IFrac⁻¹ := by
  rw [FractionalIdeal.mem_inv_iff IFrac_ne_zero]
  intro y hy
  obtain ⟨y₀, hy₀, rfl⟩ :=
    (FractionalIdeal.mem_coeIdeal
      (nonZeroDivisors A)).1 hy
  rw [FractionalIdeal.mem_one_iff]
  exact ⟨z * y₀, by simp⟩

theorem x3F_mem_inv : x3F ∈ IFrac⁻¹ :=
  integral_mem_inv _

theorem cF_mem_inv : cF ∈ IFrac⁻¹ :=
  integral_mem_inv _

theorem quotientDual_mul_combination
    (a b : A) :
    quotientDual *
        algebraMap A F
          (a * N13GoodCoordinateRingTwo.xClass u +
            b * N13GoodCoordinateRingTwo.yClass) =
      algebraMap A F
        (a *
            (N13GoodCoordinateRingTwo.yClass +
              N13GoodCoordinateRingTwo.xClass
                N13GoodCoordinateRingTwo.hPoly) +
          b * N13GoodCoordinateRingTwo.xClass (X ^ 3)) := by
  have hrelation :
      (yF + hF) * yF = uF * x3F := by
    simpa [yF, hF, uF, x3F, mul_comm] using
      congrArg (algebraMap A F) y_mul_y_add_h
  calc
    quotientDual *
          algebraMap A F
            (a * N13GoodCoordinateRingTwo.xClass u +
              b * N13GoodCoordinateRingTwo.yClass) =
        algebraMap A F a * (yF + hF) * (uF⁻¹ * uF) +
          algebraMap A F b * uF⁻¹ * ((yF + hF) * yF) := by
      simp only [quotientDual, div_eq_mul_inv,
        map_add, map_mul, uF, yF]
      ring
    _ =
        algebraMap A F a * (yF + hF) +
          algebraMap A F b * uF⁻¹ * (uF * x3F) := by
      rw [inv_mul_cancel₀ u_ne_zero, hrelation, mul_one]
    _ =
        algebraMap A F a * (yF + hF) +
          algebraMap A F b * x3F := by
      rw [show
        algebraMap A F b * uF⁻¹ * (uF * x3F) =
            algebraMap A F b * x3F by
          calc
            algebraMap A F b * uF⁻¹ * (uF * x3F) =
                algebraMap A F b * (uF⁻¹ * uF) * x3F := by
              ring
            _ = algebraMap A F b * x3F := by
              rw [inv_mul_cancel₀ u_ne_zero, mul_one]]
    _ =
        algebraMap A F
          (a *
              (N13GoodCoordinateRingTwo.yClass +
                N13GoodCoordinateRingTwo.xClass
                  N13GoodCoordinateRingTwo.hPoly) +
            b * N13GoodCoordinateRingTwo.xClass (X ^ 3)) := by
      simp [yF, hF, x3F]

theorem quotientDual_mem_inv :
    quotientDual ∈ IFrac⁻¹ := by
  rw [FractionalIdeal.mem_inv_iff IFrac_ne_zero]
  intro z hz
  obtain ⟨z₀, hz₀, rfl⟩ :=
    (FractionalIdeal.mem_coeIdeal
      (nonZeroDivisors A)).1 hz
  obtain ⟨a, b, hab⟩ :=
    Ideal.mem_span_pair.mp hz₀
  rw [← hab]
  simp only [N13GoodCoordinateRingTwo.ySubClass,
    N13GoodCoordinateRingTwo.xClass_zero, sub_zero]
  rw [quotientDual_mul_combination]
  rw [FractionalIdeal.mem_one_iff]
  exact
    ⟨a *
        (N13GoodCoordinateRingTwo.yClass +
          N13GoodCoordinateRingTwo.xClass
            N13GoodCoordinateRingTwo.hPoly) +
      b * N13GoodCoordinateRingTwo.xClass (X ^ 3),
      rfl⟩

theorem trace_relation :
    uF * x3F + (cF * uF) * quotientDual + yF * cF = 1 := by
  have hcancel : uF * uF⁻¹ = 1 :=
    mul_inv_cancel₀ u_ne_zero
  rw [quotientDual, div_eq_mul_inv]
  calc
    uF * x3F +
            (cF * uF) * ((yF + hF) * uF⁻¹) +
          yF * cF =
        uF * x3F + cF * (yF + hF) + yF * cF := by
      rw [show
        (cF * uF) * ((yF + hF) * uF⁻¹) =
          cF * (yF + hF) by
        calc
          (cF * uF) * ((yF + hF) * uF⁻¹) =
              cF * (yF + hF) * (uF * uF⁻¹) := by
            ring
          _ = cF * (yF + hF) := by rw [hcancel, mul_one]]
    _ =
        algebraMap A F
          (N13GoodCoordinateRingTwo.xClass u *
              N13GoodCoordinateRingTwo.xClass (X ^ 3) +
            N13GoodCoordinateRingTwo.xClass c *
              (N13GoodCoordinateRingTwo.yClass +
                N13GoodCoordinateRingTwo.xClass
                  N13GoodCoordinateRingTwo.hPoly) +
            N13GoodCoordinateRingTwo.yClass *
              N13GoodCoordinateRingTwo.xClass c) := by
      simp [uF, x3F, cF, yF, hF]
    _ = 1 := by rw [coordinate_identity, map_one]

/-- The three evaluations already lie in the special affine coordinate
ring, despite the denominator in the middle dual factor. -/
def product : Fin 3 → A :=
  ![
    N13GoodCoordinateRingTwo.xClass u *
      N13GoodCoordinateRingTwo.xClass (X ^ 3),
    N13GoodCoordinateRingTwo.xClass c *
      (N13GoodCoordinateRingTwo.yClass +
        N13GoodCoordinateRingTwo.xClass
          N13GoodCoordinateRingTwo.hPoly),
    N13GoodCoordinateRingTwo.yClass *
      N13GoodCoordinateRingTwo.xClass c
  ]

/-- The three primal factors in the special graph ideal. -/
def primal : Fin 3 → F :=
  ![uF, cF * uF, yF]

/-- The corresponding multiplier-dual factors. -/
def dual : Fin 3 → F :=
  ![x3F, quotientDual, cF]

theorem primal_mem (i : Fin 3) :
    primal i ∈ IFrac := by
  fin_cases i
  · exact uF_mem
  · exact cF_mul_uF_mem
  · exact yF_mem

theorem dual_mem (i : Fin 3) :
    dual i ∈ IFrac⁻¹ := by
  fin_cases i
  · exact x3F_mem_inv
  · exact quotientDual_mem_inv
  · exact cF_mem_inv

/-- Each special product is the evaluation of the corresponding primal and
multiplier-dual factors. -/
theorem algebraMap_product (i : Fin 3) :
    algebraMap A F (product i) =
      primal i * dual i := by
  fin_cases i
  · change
      algebraMap A F
          (N13GoodCoordinateRingTwo.xClass u *
            N13GoodCoordinateRingTwo.xClass (X ^ 3)) =
        uF * x3F
    rw [map_mul]
    rfl
  · change
      algebraMap A F
          (N13GoodCoordinateRingTwo.xClass c *
            (N13GoodCoordinateRingTwo.yClass +
              N13GoodCoordinateRingTwo.xClass
                N13GoodCoordinateRingTwo.hPoly)) =
        (cF * uF) * quotientDual
    rw [map_mul, map_add]
    change
      cF * (yF + hF) =
        (cF * uF) * quotientDual
    rw [quotientDual, div_eq_mul_inv]
    calc
      cF * (yF + hF) =
          cF * (yF + hF) * (uF * uF⁻¹) := by
        rw [mul_inv_cancel₀ u_ne_zero, mul_one]
      _ = (cF * uF) * ((yF + hF) * uF⁻¹) := by
        ring
  · change
      algebraMap A F
          (N13GoodCoordinateRingTwo.yClass *
            N13GoodCoordinateRingTwo.xClass c) =
        yF * cF
    rw [map_mul]
    rfl

/-- The three affine product representatives sum to one before passage to
the special function field. -/
theorem sum_product :
    ∑ i, product i = 1 := by
  rw [Fin.sum_univ_three]
  exact coordinate_identity

/-- The explicit finite multiplier evaluation is the identity. -/
theorem sum_primal_mul_dual :
    ∑ i, primal i * dual i = 1 := by
  rw [Fin.sum_univ_three]
  exact trace_relation

end

end MazurProof.N13SpecialDualFrame


