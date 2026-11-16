-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Analysis_ArctanGeometry
-- name    : liuyao_ca_fd889115_k1_Analysis_ArctanGeometry
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T18:02:52.938409+00:00
-- url     : https://prove2.me/theorems/416f6322-f899-4913-a2ff-bdf35ba7e692
-- title:
--   Computable analysis · ArctanGeometry · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableAnalysis/ArctanGeometry.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_Elementary
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_FTC
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_RationalCircle

set_option autoImplicit true

/-!
# Geometric arctangent

This module keeps the geometric arctangent and its comparison-facing API
outside the rational-circle trigonometry module.  The rational-circle module
contains the circle stages, coordinate algorithms, and identity infrastructure;
comparison with other arctangent representations imports those extra
definitions here.
-/

namespace ComputableAnalysis

namespace ArctanGeometry

/-!
Geometric arctangent.

For rational `x`, the point
`((1 - x^2) / (1 + x^2), 2x / (1 + x^2))` lies on the unit circle at angle
`2 * arctan x`, so the unit-sector area from `0` to this parameter is
`arctan x`.
-/

def stage (n : Nat) : Nat :=
  2 ^ n

theorem stage_pos (n : Nat) : 0 < stage n := by
  unfold stage
  exact Nat.pow_pos (by omega : 0 < 2)

/-- State for the update-loop presentation of geometric arctangent.  The
interval `[lo, hi]` stores current sector-area bounds, and `intervals` stores
the rational parameter intervals being refined. -/
structure AreaLoopState where
  lo : Rat
  hi : Rat
  intervals : List (Rat × Rat)
deriving Repr, DecidableEq

/-- The area added to the inscribed sector approximation when adjacent
parameters `p < q < r` replace the old interval `[p,r]` by two intervals. -/
def arctanAreaIncrement (p q r : Rat) : Rat :=
  (2 * (r - p) * (q - p) * (r - q)) /
    ((1 + p * p) * (1 + q * q) * (1 + r * r))

/-- The area removed from the outer tangent sector approximation when adjacent
parameters `p < q < r` replace the old interval `[p,r]` by two intervals. -/
def arctanAreaDecrement (p q r : Rat) : Rat :=
  ((r - p) * (q - p) * (r - q)) /
    ((1 + p * r) * (1 + p * q) * (1 + q * r))

private theorem rat_add_le_add {a b c d : Rat}
    (hab : a <= b) (hcd : c <= d) :
    a + c <= b + d := by
  grind

private theorem one_div_le_one_div_of_pos_of_le {a b : Rat}
    (ha : 0 < a) (hab : a <= b) :
    1 / b <= 1 / a := by
  have hb : 0 < b := by grind
  have hane : Not (a = 0) := Rat.ne_of_gt ha
  have hbne : Not (b = 0) := Rat.ne_of_gt hb
  have habpos : 0 < a * b := Rat.mul_pos ha hb
  refine Rat.le_of_mul_le_mul_right (c := a * b) ?_ habpos
  calc
    (1 / b) * (a * b) = a := by
      rw [Rat.div_def]
      have hcancel : b * Inv.inv b = 1 := Rat.mul_inv_cancel b hbne
      grind [Rat.mul_assoc, Rat.mul_comm]
    _ <= b := hab
    _ = (1 / a) * (a * b) := by
      rw [Rat.div_def]
      have hcancel : a * Inv.inv a = 1 := Rat.mul_inv_cancel a hane
      grind [Rat.mul_assoc, Rat.mul_comm]

/-!
The following cell formulas are the finite comparison layer between the
geometric arctangent and the definite integral of `1 / (1 + u^2)`.  No area
axiom or derivative theorem is used here: everything is a rational inequality
on one cell, then a finite sum over cells.
-/

/-- The exact decreasing kernel whose lower/upper rectangle sums compute
arctangent. -/
def integralKernel (u : Rat) : Rat :=
  1 / (1 + u * u)

/-- Exact arctangent-kernel value after a rational tangent-addition chart
change.  This is the pointwise finite algebra behind transport of rectangle
cells. -/
theorem integralKernel_chartAddParameter {u v : Rat}
    (hden : RationalCircle.Trigonometry.chartAddDen u v ≠ 0) :
    integralKernel (RationalCircle.Trigonometry.chartAddParameter u v) =
      (RationalCircle.Trigonometry.chartAddDen u v *
        RationalCircle.Trigonometry.chartAddDen u v) /
        RationalCircle.Trigonometry.chartAddNormDen u v := by
  unfold integralKernel
  rw [RationalCircle.Trigonometry.one_add_square_chartAddParameter hden]
  simp only [Rat.div_def, Rat.inv_mul_rev, Rat.inv_inv, Rat.one_mul]

/-- Lower rectangle on `[p,r]` for `1/(1+u^2)`, valid on nonnegative cells. -/
def integralLowerStep (p r : Rat) : Rat :=
  (r - p) * integralKernel r

/-- Upper rectangle on `[p,r]` for `1/(1+u^2)`, valid on nonnegative cells. -/
def integralUpperStep (p r : Rat) : Rat :=
  (r - p) * integralKernel p

/-- The lower kernel rectangle on a chart-transformed cell is the source
lower rectangle multiplied by the exact endpoint denominator ratio. -/
theorem integralLowerStep_chartAddParameter_eq {u p r : Rat}
    (hp : RationalCircle.Trigonometry.chartAddDen u p ≠ 0)
    (hr : RationalCircle.Trigonometry.chartAddDen u r ≠ 0) :
    integralLowerStep
      (RationalCircle.Trigonometry.chartAddParameter u p)
      (RationalCircle.Trigonometry.chartAddParameter u r) =
      integralLowerStep p r *
        (RationalCircle.Trigonometry.chartAddDen u r /
          RationalCircle.Trigonometry.chartAddDen u p) := by
  unfold integralLowerStep
  rw [RationalCircle.Trigonometry.chartAddParameter_sub hp hr]
  rw [integralKernel_chartAddParameter hr]
  rw [RationalCircle.Trigonometry.chartAdd_normDen_eq]
  unfold integralKernel
  simp only [Rat.div_def, Rat.inv_mul_rev]
  have hp' : 1 - u * p ≠ 0 := hp
  have hr' : 1 - u * r ≠ 0 := hr
  have hu : 1 + u * u ≠ 0 :=
    Rat.ne_of_gt (RationalCircle.Stage.one_add_square_pos u)
  have hrSquare : 1 + r * r ≠ 0 :=
    Rat.ne_of_gt (RationalCircle.Stage.one_add_square_pos r)
  grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]

/-- The upper kernel rectangle on a chart-transformed cell is the source
upper rectangle multiplied by the reciprocal endpoint denominator ratio. -/
theorem integralUpperStep_chartAddParameter_eq {u p r : Rat}
    (hp : RationalCircle.Trigonometry.chartAddDen u p ≠ 0)
    (hr : RationalCircle.Trigonometry.chartAddDen u r ≠ 0) :
    integralUpperStep
      (RationalCircle.Trigonometry.chartAddParameter u p)
      (RationalCircle.Trigonometry.chartAddParameter u r) =
      integralUpperStep p r *
        (RationalCircle.Trigonometry.chartAddDen u p /
          RationalCircle.Trigonometry.chartAddDen u r) := by
  unfold integralUpperStep
  rw [RationalCircle.Trigonometry.chartAddParameter_sub hp hr]
  rw [integralKernel_chartAddParameter hp]
  rw [RationalCircle.Trigonometry.chartAdd_normDen_eq]
  unfold integralKernel
  simp only [Rat.div_def, Rat.inv_mul_rev]
  have hp' : 1 - u * p ≠ 0 := hp
  have hr' : 1 - u * r ≠ 0 := hr
  have hu : 1 + u * u ≠ 0 :=
    Rat.ne_of_gt (RationalCircle.Stage.one_add_square_pos u)
  have hpSquare : 1 + p * p ≠ 0 :=
    Rat.ne_of_gt (RationalCircle.Stage.one_add_square_pos p)
  grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]

/-- On a nonnegative source cell with positive chart denominators, the lower
rectangle after chart transport is no larger than the source lower rectangle. -/
theorem chartAdd_integralLowerStep_le {u p r : Rat}
    (hu : 0 <= u) (hpr : p <= r)
    (hp : 0 < RationalCircle.Trigonometry.chartAddDen u p)
    (hr : 0 < RationalCircle.Trigonometry.chartAddDen u r) :
    integralLowerStep
      (RationalCircle.Trigonometry.chartAddParameter u p)
      (RationalCircle.Trigonometry.chartAddParameter u r) <=
        integralLowerStep p r := by
  have hpne : RationalCircle.Trigonometry.chartAddDen u p ≠ 0 :=
    Rat.ne_of_gt hp
  have hrne : RationalCircle.Trigonometry.chartAddDen u r ≠ 0 :=
    Rat.ne_of_gt hr
  have hden :
      RationalCircle.Trigonometry.chartAddDen u r <=
        RationalCircle.Trigonometry.chartAddDen u p := by
    unfold RationalCircle.Trigonometry.chartAddDen
    have hmul : u * p <= u * r :=
      Rat.mul_le_mul_of_nonneg_left hpr hu
    grind [Rat.sub_eq_add_neg]
  have hratio :
      RationalCircle.Trigonometry.chartAddDen u r /
        RationalCircle.Trigonometry.chartAddDen u p <= 1 := by
    apply Rat.le_of_mul_le_mul_right
      (c := RationalCircle.Trigonometry.chartAddDen u p)
    · rw [Rat.div_def]
      calc
        (RationalCircle.Trigonometry.chartAddDen u r *
            (RationalCircle.Trigonometry.chartAddDen u p)⁻¹) *
            RationalCircle.Trigonometry.chartAddDen u p =
            RationalCircle.Trigonometry.chartAddDen u r := by
              grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
        _ <= RationalCircle.Trigonometry.chartAddDen u p := hden
        _ = 1 * RationalCircle.Trigonometry.chartAddDen u p := by
              grind
    · exact hp
  rw [integralLowerStep_chartAddParameter_eq hpne hrne]
  have hsource : 0 <= integralLowerStep p r := by
    have hlen : 0 <= r - p := by
      grind [Rat.sub_eq_add_neg]
    have hkernel : 0 <= integralKernel r := by
      unfold integralKernel
      rw [Rat.div_def]
      simpa using Rat.le_of_lt ((Rat.inv_pos).2
        (RationalCircle.Stage.one_add_square_pos r))
    exact Rat.mul_nonneg hlen hkernel
  calc
    integralLowerStep p r *
        (RationalCircle.Trigonometry.chartAddDen u r /
          RationalCircle.Trigonometry.chartAddDen u p) <=
        integralLowerStep p r * 1 :=
      Rat.mul_le_mul_of_nonneg_left hratio hsource
    _ = integralLowerStep p r := by grind

/-- On a nonnegative source cell with positive chart denominators, the upper
rectangle after chart transport is no smaller than the source upper rectangle. -/
theorem integralUpperStep_le_chartAdd {u p r : Rat}
    (hu : 0 <= u) (hpr : p <= r)
    (hp : 0 < RationalCircle.Trigonometry.chartAddDen u p)
    (hr : 0 < RationalCircle.Trigonometry.chartAddDen u r) :
    integralUpperStep p r <=
      integralUpperStep
        (RationalCircle.Trigonometry.chartAddParameter u p)
        (RationalCircle.Trigonometry.chartAddParameter u r) := by
  have hpne : RationalCircle.Trigonometry.chartAddDen u p ≠ 0 :=
    Rat.ne_of_gt hp
  have hrne : RationalCircle.Trigonometry.chartAddDen u r ≠ 0 :=
    Rat.ne_of_gt hr
  have hden :
      RationalCircle.Trigonometry.chartAddDen u r <=
        RationalCircle.Trigonometry.chartAddDen u p := by
    unfold RationalCircle.Trigonometry.chartAddDen
    have hmul : u * p <= u * r :=
      Rat.mul_le_mul_of_nonneg_left hpr hu
    grind [Rat.sub_eq_add_neg]
  have hratio :
      1 <= RationalCircle.Trigonometry.chartAddDen u p /
        RationalCircle.Trigonometry.chartAddDen u r := by
    apply Rat.le_of_mul_le_mul_right
      (c := RationalCircle.Trigonometry.chartAddDen u r)
    · rw [Rat.div_def]
      calc
        1 * RationalCircle.Trigonometry.chartAddDen u r =
            RationalCircle.Trigonometry.chartAddDen u r := by grind
        _ <= RationalCircle.Trigonometry.chartAddDen u p := hden
        _ =
            (RationalCircle.Trigonometry.chartAddDen u p *
              (RationalCircle.Trigonometry.chartAddDen u r)⁻¹) *
              RationalCircle.Trigonometry.chartAddDen u r := by
                grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
    · exact hr
  rw [integralUpperStep_chartAddParameter_eq hpne hrne]
  have hsource : 0 <= integralUpperStep p r := by
    have hlen : 0 <= r - p := by
      grind [Rat.sub_eq_add_neg]
    have hkernel : 0 <= integralKernel p := by
      unfold integralKernel
      rw [Rat.div_def]
      simpa using Rat.le_of_lt ((Rat.inv_pos).2
        (RationalCircle.Stage.one_add_square_pos p))
    exact Rat.mul_nonneg hlen hkernel
  calc
    integralUpperStep p r = integralUpperStep p r * 1 := by grind
    _ <= integralUpperStep p r *
        (RationalCircle.Trigonometry.chartAddDen u p /
          RationalCircle.Trigonometry.chartAddDen u r) :=
      Rat.mul_le_mul_of_nonneg_left hratio hsource

/-- On the Machin-relevant half-unit chart, every unit-cell endpoint
displacement grows by at most a factor of eight. -/
theorem chartAddParameter_width_le_eight_mul {u p r : Rat}
    (hu0 : 0 <= u) (huHalf : u <= (1 : Rat) / 2)
    (hpr : p <= r) (hr1 : r <= 1) :
    RationalCircle.Trigonometry.chartAddParameter u r -
      RationalCircle.Trigonometry.chartAddParameter u p <=
        8 * (r - p) := by
  have hp1 : p <= 1 := Rat.le_trans hpr hr1
  have hdenP :
      (1 : Rat) / 2 <= RationalCircle.Trigonometry.chartAddDen u p := by
    unfold RationalCircle.Trigonometry.chartAddDen
    have hmul : u * p <= (1 : Rat) / 2 := by
      calc
        u * p <= u * 1 := Rat.mul_le_mul_of_nonneg_left hp1 hu0
        _ = u := by grind
        _ <= (1 : Rat) / 2 := huHalf
    grind [Rat.sub_eq_add_neg]
  have hdenR :
      (1 : Rat) / 2 <= RationalCircle.Trigonometry.chartAddDen u r := by
    unfold RationalCircle.Trigonometry.chartAddDen
    have hmul : u * r <= (1 : Rat) / 2 := by
      calc
        u * r <= u * 1 := Rat.mul_le_mul_of_nonneg_left hr1 hu0
        _ = u := by grind
        _ <= (1 : Rat) / 2 := huHalf
    grind [Rat.sub_eq_add_neg]
  have hdenPpos : 0 < RationalCircle.Trigonometry.chartAddDen u p := by
    have : (0 : Rat) < 1 / 2 := by decide +kernel
    grind
  have hdenRpos : 0 < RationalCircle.Trigonometry.chartAddDen u r := by
    have : (0 : Rat) < 1 / 2 := by decide +kernel
    grind
  have hdenProduct :
      (1 : Rat) / 2 * ((1 : Rat) / 2) <=
        RationalCircle.Trigonometry.chartAddDen u p *
          RationalCircle.Trigonometry.chartAddDen u r := by
    calc
      (1 : Rat) / 2 * ((1 : Rat) / 2) <=
          RationalCircle.Trigonometry.chartAddDen u p * ((1 : Rat) / 2) :=
        Rat.mul_le_mul_of_nonneg_right hdenP (by decide +kernel)
      _ <=
          RationalCircle.Trigonometry.chartAddDen u p *
            RationalCircle.Trigonometry.chartAddDen u r :=
        Rat.mul_le_mul_of_nonneg_left hdenR
          (Rat.le_trans (by decide +kernel : (0 : Rat) <= 1 / 2) hdenP)
  have hSquare : u * u <= 1 := by
    calc
      u * u <= u * 1 := Rat.mul_le_mul_of_nonneg_left
        (Rat.le_trans huHalf (by decide +kernel : (1 : Rat) / 2 <= 1)) hu0
      _ = u := by grind
      _ <= 1 := Rat.le_trans huHalf (by decide +kernel)
  have hNorm : 1 + u * u <= 2 := by grind
  have hproductPos :
      0 < RationalCircle.Trigonometry.chartAddDen u p *
        RationalCircle.Trigonometry.chartAddDen u r :=
    Rat.mul_pos hdenPpos hdenRpos
  have hratio :
      (1 + u * u) /
        (RationalCircle.Trigonometry.chartAddDen u p *
          RationalCircle.Trigonometry.chartAddDen u r) <= 8 := by
    apply Rat.le_of_mul_le_mul_right
      (c := RationalCircle.Trigonometry.chartAddDen u p *
        RationalCircle.Trigonometry.chartAddDen u r)
    · rw [Rat.div_def]
      calc
        ((1 + u * u) *
            (RationalCircle.Trigonometry.chartAddDen u p *
              RationalCircle.Trigonometry.chartAddDen u r)⁻¹) *
            (RationalCircle.Trigonometry.chartAddDen u p *
              RationalCircle.Trigonometry.chartAddDen u r) =
            1 + u * u := by
              grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
        _ <= 2 := hNorm
        _ = 8 * ((1 : Rat) / 2 * ((1 : Rat) / 2)) := by decide +kernel
        _ <= 8 *
            (RationalCircle.Trigonometry.chartAddDen u p *
              RationalCircle.Trigonometry.chartAddDen u r) :=
          Rat.mul_le_mul_of_nonneg_left hdenProduct
            (by decide +kernel : (0 : Rat) <= 8)
    · exact hproductPos
  have hlen : 0 <= r - p := by grind [Rat.sub_eq_add_neg]
  have hdiff :=
    RationalCircle.Trigonometry.chartAddParameter_sub
      (u := u) (p := p) (r := r)
      (Rat.ne_of_gt hdenPpos) (Rat.ne_of_gt hdenRpos)
  calc
    RationalCircle.Trigonometry.chartAddParameter u r -
        RationalCircle.Trigonometry.chartAddParameter u p =
        (r - p) *
          ((1 + u * u) /
            (RationalCircle.Trigonometry.chartAddDen u p *
              RationalCircle.Trigonometry.chartAddDen u r)) := by
          rw [hdiff]
          grind [Rat.mul_assoc, Rat.mul_comm]
    _ <= (r - p) * 8 :=
      Rat.mul_le_mul_of_nonneg_left hratio hlen
    _ = 8 * (r - p) := by grind [Rat.mul_comm]

/-- The same factor-eight distortion bound needs only a local right-endpoint
product bound.  This is the form used for a small tangent increment based at
any point of the unit branch. -/
theorem chartAddParameter_width_le_eight_mul_of_rightProduct_le_half
    {u p r : Rat} (hu0 : 0 <= u) (hu1 : u <= 1)
    (hpr : p <= r) (hur : u * r <= (1 : Rat) / 2) :
    RationalCircle.Trigonometry.chartAddParameter u r -
      RationalCircle.Trigonometry.chartAddParameter u p <=
        8 * (r - p) := by
  have hdenP :
      (1 : Rat) / 2 <= RationalCircle.Trigonometry.chartAddDen u p := by
    unfold RationalCircle.Trigonometry.chartAddDen
    have hmul : u * p <= (1 : Rat) / 2 := by
      calc
        u * p <= u * r := Rat.mul_le_mul_of_nonneg_left hpr hu0
        _ <= (1 : Rat) / 2 := hur
    grind [Rat.sub_eq_add_neg]
  have hdenR :
      (1 : Rat) / 2 <= RationalCircle.Trigonometry.chartAddDen u r := by
    unfold RationalCircle.Trigonometry.chartAddDen
    grind [Rat.sub_eq_add_neg]
  have hdenPpos : 0 < RationalCircle.Trigonometry.chartAddDen u p := by
    have : (0 : Rat) < 1 / 2 := by decide +kernel
    grind
  have hdenRpos : 0 < RationalCircle.Trigonometry.chartAddDen u r := by
    have : (0 : Rat) < 1 / 2 := by decide +kernel
    grind
  have hdenProduct :
      (1 : Rat) / 2 * ((1 : Rat) / 2) <=
        RationalCircle.Trigonometry.chartAddDen u p *
          RationalCircle.Trigonometry.chartAddDen u r := by
    calc
      (1 : Rat) / 2 * ((1 : Rat) / 2) <=
          RationalCircle.Trigonometry.chartAddDen u p * ((1 : Rat) / 2) :=
        Rat.mul_le_mul_of_nonneg_right hdenP (by decide +kernel)
      _ <= RationalCircle.Trigonometry.chartAddDen u p *
          RationalCircle.Trigonometry.chartAddDen u r :=
        Rat.mul_le_mul_of_nonneg_left hdenR
          (Rat.le_trans (by decide +kernel : (0 : Rat) <= 1 / 2) hdenP)
  have hSquare : u * u <= 1 := by
    calc
      u * u <= u * 1 := Rat.mul_le_mul_of_nonneg_left hu1 hu0
      _ = u := by grind
      _ <= 1 := hu1
  have hNorm : 1 + u * u <= 2 := by grind
  have hproductPos :
      0 < RationalCircle.Trigonometry.chartAddDen u p *
        RationalCircle.Trigonometry.chartAddDen u r :=
    Rat.mul_pos hdenPpos hdenRpos
  have hratio :
      (1 + u * u) /
        (RationalCircle.Trigonometry.chartAddDen u p *
          RationalCircle.Trigonometry.chartAddDen u r) <= 8 := by
    apply Rat.le_of_mul_le_mul_right
      (c := RationalCircle.Trigonometry.chartAddDen u p *
        RationalCircle.Trigonometry.chartAddDen u r)
    · rw [Rat.div_def]
      calc
        ((1 + u * u) *
            (RationalCircle.Trigonometry.chartAddDen u p *
              RationalCircle.Trigonometry.chartAddDen u r)⁻¹) *
            (RationalCircle.Trigonometry.chartAddDen u p *
              RationalCircle.Trigonometry.chartAddDen u r) =
            1 + u * u := by
              grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
        _ <= 2 := hNorm
        _ = 8 * ((1 : Rat) / 2 * ((1 : Rat) / 2)) := by decide +kernel
        _ <= 8 *
            (RationalCircle.Trigonometry.chartAddDen u p *
              RationalCircle.Trigonometry.chartAddDen u r) :=
          Rat.mul_le_mul_of_nonneg_left hdenProduct
            (by decide +kernel : (0 : Rat) <= 8)
    · exact hproductPos
  have hlen : 0 <= r - p := by grind [Rat.sub_eq_add_neg]
  have hdiff :=
    RationalCircle.Trigonometry.chartAddParameter_sub
      (u := u) (p := p) (r := r)
      (Rat.ne_of_gt hdenPpos) (Rat.ne_of_gt hdenRpos)
  calc
    RationalCircle.Trigonometry.chartAddParameter u r -
        RationalCircle.Trigonometry.chartAddParameter u p =
        (r - p) *
          ((1 + u * u) /
            (RationalCircle.Trigonometry.chartAddDen u p *
              RationalCircle.Trigonometry.chartAddDen u r)) := by
          rw [hdiff]
          grind [Rat.mul_assoc, Rat.mul_comm]
    _ <= (r - p) * 8 :=
      Rat.mul_le_mul_of_nonneg_left hratio hlen
    _ = 8 * (r - p) := by grind [Rat.mul_comm]

/-- Inscribed geometric sector cell between rational parameters `p` and `r`. -/
def geometricLowerStep (p r : Rat) : Rat :=
  ((r - p) * (1 + p * r)) /
    ((1 + p * p) * (1 + r * r))

/-- Circumscribed tangent-sector cell between rational parameters `p` and `r`. -/
def geometricUpperStep (p r : Rat) : Rat :=
  (r - p) / (1 + p * r)

def integralCellInterval (p r : Rat) : QInterval :=
  { lo := integralLowerStep p r, hi := integralUpperStep p r }

def geometricCellInterval (p r : Rat) : QInterval :=
  { lo := geometricLowerStep p r, hi := geometricUpperStep p r }

theorem integralKernel_pos (u : Rat) : 0 < integralKernel u := by
  unfold integralKernel
  rw [Rat.div_def]
  simpa using (Rat.inv_pos).2 (RationalCircle.Stage.one_add_square_pos u)

theorem integralKernel_le_one (u : Rat) : integralKernel u <= 1 := by
  unfold integralKernel
  have hden : 1 <= 1 + u * u := by
    have hsq := RationalCircle.Stage.ratSquare_nonneg u
    grind
  have hone : (0 : Rat) < 1 := by decide +kernel
  have h := one_div_le_one_div_of_pos_of_le hone hden
  calc
    integralKernel u <= 1 / (1 : Rat) := h
    _ = 1 := by decide +kernel

theorem integralUpperStep_nonneg {p r : Rat} (hpr : p <= r) :
    0 <= integralUpperStep p r := by
  have hlen : 0 <= r - p := by grind [Rat.sub_eq_add_neg]
  unfold integralUpperStep
  exact Rat.mul_nonneg hlen (Rat.le_of_lt (integralKernel_pos p))

theorem integralLowerStep_nonneg {p r : Rat} (hpr : p <= r) :
    0 <= integralLowerStep p r := by
  have hlen : 0 <= r - p := by grind [Rat.sub_eq_add_neg]
  unfold integralLowerStep
  exact Rat.mul_nonneg hlen (Rat.le_of_lt (integralKernel_pos r))

theorem integralUpperStep_left_subcell_le
    {p q r : Rat} (_hpq : p <= q) (hqr : q <= r) :
    integralUpperStep p q <= integralUpperStep p r := by
  have hlen : q - p <= r - p := by grind [Rat.sub_eq_add_neg]
  unfold integralUpperStep
  exact Rat.mul_le_mul_of_nonneg_right hlen
    (Rat.le_of_lt (integralKernel_pos p))

theorem integralUpperStep_le_width {p r : Rat} (hpr : p <= r) :
    integralUpperStep p r <= r - p := by
  have hlen : 0 <= r - p := by grind [Rat.sub_eq_add_neg]
  unfold integralUpperStep
  calc
    (r - p) * integralKernel p <= (r - p) * 1 :=
      Rat.mul_le_mul_of_nonneg_left (integralKernel_le_one p) hlen
    _ = r - p := by grind

private theorem containsInterval_refl (I : QInterval) :
    I.ContainsInterval I := by
  unfold QInterval.ContainsInterval
  exact ⟨Rat.le_refl, Rat.le_refl⟩

private theorem containsInterval_trans {I J K : QInterval}
    (hIJ : I.ContainsInterval J) (hJK : J.ContainsInterval K) :
    I.ContainsInterval K := by
  unfold QInterval.ContainsInterval at *
  exact ⟨Rat.le_trans hIJ.1 hJK.1, Rat.le_trans hJK.2 hIJ.2⟩

theorem integralKernel_antitone_nonneg
    {p q : Rat} (hp0 : 0 <= p) (hpq : p <= q) :
    integralKernel q <= integralKernel p := by
  have hsq : 1 + p * p <= 1 + q * q := by
    have hq0 : 0 <= q := Rat.le_trans hp0 hpq
    have hleft : p * p <= p * q :=
      Rat.mul_le_mul_of_nonneg_left hpq hp0
    have hright : p * q <= q * q :=
      Rat.mul_le_mul_of_nonneg_right hpq hq0
    have hmul : p * p <= q * q := Rat.le_trans hleft hright
    grind
  exact one_div_le_one_div_of_pos_of_le
    (RationalCircle.Stage.one_add_square_pos p) hsq

theorem integralLowerStep_le_integralUpperStep
    {p r : Rat} (hp0 : 0 <= p) (hpr : p <= r) :
    integralLowerStep p r <= integralUpperStep p r := by
  have hlen : 0 <= r - p := by grind [Rat.sub_eq_add_neg]
  have hk : integralKernel r <= integralKernel p :=
    integralKernel_antitone_nonneg hp0 hpr
  unfold integralLowerStep integralUpperStep
  exact Rat.mul_le_mul_of_nonneg_left hk hlen

theorem integralLowerStep_refine
    {p q r : Rat} (hp0 : 0 <= p) (hpq : p <= q) (hqr : q <= r) :
    integralLowerStep p r <=
      integralLowerStep p q + integralLowerStep q r := by
  have hqp : 0 <= q - p := by grind [Rat.sub_eq_add_neg]
  have hrq : 0 <= r - q := by grind [Rat.sub_eq_add_neg]
  have hq0 : 0 <= q := Rat.le_trans hp0 hpq
  have hk : integralKernel r <= integralKernel q :=
    integralKernel_antitone_nonneg hq0 hqr
  unfold integralLowerStep
  calc
    (r - p) * integralKernel r
        = (q - p) * integralKernel r + (r - q) * integralKernel r := by
          grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
            Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
    _ <= (q - p) * integralKernel q + (r - q) * integralKernel r := by
          exact rat_add_le_add
            (Rat.mul_le_mul_of_nonneg_left hk hqp)
            (Rat.le_refl)
    _ = (q - p) * integralKernel q + (r - q) * integralKernel r := rfl

theorem integralUpperStep_refine
    {p q r : Rat} (hp0 : 0 <= p) (hpq : p <= q) (hqr : q <= r) :
    integralUpperStep p q + integralUpperStep q r <=
      integralUpperStep p r := by
  have hqp : 0 <= q - p := by grind [Rat.sub_eq_add_neg]
  have hrq : 0 <= r - q := by grind [Rat.sub_eq_add_neg]
  have hk : integralKernel q <= integralKernel p :=
    integralKernel_antitone_nonneg hp0 hpq
  unfold integralUpperStep
  calc
    (q - p) * integralKernel p + (r - q) * integralKernel q
        <= (q - p) * integralKernel p + (r - q) * integralKernel p := by
          exact rat_add_le_add
            (Rat.le_refl)
            (Rat.mul_le_mul_of_nonneg_left hk hrq)
    _ = (r - p) * integralKernel p := by
          grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
            Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]

theorem arctanAreaIncrement_nonneg
    {p q r : Rat} (hpq : p <= q) (hqr : q <= r) :
    0 <= arctanAreaIncrement p q r := by
  have hqp : 0 <= q - p := by grind [Rat.sub_eq_add_neg]
  have hrq : 0 <= r - q := by grind [Rat.sub_eq_add_neg]
  have hrp : 0 <= r - p := by grind [Rat.sub_eq_add_neg]
  have hnum :
      0 <= 2 * (r - p) * (q - p) * (r - q) := by
    exact Rat.mul_nonneg
      (Rat.mul_nonneg
        (Rat.mul_nonneg (by decide +kernel : (0 : Rat) <= 2) hrp)
        hqp)
      hrq
  have hden :
      0 < (1 + p * p) * (1 + q * q) * (1 + r * r) := by
    exact Rat.mul_pos
      (Rat.mul_pos
        (RationalCircle.Stage.one_add_square_pos p)
        (RationalCircle.Stage.one_add_square_pos q))
      (RationalCircle.Stage.one_add_square_pos r)
  unfold arctanAreaIncrement
  rw [Rat.div_def]
  exact Rat.mul_nonneg hnum (Rat.le_of_lt ((Rat.inv_pos).2 hden))

theorem arctanAreaDecrement_nonneg
    {p q r : Rat} (hp0 : 0 <= p) (hpq : p <= q) (hqr : q <= r) :
    0 <= arctanAreaDecrement p q r := by
  have hq0 : 0 <= q := Rat.le_trans hp0 hpq
  have hr0 : 0 <= r := Rat.le_trans hq0 hqr
  have hqp : 0 <= q - p := by grind [Rat.sub_eq_add_neg]
  have hrq : 0 <= r - q := by grind [Rat.sub_eq_add_neg]
  have hrp : 0 <= r - p := by grind [Rat.sub_eq_add_neg]
  have hnum : 0 <= (r - p) * (q - p) * (r - q) := by
    exact Rat.mul_nonneg
      (Rat.mul_nonneg hrp hqp)
      hrq
  have hden :
      0 < (1 + p * r) * (1 + p * q) * (1 + q * r) := by
    exact Rat.mul_pos
      (Rat.mul_pos
        (RationalCircle.Stage.one_add_mul_pos_of_nonneg hp0 hr0)
        (RationalCircle.Stage.one_add_mul_pos_of_nonneg hp0 hq0))
      (RationalCircle.Stage.one_add_mul_pos_of_nonneg hq0 hr0)
  unfold arctanAreaDecrement
  rw [Rat.div_def]
  exact Rat.mul_nonneg hnum (Rat.le_of_lt ((Rat.inv_pos).2 hden))

private theorem rat_eq_of_mul_eq_mul_pos {a b c : Rat}
    (hc : 0 < c) (h : a * c = b * c) : a = b := by
  have hcne : c ≠ 0 := Rat.ne_of_gt hc
  calc
    a = (a * c) * c⁻¹ := by
      have hcancel : c * c⁻¹ = 1 := Rat.mul_inv_cancel c hcne
      grind [Rat.mul_assoc, Rat.mul_comm]
    _ = (b * c) * c⁻¹ := by rw [h]
    _ = b := by
      have hcancel : c * c⁻¹ = 1 := Rat.mul_inv_cancel c hcne
      grind [Rat.mul_assoc, Rat.mul_comm]

private theorem geometricLowerStep_refine_den_identity (p q r : Rat) :
    (q - p) * (1 + p * q) * (1 + r * r) +
      (r - q) * (1 + q * r) * (1 + p * p) =
    (r - p) * (1 + p * r) * (1 + q * q) +
      2 * (r - p) * (q - p) * (r - q) := by
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.add_assoc,
    Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]

theorem geometricLowerStep_refine (p q r : Rat) :
    geometricLowerStep p q + geometricLowerStep q r =
      geometricLowerStep p r + arctanAreaIncrement p q r := by
  let A : Rat := 1 + p * p
  let B : Rat := 1 + q * q
  let C : Rat := 1 + r * r
  let D : Rat := A * B * C
  have hApos : 0 < A := by
    dsimp [A]
    exact RationalCircle.Stage.one_add_square_pos p
  have hBpos : 0 < B := by
    dsimp [B]
    exact RationalCircle.Stage.one_add_square_pos q
  have hCpos : 0 < C := by
    dsimp [C]
    exact RationalCircle.Stage.one_add_square_pos r
  have hDpos : 0 < D := by
    dsimp [D]
    exact Rat.mul_pos (Rat.mul_pos hApos hBpos) hCpos
  have hABne : A * B ≠ 0 := Rat.ne_of_gt (Rat.mul_pos hApos hBpos)
  have hBCne : B * C ≠ 0 := Rat.ne_of_gt (Rat.mul_pos hBpos hCpos)
  have hACne : A * C ≠ 0 := Rat.ne_of_gt (Rat.mul_pos hApos hCpos)
  have hDne : D ≠ 0 := Rat.ne_of_gt hDpos
  apply rat_eq_of_mul_eq_mul_pos hDpos
  calc
    (geometricLowerStep p q + geometricLowerStep q r) * D
        = (q - p) * (1 + p * q) * C +
            (r - q) * (1 + q * r) * A := by
          dsimp [D, A, B, C]
          unfold geometricLowerStep
          rw [Rat.add_mul, Rat.div_def, Rat.div_def]
          grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
    _ = (r - p) * (1 + p * r) * B +
          2 * (r - p) * (q - p) * (r - q) := by
          dsimp [A, B, C]
          exact geometricLowerStep_refine_den_identity p q r
    _ = (geometricLowerStep p r + arctanAreaIncrement p q r) * D := by
          dsimp [D, A, B, C]
          unfold geometricLowerStep arctanAreaIncrement
          rw [Rat.add_mul, Rat.div_def, Rat.div_def]
          grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]

private theorem geometricUpperStep_refine_den_identity (p q r : Rat) :
    (q - p) * (1 + q * r) * (1 + p * r) +
      (r - q) * (1 + p * q) * (1 + p * r) =
    (r - p) * (1 + p * q) * (1 + q * r) -
      (r - p) * (q - p) * (r - q) := by
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.add_assoc,
    Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]

theorem geometricUpperStep_refine
    {p q r : Rat} (hp0 : 0 <= p) (hpq : p <= q) (hqr : q <= r) :
    geometricUpperStep p q + geometricUpperStep q r =
      geometricUpperStep p r - arctanAreaDecrement p q r := by
  let A : Rat := 1 + p * q
  let B : Rat := 1 + q * r
  let C : Rat := 1 + p * r
  let D : Rat := C * A * B
  have hq0 : 0 <= q := Rat.le_trans hp0 hpq
  have hr0 : 0 <= r := Rat.le_trans hq0 hqr
  have hApos : 0 < A := by
    dsimp [A]
    exact RationalCircle.Stage.one_add_mul_pos_of_nonneg hp0 hq0
  have hBpos : 0 < B := by
    dsimp [B]
    exact RationalCircle.Stage.one_add_mul_pos_of_nonneg hq0 hr0
  have hCpos : 0 < C := by
    dsimp [C]
    exact RationalCircle.Stage.one_add_mul_pos_of_nonneg hp0 hr0
  have hDpos : 0 < D := by
    dsimp [D]
    exact Rat.mul_pos (Rat.mul_pos hCpos hApos) hBpos
  have hAne : A ≠ 0 := Rat.ne_of_gt hApos
  have hBne : B ≠ 0 := Rat.ne_of_gt hBpos
  have hCne : C ≠ 0 := Rat.ne_of_gt hCpos
  have hDne : D ≠ 0 := Rat.ne_of_gt hDpos
  apply rat_eq_of_mul_eq_mul_pos hDpos
  calc
    (geometricUpperStep p q + geometricUpperStep q r) * D
        = (q - p) * B * C + (r - q) * A * C := by
          dsimp [D, A, B, C]
          unfold geometricUpperStep
          rw [Rat.add_mul, Rat.div_def, Rat.div_def]
          grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
    _ = (r - p) * A * B - (r - p) * (q - p) * (r - q) := by
          dsimp [A, B, C]
          have h := geometricUpperStep_refine_den_identity p q r
          grind [Rat.mul_assoc, Rat.mul_comm]
    _ = (geometricUpperStep p r - arctanAreaDecrement p q r) * D := by
          dsimp [D, A, B, C]
          unfold geometricUpperStep arctanAreaDecrement
          rw [Rat.div_def, Rat.div_def]
          grind [Rat.sub_eq_add_neg, Rat.add_mul, Rat.mul_assoc,
            Rat.mul_comm, Rat.mul_inv_cancel]

theorem geometricLowerStep_refine_le
    {p q r : Rat} (hpq : p <= q) (hqr : q <= r) :
    geometricLowerStep p r <=
      geometricLowerStep p q + geometricLowerStep q r := by
  have hinc := arctanAreaIncrement_nonneg hpq hqr
  have href := geometricLowerStep_refine p q r
  grind

theorem geometricUpperStep_refine_le
    {p q r : Rat} (hp0 : 0 <= p) (hpq : p <= q) (hqr : q <= r) :
    geometricUpperStep p q + geometricUpperStep q r <=
      geometricUpperStep p r := by
  have hdec := arctanAreaDecrement_nonneg hp0 hpq hqr
  have href := geometricUpperStep_refine hp0 hpq hqr
  grind [Rat.sub_eq_add_neg]

theorem geometricUpperStep_nonneg
    {p r : Rat} (hp0 : 0 <= p) (hpr : p <= r) :
    0 <= geometricUpperStep p r := by
  have hr0 : 0 <= r := Rat.le_trans hp0 hpr
  have hlen : 0 <= r - p := by grind [Rat.sub_eq_add_neg]
  have hden : 0 < 1 + p * r :=
    RationalCircle.Stage.one_add_mul_pos_of_nonneg hp0 hr0
  unfold geometricUpperStep
  rw [Rat.div_def]
  exact Rat.mul_nonneg hlen (Rat.le_of_lt ((Rat.inv_pos).2 hden))

theorem geometricLowerStep_nonneg
    {p r : Rat} (hp0 : 0 <= p) (hpr : p <= r) :
    0 <= geometricLowerStep p r := by
  have hr0 : 0 <= r := Rat.le_trans hp0 hpr
  have hlen : 0 <= r - p := by grind [Rat.sub_eq_add_neg]
  have hfactor : 0 <= 1 + p * r := by
    have hmul := Rat.mul_nonneg hp0 hr0
    grind
  have hleft : 0 < 1 + p * p :=
    RationalCircle.Stage.one_add_square_pos p
  have hright : 0 < 1 + r * r :=
    RationalCircle.Stage.one_add_square_pos r
  have hden : 0 < (1 + p * p) * (1 + r * r) :=
    Rat.mul_pos hleft hright
  unfold geometricLowerStep
  rw [Rat.div_def]
  exact Rat.mul_nonneg (Rat.mul_nonneg hlen hfactor)
    (Rat.le_of_lt ((Rat.inv_pos).2 hden))

theorem geometricLowerStep_zero_right (p : Rat) :
    geometricLowerStep p p = 0 := by
  grind [geometricLowerStep, Rat.sub_eq_add_neg]

private theorem left_square_le_factor {p r : Rat}
    (hp0 : 0 <= p) (hpr : p <= r) :
    1 + p * p <= 1 + p * r := by
  have hmul : p * p <= p * r :=
    Rat.mul_le_mul_of_nonneg_left hpr hp0
  grind

private theorem factor_le_right_square {p r : Rat}
    (hp0 : 0 <= p) (hpr : p <= r) :
    1 + p * r <= 1 + r * r := by
  have hr0 : 0 <= r := Rat.le_trans hp0 hpr
  have hmul : p * r <= r * r :=
    Rat.mul_le_mul_of_nonneg_right hpr hr0
  grind

theorem integralLowerStep_le_geometricLowerStep
    {p r : Rat} (hp0 : 0 <= p) (hpr : p <= r) :
    integralLowerStep p r <= geometricLowerStep p r := by
  have hlen : 0 <= r - p := by grind [Rat.sub_eq_add_neg]
  have hfac : 1 + p * p <= 1 + p * r :=
    left_square_le_factor hp0 hpr
  have hmain : (r - p) * (1 + p * p) <= (r - p) * (1 + p * r) :=
    Rat.mul_le_mul_of_nonneg_left hfac hlen
  have hpdenpos : 0 < 1 + p * p :=
    RationalCircle.Stage.one_add_square_pos p
  have hrdenpos : 0 < 1 + r * r :=
    RationalCircle.Stage.one_add_square_pos r
  have hrdenne : 1 + r * r ≠ 0 := Rat.ne_of_gt hrdenpos
  have hdenpos : 0 < (1 + p * p) * (1 + r * r) :=
    Rat.mul_pos hpdenpos hrdenpos
  refine Rat.le_of_mul_le_mul_right
    (c := (1 + p * p) * (1 + r * r)) ?_ hdenpos
  unfold integralLowerStep geometricLowerStep integralKernel
  calc
    ((r - p) * (1 / (1 + r * r))) *
        ((1 + p * p) * (1 + r * r))
        = (r - p) * (1 + p * p) := by
          rw [Rat.div_def]
          have hcancel : (1 + r * r) * (1 + r * r)⁻¹ = 1 :=
            Rat.mul_inv_cancel _ hrdenne
          grind [Rat.mul_assoc, Rat.mul_comm]
    _ <= (r - p) * (1 + p * r) := hmain
    _ = (((r - p) * (1 + p * r)) /
        ((1 + p * p) * (1 + r * r))) *
        ((1 + p * p) * (1 + r * r)) := by
          rw [Rat.div_def]
          have hcancel : ((1 + p * p) * (1 + r * r)) *
              (((1 + p * p) * (1 + r * r))⁻¹) = 1 :=
            Rat.mul_inv_cancel _ (Rat.ne_of_gt hdenpos)
          grind [Rat.mul_assoc, Rat.mul_comm]

theorem integralLowerStep_le_geometricUpperStep
    {p r : Rat} (hp0 : 0 <= p) (hpr : p <= r) :
    integralLowerStep p r <= geometricUpperStep p r := by
  have hr0 : 0 <= r := Rat.le_trans hp0 hpr
  have hlen : 0 <= r - p := by grind [Rat.sub_eq_add_neg]
  have hprpos : 0 < 1 + p * r :=
    RationalCircle.Stage.one_add_mul_pos_of_nonneg hp0 hr0
  have hfac : 1 + p * r <= 1 + r * r :=
    factor_le_right_square hp0 hpr
  have hinv : 1 / (1 + r * r) <= 1 / (1 + p * r) :=
    one_div_le_one_div_of_pos_of_le hprpos hfac
  unfold integralLowerStep geometricUpperStep integralKernel
  repeat rw [Rat.div_def] at hinv ⊢
  simpa [Rat.mul_assoc] using Rat.mul_le_mul_of_nonneg_left hinv hlen

theorem geometricLowerStep_le_integralUpperStep
    {p r : Rat} (hp0 : 0 <= p) (hpr : p <= r) :
    geometricLowerStep p r <= integralUpperStep p r := by
  have hlen : 0 <= r - p := by grind [Rat.sub_eq_add_neg]
  have hfac : 1 + p * r <= 1 + r * r :=
    factor_le_right_square hp0 hpr
  have hmain : (r - p) * (1 + p * r) <= (r - p) * (1 + r * r) :=
    Rat.mul_le_mul_of_nonneg_left hfac hlen
  have hpdenpos : 0 < 1 + p * p :=
    RationalCircle.Stage.one_add_square_pos p
  have hrdenpos : 0 < 1 + r * r :=
    RationalCircle.Stage.one_add_square_pos r
  have hpdenne : 1 + p * p ≠ 0 := Rat.ne_of_gt hpdenpos
  have hdenpos : 0 < (1 + p * p) * (1 + r * r) :=
    Rat.mul_pos hpdenpos hrdenpos
  refine Rat.le_of_mul_le_mul_right
    (c := (1 + p * p) * (1 + r * r)) ?_ hdenpos
  unfold geometricLowerStep integralUpperStep integralKernel
  calc
    (((r - p) * (1 + p * r)) /
        ((1 + p * p) * (1 + r * r))) *
        ((1 + p * p) * (1 + r * r))
        = (r - p) * (1 + p * r) := by
          rw [Rat.div_def]
          have hcancel : ((1 + p * p) * (1 + r * r)) *
              (((1 + p * p) * (1 + r * r))⁻¹) = 1 :=
            Rat.mul_inv_cancel _ (Rat.ne_of_gt hdenpos)
          grind [Rat.mul_assoc, Rat.mul_comm]
    _ <= (r - p) * (1 + r * r) := hmain
    _ = ((r - p) * (1 / (1 + p * p))) *
        ((1 + p * p) * (1 + r * r)) := by
          rw [Rat.div_def]
          have hcancel : (1 + p * p) * (1 + p * p)⁻¹ = 1 :=
            Rat.mul_inv_cancel _ hpdenne
          grind [Rat.mul_assoc, Rat.mul_comm]

theorem geometricUpperStep_le_integralUpperStep
    {p r : Rat} (hp0 : 0 <= p) (hpr : p <= r) :
    geometricUpperStep p r <= integralUpperStep p r := by
  have hlen : 0 <= r - p := by grind [Rat.sub_eq_add_neg]
  have hpdenpos : 0 < 1 + p * p :=
    RationalCircle.Stage.one_add_square_pos p
  have hfac : 1 + p * p <= 1 + p * r :=
    left_square_le_factor hp0 hpr
  have hinv : 1 / (1 + p * r) <= 1 / (1 + p * p) :=
    one_div_le_one_div_of_pos_of_le hpdenpos hfac
  unfold geometricUpperStep integralUpperStep integralKernel
  repeat rw [Rat.div_def] at hinv ⊢
  simpa [Rat.mul_assoc] using Rat.mul_le_mul_of_nonneg_left hinv hlen

private theorem geometric_factor_square_le_square_den
    {p r : Rat} :
    (1 + p * r) * (1 + p * r) <=
      (1 + p * p) * (1 + r * r) := by
  have hsq : 0 <= (r - p) * (r - p) :=
    RationalCircle.Stage.ratSquare_nonneg (r - p)
  calc
    (1 + p * r) * (1 + p * r)
        <= (1 + p * r) * (1 + p * r) + (r - p) * (r - p) := by
          grind
    _ = (1 + p * p) * (1 + r * r) := by
          grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
            Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]

theorem geometricLowerStep_le_geometricUpperStep
    {p r : Rat} (hp0 : 0 <= p) (hpr : p <= r) :
    geometricLowerStep p r <= geometricUpperStep p r := by
  let A : Rat := 1 + p * r
  let B : Rat := (1 + p * p) * (1 + r * r)
  let L : Rat := r - p
  have hr0 : 0 <= r := Rat.le_trans hp0 hpr
  have hApos : 0 < A := by
    dsimp [A]
    exact RationalCircle.Stage.one_add_mul_pos_of_nonneg hp0 hr0
  have hBpos : 0 < B := by
    dsimp [B]
    exact Rat.mul_pos
      (RationalCircle.Stage.one_add_square_pos p)
      (RationalCircle.Stage.one_add_square_pos r)
  have hlen : 0 <= L := by
    dsimp [L]
    grind [Rat.sub_eq_add_neg]
  have hfac : A * A <= B := by
    dsimp [A, B]
    exact geometric_factor_square_le_square_den
  refine Rat.le_of_mul_le_mul_right (c := B * A) ?_
    (Rat.mul_pos hBpos hApos)
  have hAne : A ≠ 0 := Rat.ne_of_gt hApos
  have hBne : B ≠ 0 := Rat.ne_of_gt hBpos
  unfold geometricLowerStep geometricUpperStep
  dsimp [A, B, L] at hApos hBpos hlen hfac ⊢
  calc
    (((r - p) * (1 + p * r)) / ((1 + p * p) * (1 + r * r))) *
        (((1 + p * p) * (1 + r * r)) * (1 + p * r))
        = (r - p) * ((1 + p * r) * (1 + p * r)) := by
          rw [Rat.div_def]
          grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
    _ <= (r - p) * ((1 + p * p) * (1 + r * r)) :=
          Rat.mul_le_mul_of_nonneg_left hfac hlen
    _ = ((r - p) / (1 + p * r)) *
        (((1 + p * p) * (1 + r * r)) * (1 + p * r)) := by
          rw [Rat.div_def]
          grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]

theorem integralCellInterval_contains_geometricCellInterval
    {p r : Rat} (hp0 : 0 <= p) (hpr : p <= r) :
    (integralCellInterval p r).ContainsInterval
      (geometricCellInterval p r) := by
  unfold QInterval.ContainsInterval integralCellInterval geometricCellInterval
  exact ⟨integralLowerStep_le_geometricLowerStep hp0 hpr,
    geometricUpperStep_le_integralUpperStep hp0 hpr⟩

theorem integralCellInterval_overlaps_geometricCellInterval
    {p r : Rat} (hp0 : 0 <= p) (hpr : p <= r) :
    QInterval.Overlaps (integralCellInterval p r)
      (geometricCellInterval p r) := by
  unfold QInterval.Overlaps integralCellInterval geometricCellInterval
  exact ⟨integralLowerStep_le_geometricUpperStep hp0 hpr,
    geometricLowerStep_le_integralUpperStep hp0 hpr⟩

/-- A finite partition whose cells lie in the nonnegative half-line. -/
def NonnegativeIntervals : List (Rat × Rat) -> Prop
  | [] => True
  | (p, r) :: rest =>
      0 <= p /\ p <= r /\ NonnegativeIntervals rest

/-- A finite partition whose cells lie in the unit interval. -/
def UnitIntervals : List (Rat × Rat) -> Prop
  | [] => True
  | (p, r) :: rest =>
      0 <= p /\ p <= r /\ r <= 1 /\ UnitIntervals rest

/-- Ordered coverage of `[a,b]` by a finite list of rational cells.  This is
the bookkeeping invariant needed to compare different lower/upper sum
schedules for the same kernel. -/
def CoversInterval : Rat -> Rat -> List (Rat × Rat) -> Prop
  | a, b, [] => a = b
  | a, b, (p, r) :: rest =>
      p = a /\ p <= r /\ CoversInterval r b rest

theorem CoversInterval.start_le_end
    {a b : Rat} {intervals : List (Rat × Rat)}
    (h : CoversInterval a b intervals) :
    a <= b := by
  induction intervals generalizing a with
  | nil =>
      have hab : a = b := by simpa [CoversInterval] using h
      rw [hab]
      exact Rat.le_refl
  | cons interval rest ih =>
      rcases interval with ⟨p, r⟩
      rcases h with ⟨hp, hpr, hrest⟩
      subst p
      exact Rat.le_trans hpr (ih hrest)

theorem CoversInterval.nonnegative
    {a b : Rat} {intervals : List (Rat × Rat)}
    (ha : 0 <= a) (h : CoversInterval a b intervals) :
    NonnegativeIntervals intervals := by
  induction intervals generalizing a with
  | nil =>
      simp [NonnegativeIntervals]
  | cons interval rest ih =>
      rcases interval with ⟨p, r⟩
      rcases h with ⟨hp, hpr, hrest⟩
      subst p
      exact ⟨ha, hpr, ih (Rat.le_trans ha hpr) hrest⟩

theorem CoversInterval.unit
    {a b : Rat} {intervals : List (Rat × Rat)}
    (ha : 0 <= a) (hb : b <= 1)
    (h : CoversInterval a b intervals) :
    UnitIntervals intervals := by
  induction intervals generalizing a with
  | nil =>
      simp [UnitIntervals]
  | cons interval rest ih =>
      rcases interval with ⟨p, r⟩
      rcases h with ⟨hp, hpr, hrest⟩
      subst p
      have hr0 : 0 <= r := Rat.le_trans ha hpr
      have hr1 : r <= 1 :=
        Rat.le_trans (CoversInterval.start_le_end hrest) hb
      exact ⟨ha, hpr, hr1, ih hr0 hrest⟩

theorem CoversInterval.append
    {a b c : Rat} {left right : List (Rat × Rat)}
    (hleft : CoversInterval a b left)
    (hright : CoversInterval b c right) :
    CoversInterval a c (left ++ right) := by
  induction left generalizing a with
  | nil =>
      have hab : a = b := by
        simpa [CoversInterval] using hleft
      subst b
      simpa [CoversInterval] using hright
  | cons interval rest ih =>
      rcases interval with ⟨p, r⟩
      rcases hleft with ⟨hp, hpr, hrest⟩
      subst p
      simp [CoversInterval]
      exact ⟨hpr, ih hrest⟩

theorem CoversInterval.single
    {a b : Rat} (hab : a <= b) :
    CoversInterval a b [(a, b)] := by
  simp [CoversInterval, hab]

theorem CoversInterval.extend_right
    {a b c : Rat} {intervals : List (Rat × Rat)}
    (h : CoversInterval a b intervals) (hbc : b <= c) :
    CoversInterval a c (intervals ++ [(b, c)]) :=
  CoversInterval.append h (CoversInterval.single hbc)

theorem unitIntervals_nonnegative
    (intervals : List (Rat × Rat))
    (hwf : UnitIntervals intervals) :
    NonnegativeIntervals intervals := by
  induction intervals with
  | nil =>
      simp [NonnegativeIntervals]
  | cons interval rest ih =>
      rcases interval with ⟨p, r⟩
      rcases hwf with ⟨hp0, hpr, _hr1, hrest⟩
      exact ⟨hp0, hpr, ih hrest⟩

def integralLowerSum : List (Rat × Rat) -> Rat
  | [] => 0
  | (p, r) :: rest => integralLowerStep p r + integralLowerSum rest

def integralUpperSum : List (Rat × Rat) -> Rat
  | [] => 0
  | (p, r) :: rest => integralUpperStep p r + integralUpperSum rest

def geometricLowerSum : List (Rat × Rat) -> Rat
  | [] => 0
  | (p, r) :: rest => geometricLowerStep p r + geometricLowerSum rest

def geometricUpperSum : List (Rat × Rat) -> Rat
  | [] => 0
  | (p, r) :: rest => geometricUpperStep p r + geometricUpperSum rest

def intervalSquareSum : List (Rat × Rat) -> Rat
  | [] => 0
  | (p, r) :: rest => (r - p) * (r - p) + intervalSquareSum rest

def integralSumInterval (intervals : List (Rat × Rat)) : QInterval :=
  { lo := integralLowerSum intervals, hi := integralUpperSum intervals }

/-- Apply the rational tangent-addition chart to every endpoint of a finite
interval partition. -/
def chartAddIntervals (u : Rat) : List (Rat × Rat) -> List (Rat × Rat)
  | [] => []
  | (p, r) :: rest =>
      (RationalCircle.Trigonometry.chartAddParameter u p,
        RationalCircle.Trigonometry.chartAddParameter u r) ::
        chartAddIntervals u rest

/-- Positivity of the two chart denominators on each cell of a finite
partition.  It is the finite admissibility condition for chart transport. -/
def ChartAddPositiveDenominators (u : Rat) : List (Rat × Rat) -> Prop
  | [] => True
  | (p, r) :: rest =>
      0 < RationalCircle.Trigonometry.chartAddDen u p /\
        0 < RationalCircle.Trigonometry.chartAddDen u r /\
          ChartAddPositiveDenominators u rest

/-- A finite source partition on which every right endpoint stays far enough
from the tangent-chart pole for the uniform factor-eight distortion bound. -/
def ChartAddRightProductAtMostHalf (u : Rat) : List (Rat × Rat) -> Prop
  | [] => True
  | (_p, r) :: rest =>
      u * r <= (1 : Rat) / 2 /\
        ChartAddRightProductAtMostHalf u rest

/-- A cover inherits the right-endpoint product bound from its final endpoint.
This is the local replacement for unnecessarily requiring the chart base to
lie in the first half of the whole unit interval. -/
theorem CoversInterval.chartAddRightProductAtMostHalf
    {u a b : Rat} {intervals : List (Rat × Rat)}
    (hu0 : 0 <= u) (hub : u * b <= (1 : Rat) / 2)
    (hcover : CoversInterval a b intervals) :
    ChartAddRightProductAtMostHalf u intervals := by
  induction intervals generalizing a with
  | nil =>
      simp [ChartAddRightProductAtMostHalf]
  | cons interval rest ih =>
      rcases interval with ⟨p, r⟩
      rcases hcover with ⟨hpa, hpr, hrest⟩
      have hrb : r <= b := CoversInterval.start_le_end hrest
      have hur : u * r <= (1 : Rat) / 2 := by
        calc
          u * r <= u * b := Rat.mul_le_mul_of_nonneg_left hrb hu0
          _ <= (1 : Rat) / 2 := hub
      simp only [ChartAddRightProductAtMostHalf]
      exact ⟨hur, ih hrest⟩

/-- Summed lower rectangles decrease under an admissible nonnegative
tangent-addition chart transport. -/
theorem chartAddIntervals_lowerSum_le
    (u : Rat) (intervals : List (Rat × Rat))
    (hu : 0 <= u)
    (hintervals : NonnegativeIntervals intervals)
    (hden : ChartAddPositiveDenominators u intervals) :
    integralLowerSum (chartAddIntervals u intervals) <=
      integralLowerSum intervals := by
  induction intervals with
  | nil =>
      simp [chartAddIntervals, integralLowerSum]
  | cons interval rest ih =>
      rcases interval with ⟨p, r⟩
      rcases hintervals with ⟨hp0, hpr, hrest⟩
      rcases hden with ⟨hpden, hrden, hdenrest⟩
      simp only [chartAddIntervals, integralLowerSum]
      exact rat_add_le_add
        (chartAdd_integralLowerStep_le hu hpr hpden hrden)
        (ih hrest hdenrest)

/-- Summed upper rectangles increase under an admissible nonnegative
tangent-addition chart transport. -/
theorem integralUpperSum_le_chartAddIntervals
    (u : Rat) (intervals : List (Rat × Rat))
    (hu : 0 <= u)
    (hintervals : NonnegativeIntervals intervals)
    (hden : ChartAddPositiveDenominators u intervals) :
    integralUpperSum intervals <=
      integralUpperSum (chartAddIntervals u intervals) := by
  induction intervals with
  | nil =>
      simp [chartAddIntervals, integralUpperSum]
  | cons interval rest ih =>
      rcases interval with ⟨p, r⟩
      rcases hintervals with ⟨hp0, hpr, hrest⟩
      rcases hden with ⟨hpden, hrden, hdenrest⟩
      simp only [chartAddIntervals, integralUpperSum]
      exact rat_add_le_add
        (integralUpperStep_le_chartAdd hu hpr hpden hrden)
        (ih hrest hdenrest)

/-- The transported rectangle bracket contains the source rectangle bracket
cell-for-cell. -/
theorem chartAddIntervals_integralSum_contains
    (u : Rat) (intervals : List (Rat × Rat))
    (hu : 0 <= u)
    (hintervals : NonnegativeIntervals intervals)
    (hden : ChartAddPositiveDenominators u intervals) :
    (integralSumInterval (chartAddIntervals u intervals)).ContainsInterval
      (integralSumInterval intervals) := by
  unfold QInterval.ContainsInterval integralSumInterval
  exact ⟨chartAddIntervals_lowerSum_le u intervals hu hintervals hden,
    integralUpperSum_le_chartAddIntervals u intervals hu hintervals hden⟩

/-- An admissible nonnegative partition remains a nonnegative partition after
the tangent-addition chart is applied to all endpoints. -/
theorem chartAddIntervals_nonnegative
    (u : Rat) (intervals : List (Rat × Rat))
    (hu : 0 <= u)
    (hintervals : NonnegativeIntervals intervals)
    (hden : ChartAddPositiveDenominators u intervals) :
    NonnegativeIntervals (chartAddIntervals u intervals) := by
  induction intervals with
  | nil =>
      simp [chartAddIntervals, NonnegativeIntervals]
  | cons interval rest ih =>
      rcases interval with ⟨p, r⟩
      rcases hintervals with ⟨hp0, hpr, hrest⟩
      rcases hden with ⟨hpden, hrden, hdenrest⟩
      have hleft :
          0 <= RationalCircle.Trigonometry.chartAddParameter u p := by
        unfold RationalCircle.Trigonometry.chartAddParameter
          RationalCircle.Trigonometry.chartAddNum
          RationalCircle.Trigonometry.chartAddDen
        rw [Rat.div_def]
        exact Rat.mul_nonneg
          (Rat.add_nonneg hu hp0)
          (Rat.le_of_lt ((Rat.inv_pos).2 hpden))
      have horder :
          RationalCircle.Trigonometry.chartAddParameter u p <=
            RationalCircle.Trigonometry.chartAddParameter u r :=
        RationalCircle.Trigonometry.chartAddParameter_mono hpden hrden hpr
      simp [chartAddIntervals, NonnegativeIntervals, hleft, horder,
        ih hrest hdenrest]

/-- Applying the chart endpointwise transports an ordered finite cover of
`[a,b]` to an ordered cover of the chart image interval. -/
theorem chartAddIntervals_covers
    (u a b : Rat) (intervals : List (Rat × Rat))
    (hcover : CoversInterval a b intervals)
    (hden : ChartAddPositiveDenominators u intervals) :
    CoversInterval
      (RationalCircle.Trigonometry.chartAddParameter u a)
      (RationalCircle.Trigonometry.chartAddParameter u b)
      (chartAddIntervals u intervals) := by
  induction intervals generalizing a with
  | nil =>
      simp [chartAddIntervals, CoversInterval] at hcover ⊢
      exact congrArg (RationalCircle.Trigonometry.chartAddParameter u) hcover
  | cons interval rest ih =>
      rcases interval with ⟨p, r⟩
      rcases hcover with ⟨hpa, hpr, hrest⟩
      rcases hden with ⟨hpden, hrden, hdenrest⟩
      subst p
      simp only [chartAddIntervals, CoversInterval]
      exact ⟨True.intro,
        RationalCircle.Trigonometry.chartAddParameter_mono
          hpden hrden hpr,
        ih r hrest hdenrest⟩

/-- A unit source endpoint has a positive tangent-chart denominator whenever
the chart parameter is nonnegative and strictly below one. -/
theorem chartAddDen_pos_of_unit
    {u t : Rat} (hu0 : 0 <= u) (hu1 : u < 1)
    (ht1 : t <= 1) :
    0 < RationalCircle.Trigonometry.chartAddDen u t := by
  unfold RationalCircle.Trigonometry.chartAddDen
  have hmul : u * t <= u := by
    calc
      u * t <= u * 1 := Rat.mul_le_mul_of_nonneg_left ht1 hu0
      _ = u := by grind
  grind [Rat.sub_eq_add_neg]

/-- A chart parameter from zero up to, but not including, one has positive
chart denominators on every cell of a unit-interval partition. -/
theorem chartAddPositiveDenominators_of_unitIntervals
    (u : Rat) (intervals : List (Rat × Rat))
    (hu0 : 0 <= u) (hu1 : u < 1)
    (hintervals : UnitIntervals intervals) :
    ChartAddPositiveDenominators u intervals := by
  induction intervals with
  | nil =>
      simp [ChartAddPositiveDenominators]
  | cons interval rest ih =>
      rcases interval with ⟨p, r⟩
      rcases hintervals with ⟨hp0, hpr, hr1, hrest⟩
      have hp1 : p <= 1 := Rat.le_trans hpr hr1
      have hmulP : u * p <= u := by
        calc
          u * p <= u * 1 := Rat.mul_le_mul_of_nonneg_left hp1 hu0
          _ = u := by grind
      have hmulR : u * r <= u := by
        calc
          u * r <= u * 1 := Rat.mul_le_mul_of_nonneg_left hr1 hu0
          _ = u := by grind
      have hdenP : 0 < RationalCircle.Trigonometry.chartAddDen u p := by
        unfold RationalCircle.Trigonometry.chartAddDen
        grind [Rat.sub_eq_add_neg]
      have hdenR : 0 < RationalCircle.Trigonometry.chartAddDen u r := by
        unfold RationalCircle.Trigonometry.chartAddDen
        grind [Rat.sub_eq_add_neg]
      exact ⟨hdenP, hdenR, ih hrest⟩

/-- On the Machin-relevant half-unit chart, endpointwise transport multiplies
the squared mesh budget by at most sixty-four. -/
theorem chartAddIntervals_squareSum_le_sixtyFour
    (u : Rat) (intervals : List (Rat × Rat))
    (hu0 : 0 <= u) (huHalf : u <= (1 : Rat) / 2)
    (hintervals : UnitIntervals intervals) :
    intervalSquareSum (chartAddIntervals u intervals) <=
      64 * intervalSquareSum intervals := by
  have hu1 : u < 1 := by
    have hhalf : (1 : Rat) / 2 < 1 := by decide +kernel
    grind
  induction intervals with
  | nil =>
      simp [chartAddIntervals, intervalSquareSum]
  | cons interval rest ih =>
      rcases interval with ⟨p, r⟩
      rcases hintervals with ⟨hp0, hpr, hr1, hrest⟩
      have hp1 : p <= 1 := Rat.le_trans hpr hr1
      have hdenP :=
        chartAddDen_pos_of_unit hu0 hu1 hp1
      have hdenR :=
        chartAddDen_pos_of_unit hu0 hu1 hr1
      have horder :
          RationalCircle.Trigonometry.chartAddParameter u p <=
            RationalCircle.Trigonometry.chartAddParameter u r :=
        RationalCircle.Trigonometry.chartAddParameter_mono hdenP hdenR hpr
      have himageNonneg :
          0 <= RationalCircle.Trigonometry.chartAddParameter u r -
            RationalCircle.Trigonometry.chartAddParameter u p := by
        grind [Rat.sub_eq_add_neg]
      have hsourceNonneg : 0 <= r - p := by
        grind [Rat.sub_eq_add_neg]
      have himage :
          RationalCircle.Trigonometry.chartAddParameter u r -
            RationalCircle.Trigonometry.chartAddParameter u p <=
              8 * (r - p) :=
        chartAddParameter_width_le_eight_mul hu0 huHalf hpr hr1
      have hscaledNonneg : 0 <= 8 * (r - p) :=
        Rat.mul_nonneg (by decide +kernel) hsourceNonneg
      have hcellSquare :
          (RationalCircle.Trigonometry.chartAddParameter u r -
            RationalCircle.Trigonometry.chartAddParameter u p) *
              (RationalCircle.Trigonometry.chartAddParameter u r -
                RationalCircle.Trigonometry.chartAddParameter u p) <=
            64 * ((r - p) * (r - p)) := by
        calc
          (RationalCircle.Trigonometry.chartAddParameter u r -
            RationalCircle.Trigonometry.chartAddParameter u p) *
              (RationalCircle.Trigonometry.chartAddParameter u r -
                RationalCircle.Trigonometry.chartAddParameter u p) <=
            (8 * (r - p)) *
              (RationalCircle.Trigonometry.chartAddParameter u r -
                RationalCircle.Trigonometry.chartAddParameter u p) :=
              Rat.mul_le_mul_of_nonneg_right himage himageNonneg
          _ <= (8 * (r - p)) * (8 * (r - p)) :=
              Rat.mul_le_mul_of_nonneg_left himage hscaledNonneg
          _ = 64 * ((r - p) * (r - p)) := by
              grind [Rat.mul_assoc, Rat.mul_comm]
      have htail := ih hrest
      simp only [chartAddIntervals, intervalSquareSum]
      calc
        (RationalCircle.Trigonometry.chartAddParameter u r -
          RationalCircle.Trigonometry.chartAddParameter u p) *
            (RationalCircle.Trigonometry.chartAddParameter u r -
              RationalCircle.Trigonometry.chartAddParameter u p) +
            intervalSquareSum (chartAddIntervals u rest) <=
          64 * ((r - p) * (r - p)) +
            64 * intervalSquareSum rest :=
              rat_add_le_add hcellSquare htail
        _ = 64 * ((r - p) * (r - p) + intervalSquareSum rest) := by
              grind [Rat.mul_add, Rat.add_assoc, Rat.add_comm]

/-- The local product condition is enough for the transported squared-mesh
bound.  Unlike the older half-chart lemma, the base may lie anywhere in the
unit interval as long as every source cell stays within the pole margin. -/
theorem chartAddIntervals_squareSum_le_sixtyFour_of_rightProduct_le_half
    (u : Rat) (intervals : List (Rat × Rat))
    (hu0 : 0 <= u) (hu1 : u <= 1)
    (hintervals : UnitIntervals intervals)
    (hproduct : ChartAddRightProductAtMostHalf u intervals) :
    intervalSquareSum (chartAddIntervals u intervals) <=
      64 * intervalSquareSum intervals := by
  induction intervals with
  | nil =>
      simp [chartAddIntervals, intervalSquareSum]
  | cons interval rest ih =>
      rcases interval with ⟨p, r⟩
      rcases hintervals with ⟨hp0, hpr, hr1, hrest⟩
      rcases hproduct with ⟨hur, hproductRest⟩
      have hmulP : u * p <= (1 : Rat) / 2 :=
        Rat.le_trans (Rat.mul_le_mul_of_nonneg_left hpr hu0) hur
      have hdenP : 0 < RationalCircle.Trigonometry.chartAddDen u p := by
        unfold RationalCircle.Trigonometry.chartAddDen
        have hhalfPos : (0 : Rat) < 1 / 2 := by decide +kernel
        grind [Rat.sub_eq_add_neg]
      have hdenR : 0 < RationalCircle.Trigonometry.chartAddDen u r := by
        unfold RationalCircle.Trigonometry.chartAddDen
        have hhalfPos : (0 : Rat) < 1 / 2 := by decide +kernel
        grind [Rat.sub_eq_add_neg]
      have horder :
          RationalCircle.Trigonometry.chartAddParameter u p <=
            RationalCircle.Trigonometry.chartAddParameter u r :=
        RationalCircle.Trigonometry.chartAddParameter_mono hdenP hdenR hpr
      have himageNonneg :
          0 <= RationalCircle.Trigonometry.chartAddParameter u r -
            RationalCircle.Trigonometry.chartAddParameter u p := by
        grind [Rat.sub_eq_add_neg]
      have hsourceNonneg : 0 <= r - p := by
        grind [Rat.sub_eq_add_neg]
      have himage :
          RationalCircle.Trigonometry.chartAddParameter u r -
            RationalCircle.Trigonometry.chartAddParameter u p <=
              8 * (r - p) :=
        chartAddParameter_width_le_eight_mul_of_rightProduct_le_half
          hu0 hu1 hpr hur
      have hscaledNonneg : 0 <= 8 * (r - p) :=
        Rat.mul_nonneg (by decide +kernel) hsourceNonneg
      have hcellSquare :
          (RationalCircle.Trigonometry.chartAddParameter u r -
            RationalCircle.Trigonometry.chartAddParameter u p) *
              (RationalCircle.Trigonometry.chartAddParameter u r -
                RationalCircle.Trigonometry.chartAddParameter u p) <=
            64 * ((r - p) * (r - p)) := by
        calc
          (RationalCircle.Trigonometry.chartAddParameter u r -
            RationalCircle.Trigonometry.chartAddParameter u p) *
              (RationalCircle.Trigonometry.chartAddParameter u r -
                RationalCircle.Trigonometry.chartAddParameter u p) <=
            (8 * (r - p)) *
              (RationalCircle.Trigonometry.chartAddParameter u r -
                RationalCircle.Trigonometry.chartAddParameter u p) :=
              Rat.mul_le_mul_of_nonneg_right himage himageNonneg
          _ <= (8 * (r - p)) * (8 * (r - p)) :=
              Rat.mul_le_mul_of_nonneg_left himage hscaledNonneg
          _ = 64 * ((r - p) * (r - p)) := by
              grind [Rat.mul_assoc, Rat.mul_comm]
      have htail := ih hrest hproductRest
      simp only [chartAddIntervals, intervalSquareSum]
      calc
        (RationalCircle.Trigonometry.chartAddParameter u r -
          RationalCircle.Trigonometry.chartAddParameter u p) *
            (RationalCircle.Trigonometry.chartAddParameter u r -
              RationalCircle.Trigonometry.chartAddParameter u p) +
            intervalSquareSum (chartAddIntervals u rest) <=
          64 * ((r - p) * (r - p)) +
            64 * intervalSquareSum rest :=
              rat_add_le_add hcellSquare htail
        _ = 64 * ((r - p) * (r - p) + intervalSquareSum rest) := by
              grind [Rat.mul_add, Rat.add_assoc, Rat.add_comm]

def geometricSumInterval (intervals : List (Rat × Rat)) : QInterval :=
  { lo := geometricLowerSum intervals, hi := geometricUpperSum intervals }

theorem integralLowerSum_le_geometricLowerSum
    (intervals : List (Rat × Rat))
    (hwf : NonnegativeIntervals intervals) :
    integralLowerSum intervals <= geometricLowerSum intervals := by
  induction intervals with
  | nil => simp [integralLowerSum, geometricLowerSum]
  | cons interval rest ih =>
      rcases interval with ⟨p, r⟩
      rcases hwf with ⟨hp0, hpr, hrest⟩
      simp [integralLowerSum, geometricLowerSum]
      exact rat_add_le_add
        (integralLowerStep_le_geometricLowerStep hp0 hpr)
        (ih hrest)

theorem integralLowerSum_le_geometricUpperSum
    (intervals : List (Rat × Rat))
    (hwf : NonnegativeIntervals intervals) :
    integralLowerSum intervals <= geometricUpperSum intervals := by
  induction intervals with
  | nil => simp [integralLowerSum, geometricUpperSum]
  | cons interval rest ih =>
      rcases interval with ⟨p, r⟩
      rcases hwf with ⟨hp0, hpr, hrest⟩
      simp [integralLowerSum, geometricUpperSum]
      exact rat_add_le_add
        (integralLowerStep_le_geometricUpperStep hp0 hpr)
        (ih hrest)

theorem geometricLowerSum_le_integralUpperSum
    (intervals : List (Rat × Rat))
    (hwf : NonnegativeIntervals intervals) :
    geometricLowerSum intervals <= integralUpperSum intervals := by
  induction intervals with
  | nil => simp [geometricLowerSum, integralUpperSum]
  | cons interval rest ih =>
      rcases interval with ⟨p, r⟩
      rcases hwf with ⟨hp0, hpr, hrest⟩
      simp [geometricLowerSum, integralUpperSum]
      exact rat_add_le_add
        (geometricLowerStep_le_integralUpperStep hp0 hpr)
        (ih hrest)

theorem geometricUpperSum_le_integralUpperSum
    (intervals : List (Rat × Rat))
    (hwf : NonnegativeIntervals intervals) :
    geometricUpperSum intervals <= integralUpperSum intervals := by
  induction intervals with
  | nil => simp [geometricUpperSum, integralUpperSum]
  | cons interval rest ih =>
      rcases interval with ⟨p, r⟩
      rcases hwf with ⟨hp0, hpr, hrest⟩
      simp [geometricUpperSum, integralUpperSum]
      exact rat_add_le_add
        (geometricUpperStep_le_integralUpperStep hp0 hpr)
        (ih hrest)

theorem geometricLowerSum_le_geometricUpperSum
    (intervals : List (Rat × Rat))
    (hwf : NonnegativeIntervals intervals) :
    geometricLowerSum intervals <= geometricUpperSum intervals := by
  induction intervals with
  | nil => simp [geometricLowerSum, geometricUpperSum]
  | cons interval rest ih =>
      rcases interval with ⟨p, r⟩
      rcases hwf with ⟨hp0, hpr, hrest⟩
      simp [geometricLowerSum, geometricUpperSum]
      exact rat_add_le_add
        (geometricLowerStep_le_geometricUpperStep hp0 hpr)
        (ih hrest)

theorem integralLowerSum_le_integralUpperSum
    (intervals : List (Rat × Rat))
    (hwf : NonnegativeIntervals intervals) :
    integralLowerSum intervals <= integralUpperSum intervals := by
  induction intervals with
  | nil => simp [integralLowerSum, integralUpperSum]
  | cons interval rest ih =>
      rcases interval with ⟨p, r⟩
      rcases hwf with ⟨hp0, hpr, hrest⟩
      simp [integralLowerSum, integralUpperSum]
      exact rat_add_le_add
        (integralLowerStep_le_integralUpperStep hp0 hpr)
        (ih hrest)

theorem integralLowerSum_nonneg
    (intervals : List (Rat × Rat))
    (hwf : NonnegativeIntervals intervals) :
    0 <= integralLowerSum intervals := by
  induction intervals with
  | nil => simp [integralLowerSum]
  | cons interval rest ih =>
      rcases interval with ⟨p, r⟩
      rcases hwf with ⟨_hp0, hpr, hrest⟩
      simp [integralLowerSum]
      have hsum := rat_add_le_add
        (integralLowerStep_nonneg hpr)
        (ih hrest)
      grind

theorem integralUpperSum_nonneg
    (intervals : List (Rat × Rat))
    (hwf : NonnegativeIntervals intervals) :
    0 <= integralUpperSum intervals := by
  induction intervals with
  | nil => simp [integralUpperSum]
  | cons interval rest ih =>
      rcases interval with ⟨p, r⟩
      rcases hwf with ⟨_hp0, hpr, hrest⟩
      simp [integralUpperSum]
      have hsum := rat_add_le_add
        (integralUpperStep_nonneg hpr)
        (ih hrest)
      grind

/-- An upper rectangle sum for a finite cover is bounded by the length of
the covered interval.  This uses only the pointwise bound
`1 / (1 + u^2) <= 1`. -/
theorem integralUpperSum_le_intervalLength
    {a b : Rat} {intervals : List (Rat × Rat)}
    (hcover : CoversInterval a b intervals) :
    integralUpperSum intervals <= b - a := by
  induction intervals generalizing a with
  | nil =>
      have hab : a = b := by
        simpa [CoversInterval] using hcover
      subst b
      simp [integralUpperSum]
      grind [Rat.sub_eq_add_neg]
  | cons interval rest ih =>
      rcases interval with ⟨p, r⟩
      rcases hcover with ⟨hp, hpr, hrest⟩
      subst p
      calc
        integralUpperSum ((a, r) :: rest) =
            integralUpperStep a r + integralUpperSum rest := rfl
        _ <= (r - a) + (b - r) :=
          rat_add_le_add (integralUpperStep_le_width hpr) (ih hrest)
        _ = b - a := by
          grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm]

theorem intervalLength_mul_integralKernel_right_le_integralLowerSum
    {a b : Rat} {intervals : List (Rat × Rat)}
    (ha : 0 <= a) (hcover : CoversInterval a b intervals) :
    (b - a) * integralKernel b <= integralLowerSum intervals := by
  induction intervals generalizing a with
  | nil =>
      have hab : a = b := by
        simpa [CoversInterval] using hcover
      subst b
      simp [integralLowerSum]
      grind [Rat.sub_eq_add_neg]
  | cons interval rest ih =>
      rcases interval with ⟨p, r⟩
      rcases hcover with ⟨hp, hpr, hrest⟩
      subst p
      have hr0 : 0 <= r := Rat.le_trans ha hpr
      have hrb : r <= b := CoversInterval.start_le_end hrest
      have hkernel : integralKernel b <= integralKernel r :=
        integralKernel_antitone_nonneg hr0 hrb
      have hlength : 0 <= r - a := by
        grind [Rat.sub_eq_add_neg]
      have hhead :
          (r - a) * integralKernel b <= integralLowerStep a r := by
        unfold integralLowerStep
        exact Rat.mul_le_mul_of_nonneg_left hkernel hlength
      calc
        (b - a) * integralKernel b =
            (r - a) * integralKernel b + (b - r) * integralKernel b := by
              grind [Rat.sub_eq_add_neg, Rat.add_mul, Rat.add_assoc,
                Rat.add_comm]
        _ <= integralLowerStep a r + integralLowerSum rest :=
          rat_add_le_add hhead (ih hr0 hrest)
        _ = integralLowerSum ((a, r) :: rest) := rfl

theorem integralLowerStep_zero_right (p : Rat) :
    integralLowerStep p p = 0 := by
  grind [integralLowerStep, Rat.sub_eq_add_neg]

theorem integralLowerSum_eq_zero_of_covers_point
    {a : Rat} {intervals : List (Rat × Rat)}
    (ha : 0 <= a) (hcover : CoversInterval a a intervals) :
    integralLowerSum intervals = 0 := by
  induction intervals generalizing a with
  | nil =>
      simp [integralLowerSum]
  | cons interval rest ih =>
      rcases interval with ⟨p, r⟩
      rcases hcover with ⟨hp, hpr, hrest⟩
      subst p
      have hra_le : r <= a := CoversInterval.start_le_end hrest
      have hra : r = a := by grind
      subst r
      have htail := ih ha hrest
      simp [integralLowerSum, integralLowerStep_zero_right, htail]
      grind

theorem geometricUpperSum_nonneg
    (intervals : List (Rat × Rat))
    (hwf : NonnegativeIntervals intervals) :
    0 <= geometricUpperSum intervals := by
  induction intervals with
  | nil => simp [geometricUpperSum]
  | cons interval rest ih =>
      rcases interval with ⟨p, r⟩
      rcases hwf with ⟨hp0, hpr, hrest⟩
      simp [geometricUpperSum]
      have hsum := rat_add_le_add
        (geometricUpperStep_nonneg hp0 hpr)
        (ih hrest)
      grind

theorem geometricLowerSum_nonneg
    (intervals : List (Rat × Rat))
    (hwf : NonnegativeIntervals intervals) :
    0 <= geometricLowerSum intervals := by
  induction intervals with
  | nil => simp [geometricLowerSum]
  | cons interval rest ih =>
      rcases interval with ⟨p, r⟩
      rcases hwf with ⟨hp0, hpr, hrest⟩
      simp [geometricLowerSum]
      have hsum := rat_add_le_add
        (geometricLowerStep_nonneg hp0 hpr)
        (ih hrest)
      grind

theorem geometricLowerSum_eq_zero_of_covers_point
    {a : Rat} {intervals : List (Rat × Rat)}
    (ha : 0 <= a) (hcover : CoversInterval a a intervals) :
    geometricLowerSum intervals = 0 := by
  induction intervals generalizing a with
  | nil =>
      simp [geometricLowerSum]
  | cons interval rest ih =>
      rcases interval with ⟨p, r⟩
      rcases hcover with ⟨hp, hpr, hrest⟩
      subst p
      have hra_le : r <= a := CoversInterval.start_le_end hrest
      have hra : r = a := by grind
      subst r
      have htail := ih ha hrest
      simp [geometricLowerSum, geometricLowerStep_zero_right, htail]
      grind

theorem integralLowerSum_append
    (left right : List (Rat × Rat)) :
    integralLowerSum (left ++ right) =
      integralLowerSum left + integralLowerSum right := by
  induction left with
  | nil =>
      simp [integralLowerSum]
      grind
  | cons interval rest ih =>
      rcases interval with ⟨p, r⟩
      simp [integralLowerSum, ih]
      grind [Rat.add_assoc, Rat.add_comm]

theorem integralUpperSum_append
    (left right : List (Rat × Rat)) :
    integralUpperSum (left ++ right) =
      integralUpperSum left + integralUpperSum right := by
  induction left with
  | nil =>
      simp [integralUpperSum]
      grind
  | cons interval rest ih =>
      rcases interval with ⟨p, r⟩
      simp [integralUpperSum, ih]
      grind [Rat.add_assoc, Rat.add_comm]

theorem geometricLowerSum_append
    (left right : List (Rat × Rat)) :
    geometricLowerSum (left ++ right) =
      geometricLowerSum left + geometricLowerSum right := by
  induction left with
  | nil =>
      simp [geometricLowerSum]
      grind
  | cons interval rest ih =>
      rcases interval with ⟨p, r⟩
      simp [geometricLowerSum, ih]
      grind [Rat.add_assoc, Rat.add_comm]

theorem geometricUpperSum_append
    (left right : List (Rat × Rat)) :
    geometricUpperSum (left ++ right) =
      geometricUpperSum left + geometricUpperSum right := by
  induction left with
  | nil =>
      simp [geometricUpperSum]
      grind
  | cons interval rest ih =>
      rcases interval with ⟨p, r⟩
      simp [geometricUpperSum, ih]
      grind [Rat.add_assoc, Rat.add_comm]

theorem integralLowerSum_le_append_of_nonnegative
    (left right : List (Rat × Rat))
    (hright : NonnegativeIntervals right) :
    integralLowerSum left <= integralLowerSum (left ++ right) := by
  rw [integralLowerSum_append]
  have hnonneg := integralLowerSum_nonneg right hright
  grind

theorem geometricLowerSum_le_append_of_nonnegative
    (left right : List (Rat × Rat))
    (hright : NonnegativeIntervals right) :
    geometricLowerSum left <= geometricLowerSum (left ++ right) := by
  rw [geometricLowerSum_append]
  have hnonneg := geometricLowerSum_nonneg right hright
  grind

theorem integralLowerSum_le_integralUpperSum_of_covers
    {a b : Rat} (ha : 0 <= a)
    (lower upper : List (Rat × Rat))
    (hlower : CoversInterval a b lower)
    (hupper : CoversInterval a b upper) :
    integralLowerSum lower <= integralUpperSum upper := by
  let N := lower.length + upper.length
  have main :
      forall N lower upper a b,
        lower.length + upper.length <= N ->
        0 <= a ->
        CoversInterval a b lower ->
        CoversInterval a b upper ->
        integralLowerSum lower <= integralUpperSum upper := by
    intro N
    induction N with
    | zero =>
        intro lower upper a b hlen ha hlower hupper
        cases lower <;> cases upper <;>
          simp [integralLowerSum, integralUpperSum] at hlen ⊢
    | succ N ih =>
        intro lower upper a b hlen ha hlower hupper
        cases lower with
        | nil =>
            have hupperNonneg :
                0 <= integralUpperSum upper :=
              integralUpperSum_nonneg upper
                (CoversInterval.nonnegative ha hupper)
            simpa [integralLowerSum] using hupperNonneg
        | cons lowerHead lowerRest =>
            cases upper with
            | nil =>
                have hab : a = b := by
                  simpa [CoversInterval] using hupper
                subst b
                have hzero :=
                  integralLowerSum_eq_zero_of_covers_point
                    (a := a) (intervals := lowerHead :: lowerRest)
                    ha hlower
                simp [integralUpperSum, hzero]
            | cons upperHead upperRest =>
                rcases lowerHead with ⟨p, r⟩
                rcases upperHead with ⟨p', s⟩
                rcases hlower with ⟨hp, hpr, hlowerRest⟩
                rcases hupper with ⟨hp', hps, hupperRest⟩
                subst p
                subst p'
                by_cases hrs : r <= s
                · have hr0 : 0 <= r := Rat.le_trans ha hpr
                  have hsplitUpper :
                      CoversInterval r b ((r, s) :: upperRest) :=
                    ⟨rfl, hrs, hupperRest⟩
                  have hlenRec :
                      lowerRest.length + (((r, s) :: upperRest).length) <= N := by
                    simp at hlen ⊢
                    omega
                  have hrec :=
                    ih lowerRest ((r, s) :: upperRest) r b
                      hlenRec hr0 hlowerRest hsplitUpper
                  have hheadLow :
                      integralLowerStep a r <= integralUpperStep a r :=
                    integralLowerStep_le_integralUpperStep ha hpr
                  have hheadSplit :
                      integralUpperStep a r + integralUpperStep r s <=
                        integralUpperStep a s :=
                    integralUpperStep_refine ha hpr hrs
                  simp [integralLowerSum, integralUpperSum] at hrec ⊢
                  calc
                    integralLowerStep a r + integralLowerSum lowerRest
                        <= integralUpperStep a r +
                            (integralUpperStep r s +
                              integralUpperSum upperRest) :=
                          rat_add_le_add hheadLow hrec
                    _ = (integralUpperStep a r + integralUpperStep r s) +
                            integralUpperSum upperRest := by
                          grind [Rat.add_assoc, Rat.add_comm]
                    _ <= integralUpperStep a s +
                            integralUpperSum upperRest :=
                          rat_add_le_add hheadSplit Rat.le_refl
                · have hsr : s <= r := by grind
                  have hs0 : 0 <= s := Rat.le_trans ha hps
                  have hsplitLower :
                      CoversInterval s b ((s, r) :: lowerRest) :=
                    ⟨rfl, hsr, hlowerRest⟩
                  have hlenRec :
                      (((s, r) :: lowerRest).length) + upperRest.length <= N := by
                    simp at hlen ⊢
                    omega
                  have hrec :=
                    ih ((s, r) :: lowerRest) upperRest s b
                      hlenRec hs0 hsplitLower hupperRest
                  have hheadSplit :
                      integralLowerStep a r <=
                        integralLowerStep a s + integralLowerStep s r :=
                    integralLowerStep_refine ha hps hsr
                  have hheadLow :
                      integralLowerStep a s <= integralUpperStep a s :=
                    integralLowerStep_le_integralUpperStep ha hps
                  simp [integralLowerSum, integralUpperSum] at hrec ⊢
                  calc
                    integralLowerStep a r + integralLowerSum lowerRest
                        <= (integralLowerStep a s + integralLowerStep s r) +
                            integralLowerSum lowerRest :=
                          rat_add_le_add hheadSplit Rat.le_refl
                    _ = integralLowerStep a s +
                            (integralLowerStep s r +
                              integralLowerSum lowerRest) := by
                          grind [Rat.add_assoc, Rat.add_comm]
                    _ <= integralLowerStep a s +
                            integralUpperSum upperRest :=
                          rat_add_le_add Rat.le_refl hrec
                    _ <= integralUpperStep a s +
                            integralUpperSum upperRest :=
                          rat_add_le_add hheadLow Rat.le_refl
  exact main N lower upper a b (Nat.le_refl N) ha hlower hupper

theorem integralSumInterval_overlaps_of_covers
    {a b : Rat} (ha : 0 <= a)
    (left right : List (Rat × Rat))
    (hleft : CoversInterval a b left)
    (hright : CoversInterval a b right) :
    QInterval.Overlaps (integralSumInterval left)
      (integralSumInterval right) := by
  unfold QInterval.Overlaps integralSumInterval
  exact ⟨
    integralLowerSum_le_integralUpperSum_of_covers
      ha left right hleft hright,
    integralLowerSum_le_integralUpperSum_of_covers
      ha right left hright hleft⟩

theorem integralLowerSum_le_geometricUpperSum_of_covers
    {a b : Rat} (ha : 0 <= a)
    (lower upper : List (Rat × Rat))
    (hlower : CoversInterval a b lower)
    (hupper : CoversInterval a b upper) :
    integralLowerSum lower <= geometricUpperSum upper := by
  let N := lower.length + upper.length
  have main :
      forall N lower upper a b,
        lower.length + upper.length <= N ->
        0 <= a ->
        CoversInterval a b lower ->
        CoversInterval a b upper ->
        integralLowerSum lower <= geometricUpperSum upper := by
    intro N
    induction N with
    | zero =>
        intro lower upper a b hlen ha hlower hupper
        cases lower <;> cases upper <;>
          simp [integralLowerSum, geometricUpperSum] at hlen ⊢
    | succ N ih =>
        intro lower upper a b hlen ha hlower hupper
        cases lower with
        | nil =>
            have hupperNonneg :
                0 <= geometricUpperSum upper :=
              geometricUpperSum_nonneg upper
                (CoversInterval.nonnegative ha hupper)
            simpa [integralLowerSum] using hupperNonneg
        | cons lowerHead lowerRest =>
            cases upper with
            | nil =>
                have hab : a = b := by
                  simpa [CoversInterval] using hupper
                subst b
                have hzero :=
                  integralLowerSum_eq_zero_of_covers_point
                    (a := a) (intervals := lowerHead :: lowerRest)
                    ha hlower
                simp [geometricUpperSum, hzero]
            | cons upperHead upperRest =>
                rcases lowerHead with ⟨p, r⟩
                rcases upperHead with ⟨p', s⟩
                rcases hlower with ⟨hp, hpr, hlowerRest⟩
                rcases hupper with ⟨hp', hps, hupperRest⟩
                subst p
                subst p'
                by_cases hrs : r <= s
                · have hr0 : 0 <= r := Rat.le_trans ha hpr
                  have hsplitUpper :
                      CoversInterval r b ((r, s) :: upperRest) :=
                    ⟨rfl, hrs, hupperRest⟩
                  have hlenRec :
                      lowerRest.length + (((r, s) :: upperRest).length) <= N := by
                    simp at hlen ⊢
                    omega
                  have hrec :=
                    ih lowerRest ((r, s) :: upperRest) r b
                      hlenRec hr0 hlowerRest hsplitUpper
                  have hheadLow :
                      integralLowerStep a r <= geometricUpperStep a r :=
                    integralLowerStep_le_geometricUpperStep ha hpr
                  have hheadSplit :
                      geometricUpperStep a r + geometricUpperStep r s <=
                        geometricUpperStep a s :=
                    geometricUpperStep_refine_le ha hpr hrs
                  simp [integralLowerSum, geometricUpperSum] at hrec ⊢
                  calc
                    integralLowerStep a r + integralLowerSum lowerRest
                        <= geometricUpperStep a r +
                            (geometricUpperStep r s +
                              geometricUpperSum upperRest) :=
                          rat_add_le_add hheadLow hrec
                    _ = (geometricUpperStep a r + geometricUpperStep r s) +
                            geometricUpperSum upperRest := by
                          grind [Rat.add_assoc, Rat.add_comm]
                    _ <= geometricUpperStep a s +
                            geometricUpperSum upperRest :=
                          rat_add_le_add hheadSplit Rat.le_refl
                · have hsr : s <= r := by grind
                  have hs0 : 0 <= s := Rat.le_trans ha hps
                  have hsplitLower :
                      CoversInterval s b ((s, r) :: lowerRest) :=
                    ⟨rfl, hsr, hlowerRest⟩
                  have hlenRec :
                      (((s, r) :: lowerRest).length) + upperRest.length <= N := by
                    simp at hlen ⊢
                    omega
                  have hrec :=
                    ih ((s, r) :: lowerRest) upperRest s b
                      hlenRec hs0 hsplitLower hupperRest
                  have hheadSplit :
                      integralLowerStep a r <=
                        integralLowerStep a s + integralLowerStep s r :=
                    integralLowerStep_refine ha hps hsr
                  have hheadLow :
                      integralLowerStep a s <= geometricUpperStep a s :=
                    integralLowerStep_le_geometricUpperStep ha hps
                  simp [integralLowerSum, geometricUpperSum] at hrec ⊢
                  calc
                    integralLowerStep a r + integralLowerSum lowerRest
                        <= (integralLowerStep a s + integralLowerStep s r) +
                            integralLowerSum lowerRest :=
                          rat_add_le_add hheadSplit Rat.le_refl
                    _ = integralLowerStep a s +
                            (integralLowerStep s r +
                              integralLowerSum lowerRest) := by
                          grind [Rat.add_assoc, Rat.add_comm]
                    _ <= integralLowerStep a s +
                            geometricUpperSum upperRest :=
                          rat_add_le_add Rat.le_refl hrec
                    _ <= geometricUpperStep a s +
                            geometricUpperSum upperRest :=
                          rat_add_le_add hheadLow Rat.le_refl
  exact main N lower upper a b (Nat.le_refl N) ha hlower hupper

theorem geometricLowerSum_le_integralUpperSum_of_covers
    {a b : Rat} (ha : 0 <= a)
    (lower upper : List (Rat × Rat))
    (hlower : CoversInterval a b lower)
    (hupper : CoversInterval a b upper) :
    geometricLowerSum lower <= integralUpperSum upper := by
  let N := lower.length + upper.length
  have main :
      forall N lower upper a b,
        lower.length + upper.length <= N ->
        0 <= a ->
        CoversInterval a b lower ->
        CoversInterval a b upper ->
        geometricLowerSum lower <= integralUpperSum upper := by
    intro N
    induction N with
    | zero =>
        intro lower upper a b hlen ha hlower hupper
        cases lower <;> cases upper <;>
          simp [geometricLowerSum, integralUpperSum] at hlen ⊢
    | succ N ih =>
        intro lower upper a b hlen ha hlower hupper
        cases lower with
        | nil =>
            have hupperNonneg :
                0 <= integralUpperSum upper :=
              integralUpperSum_nonneg upper
                (CoversInterval.nonnegative ha hupper)
            simpa [geometricLowerSum] using hupperNonneg
        | cons lowerHead lowerRest =>
            cases upper with
            | nil =>
                have hab : a = b := by
                  simpa [CoversInterval] using hupper
                subst b
                have hzero :=
                  geometricLowerSum_eq_zero_of_covers_point
                    (a := a) (intervals := lowerHead :: lowerRest)
                    ha hlower
                simp [integralUpperSum, hzero]
            | cons upperHead upperRest =>
                rcases lowerHead with ⟨p, r⟩
                rcases upperHead with ⟨p', s⟩
                rcases hlower with ⟨hp, hpr, hlowerRest⟩
                rcases hupper with ⟨hp', hps, hupperRest⟩
                subst p
                subst p'
                by_cases hrs : r <= s
                · have hr0 : 0 <= r := Rat.le_trans ha hpr
                  have hsplitUpper :
                      CoversInterval r b ((r, s) :: upperRest) :=
                    ⟨rfl, hrs, hupperRest⟩
                  have hlenRec :
                      lowerRest.length + (((r, s) :: upperRest).length) <= N := by
                    simp at hlen ⊢
                    omega
                  have hrec :=
                    ih lowerRest ((r, s) :: upperRest) r b
                      hlenRec hr0 hlowerRest hsplitUpper
                  have hheadLow :
                      geometricLowerStep a r <= integralUpperStep a r :=
                    geometricLowerStep_le_integralUpperStep ha hpr
                  have hheadSplit :
                      integralUpperStep a r + integralUpperStep r s <=
                        integralUpperStep a s :=
                    integralUpperStep_refine ha hpr hrs
                  simp [geometricLowerSum, integralUpperSum] at hrec ⊢
                  calc
                    geometricLowerStep a r + geometricLowerSum lowerRest
                        <= integralUpperStep a r +
                            (integralUpperStep r s +
                              integralUpperSum upperRest) :=
                          rat_add_le_add hheadLow hrec
                    _ = (integralUpperStep a r + integralUpperStep r s) +
                            integralUpperSum upperRest := by
                          grind [Rat.add_assoc, Rat.add_comm]
                    _ <= integralUpperStep a s +
                            integralUpperSum upperRest :=
                          rat_add_le_add hheadSplit Rat.le_refl
                · have hsr : s <= r := by grind
                  have hs0 : 0 <= s := Rat.le_trans ha hps
                  have hsplitLower :
                      CoversInterval s b ((s, r) :: lowerRest) :=
                    ⟨rfl, hsr, hlowerRest⟩
                  have hlenRec :
                      (((s, r) :: lowerRest).length) + upperRest.length <= N := by
                    simp at hlen ⊢
                    omega
                  have hrec :=
                    ih ((s, r) :: lowerRest) upperRest s b
                      hlenRec hs0 hsplitLower hupperRest
                  have hheadSplit :
                      geometricLowerStep a r <=
                        geometricLowerStep a s + geometricLowerStep s r :=
                    geometricLowerStep_refine_le hps hsr
                  have hheadLow :
                      geometricLowerStep a s <= integralUpperStep a s :=
                    geometricLowerStep_le_integralUpperStep ha hps
                  simp [geometricLowerSum, integralUpperSum] at hrec ⊢
                  calc
                    geometricLowerStep a r + geometricLowerSum lowerRest
                        <=
                          (geometricLowerStep a s + geometricLowerStep s r) +
                            geometricLowerSum lowerRest :=
                          rat_add_le_add hheadSplit Rat.le_refl
                    _ = geometricLowerStep a s +
                            (geometricLowerStep s r +
                              geometricLowerSum lowerRest) := by
                          grind [Rat.add_assoc, Rat.add_comm]
                    _ <= geometricLowerStep a s +
                            integralUpperSum upperRest :=
                          rat_add_le_add Rat.le_refl hrec
                    _ <= integralUpperStep a s +
                            integralUpperSum upperRest :=
                          rat_add_le_add hheadLow Rat.le_refl
  exact main N lower upper a b (Nat.le_refl N) ha hlower hupper

theorem integralLowerSum_le_geometricUpperSum_of_covers_right
    {a b c : Rat} (ha : 0 <= a) (hbc : b <= c)
    (lower upper : List (Rat × Rat))
    (hlower : CoversInterval a b lower)
    (hupper : CoversInterval a c upper) :
    integralLowerSum lower <= geometricUpperSum upper := by
  have hlong : CoversInterval a c (lower ++ [(b, c)]) :=
    CoversInterval.extend_right hlower hbc
  have hb0 : 0 <= b :=
    Rat.le_trans ha (CoversInterval.start_le_end hlower)
  have htail : NonnegativeIntervals [(b, c)] := by
    simp [NonnegativeIntervals, hb0, hbc]
  have hprefix :
      integralLowerSum lower <=
        integralLowerSum (lower ++ [(b, c)]) :=
    integralLowerSum_le_append_of_nonnegative lower [(b, c)] htail
  have hcompare :
      integralLowerSum (lower ++ [(b, c)]) <=
        geometricUpperSum upper :=
    integralLowerSum_le_geometricUpperSum_of_covers
      ha (lower ++ [(b, c)]) upper hlong hupper
  exact Rat.le_trans hprefix hcompare

theorem geometricLowerSum_le_integralUpperSum_of_covers_right
    {a b c : Rat} (ha : 0 <= a) (hbc : b <= c)
    (lower upper : List (Rat × Rat))
    (hlower : CoversInterval a b lower)
    (hupper : CoversInterval a c upper) :
    geometricLowerSum lower <= integralUpperSum upper := by
  have hlong : CoversInterval a c (lower ++ [(b, c)]) :=
    CoversInterval.extend_right hlower hbc
  have hb0 : 0 <= b :=
    Rat.le_trans ha (CoversInterval.start_le_end hlower)
  have htail : NonnegativeIntervals [(b, c)] := by
    simp [NonnegativeIntervals, hb0, hbc]
  have hprefix :
      geometricLowerSum lower <=
        geometricLowerSum (lower ++ [(b, c)]) :=
    geometricLowerSum_le_append_of_nonnegative lower [(b, c)] htail
  have hcompare :
      geometricLowerSum (lower ++ [(b, c)]) <=
        integralUpperSum upper :=
    geometricLowerSum_le_integralUpperSum_of_covers
      ha (lower ++ [(b, c)]) upper hlong hupper
  exact Rat.le_trans hprefix hcompare

theorem integralSumInterval_overlaps_geometricSumInterval_of_covers
    {a b : Rat} (ha : 0 <= a)
    (integral geometric : List (Rat × Rat))
    (hintegral : CoversInterval a b integral)
    (hgeometric : CoversInterval a b geometric) :
    QInterval.Overlaps (integralSumInterval integral)
      (geometricSumInterval geometric) := by
  unfold QInterval.Overlaps integralSumInterval geometricSumInterval
  exact ⟨
    integralLowerSum_le_geometricUpperSum_of_covers
      ha integral geometric hintegral hgeometric,
    geometricLowerSum_le_integralUpperSum_of_covers
      ha geometric integral hgeometric hintegral⟩

theorem integralBracketInterval_overlaps_geometricSumInterval_of_covers
    {a lowerEnd x upperEnd : Rat} (ha : 0 <= a)
    (hlowerEnd : lowerEnd <= x) (hupperEnd : x <= upperEnd)
    (lower upper geometric : List (Rat × Rat))
    (hlower : CoversInterval a lowerEnd lower)
    (hupper : CoversInterval a upperEnd upper)
    (hgeometric : CoversInterval a x geometric) :
    QInterval.Overlaps
      { lo := integralLowerSum lower, hi := integralUpperSum upper }
      (geometricSumInterval geometric) := by
  unfold QInterval.Overlaps geometricSumInterval
  exact ⟨
    integralLowerSum_le_geometricUpperSum_of_covers_right
      ha hlowerEnd lower geometric hlower hgeometric,
    geometricLowerSum_le_integralUpperSum_of_covers_right
      ha hupperEnd geometric upper hgeometric hupper⟩

theorem integralSumInterval_ordered
    (intervals : List (Rat × Rat))
    (hwf : NonnegativeIntervals intervals) :
    0 <= (integralSumInterval intervals).width := by
  unfold integralSumInterval QInterval.width
  have hle := integralLowerSum_le_integralUpperSum intervals hwf
  grind [Rat.sub_eq_add_neg]

theorem geometricSumInterval_ordered
    (intervals : List (Rat × Rat))
    (hwf : NonnegativeIntervals intervals) :
    0 <= (geometricSumInterval intervals).width := by
  unfold geometricSumInterval QInterval.width
  have hle := geometricLowerSum_le_geometricUpperSum intervals hwf
  grind [Rat.sub_eq_add_neg]

private theorem one_le_one_add_square (x : Rat) :
    1 <= 1 + x * x := by
  have hsq := RationalCircle.Stage.ratSquare_nonneg x
  grind

private theorem one_le_square_den (p r : Rat) :
    1 <= (1 + p * p) * (1 + r * r) := by
  have hp1 : 1 <= 1 + p * p := one_le_one_add_square p
  have hr1 : 1 <= 1 + r * r := one_le_one_add_square r
  calc
    1 = 1 * 1 := by grind
    _ <= (1 + p * p) * 1 :=
          Rat.mul_le_mul_of_nonneg_right hp1 (by decide +kernel)
    _ <= (1 + p * p) * (1 + r * r) :=
          Rat.mul_le_mul_of_nonneg_left hr1 (by grind)

private theorem div_le_two_of_sum_le_two {p r D : Rat}
    (hDpos : 0 < D) (hD1 : 1 <= D) (hsum : p + r <= 2) :
    (p + r) / D <= 2 := by
  have hDne : D ≠ 0 := Rat.ne_of_gt hDpos
  apply Rat.le_of_mul_le_mul_right (c := D)
  · calc
      ((p + r) / D) * D = p + r := by
        rw [Rat.div_def]
        grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
      _ <= 2 := hsum
      _ <= 2 * D := by
        calc
          (2 : Rat) = 2 * 1 := by grind
          _ <= 2 * D := Rat.mul_le_mul_of_nonneg_left hD1 (by decide +kernel)
  · exact hDpos

private theorem kernel_diff_le_two_len {p r : Rat}
    (hpr : p <= r) (hr1 : r <= 1) :
    integralKernel p - integralKernel r <= 2 * (r - p) := by
  let A : Rat := 1 + p * p
  let B : Rat := 1 + r * r
  let D : Rat := A * B
  have hApos : 0 < A := by
    dsimp [A]
    exact RationalCircle.Stage.one_add_square_pos p
  have hBpos : 0 < B := by
    dsimp [B]
    exact RationalCircle.Stage.one_add_square_pos r
  have hDpos : 0 < D := by
    dsimp [D]
    exact Rat.mul_pos hApos hBpos
  have hD1 : 1 <= D := by
    dsimp [D, A, B]
    exact one_le_square_den p r
  have hp1 : p <= 1 := Rat.le_trans hpr hr1
  have hsum : p + r <= 2 := by grind
  have hratio : (p + r) / D <= 2 :=
    div_le_two_of_sum_le_two hDpos hD1 hsum
  have hlen : 0 <= r - p := by grind [Rat.sub_eq_add_neg]
  apply Rat.le_of_mul_le_mul_right (c := D)
  · calc
      (integralKernel p - integralKernel r) * D =
          (r - p) * (p + r) := by
        dsimp [D, A, B]
        unfold integralKernel
        rw [Rat.div_def, Rat.div_def]
        grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
          Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm,
          Rat.mul_inv_cancel]
      _ = (r - p) * ((p + r) / D) * D := by
        dsimp [D, A, B]
        rw [Rat.div_def]
        grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
      _ <= (r - p) * 2 * D := by
        exact Rat.mul_le_mul_of_nonneg_right
          (Rat.mul_le_mul_of_nonneg_left hratio hlen)
          (Rat.le_of_lt hDpos)
      _ = (2 * (r - p)) * D := by
        grind [Rat.mul_assoc, Rat.mul_comm]
  · exact hDpos

theorem integralCellWidth_le_two_square {p r : Rat}
    (hpr : p <= r) (hr1 : r <= 1) :
    integralUpperStep p r - integralLowerStep p r <=
      2 * ((r - p) * (r - p)) := by
  have hlen : 0 <= r - p := by grind [Rat.sub_eq_add_neg]
  have hdiff := kernel_diff_le_two_len hpr hr1
  unfold integralUpperStep integralLowerStep
  calc
    (r - p) * integralKernel p - (r - p) * integralKernel r
        = (r - p) * (integralKernel p - integralKernel r) := by
          grind [Rat.sub_eq_add_neg, Rat.mul_add]
    _ <= (r - p) * (2 * (r - p)) :=
          Rat.mul_le_mul_of_nonneg_left hdiff hlen
    _ = 2 * ((r - p) * (r - p)) := by
          grind [Rat.mul_assoc, Rat.mul_comm]

theorem integralSumInterval_width_le_two_squareSum
    (intervals : List (Rat × Rat))
    (hwf : UnitIntervals intervals) :
    (integralSumInterval intervals).width <=
      2 * intervalSquareSum intervals := by
  induction intervals with
  | nil =>
      change (0 : Rat) - 0 <= 2 * 0
      decide +kernel
  | cons interval rest ih =>
      rcases interval with ⟨p, r⟩
      rcases hwf with ⟨_hp0, hpr, hr1, hrest⟩
      have hcell := integralCellWidth_le_two_square hpr hr1
      have htail := ih hrest
      unfold integralSumInterval QInterval.width
      simp [integralLowerSum, integralUpperSum, intervalSquareSum]
      calc
        integralUpperStep p r + integralUpperSum rest -
              (integralLowerStep p r + integralLowerSum rest)
            = (integralUpperStep p r - integralLowerStep p r) +
                (integralUpperSum rest - integralLowerSum rest) := by
              grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm]
        _ <= 2 * ((r - p) * (r - p)) +
              2 * intervalSquareSum rest :=
              rat_add_le_add hcell htail
        _ = 2 * (((r - p) * (r - p)) +
              intervalSquareSum rest) := by
              grind [Rat.mul_add, Rat.add_assoc, Rat.add_comm]

theorem integralSumInterval_contains_geometricSumInterval
    (intervals : List (Rat × Rat))
    (hwf : NonnegativeIntervals intervals) :
    (integralSumInterval intervals).ContainsInterval
      (geometricSumInterval intervals) := by
  unfold QInterval.ContainsInterval integralSumInterval geometricSumInterval
  exact ⟨integralLowerSum_le_geometricLowerSum intervals hwf,
    geometricUpperSum_le_integralUpperSum intervals hwf⟩

theorem integralSumInterval_overlaps_geometricSumInterval
    (intervals : List (Rat × Rat))
    (hwf : NonnegativeIntervals intervals) :
    QInterval.Overlaps (integralSumInterval intervals)
      (geometricSumInterval intervals) := by
  unfold QInterval.Overlaps integralSumInterval geometricSumInterval
  exact ⟨integralLowerSum_le_geometricUpperSum intervals hwf,
    geometricLowerSum_le_integralUpperSum intervals hwf⟩

namespace AreaLoopState

def refineAux : Rat -> Rat -> List (Rat × Rat) -> AreaLoopState
  | lo, hi, [] => { lo := lo, hi := hi, intervals := [] }
  | lo, hi, (p, r) :: rest =>
      let q := (p + r) / 2
      let next := refineAux
        (lo + arctanAreaIncrement p q r)
        (hi - arctanAreaDecrement p q r)
        rest
      { next with intervals := (p, q) :: (q, r) :: next.intervals }

end AreaLoopState

private theorem midpoint_nonneg {p r : Rat}
    (hp0 : 0 <= p) (hr0 : 0 <= r) :
    0 <= (p + r) / 2 := by
  rw [Rat.div_def]
  exact Rat.mul_nonneg (Rat.add_nonneg hp0 hr0)
    (Rat.le_of_lt ((Rat.inv_pos).2 (by decide +kernel : (0 : Rat) < 2)))

private theorem left_le_midpoint {p r : Rat} (hpr : p <= r) :
    p <= (p + r) / 2 := by
  apply Rat.le_of_mul_le_mul_right (c := (2 : Rat))
  · rw [Rat.div_def]
    have h2 : (2 : Rat) ≠ 0 := by decide +kernel
    calc
      p * 2 <= p + r := by grind
      _ = ((p + r) * (2 : Rat)⁻¹) * 2 := by
        grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
  · decide +kernel

private theorem midpoint_le_right {p r : Rat} (hpr : p <= r) :
    (p + r) / 2 <= r := by
  apply Rat.le_of_mul_le_mul_right (c := (2 : Rat))
  · rw [Rat.div_def]
    have h2 : (2 : Rat) ≠ 0 := by decide +kernel
    calc
      ((p + r) * (2 : Rat)⁻¹) * 2 = p + r := by
        grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
      _ <= r * 2 := by grind
  · decide +kernel

private theorem refineAux_intervals_nonnegative
    (lo hi : Rat) (intervals : List (Rat × Rat))
    (hwf : NonnegativeIntervals intervals) :
    NonnegativeIntervals
      (AreaLoopState.refineAux lo hi intervals).intervals := by
  induction intervals generalizing lo hi with
  | nil =>
      simp [AreaLoopState.refineAux, NonnegativeIntervals]
  | cons interval rest ih =>
      rcases interval with ⟨p, r⟩
      rcases hwf with ⟨hp0, hpr, hrest⟩
      let q : Rat := (p + r) / 2
      have hq0 : 0 <= q := by
        dsimp [q]
        exact midpoint_nonneg hp0 (Rat.le_trans hp0 hpr)
      have hpq : p <= q := by
        dsimp [q]
        exact left_le_midpoint hpr
      have hqr : q <= r := by
        dsimp [q]
        exact midpoint_le_right hpr
      have htail :=
        ih (lo + arctanAreaIncrement p q r)
          (hi - arctanAreaDecrement p q r) hrest
      simp [AreaLoopState.refineAux, NonnegativeIntervals, q,
        hp0, hpq, hq0, hqr, htail]

private theorem refineAux_intervals_unit
    (lo hi : Rat) (intervals : List (Rat × Rat))
    (hwf : UnitIntervals intervals) :
    UnitIntervals
      (AreaLoopState.refineAux lo hi intervals).intervals := by
  induction intervals generalizing lo hi with
  | nil =>
      simp [AreaLoopState.refineAux, UnitIntervals]
  | cons interval rest ih =>
      rcases interval with ⟨p, r⟩
      rcases hwf with ⟨hp0, hpr, hr1, hrest⟩
      let q : Rat := (p + r) / 2
      have hq0 : 0 <= q := by
        dsimp [q]
        exact midpoint_nonneg hp0 (Rat.le_trans hp0 hpr)
      have hpq : p <= q := by
        dsimp [q]
        exact left_le_midpoint hpr
      have hqr : q <= r := by
        dsimp [q]
        exact midpoint_le_right hpr
      have hq1 : q <= 1 := Rat.le_trans hqr hr1
      have htail :=
        ih (lo + arctanAreaIncrement p q r)
          (hi - arctanAreaDecrement p q r) hrest
      simp [AreaLoopState.refineAux, UnitIntervals, q,
        hp0, hpq, hq0, hqr, hq1, hr1, htail]

private theorem refineAux_intervals_covers
    (lo hi a b : Rat) (intervals : List (Rat × Rat))
    (hcover : CoversInterval a b intervals) :
    CoversInterval a b
      (AreaLoopState.refineAux lo hi intervals).intervals := by
  induction intervals generalizing lo hi a with
  | nil =>
      simpa [AreaLoopState.refineAux, CoversInterval] using hcover
  | cons interval rest ih =>
      rcases interval with ⟨p, r⟩
      rcases hcover with ⟨hp, hpr, hrest⟩
      let q : Rat := (p + r) / 2
      have hpq : p <= q := by
        dsimp [q]
        exact left_le_midpoint hpr
      have hqr : q <= r := by
        dsimp [q]
        exact midpoint_le_right hpr
      have htail :=
        ih (lo + arctanAreaIncrement p q r)
          (hi - arctanAreaDecrement p q r) r hrest
      simp [AreaLoopState.refineAux, CoversInterval]
      exact ⟨hp, hpq, hqr, htail⟩

private theorem midpoint_left_sub (p r : Rat) :
    (p + r) / 2 - p = (r - p) / 2 := by
  rw [Rat.div_def, Rat.div_def]
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
    Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm,
    Rat.mul_inv_cancel]

private theorem midpoint_right_sub (p r : Rat) :
    r - (p + r) / 2 = (r - p) / 2 := by
  rw [Rat.div_def, Rat.div_def]
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
    Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm,
    Rat.mul_inv_cancel]

private theorem square_midpoint_split (p r : Rat) :
    let q : Rat := (p + r) / 2
    (q - p) * (q - p) + (r - q) * (r - q) =
      ((r - p) * (r - p)) / 2 := by
  intro q
  dsimp [q]
  rw [midpoint_left_sub, midpoint_right_sub]
  repeat rw [Rat.div_def]
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
    Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm,
    Rat.mul_inv_cancel]

private theorem refineAux_squareSum
    (lo hi : Rat) (intervals : List (Rat × Rat)) :
    intervalSquareSum
        (AreaLoopState.refineAux lo hi intervals).intervals =
      intervalSquareSum intervals / 2 := by
  induction intervals generalizing lo hi with
  | nil =>
      change (0 : Rat) = 0 / 2
      decide +kernel
  | cons interval rest ih =>
      rcases interval with ⟨p, r⟩
      let q : Rat := (p + r) / 2
      have htail :=
        ih (lo + arctanAreaIncrement p q r)
          (hi - arctanAreaDecrement p q r)
      have hsplit := square_midpoint_split p r
      simp [AreaLoopState.refineAux, intervalSquareSum]
      calc
        (q - p) * (q - p) +
              ((r - q) * (r - q) +
                intervalSquareSum
                  (AreaLoopState.refineAux
                    (lo + arctanAreaIncrement p q r)
                    (hi - arctanAreaDecrement p q r) rest).intervals)
            = ((r - p) * (r - p)) / 2 +
                intervalSquareSum rest / 2 := by
              rw [htail]
              dsimp [q] at hsplit
              rw [← hsplit]
              grind [Rat.add_assoc, Rat.add_comm]
        _ = (((r - p) * (r - p)) +
              intervalSquareSum rest) / 2 := by
              rw [Rat.div_def, Rat.div_def, Rat.div_def]
              grind [Rat.mul_add, Rat.add_mul, Rat.add_assoc,
                Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]

private theorem refineAux_endpoint_refines
    (lo hi : Rat) (intervals : List (Rat × Rat))
    (hwf : NonnegativeIntervals intervals) :
    lo <= (AreaLoopState.refineAux lo hi intervals).lo /\
      (AreaLoopState.refineAux lo hi intervals).hi <= hi := by
  induction intervals generalizing lo hi with
  | nil =>
      simp [AreaLoopState.refineAux]
  | cons interval rest ih =>
      rcases interval with ⟨p, r⟩
      rcases hwf with ⟨hp0, hpr, hrest⟩
      let q : Rat := (p + r) / 2
      have hpq : p <= q := by
        dsimp [q]
        exact left_le_midpoint hpr
      have hqr : q <= r := by
        dsimp [q]
        exact midpoint_le_right hpr
      have hinc : 0 <= arctanAreaIncrement p q r :=
        arctanAreaIncrement_nonneg hpq hqr
      have hdec : 0 <= arctanAreaDecrement p q r :=
        arctanAreaDecrement_nonneg hp0 hpq hqr
      have htail :=
        ih (lo + arctanAreaIncrement p q r)
          (hi - arctanAreaDecrement p q r) hrest
      simp [AreaLoopState.refineAux]
      exact ⟨Rat.le_trans (by grind) htail.1,
        Rat.le_trans htail.2 (by grind)⟩

private theorem refineAux_lo_eq_geometricLowerSum_extra
    (extra lo hi : Rat) (intervals : List (Rat × Rat))
    (hlo : lo = extra + geometricLowerSum intervals) :
    let next := AreaLoopState.refineAux lo hi intervals
    next.lo = extra + geometricLowerSum next.intervals := by
  induction intervals generalizing extra lo hi with
  | nil =>
      simp [AreaLoopState.refineAux, geometricLowerSum] at hlo ⊢
      exact hlo
  | cons interval rest ih =>
      rcases interval with ⟨p, r⟩
      let q : Rat := (p + r) / 2
      let extra' : Rat :=
        extra + geometricLowerStep p q + geometricLowerStep q r
      have hstart :
          lo + arctanAreaIncrement p q r =
            extra' + geometricLowerSum rest := by
        dsimp [extra']
        simp [geometricLowerSum] at hlo
        rw [hlo]
        have hlocal := geometricLowerStep_refine p q r
        grind [Rat.add_assoc, Rat.add_comm]
      have htail :=
        ih extra' (lo + arctanAreaIncrement p q r)
          (hi - arctanAreaDecrement p q r) hstart
      simp [AreaLoopState.refineAux, geometricLowerSum]
      simpa [extra', geometricLowerSum, Rat.add_assoc, Rat.add_comm] using htail

private theorem refineAux_hi_eq_geometricUpperSum_extra
    (extra lo hi : Rat) (intervals : List (Rat × Rat))
    (hwf : NonnegativeIntervals intervals)
    (hhi : hi = extra + geometricUpperSum intervals) :
    let next := AreaLoopState.refineAux lo hi intervals
    next.hi = extra + geometricUpperSum next.intervals := by
  induction intervals generalizing extra lo hi with
  | nil =>
      simp [AreaLoopState.refineAux, geometricUpperSum] at hhi ⊢
      exact hhi
  | cons interval rest ih =>
      rcases interval with ⟨p, r⟩
      rcases hwf with ⟨hp0, hpr, hrest⟩
      let q : Rat := (p + r) / 2
      have hq0 : 0 <= q := by
        dsimp [q]
        exact midpoint_nonneg hp0 (Rat.le_trans hp0 hpr)
      have hpq : p <= q := by
        dsimp [q]
        exact left_le_midpoint hpr
      have hqr : q <= r := by
        dsimp [q]
        exact midpoint_le_right hpr
      let extra' : Rat :=
        extra + geometricUpperStep p q + geometricUpperStep q r
      have hstart :
          hi - arctanAreaDecrement p q r =
            extra' + geometricUpperSum rest := by
        dsimp [extra']
        simp [geometricUpperSum] at hhi
        rw [hhi]
        have hlocal := geometricUpperStep_refine hp0 hpq hqr
        grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm]
      have htail :=
        ih extra' (lo + arctanAreaIncrement p q r)
          (hi - arctanAreaDecrement p q r) hrest hstart
      simp [AreaLoopState.refineAux, geometricUpperSum]
      simpa [extra', geometricUpperSum, Rat.add_assoc, Rat.add_comm] using htail

private theorem refineAux_integralLowerSum_mono
    (lo hi : Rat) (intervals : List (Rat × Rat))
    (hwf : NonnegativeIntervals intervals) :
    integralLowerSum intervals <=
      integralLowerSum
        (AreaLoopState.refineAux lo hi intervals).intervals := by
  induction intervals generalizing lo hi with
  | nil =>
      simp [AreaLoopState.refineAux, integralLowerSum]
  | cons interval rest ih =>
      rcases interval with ⟨p, r⟩
      rcases hwf with ⟨hp0, hpr, hrest⟩
      let q : Rat := (p + r) / 2
      have hpq : p <= q := by
        dsimp [q]
        exact left_le_midpoint hpr
      have hqr : q <= r := by
        dsimp [q]
        exact midpoint_le_right hpr
      have htail :=
        ih (lo + arctanAreaIncrement p q r)
          (hi - arctanAreaDecrement p q r) hrest
      have hhead := integralLowerStep_refine hp0 hpq hqr
      simp [AreaLoopState.refineAux, integralLowerSum]
      calc
        integralLowerStep p r + integralLowerSum rest
            <= (integralLowerStep p q + integralLowerStep q r) +
                integralLowerSum rest :=
              rat_add_le_add hhead (Rat.le_refl)
        _ <= (integralLowerStep p q + integralLowerStep q r) +
              integralLowerSum
                (AreaLoopState.refineAux
                  (lo + arctanAreaIncrement p q r)
                  (hi - arctanAreaDecrement p q r) rest).intervals :=
              rat_add_le_add (Rat.le_refl) htail
        _ = integralLowerStep p q +
              (integralLowerStep q r +
                integralLowerSum
                  (AreaLoopState.refineAux
                    (lo + arctanAreaIncrement p q r)
                    (hi - arctanAreaDecrement p q r) rest).intervals) := by
              grind [Rat.add_assoc, Rat.add_comm]

private theorem refineAux_integralUpperSum_anti
    (lo hi : Rat) (intervals : List (Rat × Rat))
    (hwf : NonnegativeIntervals intervals) :
    integralUpperSum
        (AreaLoopState.refineAux lo hi intervals).intervals <=
      integralUpperSum intervals := by
  induction intervals generalizing lo hi with
  | nil =>
      simp [AreaLoopState.refineAux, integralUpperSum]
  | cons interval rest ih =>
      rcases interval with ⟨p, r⟩
      rcases hwf with ⟨hp0, hpr, hrest⟩
      let q : Rat := (p + r) / 2
      have hpq : p <= q := by
        dsimp [q]
        exact left_le_midpoint hpr
      have hqr : q <= r := by
        dsimp [q]
        exact midpoint_le_right hpr
      have htail :=
        ih (lo + arctanAreaIncrement p q r)
          (hi - arctanAreaDecrement p q r) hrest
      have hhead := integralUpperStep_refine hp0 hpq hqr
      simp [AreaLoopState.refineAux, integralUpperSum]
      calc
        integralUpperStep p q +
              (integralUpperStep q r +
                integralUpperSum
                  (AreaLoopState.refineAux
                    (lo + arctanAreaIncrement p q r)
                    (hi - arctanAreaDecrement p q r) rest).intervals)
            = (integralUpperStep p q + integralUpperStep q r) +
                integralUpperSum
                  (AreaLoopState.refineAux
                    (lo + arctanAreaIncrement p q r)
                    (hi - arctanAreaDecrement p q r) rest).intervals := by
              grind [Rat.add_assoc, Rat.add_comm]
        _ <= (integralUpperStep p q + integralUpperStep q r) +
              integralUpperSum rest :=
              rat_add_le_add (Rat.le_refl) htail
        _ <= integralUpperStep p r + integralUpperSum rest :=
              rat_add_le_add hhead (Rat.le_refl)

def refineAreaLoopState (state : AreaLoopState) : AreaLoopState :=
  AreaLoopState.refineAux state.lo state.hi state.intervals

theorem refineAreaLoopState_intervals_nonnegative
    (state : AreaLoopState)
    (hwf : NonnegativeIntervals state.intervals) :
    NonnegativeIntervals (refineAreaLoopState state).intervals := by
  cases state with
  | mk lo hi intervals =>
      exact refineAux_intervals_nonnegative lo hi intervals hwf

theorem refineAreaLoopState_intervals_unit
    (state : AreaLoopState)
    (hwf : UnitIntervals state.intervals) :
    UnitIntervals (refineAreaLoopState state).intervals := by
  cases state with
  | mk lo hi intervals =>
      exact refineAux_intervals_unit lo hi intervals hwf

theorem refineAreaLoopState_intervals_covers
    (state : AreaLoopState) {a b : Rat}
    (hcover : CoversInterval a b state.intervals) :
    CoversInterval a b (refineAreaLoopState state).intervals := by
  cases state with
  | mk lo hi intervals =>
      exact refineAux_intervals_covers lo hi a b intervals hcover

theorem refineAreaLoopState_squareSum
    (state : AreaLoopState) :
    intervalSquareSum (refineAreaLoopState state).intervals =
      intervalSquareSum state.intervals / 2 := by
  cases state with
  | mk lo hi intervals =>
      exact refineAux_squareSum lo hi intervals

theorem refineAreaLoopState_lo_eq_geometricLowerSum
    (state : AreaLoopState)
    (hlo : state.lo = geometricLowerSum state.intervals) :
    (refineAreaLoopState state).lo =
      geometricLowerSum (refineAreaLoopState state).intervals := by
  cases state with
  | mk lo hi intervals =>
      have hstart : lo = 0 + geometricLowerSum intervals := by
        grind
      have h := refineAux_lo_eq_geometricLowerSum_extra
        0 lo hi intervals hstart
      unfold refineAreaLoopState
      grind

theorem refineAreaLoopState_hi_eq_geometricUpperSum
    (state : AreaLoopState)
    (hwf : NonnegativeIntervals state.intervals)
    (hhi : state.hi = geometricUpperSum state.intervals) :
    (refineAreaLoopState state).hi =
      geometricUpperSum (refineAreaLoopState state).intervals := by
  cases state with
  | mk lo hi intervals =>
      have hstart : hi = 0 + geometricUpperSum intervals := by
        grind
      have h := refineAux_hi_eq_geometricUpperSum_extra
        0 lo hi intervals hwf hstart
      unfold refineAreaLoopState
      grind

theorem refineAreaLoopState_integralSumInterval_refines
    (state : AreaLoopState)
    (hwf : NonnegativeIntervals state.intervals) :
    (integralSumInterval state.intervals).ContainsInterval
      (integralSumInterval (refineAreaLoopState state).intervals) := by
  cases state with
  | mk lo hi intervals =>
      unfold QInterval.ContainsInterval integralSumInterval refineAreaLoopState
      exact ⟨refineAux_integralLowerSum_mono lo hi intervals hwf,
        refineAux_integralUpperSum_anti lo hi intervals hwf⟩

theorem refineAreaLoopState_endpoint_refines
    (state : AreaLoopState)
    (hwf : NonnegativeIntervals state.intervals) :
    state.lo <= (refineAreaLoopState state).lo /\
      (refineAreaLoopState state).hi <= state.hi := by
  cases state with
  | mk lo hi intervals =>
      exact refineAux_endpoint_refines lo hi intervals hwf

def iterateAreaLoopState : Nat -> AreaLoopState -> AreaLoopState
  | 0, state => state
  | n + 1, state => iterateAreaLoopState n (refineAreaLoopState state)

theorem iterateAreaLoopState_succ_refine
    (n : Nat) (state : AreaLoopState) :
    iterateAreaLoopState (n + 1) state =
      refineAreaLoopState (iterateAreaLoopState n state) := by
  induction n generalizing state with
  | zero =>
      rfl
  | succ n ih =>
      simp [iterateAreaLoopState]
      exact ih (refineAreaLoopState state)

theorem iterateAreaLoopState_intervals_nonnegative
    (n : Nat) (state : AreaLoopState)
    (hwf : NonnegativeIntervals state.intervals) :
    NonnegativeIntervals (iterateAreaLoopState n state).intervals := by
  induction n generalizing state with
  | zero =>
      simpa [iterateAreaLoopState] using hwf
  | succ n ih =>
      simpa [iterateAreaLoopState] using
        ih (refineAreaLoopState state)
          (refineAreaLoopState_intervals_nonnegative state hwf)

theorem iterateAreaLoopState_intervals_unit
    (n : Nat) (state : AreaLoopState)
    (hwf : UnitIntervals state.intervals) :
    UnitIntervals (iterateAreaLoopState n state).intervals := by
  induction n generalizing state with
  | zero =>
      simpa [iterateAreaLoopState] using hwf
  | succ n ih =>
      simpa [iterateAreaLoopState] using
        ih (refineAreaLoopState state)
          (refineAreaLoopState_intervals_unit state hwf)

theorem iterateAreaLoopState_intervals_covers
    (n : Nat) (state : AreaLoopState) {a b : Rat}
    (hcover : CoversInterval a b state.intervals) :
    CoversInterval a b (iterateAreaLoopState n state).intervals := by
  induction n generalizing state with
  | zero =>
      simpa [iterateAreaLoopState] using hcover
  | succ n ih =>
      simpa [iterateAreaLoopState] using
        ih (refineAreaLoopState state)
          (refineAreaLoopState_intervals_covers state hcover)

theorem iterateAreaLoopState_lo_eq_geometricLowerSum
    (n : Nat) (state : AreaLoopState)
    (hlo : state.lo = geometricLowerSum state.intervals) :
    (iterateAreaLoopState n state).lo =
      geometricLowerSum (iterateAreaLoopState n state).intervals := by
  induction n generalizing state with
  | zero =>
      simpa [iterateAreaLoopState] using hlo
  | succ n ih =>
      simpa [iterateAreaLoopState] using
        ih (refineAreaLoopState state)
          (refineAreaLoopState_lo_eq_geometricLowerSum state hlo)

theorem iterateAreaLoopState_hi_eq_geometricUpperSum
    (n : Nat) (state : AreaLoopState)
    (hwf : NonnegativeIntervals state.intervals)
    (hhi : state.hi = geometricUpperSum state.intervals) :
    (iterateAreaLoopState n state).hi =
      geometricUpperSum (iterateAreaLoopState n state).intervals := by
  induction n generalizing state with
  | zero =>
      simpa [iterateAreaLoopState] using hhi
  | succ n ih =>
      simpa [iterateAreaLoopState] using
        ih (refineAreaLoopState state)
          (refineAreaLoopState_intervals_nonnegative state hwf)
          (refineAreaLoopState_hi_eq_geometricUpperSum state hwf hhi)

def arctanAreaLoopInitial (x : Rat) : AreaLoopState :=
  { lo := x / (1 + x * x), hi := x, intervals := [(0, x)] }

def arctanAreaLoopState (x : Rat) (n : Nat) : AreaLoopState :=
  iterateAreaLoopState n (arctanAreaLoopInitial x)

theorem arctanAreaLoopState_succ (x : Rat) (n : Nat) :
    arctanAreaLoopState x (n + 1) =
      refineAreaLoopState (arctanAreaLoopState x n) := by
  unfold arctanAreaLoopState
  exact iterateAreaLoopState_succ_refine n (arctanAreaLoopInitial x)

theorem arctanAreaLoopInitial_intervals_nonnegative
    {x : Rat} (hx : 0 <= x) :
    NonnegativeIntervals (arctanAreaLoopInitial x).intervals := by
  simp [arctanAreaLoopInitial, NonnegativeIntervals, hx]

theorem arctanAreaLoopInitial_intervals_unit
    {x : Rat} (hx0 : 0 <= x) (hx1 : x <= 1) :
    UnitIntervals (arctanAreaLoopInitial x).intervals := by
  simp [arctanAreaLoopInitial, UnitIntervals, hx0, hx1]

theorem arctanAreaLoopInitial_intervals_covers
    {x : Rat} (hx : 0 <= x) :
    CoversInterval 0 x (arctanAreaLoopInitial x).intervals := by
  simp [arctanAreaLoopInitial, CoversInterval, hx]

theorem arctanAreaLoopState_intervals_nonnegative
    {x : Rat} (hx : 0 <= x) (n : Nat) :
    NonnegativeIntervals (arctanAreaLoopState x n).intervals := by
  unfold arctanAreaLoopState
  exact iterateAreaLoopState_intervals_nonnegative n
    (arctanAreaLoopInitial x)
    (arctanAreaLoopInitial_intervals_nonnegative hx)

theorem arctanAreaLoopState_intervals_unit
    {x : Rat} (hx0 : 0 <= x) (hx1 : x <= 1) (n : Nat) :
    UnitIntervals (arctanAreaLoopState x n).intervals := by
  unfold arctanAreaLoopState
  exact iterateAreaLoopState_intervals_unit n
    (arctanAreaLoopInitial x)
    (arctanAreaLoopInitial_intervals_unit hx0 hx1)

theorem arctanAreaLoopState_intervals_covers
    {x : Rat} (hx : 0 <= x) (n : Nat) :
    CoversInterval 0 x (arctanAreaLoopState x n).intervals := by
  unfold arctanAreaLoopState
  exact iterateAreaLoopState_intervals_covers n
    (arctanAreaLoopInitial x)
    (arctanAreaLoopInitial_intervals_covers hx)

/-- The stagewise chart image of a unit source partition gives an explicit
finite cover of the image interval. -/
theorem chartAddAreaLoop_covers
    {u x : Rat} (hu0 : 0 <= u) (hu1 : u < 1)
    (hx0 : 0 <= x) (hx1 : x <= 1) (n : Nat) :
    CoversInterval
      (RationalCircle.Trigonometry.chartAddParameter u 0)
      (RationalCircle.Trigonometry.chartAddParameter u x)
      (chartAddIntervals u (arctanAreaLoopState x n).intervals) := by
  apply chartAddIntervals_covers
  · exact arctanAreaLoopState_intervals_covers hx0 n
  · exact chartAddPositiveDenominators_of_unitIntervals u
      (arctanAreaLoopState x n).intervals hu0 hu1
      (arctanAreaLoopState_intervals_unit hx0 hx1 n)

/-- If the chart image endpoint stays in the unit interval, every transported
area-loop cell stays there as well. -/
theorem chartAddAreaLoop_intervals_unit
    {u x : Rat} (hu0 : 0 <= u) (huHalf : u <= (1 : Rat) / 2)
    (hx0 : 0 <= x) (hx1 : x <= 1)
    (himage :
      RationalCircle.Trigonometry.chartAddParameter u x <= 1)
    (n : Nat) :
    UnitIntervals
      (chartAddIntervals u (arctanAreaLoopState x n).intervals) := by
  have hu1 : u < 1 := by
    have hhalf : (1 : Rat) / 2 < 1 := by decide +kernel
    grind
  have hcover :=
    chartAddAreaLoop_covers hu0 hu1 hx0 hx1 n
  have hstart :
      0 <= RationalCircle.Trigonometry.chartAddParameter u 0 := by
    rw [RationalCircle.Trigonometry.chartAddParameter_zero_right]
    exact hu0
  exact CoversInterval.unit hstart himage hcover

/-- Unit-range preservation for a transported area loop only needs a positive
chart denominator and an explicit bound on the transported endpoint. -/
theorem chartAddAreaLoop_intervals_unit_of_lt
    {u x : Rat} (hu0 : 0 <= u) (hu1 : u < 1)
    (hx0 : 0 <= x) (hx1 : x <= 1)
    (himage : RationalCircle.Trigonometry.chartAddParameter u x <= 1)
    (n : Nat) :
    UnitIntervals
      (chartAddIntervals u (arctanAreaLoopState x n).intervals) := by
  have hcover := chartAddAreaLoop_covers hu0 hu1 hx0 hx1 n
  have hstart :
      0 <= RationalCircle.Trigonometry.chartAddParameter u 0 := by
    rw [RationalCircle.Trigonometry.chartAddParameter_zero_right]
    exact hu0
  exact CoversInterval.unit hstart himage hcover

private theorem div_two_pow_succ (a : Rat) (n : Nat) :
    (a / (((2 ^ n : Nat) : Rat))) / 2 =
      a / (((2 ^ (n + 1) : Nat) : Rat)) := by
  let A : Rat := ((2 ^ n : Nat) : Rat)
  have hApos : 0 < A := by
    dsimp [A]
    exact (Rat.natCast_pos).2 (Nat.pow_pos (by omega : 0 < 2))
  have hAne : A ≠ 0 := Rat.ne_of_gt hApos
  have h2 : (2 : Rat) ≠ 0 := by decide +kernel
  have hA2 : A * 2 ≠ 0 := by
    intro hz
    grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
  have hpow :
      (((2 ^ (n + 1) : Nat) : Rat)) = A * 2 := by
    dsimp [A]
    exact_mod_cast (by
      simpa using (Nat.pow_succ 2 n))
  rw [hpow]
  rw [Rat.div_def, Rat.div_def, Rat.div_def]
  grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]

theorem arctanAreaLoopInitial_squareSum (x : Rat) :
    intervalSquareSum (arctanAreaLoopInitial x).intervals = x * x := by
  simp [arctanAreaLoopInitial, intervalSquareSum]
  grind [Rat.sub_eq_add_neg]

theorem arctanAreaLoopState_squareSum (x : Rat) (n : Nat) :
    intervalSquareSum (arctanAreaLoopState x n).intervals =
      (x * x) / (((2 ^ n : Nat) : Rat)) := by
  induction n with
  | zero =>
      calc
        intervalSquareSum (arctanAreaLoopState x 0).intervals =
            x * x := by
          simpa [arctanAreaLoopState, iterateAreaLoopState]
            using arctanAreaLoopInitial_squareSum x
        _ = (x * x) / (((2 ^ 0 : Nat) : Rat)) := by
          rw [show (((2 ^ 0 : Nat) : Rat)) = 1 by decide +kernel]
          rw [Rat.div_def]
          grind
  | succ n ih =>
      rw [arctanAreaLoopState_succ, refineAreaLoopState_squareSum, ih]
      exact div_two_pow_succ (x * x) n

theorem arctanAreaLoopState_one_squareSum (n : Nat) :
    intervalSquareSum (arctanAreaLoopState 1 n).intervals =
      1 / (((2 ^ n : Nat) : Rat)) := by
  simpa using arctanAreaLoopState_squareSum (1 : Rat) n

/-- Mesh-budget form for the midpoint-rectangle arctangent schedule.

After `n` midpoint refinements of `[0,x]`, the sum of squared cell lengths is
exactly `x^2 / 2^n`.  This is the dyadic estimate used by the rectangle
integral validity proof. -/
theorem arctanIntegralRectangle_dyadicSquareMesh (x : Rat) (n : Nat) :
    intervalSquareSum (arctanAreaLoopState x n).intervals =
      (x * x) / (((2 ^ n : Nat) : Rat)) :=
  arctanAreaLoopState_squareSum x n

/-- Unit-endpoint specialization of `arctanIntegralRectangle_dyadicSquareMesh`. -/
theorem arctanIntegralRectangleAtOne_dyadicSquareMesh (n : Nat) :
    intervalSquareSum (arctanAreaLoopState 1 n).intervals =
      1 / (((2 ^ n : Nat) : Rat)) :=
  arctanAreaLoopState_one_squareSum n

/-- The transported midpoint partition has a squared mesh budget at most
sixty-four times that of its source on the half-unit chart. -/
theorem chartAddAreaLoop_squareSum_le_sixtyFour
    {u x : Rat} (hu0 : 0 <= u) (huHalf : u <= (1 : Rat) / 2)
    (hx0 : 0 <= x) (hx1 : x <= 1) (n : Nat) :
    intervalSquareSum
      (chartAddIntervals u (arctanAreaLoopState x n).intervals) <=
        64 * ((x * x) / (((2 ^ n : Nat) : Rat))) := by
  calc
    intervalSquareSum
      (chartAddIntervals u (arctanAreaLoopState x n).intervals) <=
        64 * intervalSquareSum (arctanAreaLoopState x n).intervals :=
      chartAddIntervals_squareSum_le_sixtyFour u
        (arctanAreaLoopState x n).intervals hu0 huHalf
        (arctanAreaLoopState_intervals_unit hx0 hx1 n)
    _ = 64 * ((x * x) / (((2 ^ n : Nat) : Rat))) := by
      rw [arctanAreaLoopState_squareSum]

/-- The interval width of a transported midpoint rectangle bracket has the
same dyadic decay, with an explicit rational factor. -/
theorem chartAddAreaLoop_integralSum_width_le
    {u x : Rat} (hu0 : 0 <= u) (huHalf : u <= (1 : Rat) / 2)
    (hx0 : 0 <= x) (hx1 : x <= 1)
    (himage : RationalCircle.Trigonometry.chartAddParameter u x <= 1)
    (n : Nat) :
    (integralSumInterval
      (chartAddIntervals u (arctanAreaLoopState x n).intervals)).width <=
        128 * ((x * x) / (((2 ^ n : Nat) : Rat))) := by
  calc
    (integralSumInterval
      (chartAddIntervals u (arctanAreaLoopState x n).intervals)).width <=
        2 * intervalSquareSum
          (chartAddIntervals u (arctanAreaLoopState x n).intervals) :=
      integralSumInterval_width_le_two_squareSum
        (chartAddIntervals u (arctanAreaLoopState x n).intervals)
        (chartAddAreaLoop_intervals_unit hu0 huHalf hx0 hx1 himage n)
    _ <= 2 * (64 * ((x * x) / (((2 ^ n : Nat) : Rat)))) :=
      Rat.mul_le_mul_of_nonneg_left
        (chartAddAreaLoop_squareSum_le_sixtyFour hu0 huHalf hx0 hx1 n)
        (by decide +kernel : (0 : Rat) <= 2)
    _ = 128 * ((x * x) / (((2 ^ n : Nat) : Rat))) := by
      grind [Rat.mul_assoc, Rat.mul_comm]

/-- The local pole-margin hypothesis gives the same transported mesh budget
even when the chart base is in the right half of the unit branch. -/
theorem chartAddAreaLoop_squareSum_le_sixtyFour_of_rightProduct_le_half
    {u x : Rat} (hu0 : 0 <= u) (hu1 : u <= 1)
    (hx0 : 0 <= x) (hx1 : x <= 1)
    (hux : u * x <= (1 : Rat) / 2) (n : Nat) :
    intervalSquareSum
      (chartAddIntervals u (arctanAreaLoopState x n).intervals) <=
        64 * ((x * x) / (((2 ^ n : Nat) : Rat))) := by
  have hcover : CoversInterval 0 x (arctanAreaLoopState x n).intervals :=
    arctanAreaLoopState_intervals_covers hx0 n
  have hproduct :
      ChartAddRightProductAtMostHalf u
        (arctanAreaLoopState x n).intervals :=
    CoversInterval.chartAddRightProductAtMostHalf hu0 hux hcover
  calc
    intervalSquareSum
      (chartAddIntervals u (arctanAreaLoopState x n).intervals) <=
        64 * intervalSquareSum (arctanAreaLoopState x n).intervals :=
      chartAddIntervals_squareSum_le_sixtyFour_of_rightProduct_le_half u
        (arctanAreaLoopState x n).intervals hu0 hu1
        (arctanAreaLoopState_intervals_unit hx0 hx1 n) hproduct
    _ = 64 * ((x * x) / (((2 ^ n : Nat) : Rat))) := by
      rw [arctanAreaLoopState_squareSum]

/-- A transported rectangle width under the local pole-margin condition. -/
theorem chartAddAreaLoop_integralSum_width_le_of_rightProduct_le_half
    {u x : Rat} (hu0 : 0 <= u) (hu1 : u < 1) (huOne : u <= 1)
    (hx0 : 0 <= x) (hx1 : x <= 1)
    (hux : u * x <= (1 : Rat) / 2)
    (himage : RationalCircle.Trigonometry.chartAddParameter u x <= 1)
    (n : Nat) :
    (integralSumInterval
      (chartAddIntervals u (arctanAreaLoopState x n).intervals)).width <=
        128 * ((x * x) / (((2 ^ n : Nat) : Rat))) := by
  calc
    (integralSumInterval
      (chartAddIntervals u (arctanAreaLoopState x n).intervals)).width <=
        2 * intervalSquareSum
          (chartAddIntervals u (arctanAreaLoopState x n).intervals) :=
      integralSumInterval_width_le_two_squareSum
        (chartAddIntervals u (arctanAreaLoopState x n).intervals)
        (chartAddAreaLoop_intervals_unit_of_lt hu0 hu1 hx0 hx1 himage n)
    _ <= 2 * (64 * ((x * x) / (((2 ^ n : Nat) : Rat)))) :=
      Rat.mul_le_mul_of_nonneg_left
        (chartAddAreaLoop_squareSum_le_sixtyFour_of_rightProduct_le_half
          hu0 huOne hx0 hx1 hux n)
        (by decide +kernel : (0 : Rat) <= 2)
    _ = 128 * ((x * x) / (((2 ^ n : Nat) : Rat))) := by
      grind [Rat.mul_assoc, Rat.mul_comm]

/-- Endpointwise chart transport commutes with the *refinement order* needed
for rectangle sums.  The charted split point need not be the midpoint of its
image cell: monotonicity of lower and upper rectangles is enough. -/
private theorem chartAdd_refineAux_integralSum_refines
    (u lo hi : Rat) (intervals : List (Rat × Rat))
    (hu0 : 0 <= u) (hu1 : u < 1)
    (hintervals : UnitIntervals intervals) :
    (integralSumInterval (chartAddIntervals u intervals)).ContainsInterval
      (integralSumInterval
        (chartAddIntervals u
          (AreaLoopState.refineAux lo hi intervals).intervals)) := by
  induction intervals generalizing lo hi with
  | nil =>
      simp [AreaLoopState.refineAux, chartAddIntervals, integralSumInterval,
        QInterval.ContainsInterval]
  | cons interval rest ih =>
      rcases interval with ⟨p, r⟩
      rcases hintervals with ⟨hp0, hpr, hr1, hrest⟩
      let q : Rat := (p + r) / 2
      have hpq : p <= q := by
        dsimp [q]
        exact left_le_midpoint hpr
      have hqr : q <= r := by
        dsimp [q]
        exact midpoint_le_right hpr
      have hq1 : q <= 1 := Rat.le_trans hqr hr1
      have hp1 : p <= 1 := Rat.le_trans hpq hq1
      have hdenP : 0 < RationalCircle.Trigonometry.chartAddDen u p :=
        chartAddDen_pos_of_unit hu0 hu1 hp1
      have hdenQ : 0 < RationalCircle.Trigonometry.chartAddDen u q :=
        chartAddDen_pos_of_unit hu0 hu1 hq1
      have hdenR : 0 < RationalCircle.Trigonometry.chartAddDen u r :=
        chartAddDen_pos_of_unit hu0 hu1 hr1
      have himageP : 0 <= RationalCircle.Trigonometry.chartAddParameter u p := by
        unfold RationalCircle.Trigonometry.chartAddParameter
          RationalCircle.Trigonometry.chartAddNum
          RationalCircle.Trigonometry.chartAddDen
        rw [Rat.div_def]
        exact Rat.mul_nonneg (Rat.add_nonneg hu0 hp0)
          (Rat.le_of_lt ((Rat.inv_pos).2 hdenP))
      have himagePQ :
          RationalCircle.Trigonometry.chartAddParameter u p <=
            RationalCircle.Trigonometry.chartAddParameter u q :=
        RationalCircle.Trigonometry.chartAddParameter_mono hdenP hdenQ hpq
      have himageQR :
          RationalCircle.Trigonometry.chartAddParameter u q <=
            RationalCircle.Trigonometry.chartAddParameter u r :=
        RationalCircle.Trigonometry.chartAddParameter_mono hdenQ hdenR hqr
      have htail :=
        ih (lo + arctanAreaIncrement p q r)
          (hi - arctanAreaDecrement p q r) hrest
      have hlower := integralLowerStep_refine himageP himagePQ himageQR
      have hupper := integralUpperStep_refine himageP himagePQ himageQR
      unfold QInterval.ContainsInterval integralSumInterval at htail ⊢
      simp only [AreaLoopState.refineAux, chartAddIntervals,
        integralLowerSum, integralUpperSum]
      constructor
      · calc
          integralLowerStep
              (RationalCircle.Trigonometry.chartAddParameter u p)
              (RationalCircle.Trigonometry.chartAddParameter u r) +
              integralLowerSum (chartAddIntervals u rest)
              <=
              (integralLowerStep
                (RationalCircle.Trigonometry.chartAddParameter u p)
                (RationalCircle.Trigonometry.chartAddParameter u q) +
                integralLowerStep
                  (RationalCircle.Trigonometry.chartAddParameter u q)
                  (RationalCircle.Trigonometry.chartAddParameter u r)) +
                integralLowerSum (chartAddIntervals u rest) :=
                rat_add_le_add hlower (Rat.le_refl)
          _ <=
              (integralLowerStep
                (RationalCircle.Trigonometry.chartAddParameter u p)
                (RationalCircle.Trigonometry.chartAddParameter u q) +
                integralLowerStep
                  (RationalCircle.Trigonometry.chartAddParameter u q)
                  (RationalCircle.Trigonometry.chartAddParameter u r)) +
                integralLowerSum
                  (chartAddIntervals u
                    (AreaLoopState.refineAux
                      (lo + arctanAreaIncrement p q r)
                      (hi - arctanAreaDecrement p q r) rest).intervals) :=
                rat_add_le_add (Rat.le_refl) htail.1
          _ =
              integralLowerStep
                (RationalCircle.Trigonometry.chartAddParameter u p)
                (RationalCircle.Trigonometry.chartAddParameter u q) +
              (integralLowerStep
                (RationalCircle.Trigonometry.chartAddParameter u q)
                (RationalCircle.Trigonometry.chartAddParameter u r) +
                integralLowerSum
                  (chartAddIntervals u
                    (AreaLoopState.refineAux
                      (lo + arctanAreaIncrement p q r)
                      (hi - arctanAreaDecrement p q r) rest).intervals)) := by
                grind [Rat.add_assoc, Rat.add_comm]
      · calc
          integralUpperStep
              (RationalCircle.Trigonometry.chartAddParameter u p)
              (RationalCircle.Trigonometry.chartAddParameter u q) +
            (integralUpperStep
              (RationalCircle.Trigonometry.chartAddParameter u q)
              (RationalCircle.Trigonometry.chartAddParameter u r) +
              integralUpperSum
                (chartAddIntervals u
                  (AreaLoopState.refineAux
                    (lo + arctanAreaIncrement p q r)
                    (hi - arctanAreaDecrement p q r) rest).intervals))
              =
              (integralUpperStep
                (RationalCircle.Trigonometry.chartAddParameter u p)
                (RationalCircle.Trigonometry.chartAddParameter u q) +
                integralUpperStep
                  (RationalCircle.Trigonometry.chartAddParameter u q)
                  (RationalCircle.Trigonometry.chartAddParameter u r)) +
                integralUpperSum
                  (chartAddIntervals u
                    (AreaLoopState.refineAux
                      (lo + arctanAreaIncrement p q r)
                      (hi - arctanAreaDecrement p q r) rest).intervals) := by
                grind [Rat.add_assoc, Rat.add_comm]
          _ <=
              (integralUpperStep
                (RationalCircle.Trigonometry.chartAddParameter u p)
                (RationalCircle.Trigonometry.chartAddParameter u q) +
                integralUpperStep
                  (RationalCircle.Trigonometry.chartAddParameter u q)
                  (RationalCircle.Trigonometry.chartAddParameter u r)) +
                integralUpperSum (chartAddIntervals u rest) :=
                rat_add_le_add (Rat.le_refl) htail.2
          _ <=
              integralUpperStep
                (RationalCircle.Trigonometry.chartAddParameter u p)
                (RationalCircle.Trigonometry.chartAddParameter u r) +
                integralUpperSum (chartAddIntervals u rest) :=
                rat_add_le_add hupper (Rat.le_refl)

theorem arctanAreaLoop_integralSum_contains_geometricSum
    {x : Rat} (hx : 0 <= x) (n : Nat) :
    (integralSumInterval (arctanAreaLoopState x n).intervals).ContainsInterval
      (geometricSumInterval (arctanAreaLoopState x n).intervals) :=
  integralSumInterval_contains_geometricSumInterval
    (arctanAreaLoopState x n).intervals
    (arctanAreaLoopState_intervals_nonnegative hx n)

theorem arctanAreaLoop_integralSum_overlaps_geometricSum
    {x : Rat} (hx : 0 <= x) (n : Nat) :
    QInterval.Overlaps
      (integralSumInterval (arctanAreaLoopState x n).intervals)
      (geometricSumInterval (arctanAreaLoopState x n).intervals) :=
  integralSumInterval_overlaps_geometricSumInterval
    (arctanAreaLoopState x n).intervals
    (arctanAreaLoopState_intervals_nonnegative hx n)

theorem arctanAreaLoop_integralSum_ordered
    {x : Rat} (hx : 0 <= x) (n : Nat) :
    0 <= (integralSumInterval (arctanAreaLoopState x n).intervals).width :=
  integralSumInterval_ordered
    (arctanAreaLoopState x n).intervals
    (arctanAreaLoopState_intervals_nonnegative hx n)

theorem arctanAreaLoop_integralSum_step_refines
    {x : Rat} (hx : 0 <= x) (n : Nat) :
    (integralSumInterval (arctanAreaLoopState x n).intervals).ContainsInterval
      (integralSumInterval (arctanAreaLoopState x (n + 1)).intervals) := by
  rw [arctanAreaLoopState_succ]
  exact refineAreaLoopState_integralSumInterval_refines
    (arctanAreaLoopState x n)
    (arctanAreaLoopState_intervals_nonnegative hx n)

theorem arctanAreaLoop_integralSum_refines_add
    {x : Rat} (hx : 0 <= x) (n k : Nat) :
    (integralSumInterval (arctanAreaLoopState x n).intervals).ContainsInterval
      (integralSumInterval (arctanAreaLoopState x (n + k)).intervals) := by
  induction k with
  | zero =>
      simp
      exact containsInterval_refl
        (integralSumInterval (arctanAreaLoopState x n).intervals)
  | succ k ih =>
      rw [show n + (k + 1) = (n + k) + 1 by omega]
      exact containsInterval_trans ih
        (arctanAreaLoop_integralSum_step_refines hx (n + k))

private theorem arctanAreaLoopInitial_lo_eq_geometricLowerSum
    (x : Rat) :
    (arctanAreaLoopInitial x).lo =
      geometricLowerSum (arctanAreaLoopInitial x).intervals := by
  simp [arctanAreaLoopInitial, geometricLowerSum, geometricLowerStep]
  rw [Rat.div_def, Rat.div_def]
  grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]

private theorem arctanAreaLoopInitial_hi_eq_geometricUpperSum
    (x : Rat) :
    (arctanAreaLoopInitial x).hi =
      geometricUpperSum (arctanAreaLoopInitial x).intervals := by
  simp [arctanAreaLoopInitial, geometricUpperSum, geometricUpperStep]
  rw [Rat.div_def]
  grind [Rat.sub_eq_add_neg, Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]

theorem arctanAreaLoopState_lo_eq_geometricLowerSum
    (x : Rat) (n : Nat) :
    (arctanAreaLoopState x n).lo =
      geometricLowerSum (arctanAreaLoopState x n).intervals := by
  unfold arctanAreaLoopState
  exact iterateAreaLoopState_lo_eq_geometricLowerSum n
    (arctanAreaLoopInitial x)
    (arctanAreaLoopInitial_lo_eq_geometricLowerSum x)

theorem arctanAreaLoopState_hi_eq_geometricUpperSum
    {x : Rat} (hx : 0 <= x) (n : Nat) :
    (arctanAreaLoopState x n).hi =
      geometricUpperSum (arctanAreaLoopState x n).intervals := by
  unfold arctanAreaLoopState
  exact iterateAreaLoopState_hi_eq_geometricUpperSum n
    (arctanAreaLoopInitial x)
    (arctanAreaLoopInitial_intervals_nonnegative hx)
    (arctanAreaLoopInitial_hi_eq_geometricUpperSum x)

def positiveLoopComputeAtStage (x : Rat) (n : Nat) : QInterval :=
  let state := arctanAreaLoopState x n
  { lo := state.lo, hi := state.hi }

theorem positiveLoopComputeAtStage_eq_geometricSumInterval
    {x : Rat} (hx : 0 <= x) (n : Nat) :
    positiveLoopComputeAtStage x n =
      geometricSumInterval (arctanAreaLoopState x n).intervals := by
  unfold positiveLoopComputeAtStage geometricSumInterval
  simp [arctanAreaLoopState_lo_eq_geometricLowerSum,
    arctanAreaLoopState_hi_eq_geometricUpperSum hx]

theorem arctanAreaLoop_integralSum_contains_positiveLoop
    {x : Rat} (hx : 0 <= x) (n : Nat) :
    (integralSumInterval (arctanAreaLoopState x n).intervals).ContainsInterval
      (positiveLoopComputeAtStage x n) := by
  rw [positiveLoopComputeAtStage_eq_geometricSumInterval hx n]
  exact arctanAreaLoop_integralSum_contains_geometricSum hx n

theorem arctanAreaLoop_integralSum_overlaps_positiveLoop
    {x : Rat} (hx : 0 <= x) (n : Nat) :
    QInterval.Overlaps
      (integralSumInterval (arctanAreaLoopState x n).intervals)
      (positiveLoopComputeAtStage x n) := by
  rw [positiveLoopComputeAtStage_eq_geometricSumInterval hx n]
  exact arctanAreaLoop_integralSum_overlaps_geometricSum hx n

theorem positiveLoopComputeAtStage_ordered
    {x : Rat} (hx : 0 <= x) (n : Nat) :
    0 <= (positiveLoopComputeAtStage x n).width := by
  rw [positiveLoopComputeAtStage_eq_geometricSumInterval hx n]
  exact geometricSumInterval_ordered
    (arctanAreaLoopState x n).intervals
    (arctanAreaLoopState_intervals_nonnegative hx n)

theorem positiveLoopComputeAtStage_step_refines
    {x : Rat} (hx : 0 <= x) (n : Nat) :
    (positiveLoopComputeAtStage x n).lo <=
      (positiveLoopComputeAtStage x (n + 1)).lo /\
    (positiveLoopComputeAtStage x (n + 1)).hi <=
      (positiveLoopComputeAtStage x n).hi := by
  unfold positiveLoopComputeAtStage
  rw [arctanAreaLoopState_succ]
  exact refineAreaLoopState_endpoint_refines
    (arctanAreaLoopState x n)
    (arctanAreaLoopState_intervals_nonnegative hx n)

theorem positiveLoopComputeAtStage_nested
    {x : Rat} (hx : 0 <= x) :
    forall n m, n <= m ->
      (positiveLoopComputeAtStage x n).lo <=
        (positiveLoopComputeAtStage x m).lo /\
      (positiveLoopComputeAtStage x m).lo <=
        (positiveLoopComputeAtStage x m).hi /\
      (positiveLoopComputeAtStage x m).hi <=
        (positiveLoopComputeAtStage x n).hi := by
  intro n m hnm
  induction hnm with
  | refl =>
      have hordered := positiveLoopComputeAtStage_ordered hx n
      constructor
      · exact Rat.le_refl
      · constructor
        · grind [QInterval.width, Rat.sub_eq_add_neg]
        · exact Rat.le_refl
  | step hnk ih =>
      rename_i k
      have hstep := positiveLoopComputeAtStage_step_refines hx k
      have hordered := positiveLoopComputeAtStage_ordered hx (k + 1)
      constructor
      · exact Rat.le_trans ih.1 hstep.1
      · constructor
        · grind [QInterval.width, Rat.sub_eq_add_neg]
        · exact Rat.le_trans hstep.2 ih.2.2

/-- Rectangle-sum arctangent computation at a rational endpoint `x`, using the
same midpoint partition schedule as `arctanGeom x`. -/
def arctanIntegralRectangleCompute (x : Rat) (n : Nat) : QInterval :=
  integralSumInterval (arctanAreaLoopState x n).intervals

/-- Every lower rectangle sum on a nonnegative arctangent interval is
nonnegative. -/
theorem arctanIntegralRectangleCompute_lower_nonnegative
    {x : Rat} (hx : 0 <= x) (n : Nat) :
    0 <= (arctanIntegralRectangleCompute x n).lo := by
  unfold arctanIntegralRectangleCompute integralSumInterval
  exact integralLowerSum_nonneg (arctanAreaLoopState x n).intervals
    (arctanAreaLoopState_intervals_nonnegative hx n)

/-- Every upper rectangle sum on a nonnegative arctangent interval is at
most the interval length. -/
theorem arctanIntegralRectangleCompute_upper_le_input
    {x : Rat} (hx : 0 <= x) (n : Nat) :
    (arctanIntegralRectangleCompute x n).hi <= x := by
  unfold arctanIntegralRectangleCompute integralSumInterval
  calc
    integralUpperSum (arctanAreaLoopState x n).intervals <= x - 0 :=
      integralUpperSum_le_intervalLength
      (arctanAreaLoopState_intervals_covers hx n)
    _ = x := by grind [Rat.sub_eq_add_neg]

theorem arctanIntegralRectangleCompute_input_mul_kernel_le_lower
    {x : Rat} (hx : 0 <= x) (n : Nat) :
    x * integralKernel x <= (arctanIntegralRectangleCompute x n).lo := by
  unfold arctanIntegralRectangleCompute integralSumInterval
  have hbound := intervalLength_mul_integralKernel_right_le_integralLowerSum
    (a := 0) (b := x) (intervals := (arctanAreaLoopState x n).intervals)
    (by decide +kernel : (0 : Rat) <= 0)
    (arctanAreaLoopState_intervals_covers hx n)
  calc
    x * integralKernel x = (x - 0) * integralKernel x := by
      congr 1
      grind [Rat.sub_eq_add_neg]
    _ <= integralLowerSum (arctanAreaLoopState x n).intervals := hbound

theorem arctanIntegralRectangleCompute_input_sub_lower_le_cube
    {x : Rat} (hx : 0 <= x) (n : Nat) :
    x - (arctanIntegralRectangleCompute x n).lo <= x * x * x := by
  have hlower := arctanIntegralRectangleCompute_input_mul_kernel_le_lower hx n
  have hkernelError : x - x * integralKernel x <= x * x * x := by
    let d : Rat := 1 + x * x
    have hdpos : 0 < d := by
      dsimp [d]
      have hsq := RationalCircle.Stage.ratSquare_nonneg x
      grind
    have hdone : 1 <= d := by
      dsimp [d]
      have hsq := RationalCircle.Stage.ratSquare_nonneg x
      grind
    have hcube : 0 <= x * x * x := by
      have hsq : 0 <= x * x := Rat.mul_nonneg hx hx
      exact Rat.mul_nonneg hsq hx
    have hdinv : d⁻¹ <= 1 := by
      apply Rat.le_of_mul_le_mul_right (c := d)
      · calc
          d⁻¹ * d = d * d⁻¹ := by rw [Rat.mul_comm]
          _ = 1 := Rat.mul_inv_cancel _ (Rat.ne_of_gt hdpos)
          _ <= 1 * d := by simpa using hdone
      · exact hdpos
    calc
      x - x * integralKernel x = (x * x * x) * d⁻¹ := by
        unfold integralKernel
        rw [Rat.div_def]
        have hcancel : d * d⁻¹ = 1 :=
          Rat.mul_inv_cancel _ (Rat.ne_of_gt hdpos)
        dsimp [d] at hcancel ⊢
        grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
          Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
      _ <= (x * x * x) * 1 :=
        Rat.mul_le_mul_of_nonneg_left hdinv hcube
      _ = x * x * x := by grind
  exact Rat.le_trans (by grind [Rat.sub_eq_add_neg]) hkernelError

/-- Every finite rectangle bracket for arctangent is contained in the
elementary tangent enclosure `[x - x^3, x]`. -/
theorem arctanIntegralRectangleCompute_tangent_box_contains
    {x : Rat} (hx : 0 <= x) (n : Nat) :
    ({ lo := x - x * x * x, hi := x } : QInterval).ContainsInterval
      (arctanIntegralRectangleCompute x n) := by
  unfold QInterval.ContainsInterval
  constructor
  · have hlower := arctanIntegralRectangleCompute_input_sub_lower_le_cube hx n
    grind [Rat.sub_eq_add_neg]
  · exact arctanIntegralRectangleCompute_upper_le_input hx n

/-- The lower endpoint of the rectangle bracket is exactly zero at the
zero upper endpoint. -/
theorem arctanIntegralRectangleCompute_zero_lower (n : Nat) :
    (arctanIntegralRectangleCompute 0 n).lo = 0 := by
  have hlow : 0 <= (arctanIntegralRectangleCompute 0 n).lo :=
    arctanIntegralRectangleCompute_lower_nonnegative (by decide +kernel) n
  have hupper : (arctanIntegralRectangleCompute 0 n).hi <= 0 :=
    arctanIntegralRectangleCompute_upper_le_input (by decide +kernel) n
  have hordered :
      (arctanIntegralRectangleCompute 0 n).lo <=
        (arctanIntegralRectangleCompute 0 n).hi := by
    unfold arctanIntegralRectangleCompute integralSumInterval
    exact integralLowerSum_le_integralUpperSum
      (arctanAreaLoopState 0 n).intervals
      (arctanAreaLoopState_intervals_nonnegative (by decide +kernel) n)
  exact Rat.le_antisymm (Rat.le_trans hordered hupper) hlow

/-- The upper endpoint of the rectangle bracket is exactly zero at the
zero upper endpoint. -/
theorem arctanIntegralRectangleCompute_zero_upper (n : Nat) :
    (arctanIntegralRectangleCompute 0 n).hi = 0 := by
  have hlow : 0 <= (arctanIntegralRectangleCompute 0 n).lo :=
    arctanIntegralRectangleCompute_lower_nonnegative (by decide +kernel) n
  have hupper : (arctanIntegralRectangleCompute 0 n).hi <= 0 :=
    arctanIntegralRectangleCompute_upper_le_input (by decide +kernel) n
  have hordered :
      (arctanIntegralRectangleCompute 0 n).lo <=
        (arctanIntegralRectangleCompute 0 n).hi := by
    unfold arctanIntegralRectangleCompute integralSumInterval
    exact integralLowerSum_le_integralUpperSum
      (arctanAreaLoopState 0 n).intervals
      (arctanAreaLoopState_intervals_nonnegative (by decide +kernel) n)
  exact Rat.le_antisymm hupper (Rat.le_trans hlow hordered)

/-- Dividing the finite tangent enclosure at the zero endpoint gives a
basepoint difference-quotient bracket of width `h^2`. -/
theorem arctanIntegralRectangleCompute_zero_tangent_quotient_contains
    {h : Rat} (hpos : 0 < h) (n : Nat) :
    ({ lo := 1 - h * h, hi := 1 } : QInterval).ContainsInterval
      (QInterval.differenceQuotient
        (arctanIntegralRectangleCompute h n)
        (arctanIntegralRectangleCompute 0 n) h) := by
  have hne : h ≠ 0 := Rat.ne_of_gt hpos
  have hinv : 0 <= 1 / h := by
    rw [Rat.div_def]
    simpa using Rat.le_of_lt ((Rat.inv_pos).2 hpos)
  have hbox := arctanIntegralRectangleCompute_tangent_box_contains
    (Rat.le_of_lt hpos) n
  have hleft :
      1 - h * h <= (1 / h) * (arctanIntegralRectangleCompute h n).lo := by
    apply Rat.le_of_mul_le_mul_right (c := h)
    · calc
        (1 - h * h) * h = h - h * h * h := by
          grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
            Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
        _ <= (arctanIntegralRectangleCompute h n).lo := hbox.1
        _ = ((1 / h) * (arctanIntegralRectangleCompute h n).lo) * h := by
          rw [Rat.div_def]
          have hcancel : h * h⁻¹ = 1 := Rat.mul_inv_cancel h hne
          grind [Rat.mul_assoc, Rat.mul_comm]
    · exact hpos
  have hright :
      (1 / h) * (arctanIntegralRectangleCompute h n).hi <= 1 := by
    apply Rat.le_of_mul_le_mul_right (c := h)
    · calc
        ((1 / h) * (arctanIntegralRectangleCompute h n).hi) * h =
            (arctanIntegralRectangleCompute h n).hi := by
              rw [Rat.div_def]
              have hcancel : h * h⁻¹ = 1 := Rat.mul_inv_cancel h hne
              grind [Rat.mul_assoc, Rat.mul_comm]
        _ <= h := arctanIntegralRectangleCompute_upper_le_input
          (Rat.le_of_lt hpos) n
        _ = 1 * h := by grind
    · exact hpos
  unfold QInterval.ContainsInterval QInterval.differenceQuotient
    QInterval.divRat QInterval.sub QInterval.scaleRat
  rw [if_pos hinv]
  rw [arctanIntegralRectangleCompute_zero_lower,
    arctanIntegralRectangleCompute_zero_upper]
  constructor
  · calc
      1 - h * h <= (1 / h) * (arctanIntegralRectangleCompute h n).lo := hleft
      _ = (1 / h) * ((arctanIntegralRectangleCompute h n).lo - 0) := by
        congr 1
        grind [Rat.sub_eq_add_neg]
  · calc
      (1 / h) * ((arctanIntegralRectangleCompute h n).hi - 0) =
          (1 / h) * (arctanIntegralRectangleCompute h n).hi := by
            congr 1
            grind [Rat.sub_eq_add_neg]
      _ <= 1 := hright

/-- Finite monotonicity in the upper endpoint of the rectangle arctangent.
The proof appends the rational tail from x to y to the cover from 0 to x and
then compares its lower sum with the upper sum from the stage cover from 0 to
y. -/
theorem arctanIntegralRectangleCompute_lower_le_upper_of_le
    {x y : Rat} (hx0 : 0 <= x) (hxy : x <= y) (n : Nat) :
    (arctanIntegralRectangleCompute x n).lo <=
      (arctanIntegralRectangleCompute y n).hi := by
  let left : List (Rat × Rat) := (arctanAreaLoopState x n).intervals
  let right : List (Rat × Rat) := (arctanAreaLoopState y n).intervals
  have hleft : CoversInterval 0 x left := by
    dsimp [left]
    exact arctanAreaLoopState_intervals_covers hx0 n
  have hy0 : 0 <= y := Rat.le_trans hx0 hxy
  have hright : CoversInterval 0 y right := by
    dsimp [right]
    exact arctanAreaLoopState_intervals_covers hy0 n
  have htail : NonnegativeIntervals [(x, y)] := by
    simp [NonnegativeIntervals, hx0, hxy]
  have hprefix :
      integralLowerSum left <= integralLowerSum (left ++ [(x, y)]) :=
    integralLowerSum_le_append_of_nonnegative left [(x, y)] htail
  have hcover : CoversInterval 0 y (left ++ [(x, y)]) :=
    CoversInterval.extend_right hleft hxy
  have hcompare :
      integralLowerSum (left ++ [(x, y)]) <= integralUpperSum right :=
    integralLowerSum_le_integralUpperSum_of_covers
      (a := 0) (b := y) (by decide +kernel) (left ++ [(x, y)]) right
      hcover hright
  change integralLowerSum left <= integralUpperSum right
  exact Rat.le_trans hprefix hcompare

/-- At every midpoint-refinement stage, the endpointwise chart image of a
unit source partition has a target rectangle bracket containing the source
bracket. -/
theorem chartAddAreaLoop_integralSum_contains
    {u x : Rat} (hu0 : 0 <= u) (hu1 : u < 1)
    (hx0 : 0 <= x) (hx1 : x <= 1) (n : Nat) :
    (integralSumInterval
      (chartAddIntervals u (arctanAreaLoopState x n).intervals)).ContainsInterval
        (arctanIntegralRectangleCompute x n) := by
  unfold arctanIntegralRectangleCompute
  apply chartAddIntervals_integralSum_contains
  · exact hu0
  · exact unitIntervals_nonnegative _
      (arctanAreaLoopState_intervals_unit hx0 hx1 n)
  · exact chartAddPositiveDenominators_of_unitIntervals u
      (arctanAreaLoopState x n).intervals hu0 hu1
      (arctanAreaLoopState_intervals_unit hx0 hx1 n)

/-- A raw stage for the finite rectangle bracket obtained by transporting the
midpoint partition through the rational tangent-addition chart. -/
def chartAddAreaLoopCompute (u x : Rat) (n : Nat) : QInterval :=
  integralSumInterval
    (chartAddIntervals u (arctanAreaLoopState x n).intervals)

def chartAddAreaLoopRaw (u x : Rat) : RealCompute where
  compute := chartAddAreaLoopCompute u x

theorem chartAddAreaLoopCompute_ordered
    {u x : Rat} (hu0 : 0 <= u) (hu1 : u < 1)
    (hx0 : 0 <= x) (hx1 : x <= 1) (n : Nat) :
    0 <= (chartAddAreaLoopCompute u x n).width := by
  unfold chartAddAreaLoopCompute
  exact integralSumInterval_ordered
    (chartAddIntervals u (arctanAreaLoopState x n).intervals)
    (chartAddIntervals_nonnegative u
      (arctanAreaLoopState x n).intervals hu0
      (arctanAreaLoopState_intervals_nonnegative hx0 n)
      (chartAddPositiveDenominators_of_unitIntervals u
        (arctanAreaLoopState x n).intervals hu0 hu1
        (arctanAreaLoopState_intervals_unit hx0 hx1 n)))

private theorem chartAddAreaLoopCompute_step_refines
    {u x : Rat} (hu0 : 0 <= u) (hu1 : u < 1)
    (hx0 : 0 <= x) (hx1 : x <= 1) (n : Nat) :
    (chartAddAreaLoopCompute u x n).ContainsInterval
      (chartAddAreaLoopCompute u x (n + 1)) := by
  unfold chartAddAreaLoopCompute
  rw [arctanAreaLoopState_succ]
  exact chartAdd_refineAux_integralSum_refines u
    (arctanAreaLoopState x n).lo (arctanAreaLoopState x n).hi
    (arctanAreaLoopState x n).intervals hu0 hu1
    (arctanAreaLoopState_intervals_unit hx0 hx1 n)

theorem chartAddAreaLoopCompute_nested
    {u x : Rat} (hu0 : 0 <= u) (hu1 : u < 1)
    (hx0 : 0 <= x) (hx1 : x <= 1) :
    forall n m, n <= m ->
      (chartAddAreaLoopCompute u x n).lo <=
        (chartAddAreaLoopCompute u x m).lo /\
      (chartAddAreaLoopCompute u x m).lo <=
        (chartAddAreaLoopCompute u x m).hi /\
      (chartAddAreaLoopCompute u x m).hi <=
        (chartAddAreaLoopCompute u x n).hi := by
  intro n m hnm
  induction hnm with
  | refl =>
      have hordered := chartAddAreaLoopCompute_ordered hu0 hu1 hx0 hx1 n
      constructor
      · exact Rat.le_refl
      · constructor
        · grind [QInterval.width, Rat.sub_eq_add_neg]
        · exact Rat.le_refl
  | step hnk ih =>
      rename_i k
      have hstep := chartAddAreaLoopCompute_step_refines hu0 hu1 hx0 hx1 k
      unfold QInterval.ContainsInterval at hstep
      have hordered := chartAddAreaLoopCompute_ordered hu0 hu1 hx0 hx1 (k + 1)
      constructor
      · exact Rat.le_trans ih.1 hstep.1
      · constructor
        · grind [QInterval.width, Rat.sub_eq_add_neg]
        · exact Rat.le_trans hstep.2 ih.2.2

def arctanIntegralRectangleRaw (x : Rat) : RealCompute where
  compute := arctanIntegralRectangleCompute x

theorem arctanIntegralRectangleCompute_ordered
    {x : Rat} (hx : 0 <= x) (n : Nat) :
    0 <= (arctanIntegralRectangleCompute x n).width := by
  unfold arctanIntegralRectangleCompute
  exact arctanAreaLoop_integralSum_ordered hx n

private theorem arctanIntegralRectangleCompute_step_refines
    {x : Rat} (hx : 0 <= x) (n : Nat) :
    (arctanIntegralRectangleCompute x n).ContainsInterval
      (arctanIntegralRectangleCompute x (n + 1)) := by
  unfold arctanIntegralRectangleCompute
  exact arctanAreaLoop_integralSum_step_refines hx n

theorem arctanIntegralRectangleCompute_nested
    {x : Rat} (hx : 0 <= x) :
    forall n m, n <= m ->
      (arctanIntegralRectangleCompute x n).lo <=
        (arctanIntegralRectangleCompute x m).lo /\
      (arctanIntegralRectangleCompute x m).lo <=
        (arctanIntegralRectangleCompute x m).hi /\
      (arctanIntegralRectangleCompute x m).hi <=
        (arctanIntegralRectangleCompute x n).hi := by
  intro n m hnm
  induction hnm with
  | refl =>
      have hordered := arctanIntegralRectangleCompute_ordered hx n
      constructor
      · exact Rat.le_refl
      · constructor
        · grind [QInterval.width, Rat.sub_eq_add_neg]
        · exact Rat.le_refl
  | step hnk ih =>
      rename_i k
      have hstep := arctanIntegralRectangleCompute_step_refines hx k
      unfold QInterval.ContainsInterval at hstep
      have hordered := arctanIntegralRectangleCompute_ordered hx (k + 1)
      constructor
      · exact Rat.le_trans ih.1 hstep.1
      · constructor
        · grind [QInterval.width, Rat.sub_eq_add_neg]
        · exact Rat.le_trans hstep.2 ih.2.2

/-- The rectangle-sum arctangent computation at `1`, using the same midpoint
partition schedule as `arctanGeom`. -/
def arctanIntegralRectangleComputeAtOne (n : Nat) : QInterval :=
  integralSumInterval (arctanAreaLoopState 1 n).intervals

def arctanIntegralRectangleRawAtOne : RealCompute where
  compute := arctanIntegralRectangleComputeAtOne

theorem arctanIntegralRectangleComputeAtOne_ordered (n : Nat) :
    0 <= (arctanIntegralRectangleComputeAtOne n).width := by
  unfold arctanIntegralRectangleComputeAtOne
  exact arctanAreaLoop_integralSum_ordered
    (x := 1) (by decide +kernel) n

private theorem arctanIntegralRectangleComputeAtOne_step_refines (n : Nat) :
    (arctanIntegralRectangleComputeAtOne n).ContainsInterval
      (arctanIntegralRectangleComputeAtOne (n + 1)) := by
  unfold arctanIntegralRectangleComputeAtOne
  exact arctanAreaLoop_integralSum_step_refines
    (x := 1) (by decide +kernel) n

theorem arctanIntegralRectangleComputeAtOne_nested :
    forall n m, n <= m ->
      (arctanIntegralRectangleComputeAtOne n).lo <=
        (arctanIntegralRectangleComputeAtOne m).lo /\
      (arctanIntegralRectangleComputeAtOne m).lo <=
        (arctanIntegralRectangleComputeAtOne m).hi /\
      (arctanIntegralRectangleComputeAtOne m).hi <=
        (arctanIntegralRectangleComputeAtOne n).hi := by
  intro n m hnm
  induction hnm with
  | refl =>
      have hordered := arctanIntegralRectangleComputeAtOne_ordered n
      constructor
      · exact Rat.le_refl
      · constructor
        · grind [QInterval.width, Rat.sub_eq_add_neg]
        · exact Rat.le_refl
  | step hnk ih =>
      rename_i k
      have hstep := arctanIntegralRectangleComputeAtOne_step_refines k
      unfold QInterval.ContainsInterval at hstep
      have hordered := arctanIntegralRectangleComputeAtOne_ordered (k + 1)
      constructor
      · exact Rat.le_trans ih.1 hstep.1
      · constructor
        · grind [QInterval.width, Rat.sub_eq_add_neg]
        · exact Rat.le_trans hstep.2 ih.2.2

private theorem succ_le_two_pow_succ (n : Nat) :
    n + 1 <= 2 ^ (n + 1) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      calc
        n + 1 + 1 <= 2 * (n + 1) := by omega
        _ <= 2 * 2 ^ (n + 1) := Nat.mul_le_mul_left 2 ih
        _ = 2 ^ (n + 1 + 1) := by
          rw [Nat.pow_succ]
          omega

private theorem four_mul_one_div_eq_div (N : Nat) :
    4 * (1 / (N : Rat)) = 4 / (N : Rat) := by
  rw [Rat.div_def]
  grind [Rat.mul_assoc]

private theorem two_mul_one_div_two_pow_eq_four_mul_one_div_two_pow_succ
    (n : Nat) :
    2 * (1 / (((2 ^ n : Nat) : Rat))) =
      4 * (1 / (((2 ^ (n + 1) : Nat) : Rat))) := by
  let A : Rat := ((2 ^ n : Nat) : Rat)
  have hApos : 0 < A := by
    dsimp [A]
    exact (Rat.natCast_pos).2 (Nat.pow_pos (by omega : 0 < 2))
  have hAne : A ≠ 0 := Rat.ne_of_gt hApos
  have h2 : (2 : Rat) ≠ 0 := by decide +kernel
  have hA2 : A * 2 ≠ 0 := by
    intro hz
    grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
  have hpow :
      (((2 ^ (n + 1) : Nat) : Rat)) = A * 2 := by
    dsimp [A]
    exact_mod_cast (by
      simpa using (Nat.pow_succ 2 n))
  rw [hpow]
  repeat rw [Rat.div_def]
  grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]

private theorem square_le_one_of_unit {x : Rat}
    (hx0 : 0 <= x) (hx1 : x <= 1) :
    x * x <= 1 := by
  have hxx : x * x <= x * 1 :=
    Rat.mul_le_mul_of_nonneg_left hx1 hx0
  calc
    x * x <= x * 1 := hxx
    _ = x := by grind
    _ <= 1 := hx1

private theorem square_div_two_pow_le_one_div_two_pow
    {x : Rat} (hx0 : 0 <= x) (hx1 : x <= 1) (n : Nat) :
    (x * x) / (((2 ^ n : Nat) : Rat)) <=
      1 / (((2 ^ n : Nat) : Rat)) := by
  let D : Rat := ((2 ^ n : Nat) : Rat)
  have hDpos : 0 < D := by
    dsimp [D]
    exact (Rat.natCast_pos).2 (Nat.pow_pos (by omega : 0 < 2))
  have hinv_nonneg : 0 <= D⁻¹ :=
    Rat.le_of_lt ((Rat.inv_pos).2 hDpos)
  have hsquare : x * x <= 1 := square_le_one_of_unit hx0 hx1
  rw [Rat.div_def, Rat.div_def]
  exact Rat.mul_le_mul_of_nonneg_right hsquare hinv_nonneg

theorem arctanIntegralRectangleCompute_width_le_four_div_succ
    {x : Rat} (hx0 : 0 <= x) (hx1 : x <= 1) (n : Nat) :
    (arctanIntegralRectangleCompute x n).width <=
      (4 : Rat) / (((n + 1 : Nat) : Rat)) := by
  have hmesh :
      (arctanIntegralRectangleCompute x n).width <=
        2 * (1 / (((2 ^ n : Nat) : Rat))) := by
    unfold arctanIntegralRectangleCompute
    calc
      (integralSumInterval (arctanAreaLoopState x n).intervals).width
          <= 2 * intervalSquareSum
              (arctanAreaLoopState x n).intervals :=
            integralSumInterval_width_le_two_squareSum
              (arctanAreaLoopState x n).intervals
              (arctanAreaLoopState_intervals_unit hx0 hx1 n)
      _ = 2 * ((x * x) / (((2 ^ n : Nat) : Rat))) := by
            rw [arctanAreaLoopState_squareSum x n]
      _ <= 2 * (1 / (((2 ^ n : Nat) : Rat))) := by
            exact Rat.mul_le_mul_of_nonneg_left
              (square_div_two_pow_le_one_div_two_pow hx0 hx1 n)
              (by decide +kernel : (0 : Rat) <= 2)
  calc
    (arctanIntegralRectangleCompute x n).width
        <= 2 * (1 / (((2 ^ n : Nat) : Rat))) := hmesh
    _ = 4 * (1 / (((2 ^ (n + 1) : Nat) : Rat))) :=
          two_mul_one_div_two_pow_eq_four_mul_one_div_two_pow_succ n
    _ <= 4 * (1 / (((n + 1 : Nat) : Rat))) := by
          have hone :
              1 / (((2 ^ (n + 1) : Nat) : Rat)) <=
                1 / (((n + 1 : Nat) : Rat)) :=
            FTC.one_div_nat_antitone (Nat.succ_pos n)
              (Nat.pow_pos (by omega : 0 < 2))
              (succ_le_two_pow_succ n)
          exact Rat.mul_le_mul_of_nonneg_left hone
            (by decide +kernel : (0 : Rat) <= 4)
    _ = 4 / (((n + 1 : Nat) : Rat)) := by
          exact four_mul_one_div_eq_div (n + 1)

private theorem arctanIntegralRectangleCompute_width_le_sixteenth_gap
    {x : Rat} (hx0 : 0 <= x) (hx1 : x <= 1) (n : Nat) :
    (arctanIntegralRectangleCompute x (64 * (n + 1))).width <=
      1 / (16 * (((n + 1 : Nat) : Rat))) := by
  have hbound := arctanIntegralRectangleCompute_width_le_four_div_succ
    hx0 hx1 (64 * (n + 1))
  let d : Rat := ((n + 1 : Nat) : Rat)
  let e : Rat := ((64 * (n + 1) + 1 : Nat) : Rat)
  have hdpos : 0 < d := by
    dsimp [d]
    exact (Rat.natCast_pos).2 (Nat.succ_pos n)
  have heq : e = 64 * d + 1 := by
    dsimp [e, d]
    rw [Rat.natCast_add, Rat.natCast_mul]
    change (64 : Rat) * ((n + 1 : Nat) : Rat) + 1 =
      64 * ((n + 1 : Nat) : Rat) + 1
    rfl
  have hepos : 0 < e := by
    rw [heq]
    have hnonneg : 0 <= 64 * d :=
      Rat.mul_nonneg (by decide +kernel) (Rat.le_of_lt hdpos)
    grind
  have hscaledpos : 0 < e * (16 * d) :=
    Rat.mul_pos hepos (Rat.mul_pos (by decide +kernel) hdpos)
  change (arctanIntegralRectangleCompute x (64 * (n + 1))).width <=
    4 / e at hbound
  calc
    (arctanIntegralRectangleCompute x (64 * (n + 1))).width <= 4 / e := hbound
    _ <= 1 / (16 * d) := by
      apply Rat.le_of_mul_le_mul_right (c := e * (16 * d))
      · calc
          (4 / e) * (e * (16 * d)) = 64 * d := by
            rw [Rat.div_def]
            have hcancel : e⁻¹ * e = 1 :=
              Rat.inv_mul_cancel e (Rat.ne_of_gt hepos)
            grind [Rat.mul_assoc, Rat.mul_comm]
          _ <= 64 * d + 1 := by grind
          _ = (1 / (16 * d)) * (e * (16 * d)) := by
            rw [Rat.div_def]
            have hcancel : (16 * d)⁻¹ * (16 * d) = 1 :=
              Rat.inv_mul_cancel _
                (Rat.ne_of_gt (Rat.mul_pos (by decide +kernel) hdpos))
            rw [← heq]
            grind [Rat.mul_assoc, Rat.mul_comm]
      · exact hscaledpos
    _ = 1 / (16 * (((n + 1 : Nat) : Rat))) := by rfl

private theorem arctanIntegralRectangleCompute_kernel_half_lower
    {x : Rat} (hx0 : 0 <= x) (hx1 : x <= 1) :
    (1 : Rat) / 2 <= integralKernel x := by
  let d : Rat := 1 + x * x
  have hdpos : 0 < d := by
    dsimp [d]
    exact RationalCircle.Stage.one_add_square_pos x
  have hdle : d <= 2 := by
    dsimp [d]
    have hsq := square_le_one_of_unit hx0 hx1
    grind
  unfold integralKernel
  exact one_div_le_one_div_of_pos_of_le hdpos hdle

/-- A finite effective-separation certificate for the rational arctangent
branch on `[0,1]`.  If two rational inputs differ by at least `1/(n+1)`,
the independently computed rectangle boxes are strictly disjoint at stage
`64 * (n+1)`.  This is search data for a branch-local inverse algorithm; it
does not assert an IVT or an inverse equality. -/
theorem arctanIntegralRectangleCompute_boxes_strictly_separated
    {x y : Rat} (hx0 : 0 <= x) (hx1 : x <= 1)
    (hy0 : 0 <= y) (hy1 : y <= 1) (n : Nat)
    (hsep : x + 1 / (((n + 1 : Nat) : Rat)) <= y) :
    (arctanIntegralRectangleCompute x (64 * (n + 1))).hi <
      (arctanIntegralRectangleCompute y (64 * (n + 1))).lo := by
  let d : Rat := ((n + 1 : Nat) : Rat)
  let delta : Rat := 1 / d
  have hdpos : 0 < d := by
    dsimp [d]
    exact (Rat.natCast_pos).2 (Nat.succ_pos n)
  have hdeltaPos : 0 < delta := by
    dsimp [delta]
    rw [Rat.div_def, Rat.one_mul]
    exact (Rat.inv_pos).2 hdpos
  have hsep' : x + delta <= y := by
    simpa [delta, d] using hsep
  have hxy : x <= y := by
    have hdeltaNonneg : 0 <= delta := Rat.le_of_lt hdeltaPos
    grind
  let left : List (Rat × Rat) :=
    (arctanAreaLoopState x (64 * (n + 1))).intervals
  let right : List (Rat × Rat) :=
    (arctanAreaLoopState y (64 * (n + 1))).intervals
  have hleft : CoversInterval 0 x left := by
    dsimp [left]
    exact arctanAreaLoopState_intervals_covers hx0 _
  have hright : CoversInterval 0 y right := by
    dsimp [right]
    exact arctanAreaLoopState_intervals_covers hy0 _
  have hcover : CoversInterval 0 y (left ++ [(x, y)]) :=
    CoversInterval.extend_right hleft hxy
  have hcompare :
      integralLowerSum (left ++ [(x, y)]) <= integralUpperSum right :=
    integralLowerSum_le_integralUpperSum_of_covers
      (a := 0) (b := y) (by decide +kernel) (left ++ [(x, y)]) right
      hcover hright
  rw [integralLowerSum_append] at hcompare
  have hcompareTail :
      integralLowerSum left + integralLowerStep x y <= integralUpperSum right := by
    simpa [integralLowerSum, Rat.add_zero] using hcompare
  have hcompare' :
      (arctanIntegralRectangleCompute x (64 * (n + 1))).lo +
          (y - x) * integralKernel y <=
        (arctanIntegralRectangleCompute y (64 * (n + 1))).hi := by
    change integralLowerSum left + (y - x) * integralKernel y <=
      integralUpperSum right
    exact hcompareTail
  have hstep : delta <= y - x := by
    grind [Rat.sub_eq_add_neg]
  have htail : delta / 2 <= (y - x) * integralKernel y := by
    have hkernel := arctanIntegralRectangleCompute_kernel_half_lower hy0 hy1
    calc
      delta / 2 = delta * ((1 : Rat) / 2) := by
        rw [Rat.div_def]
        grind [Rat.mul_assoc]
      _ <= (y - x) * ((1 : Rat) / 2) :=
        Rat.mul_le_mul_of_nonneg_right hstep (by decide +kernel)
      _ <= (y - x) * integralKernel y :=
        Rat.mul_le_mul_of_nonneg_left hkernel (by grind [Rat.sub_eq_add_neg])
  have hwidthX := arctanIntegralRectangleCompute_width_le_sixteenth_gap hx0 hx1 n
  have hwidthY := arctanIntegralRectangleCompute_width_le_sixteenth_gap hy0 hy1 n
  have hsixteenth : 1 / (16 * d) = delta / 16 := by
    dsimp [delta]
    rw [Rat.div_def, Rat.inv_mul_rev]
    grind [Rat.mul_assoc, Rat.mul_comm]
  have hwidthX' :
      (arctanIntegralRectangleCompute x (64 * (n + 1))).width <= delta / 16 := by
    rw [← hsixteenth]
    simpa [d] using hwidthX
  have hwidthY' :
      (arctanIntegralRectangleCompute y (64 * (n + 1))).width <= delta / 16 := by
    rw [← hsixteenth]
    simpa [d] using hwidthY
  have herrors :
      (arctanIntegralRectangleCompute x (64 * (n + 1))).width +
          (arctanIntegralRectangleCompute y (64 * (n + 1))).width <= delta / 8 := by
    calc
      _ <= delta / 16 + delta / 16 := rat_add_le_add hwidthX' hwidthY'
      _ = delta / 8 := by
        rw [Rat.div_def]
        grind [Rat.mul_assoc, Rat.mul_comm]
  have hmargin :
      (arctanIntegralRectangleCompute x (64 * (n + 1))).width +
          (arctanIntegralRectangleCompute y (64 * (n + 1))).width <
        (y - x) * integralKernel y := by
    have hsmall : delta / 8 < delta / 2 := by
      calc
        delta / 8 = delta * ((1 : Rat) / 8) := by
          rw [Rat.div_def]
          grind [Rat.mul_assoc]
        _ < delta * ((1 : Rat) / 2) := by
          exact Rat.mul_lt_mul_of_pos_left (by decide +kernel) hdeltaPos
        _ = delta / 2 := by
          rw [Rat.div_def]
          grind [Rat.mul_assoc]
    grind
  have hupperX :
      (arctanIntegralRectangleCompute x (64 * (n + 1))).hi <=
        (arctanIntegralRectangleCompute x (64 * (n + 1))).lo +
          (arctanIntegralRectangleCompute x (64 * (n + 1))).width := by
    unfold QInterval.width
    grind [Rat.sub_eq_add_neg]
  have hsum :
      (arctanIntegralRectangleCompute x (64 * (n + 1))).hi +
          (arctanIntegralRectangleCompute y (64 * (n + 1))).width <
        (arctanIntegralRectangleCompute y (64 * (n + 1))).hi := by
    have hfirst :
        (arctanIntegralRectangleCompute x (64 * (n + 1))).hi +
            (arctanIntegralRectangleCompute y (64 * (n + 1))).width <=
          (arctanIntegralRectangleCompute x (64 * (n + 1))).lo +
            (arctanIntegralRectangleCompute x (64 * (n + 1))).width +
            (arctanIntegralRectangleCompute y (64 * (n + 1))).width :=
      (Rat.add_le_add_right).2 hupperX
    have hsecond :
        (arctanIntegralRectangleCompute x (64 * (n + 1))).lo +
            (arctanIntegralRectangleCompute x (64 * (n + 1))).width +
            (arctanIntegralRectangleCompute y (64 * (n + 1))).width <
          (arctanIntegralRectangleCompute x (64 * (n + 1))).lo +
            (y - x) * integralKernel y := by
      grind [Rat.sub_eq_add_neg]
    grind [Rat.sub_eq_add_neg]
  unfold QInterval.width at hsum
  grind [Rat.sub_eq_add_neg]

/-- Any rational interval algorithm with an explicit `C / (n + 1)` width
bound is a shrinking raw-real representative.  Kept local because it is the
rational convergence bridge used by the two midpoint rectangle schedules. -/
private theorem widthsShrink_of_natOverSuccBound
    {compute : Nat -> QInterval} {C : Nat}
    (hbound : forall n,
      (compute n).width <= (C : Rat) / (((n + 1 : Nat) : Rat))) :
    RealCompute.WidthsShrinkToZero compute := by
  intro eps
  refine ⟨C * (eps.val.den + 1), ?_⟩
  intro n hn
  have hmain :
      (C : Rat) / (((n + 1 : Nat) : Rat)) <=
        1 / (((eps.val.den + 1 : Nat) : Rat)) := by
    let A : Rat := ((n + 1 : Nat) : Rat)
    let B : Rat := ((eps.val.den + 1 : Nat) : Rat)
    let K : Rat := (C : Rat)
    have hApos : 0 < A := by
      dsimp [A]
      exact (Rat.natCast_pos).2 (Nat.succ_pos n)
    have hBpos : 0 < B := by
      dsimp [B]
      exact (Rat.natCast_pos).2 (Nat.succ_pos eps.val.den)
    have hAne : A ≠ 0 := Rat.ne_of_gt hApos
    have hBne : B ≠ 0 := Rat.ne_of_gt hBpos
    have hABpos : 0 < A * B := Rat.mul_pos hApos hBpos
    have hscaledRat : K * B <= A := by
      dsimp [A, B, K]
      exact_mod_cast (by omega :
        C * (eps.val.den + 1) <= n + 1)
    apply Rat.le_of_mul_le_mul_right (c := A * B)
    · calc
        (K / A) * (A * B) = K * B := by
          rw [Rat.div_def]
          grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
        _ <= A := hscaledRat
        _ = (1 / B) * (A * B) := by
          rw [Rat.div_def]
          grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
    · exact hABpos
  exact Rat.le_trans (hbound n)
    (Rat.le_trans hmain
      (FTC.one_div_den_succ_le_of_pos eps.property))

private theorem twoFiveSix_mul_one_div_eq_div (N : Nat) :
    256 * (1 / (N : Rat)) = 256 / (N : Rat) := by
  rw [Rat.div_def]
  grind [Rat.mul_assoc]

/-- The transported schedule has an explicit `256 / (n+1)` width bound.
The constant is intentionally coarse: it exposes exactly the factor-eight
chart distortion, squared into the mesh, and the two rectangle endpoints. -/
theorem chartAddAreaLoopCompute_width_le_twoFiveSix_div_succ
    {u x : Rat} (hu0 : 0 <= u) (huHalf : u <= (1 : Rat) / 2)
    (hx0 : 0 <= x) (hx1 : x <= 1)
    (himage : RationalCircle.Trigonometry.chartAddParameter u x <= 1)
    (n : Nat) :
    (chartAddAreaLoopCompute u x n).width <=
      (256 : Rat) / (((n + 1 : Nat) : Rat)) := by
  have hmesh :
      (chartAddAreaLoopCompute u x n).width <=
        128 * ((x * x) / (((2 ^ n : Nat) : Rat))) := by
    exact chartAddAreaLoop_integralSum_width_le hu0 huHalf hx0 hx1 himage n
  calc
    (chartAddAreaLoopCompute u x n).width
        <= 128 * ((x * x) / (((2 ^ n : Nat) : Rat))) := hmesh
    _ <= 128 * (1 / (((2 ^ n : Nat) : Rat))) := by
      exact Rat.mul_le_mul_of_nonneg_left
        (square_div_two_pow_le_one_div_two_pow hx0 hx1 n)
        (by decide +kernel : (0 : Rat) <= 128)
    _ = 64 * (2 * (1 / (((2 ^ n : Nat) : Rat)))) := by
      grind [Rat.mul_assoc, Rat.mul_comm]
    _ = 64 * (4 * (1 / (((2 ^ (n + 1) : Nat) : Rat)))) := by
      rw [two_mul_one_div_two_pow_eq_four_mul_one_div_two_pow_succ n]
    _ = 256 * (1 / (((2 ^ (n + 1) : Nat) : Rat))) := by
      grind [Rat.mul_assoc, Rat.mul_comm]
    _ <= 256 * (1 / (((n + 1 : Nat) : Rat))) := by
      have hone :
          1 / (((2 ^ (n + 1) : Nat) : Rat)) <=
            1 / (((n + 1 : Nat) : Rat)) :=
        FTC.one_div_nat_antitone (Nat.succ_pos n)
          (Nat.pow_pos (by omega : 0 < 2))
          (succ_le_two_pow_succ n)
      exact Rat.mul_le_mul_of_nonneg_left hone
        (by decide +kernel : (0 : Rat) <= 256)
    _ = 256 / (((n + 1 : Nat) : Rat)) := by
      exact twoFiveSix_mul_one_div_eq_div (n + 1)

/-- The explicit transported width schedule under the local pole-margin
condition.  It has the same `256/(n+1)` rate as the first-half chart. -/
theorem chartAddAreaLoopCompute_width_le_twoFiveSix_div_succ_of_rightProduct_le_half
    {u x : Rat} (hu0 : 0 <= u) (hu1 : u < 1) (huOne : u <= 1)
    (hx0 : 0 <= x) (hx1 : x <= 1)
    (hux : u * x <= (1 : Rat) / 2)
    (himage : RationalCircle.Trigonometry.chartAddParameter u x <= 1)
    (n : Nat) :
    (chartAddAreaLoopCompute u x n).width <=
      (256 : Rat) / (((n + 1 : Nat) : Rat)) := by
  have hmesh :
      (chartAddAreaLoopCompute u x n).width <=
        128 * ((x * x) / (((2 ^ n : Nat) : Rat))) := by
    exact chartAddAreaLoop_integralSum_width_le_of_rightProduct_le_half
      hu0 hu1 huOne hx0 hx1 hux himage n
  calc
    (chartAddAreaLoopCompute u x n).width
        <= 128 * ((x * x) / (((2 ^ n : Nat) : Rat))) := hmesh
    _ <= 128 * (1 / (((2 ^ n : Nat) : Rat))) := by
      exact Rat.mul_le_mul_of_nonneg_left
        (square_div_two_pow_le_one_div_two_pow hx0 hx1 n)
        (by decide +kernel : (0 : Rat) <= 128)
    _ = 64 * (2 * (1 / (((2 ^ n : Nat) : Rat)))) := by
      grind [Rat.mul_assoc, Rat.mul_comm]
    _ = 64 * (4 * (1 / (((2 ^ (n + 1) : Nat) : Rat)))) := by
      rw [two_mul_one_div_two_pow_eq_four_mul_one_div_two_pow_succ n]
    _ = 256 * (1 / (((2 ^ (n + 1) : Nat) : Rat))) := by
      grind [Rat.mul_assoc, Rat.mul_comm]
    _ <= 256 * (1 / (((n + 1 : Nat) : Rat))) := by
      have hone :
          1 / (((2 ^ (n + 1) : Nat) : Rat)) <=
            1 / (((n + 1 : Nat) : Rat)) :=
        FTC.one_div_nat_antitone (Nat.succ_pos n)
          (Nat.pow_pos (by omega : 0 < 2))
          (succ_le_two_pow_succ n)
      exact Rat.mul_le_mul_of_nonneg_left hone
        (by decide +kernel : (0 : Rat) <= 256)
    _ = 256 / (((n + 1 : Nat) : Rat)) := by
      exact twoFiveSix_mul_one_div_eq_div (n + 1)

theorem chartAddAreaLoopCompute_widthsShrink
    {u x : Rat} (hu0 : 0 <= u) (huHalf : u <= (1 : Rat) / 2)
    (hx0 : 0 <= x) (hx1 : x <= 1)
    (himage : RationalCircle.Trigonometry.chartAddParameter u x <= 1) :
    RealCompute.WidthsShrinkToZero (chartAddAreaLoopCompute u x) :=
  widthsShrink_of_natOverSuccBound
    (chartAddAreaLoopCompute_width_le_twoFiveSix_div_succ
      hu0 huHalf hx0 hx1 himage)

/-- The explicit transported-chart precision schedule.  The larger constant
comes only from the finite chart-distortion bound, and is suitable for
dividing a chart comparison by a small positive rational increment. -/
theorem chartAddAreaLoopCompute_width_le_eps_of_precision
    {u x : Rat} (hu0 : 0 <= u) (huHalf : u <= (1 : Rat) / 2)
    (hx0 : 0 <= x) (hx1 : x <= 1)
    (himage : RationalCircle.Trigonometry.chartAddParameter u x <= 1)
    (eps : QPos) (n : Nat) (hn : 256 * (eps.val.den + 1) <= n) :
    (chartAddAreaLoopCompute u x n).width <= eps.val := by
  have hmain :
      (256 : Rat) / (((n + 1 : Nat) : Rat)) <=
        1 / (((eps.val.den + 1 : Nat) : Rat)) := by
    let A : Rat := ((n + 1 : Nat) : Rat)
    let B : Rat := ((eps.val.den + 1 : Nat) : Rat)
    let K : Rat := (256 : Rat)
    have hApos : 0 < A := by
      dsimp [A]
      exact (Rat.natCast_pos).2 (Nat.succ_pos n)
    have hBpos : 0 < B := by
      dsimp [B]
      exact (Rat.natCast_pos).2 (Nat.succ_pos eps.val.den)
    have hABpos : 0 < A * B := Rat.mul_pos hApos hBpos
    have hscaledRat : K * B <= A := by
      dsimp [A, B, K]
      exact_mod_cast (by omega :
        256 * (eps.val.den + 1) <= n + 1)
    apply Rat.le_of_mul_le_mul_right (c := A * B)
    · calc
        (K / A) * (A * B) = K * B := by
          rw [Rat.div_def]
          grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
        _ <= A := hscaledRat
        _ = (1 / B) * (A * B) := by
          rw [Rat.div_def]
          grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
    · exact hABpos
  exact Rat.le_trans
    (chartAddAreaLoopCompute_width_le_twoFiveSix_div_succ
      hu0 huHalf hx0 hx1 himage n)
    (Rat.le_trans hmain
      (FTC.one_div_den_succ_le_of_pos eps.property))

/-- The precision-indexed form of the local pole-margin width schedule. -/
theorem chartAddAreaLoopCompute_width_le_eps_of_rightProduct_le_half
    {u x : Rat} (hu0 : 0 <= u) (hu1 : u < 1) (huOne : u <= 1)
    (hx0 : 0 <= x) (hx1 : x <= 1)
    (hux : u * x <= (1 : Rat) / 2)
    (himage : RationalCircle.Trigonometry.chartAddParameter u x <= 1)
    (eps : QPos) (n : Nat) (hn : 256 * (eps.val.den + 1) <= n) :
    (chartAddAreaLoopCompute u x n).width <= eps.val := by
  have hmain :
      (256 : Rat) / (((n + 1 : Nat) : Rat)) <=
        1 / (((eps.val.den + 1 : Nat) : Rat)) := by
    let A : Rat := ((n + 1 : Nat) : Rat)
    let B : Rat := ((eps.val.den + 1 : Nat) : Rat)
    let K : Rat := (256 : Rat)
    have hApos : 0 < A := by
      dsimp [A]
      exact (Rat.natCast_pos).2 (Nat.succ_pos n)
    have hBpos : 0 < B := by
      dsimp [B]
      exact (Rat.natCast_pos).2 (Nat.succ_pos eps.val.den)
    have hABpos : 0 < A * B := Rat.mul_pos hApos hBpos
    have hscaledRat : K * B <= A := by
      dsimp [A, B, K]
      exact_mod_cast (by omega :
        256 * (eps.val.den + 1) <= n + 1)
    apply Rat.le_of_mul_le_mul_right (c := A * B)
    · calc
        (K / A) * (A * B) = K * B := by
          rw [Rat.div_def]
          grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
        _ <= A := hscaledRat
        _ = (1 / B) * (A * B) := by
          rw [Rat.div_def]
          grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
    · exact hABpos
  exact Rat.le_trans
    (chartAddAreaLoopCompute_width_le_twoFiveSix_div_succ_of_rightProduct_le_half
      hu0 hu1 huOne hx0 hx1 hux himage n)
    (Rat.le_trans hmain
      (FTC.one_div_den_succ_le_of_pos eps.property))

/-- The explicit rectangle precision schedule: any stage at least
`4 * (eps.den + 1)` has box width at most the requested positive rational
tolerance. -/
theorem arctanIntegralRectangleCompute_width_le_eps_of_precision
    {x : Rat} (hx0 : 0 <= x) (hx1 : x <= 1)
    (eps : QPos) (n : Nat) (hn : 4 * (eps.val.den + 1) <= n) :
    (arctanIntegralRectangleCompute x n).width <= eps.val := by
  have hmain :
      (4 : Rat) / (((n + 1 : Nat) : Rat)) <=
        1 / (((eps.val.den + 1 : Nat) : Rat)) := by
    let A : Rat := ((n + 1 : Nat) : Rat)
    let B : Rat := ((eps.val.den + 1 : Nat) : Rat)
    let K : Rat := (4 : Rat)
    have hApos : 0 < A := by
      dsimp [A]
      exact (Rat.natCast_pos).2 (Nat.succ_pos n)
    have hBpos : 0 < B := by
      dsimp [B]
      exact (Rat.natCast_pos).2 (Nat.succ_pos eps.val.den)
    have hAne : A ≠ 0 := Rat.ne_of_gt hApos
    have hBne : B ≠ 0 := Rat.ne_of_gt hBpos
    have hABpos : 0 < A * B := Rat.mul_pos hApos hBpos
    have hscaledRat : K * B <= A := by
      dsimp [A, B, K]
      exact_mod_cast (by omega :
        4 * (eps.val.den + 1) <= n + 1)
    apply Rat.le_of_mul_le_mul_right (c := A * B)
    · calc
        (K / A) * (A * B) = K * B := by
          rw [Rat.div_def]
          grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
        _ <= A := hscaledRat
        _ = (1 / B) * (A * B) := by
          rw [Rat.div_def]
          grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
    · exact hABpos
  exact Rat.le_trans
    (arctanIntegralRectangleCompute_width_le_four_div_succ hx0 hx1 n)
    (Rat.le_trans hmain
      (FTC.one_div_den_succ_le_of_pos eps.property))

theorem arctanIntegralRectangleCompute_widthsShrink
    {x : Rat} (hx0 : 0 <= x) (hx1 : x <= 1) :
    RealCompute.WidthsShrinkToZero (arctanIntegralRectangleCompute x) := by
  intro eps
  refine ⟨4 * (eps.val.den + 1), ?_⟩
  intro n hn
  exact arctanIntegralRectangleCompute_width_le_eps_of_precision
    hx0 hx1 eps n hn

private theorem width_le_of_contains
    {outer inner : QInterval} (h : outer.ContainsInterval inner) :
    inner.width <= outer.width := by
  unfold QInterval.ContainsInterval at h
  unfold QInterval.width
  grind [Rat.sub_eq_add_neg]

theorem positiveLoopComputeAtStage_width_le_rectangle
    {x : Rat} (hx : 0 <= x) (n : Nat) :
    (positiveLoopComputeAtStage x n).width <=
      (arctanIntegralRectangleCompute x n).width := by
  unfold arctanIntegralRectangleCompute
  exact width_le_of_contains
    (arctanAreaLoop_integralSum_contains_positiveLoop hx n)

theorem positiveLoopComputeAtStage_width_le_four_div_succ
    {x : Rat} (hx0 : 0 <= x) (hx1 : x <= 1) (n : Nat) :
    (positiveLoopComputeAtStage x n).width <=
      (4 : Rat) / (((n + 1 : Nat) : Rat)) :=
  Rat.le_trans (positiveLoopComputeAtStage_width_le_rectangle hx0 n)
    (arctanIntegralRectangleCompute_width_le_four_div_succ hx0 hx1 n)

theorem positiveLoopComputeAtStage_widthsShrink
    {x : Rat} (hx0 : 0 <= x) (hx1 : x <= 1) :
    RealCompute.WidthsShrinkToZero (positiveLoopComputeAtStage x) := by
  intro eps
  obtain ⟨N, hN⟩ :=
    arctanIntegralRectangleCompute_widthsShrink hx0 hx1 eps
  refine ⟨N, ?_⟩
  intro n hn
  exact Rat.le_trans
    (positiveLoopComputeAtStage_width_le_rectangle hx0 n)
    (hN n hn)

theorem arctanIntegralRectangleRaw_valid
    {x : Rat} (hx0 : 0 <= x) (hx1 : x <= 1) :
    (arctanIntegralRectangleRaw x).Valid := by
  change RealCompute.ValidCompute (arctanIntegralRectangleCompute x)
  constructor
  · exact arctanIntegralRectangleCompute_ordered hx0
  · constructor
    · exact arctanIntegralRectangleCompute_nested hx0
    · exact arctanIntegralRectangleCompute_widthsShrink hx0 hx1

/-- The transported midpoint rectangle schedule is a valid raw real whenever
the source and its chart image both remain in the unit interval. -/
theorem chartAddAreaLoopRaw_valid
    {u x : Rat} (hu0 : 0 <= u) (huHalf : u <= (1 : Rat) / 2)
    (hx0 : 0 <= x) (hx1 : x <= 1)
    (himage : RationalCircle.Trigonometry.chartAddParameter u x <= 1) :
    (chartAddAreaLoopRaw u x).Valid := by
  have hu1 : u < 1 := by
    have hhalf : (1 : Rat) / 2 < 1 := by decide +kernel
    grind
  change RealCompute.ValidCompute (chartAddAreaLoopCompute u x)
  constructor
  · exact chartAddAreaLoopCompute_ordered hu0 hu1 hx0 hx1
  · constructor
    · exact chartAddAreaLoopCompute_nested hu0 hu1 hx0 hx1
    · exact chartAddAreaLoopCompute_widthsShrink hu0 huHalf hx0 hx1 himage

/-- The transported midpoint rectangle schedule is also valid under the
local pole-margin condition used by the full unit-branch tangent chart.  The
finite cover and nesting arguments require only a basepoint below the pole;
the product margin supplies the explicit shrinking-width schedule. -/
theorem chartAddAreaLoopRaw_valid_of_rightProduct_le_half
    {u x : Rat} (hu0 : 0 <= u) (hu1 : u < 1) (huUnit : u <= 1)
    (hx0 : 0 <= x) (hx1 : x <= 1)
    (hux : u * x <= (1 : Rat) / 2)
    (himage : RationalCircle.Trigonometry.chartAddParameter u x <= 1) :
    (chartAddAreaLoopRaw u x).Valid := by
  change RealCompute.ValidCompute (chartAddAreaLoopCompute u x)
  constructor
  · exact chartAddAreaLoopCompute_ordered hu0 hu1 hx0 hx1
  · constructor
    · exact chartAddAreaLoopCompute_nested hu0 hu1 hx0 hx1
    · intro eps
      refine ⟨256 * (eps.val.den + 1), ?_⟩
      intro n hn
      exact chartAddAreaLoopCompute_width_le_eps_of_rightProduct_le_half
        hu0 hu1 huUnit hx0 hx1 hux himage eps n hn

/-- At every common stage the source midpoint rectangle bracket is enclosed
by its transported bracket.  Consequently the two valid raw constructions
are equivalent; this is the construction-level substitution half of the
arctangent addition argument. -/
theorem arctanIntegralRectangleRaw_equiv_chartAddAreaLoopRaw
    {u x : Rat} (hu0 : 0 <= u) (hu1 : u < 1)
    (hx0 : 0 <= x) (hx1 : x <= 1) :
    (arctanIntegralRectangleRaw x).Equiv (chartAddAreaLoopRaw u x) := by
  apply RealCompute.sameStageOverlap_equiv
  intro n
  apply (RealCompute.compareAt_overlap_iff
    (arctanIntegralRectangleRaw x) (chartAddAreaLoopRaw u x) n n).2
  change QInterval.Overlaps (arctanIntegralRectangleCompute x n)
    (integralSumInterval
      (chartAddIntervals u (arctanAreaLoopState x n).intervals))
  have hcontains := chartAddAreaLoop_integralSum_contains
    hu0 hu1 hx0 hx1 n
  have hordered := arctanIntegralRectangleCompute_ordered hx0 n
  unfold QInterval.ContainsInterval at hcontains
  unfold QInterval.width at hordered
  unfold QInterval.Overlaps
  constructor <;> grind [Rat.sub_eq_add_neg]

/-- The transported bracket for `[u,T_u(x)]` overlaps the difference of the
canonical midpoint brackets for `[0,T_u(x)]` and `[0,u]`.

This is a purely finite statement: append the `[0,u]` source partition to the
charted target partition, and compare the resulting two covers of
`[0,T_u(x)]`. -/
theorem chartAddAreaLoopCompute_overlaps_rectangleSub
    {u x : Rat} (hu0 : 0 <= u) (huHalf : u <= (1 : Rat) / 2)
    (hx0 : 0 <= x) (hx1 : x <= 1)
    (n : Nat) :
    QInterval.Overlaps (chartAddAreaLoopCompute u x n)
      (QInterval.subInterval
        (arctanIntegralRectangleCompute
          (RationalCircle.Trigonometry.chartAddParameter u x) n)
        (arctanIntegralRectangleCompute u n)) := by
  have hu1 : u < 1 := by
    have hhalf : (1 : Rat) / 2 < 1 := by decide +kernel
    grind
  have huUnit : u <= 1 := by
    exact Rat.le_trans huHalf (by decide +kernel : (1 : Rat) / 2 <= 1)
  let v : Rat := RationalCircle.Trigonometry.chartAddParameter u x
  let A : List (Rat × Rat) := (arctanAreaLoopState u n).intervals
  let B : List (Rat × Rat) := (arctanAreaLoopState v n).intervals
  let C : List (Rat × Rat) :=
    chartAddIntervals u (arctanAreaLoopState x n).intervals
  have hcoverC : CoversInterval u v C := by
    dsimp [v, C]
    simpa only [RationalCircle.Trigonometry.chartAddParameter_zero_right] using
      (chartAddAreaLoop_covers hu0 hu1 hx0 hx1 n)
  have huv : u <= v := CoversInterval.start_le_end hcoverC
  have hv0 : 0 <= v := Rat.le_trans hu0 huv
  have hcoverA : CoversInterval 0 u A := by
    dsimp [A]
    exact arctanAreaLoopState_intervals_covers hu0 n
  have hcoverB : CoversInterval 0 v B := by
    dsimp [B]
    exact arctanAreaLoopState_intervals_covers hv0 n
  have hcoverAppend : CoversInterval 0 v (A ++ C) :=
    CoversInterval.append hcoverA hcoverC
  have hlower :
      integralLowerSum (A ++ C) <= integralUpperSum B :=
    integralLowerSum_le_integralUpperSum_of_covers
      (a := 0) (b := v) (by decide +kernel) (A ++ C) B
      hcoverAppend hcoverB
  have hupper :
      integralLowerSum B <= integralUpperSum (A ++ C) :=
    integralLowerSum_le_integralUpperSum_of_covers
      (a := 0) (b := v) (by decide +kernel) B (A ++ C)
      hcoverB hcoverAppend
  rw [integralLowerSum_append] at hlower
  rw [integralUpperSum_append] at hupper
  change QInterval.Overlaps (integralSumInterval C)
    (QInterval.subInterval (integralSumInterval B) (integralSumInterval A))
  unfold QInterval.Overlaps QInterval.subInterval integralSumInterval
  constructor <;> grind [Rat.sub_eq_add_neg]

/-- The finite subtraction overlap itself only needs the chart base to stay
strictly below the pole.  The half-unit restriction belongs to the older
uniform-width theorem, not to this exact cover comparison. -/
theorem chartAddAreaLoopCompute_overlaps_rectangleSub_of_lt
    {u x : Rat} (hu0 : 0 <= u) (hu1 : u < 1)
    (hx0 : 0 <= x) (hx1 : x <= 1)
    (n : Nat) :
    QInterval.Overlaps (chartAddAreaLoopCompute u x n)
      (QInterval.subInterval
        (arctanIntegralRectangleCompute
          (RationalCircle.Trigonometry.chartAddParameter u x) n)
        (arctanIntegralRectangleCompute u n)) := by
  let v : Rat := RationalCircle.Trigonometry.chartAddParameter u x
  let A : List (Rat × Rat) := (arctanAreaLoopState u n).intervals
  let B : List (Rat × Rat) := (arctanAreaLoopState v n).intervals
  let C : List (Rat × Rat) :=
    chartAddIntervals u (arctanAreaLoopState x n).intervals
  have hcoverC : CoversInterval u v C := by
    dsimp [v, C]
    simpa only [RationalCircle.Trigonometry.chartAddParameter_zero_right] using
      (chartAddAreaLoop_covers hu0 hu1 hx0 hx1 n)
  have huv : u <= v := CoversInterval.start_le_end hcoverC
  have hv0 : 0 <= v := Rat.le_trans hu0 huv
  have hcoverA : CoversInterval 0 u A := by
    dsimp [A]
    exact arctanAreaLoopState_intervals_covers hu0 n
  have hcoverB : CoversInterval 0 v B := by
    dsimp [B]
    exact arctanAreaLoopState_intervals_covers hv0 n
  have hcoverAppend : CoversInterval 0 v (A ++ C) :=
    CoversInterval.append hcoverA hcoverC
  have hlower :
      integralLowerSum (A ++ C) <= integralUpperSum B :=
    integralLowerSum_le_integralUpperSum_of_covers
      (a := 0) (b := v) (by decide +kernel) (A ++ C) B
      hcoverAppend hcoverB
  have hupper :
      integralLowerSum B <= integralUpperSum (A ++ C) :=
    integralLowerSum_le_integralUpperSum_of_covers
      (a := 0) (b := v) (by decide +kernel) B (A ++ C)
      hcoverB hcoverAppend
  rw [integralLowerSum_append] at hlower
  rw [integralUpperSum_append] at hupper
  change QInterval.Overlaps (integralSumInterval C)
    (QInterval.subInterval (integralSumInterval B) (integralSumInterval A))
  unfold QInterval.Overlaps QInterval.subInterval integralSumInterval
  constructor <;> grind [Rat.sub_eq_add_neg]

/-- The exact finite subtraction comparison is a raw-real equivalence as
soon as the chart base stays below its pole.  Unlike the earlier half-unit
version, its validity can use the local product margin supplied by a concrete
application. -/
theorem chartAddAreaLoopRaw_equiv_rectangleSub_of_lt
    {u x : Rat} (hu0 : 0 <= u) (hu1 : u < 1)
    (hx0 : 0 <= x) (hx1 : x <= 1) :
    (chartAddAreaLoopRaw u x).Equiv
      (arctanIntegralRectangleRaw
        (RationalCircle.Trigonometry.chartAddParameter u x) -
        arctanIntegralRectangleRaw u) := by
  apply RealCompute.sameStageOverlap_equiv
  intro n
  apply (RealCompute.compareAt_overlap_iff
    (chartAddAreaLoopRaw u x)
    (arctanIntegralRectangleRaw
      (RationalCircle.Trigonometry.chartAddParameter u x) -
      arctanIntegralRectangleRaw u) n n).2
  exact chartAddAreaLoopCompute_overlaps_rectangleSub_of_lt
    hu0 hu1 hx0 hx1 n

/-- The finite overlap above is promoted to a raw equivalence between the
transported interval construction and the difference of canonical midpoint
rectangle constructions. -/
theorem chartAddAreaLoopRaw_equiv_rectangleSub
    {u x : Rat} (hu0 : 0 <= u) (huHalf : u <= (1 : Rat) / 2)
    (hx0 : 0 <= x) (hx1 : x <= 1) :
    (chartAddAreaLoopRaw u x).Equiv
      (arctanIntegralRectangleRaw
        (RationalCircle.Trigonometry.chartAddParameter u x) -
        arctanIntegralRectangleRaw u) := by
  apply RealCompute.sameStageOverlap_equiv
  intro n
  apply (RealCompute.compareAt_overlap_iff
    (chartAddAreaLoopRaw u x)
    (arctanIntegralRectangleRaw
      (RationalCircle.Trigonometry.chartAddParameter u x) -
      arctanIntegralRectangleRaw u) n n).2
  exact chartAddAreaLoopCompute_overlaps_rectangleSub hu0 huHalf hx0 hx1 n

theorem arctanIntegralRectangleComputeAtOne_width_le_four_div_succ
    (n : Nat) :
    (arctanIntegralRectangleComputeAtOne n).width <=
      (4 : Rat) / (((n + 1 : Nat) : Rat)) := by
  have hmesh :
      (arctanIntegralRectangleComputeAtOne n).width <=
        2 * (1 / (((2 ^ n : Nat) : Rat))) := by
    unfold arctanIntegralRectangleComputeAtOne
    calc
      (integralSumInterval (arctanAreaLoopState 1 n).intervals).width
          <= 2 * intervalSquareSum
              (arctanAreaLoopState 1 n).intervals :=
            integralSumInterval_width_le_two_squareSum
              (arctanAreaLoopState 1 n).intervals
              (arctanAreaLoopState_intervals_unit
                (x := 1) (by decide +kernel) (by decide +kernel) n)
      _ = 2 * (1 / (((2 ^ n : Nat) : Rat))) := by
            rw [arctanAreaLoopState_one_squareSum n]
  calc
    (arctanIntegralRectangleComputeAtOne n).width
        <= 2 * (1 / (((2 ^ n : Nat) : Rat))) := hmesh
    _ = 4 * (1 / (((2 ^ (n + 1) : Nat) : Rat))) :=
          two_mul_one_div_two_pow_eq_four_mul_one_div_two_pow_succ n
    _ <= 4 * (1 / (((n + 1 : Nat) : Rat))) := by
          have hone :
              1 / (((2 ^ (n + 1) : Nat) : Rat)) <=
                1 / (((n + 1 : Nat) : Rat)) :=
            FTC.one_div_nat_antitone (Nat.succ_pos n)
              (Nat.pow_pos (by omega : 0 < 2))
              (succ_le_two_pow_succ n)
          exact Rat.mul_le_mul_of_nonneg_left hone
            (by decide +kernel : (0 : Rat) <= 4)
    _ = 4 / (((n + 1 : Nat) : Rat)) := by
          exact four_mul_one_div_eq_div (n + 1)

theorem arctanIntegralRectangleComputeAtOne_widthsShrink :
    RealCompute.WidthsShrinkToZero arctanIntegralRectangleComputeAtOne := by
  intro eps
  refine ⟨4 * (eps.val.den + 1), ?_⟩
  intro n hn
  have hmain :
      (4 : Rat) / (((n + 1 : Nat) : Rat)) <=
        1 / (((eps.val.den + 1 : Nat) : Rat)) := by
    let A : Rat := ((n + 1 : Nat) : Rat)
    let B : Rat := ((eps.val.den + 1 : Nat) : Rat)
    let K : Rat := (4 : Rat)
    have hApos : 0 < A := by
      dsimp [A]
      exact (Rat.natCast_pos).2 (Nat.succ_pos n)
    have hBpos : 0 < B := by
      dsimp [B]
      exact (Rat.natCast_pos).2 (Nat.succ_pos eps.val.den)
    have hAne : A ≠ 0 := Rat.ne_of_gt hApos
    have hBne : B ≠ 0 := Rat.ne_of_gt hBpos
    have hABpos : 0 < A * B := Rat.mul_pos hApos hBpos
    have hscaledRat : K * B <= A := by
      dsimp [A, B, K]
      exact_mod_cast (by omega :
        4 * (eps.val.den + 1) <= n + 1)
    apply Rat.le_of_mul_le_mul_right (c := A * B)
    · calc
        (K / A) * (A * B) = K * B := by
          rw [Rat.div_def]
          grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
        _ <= A := hscaledRat
        _ = (1 / B) * (A * B) := by
          rw [Rat.div_def]
          grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
    · exact hABpos
  exact Rat.le_trans
    (arctanIntegralRectangleComputeAtOne_width_le_four_div_succ n)
    (Rat.le_trans hmain
      (FTC.one_div_den_succ_le_of_pos eps.property))

theorem arctanIntegralRectangleRawAtOne_valid :
    arctanIntegralRectangleRawAtOne.Valid := by
  change RealCompute.ValidCompute arctanIntegralRectangleComputeAtOne
  constructor
  · exact arctanIntegralRectangleComputeAtOne_ordered
  · constructor
    · exact arctanIntegralRectangleComputeAtOne_nested
    · exact arctanIntegralRectangleComputeAtOne_widthsShrink

def positiveLoopRaw (x : Rat) : RealCompute where
  compute := positiveLoopComputeAtStage x

theorem positiveLoopRaw_valid_on_unit
    {x : Rat} (hx0 : 0 <= x) (hx1 : x <= 1) :
    (positiveLoopRaw x).Valid := by
  change RealCompute.ValidCompute (positiveLoopComputeAtStage x)
  constructor
  · exact positiveLoopComputeAtStage_ordered hx0
  · constructor
    · exact positiveLoopComputeAtStage_nested hx0
    · exact positiveLoopComputeAtStage_widthsShrink hx0 hx1

/-- Geometric arctangent, presented as an explicit rational update algorithm.
This duplicates the exhaustion algorithm rather than factoring it through the
pi definition, so the later comparison theorem can relate two independent raw
objects. -/
def arctanGeom (x : Rat) : RealCompute :=
  if x = 0 then
    RealCompute.ofRat 0
  else if 0 <= x then
    positiveLoopRaw x
  else
    -positiveLoopRaw (-x)

theorem arctanGeom_valid_on_unit
    {x : Rat} (hx0 : 0 <= x) (hx1 : x <= 1) :
    (arctanGeom x).Valid := by
  by_cases hzero : x = 0
  · subst x
    change RealCompute.ValidCompute (RealCompute.ofRat (0 : Rat)).compute
    exact RealCompute.ofRat_valid (0 : Rat)
  · simpa [arctanGeom, positiveLoopRaw, hzero, hx0] using
      positiveLoopRaw_valid_on_unit hx0 hx1

theorem arctanGeom_valid_on_powerSeriesDomain
    {x : Rat} (hx : Elementary.Arctan.powerSeriesDomain x) :
    (arctanGeom x).Valid := by
  by_cases hx0 : 0 <= x
  · have hnotlt : ¬ x < 0 := by grind
    have hx1 : x <= 1 := by
      simpa [Elementary.Arctan.powerSeriesDomain, qabs, hnotlt] using hx
    exact arctanGeom_valid_on_unit hx0 hx1
  · have hxlt : x < 0 := by grind
    have hneg0 : 0 <= -x := by grind
    have hneg1 : -x <= 1 := by
      simpa [Elementary.Arctan.powerSeriesDomain, qabs, hxlt] using hx
    have hpos : (positiveLoopRaw (-x)).Valid :=
      positiveLoopRaw_valid_on_unit hneg0 hneg1
    have hzero : x ≠ 0 := by grind
    simpa [arctanGeom, hzero, hx0] using RealCompute.neg_valid hpos

theorem arctanAreaIncrement_eq_circleAreaIncrement (p m q : Rat) :
    arctanAreaIncrement p m q = circleAreaIncrement p m q := rfl

theorem arctanAreaDecrement_eq_circleAreaDecrement (p m q : Rat) :
    arctanAreaDecrement p m q = circleAreaDecrement p m q := rfl

theorem arctanGeom_nonneg_compute_eq
    {x : Rat} (hx0 : x ≠ 0) (hx : 0 <= x) (n : Nat) :
    (arctanGeom x).compute n = positiveLoopComputeAtStage x n := by
  simp [arctanGeom, positiveLoopRaw, hx0, hx]

theorem arctanGeom_one_compute_eq (n : Nat) :
    (arctanGeom 1).compute n = positiveLoopComputeAtStage 1 n := by
  have hnonzero : ¬(1 : Rat) = 0 := by decide +kernel
  have hnonneg : (0 : Rat) <= 1 := by decide +kernel
  exact arctanGeom_nonneg_compute_eq hnonzero hnonneg n

private def ZeroIntervals : List (Rat × Rat) -> Prop
  | [] => True
  | (p, r) :: rest => p = 0 ∧ r = 0 ∧ ZeroIntervals rest

private theorem refineAux_zero
    {lo hi : Rat} {intervals : List (Rat × Rat)}
    (hlo : lo = 0) (hhi : hi = 0) (hz : ZeroIntervals intervals) :
    (AreaLoopState.refineAux lo hi intervals).lo = 0 ∧
      (AreaLoopState.refineAux lo hi intervals).hi = 0 ∧
      ZeroIntervals (AreaLoopState.refineAux lo hi intervals).intervals := by
  induction intervals generalizing lo hi with
  | nil =>
      simp [AreaLoopState.refineAux, ZeroIntervals, hlo, hhi]
  | cons interval rest ih =>
      rcases interval with ⟨p, r⟩
      rcases hz with ⟨hp, hr, hrest⟩
      subst p
      subst r
      subst lo
      subst hi
      have hnext := ih (lo := 0 + arctanAreaIncrement 0 ((0 + 0) / 2) 0)
        (hi := 0 - arctanAreaDecrement 0 ((0 + 0) / 2) 0)
        (by decide +kernel)
        (by decide +kernel)
        hrest
      simp [AreaLoopState.refineAux, ZeroIntervals, hnext]
      decide +kernel

private theorem arctanAreaLoopState_zero (n : Nat) :
    (arctanAreaLoopState 0 n).lo = 0 ∧
      (arctanAreaLoopState 0 n).hi = 0 ∧
      ZeroIntervals (arctanAreaLoopState 0 n).intervals := by
  induction n with
  | zero =>
      simp [arctanAreaLoopState, iterateAreaLoopState, arctanAreaLoopInitial,
        ZeroIntervals]
      decide +kernel
  | succ n ih =>
      rw [arctanAreaLoopState_succ]
      exact refineAux_zero ih.1 ih.2.1 ih.2.2

theorem positiveLoopComputeAtStage_zero (n : Nat) :
    positiveLoopComputeAtStage 0 n = { lo := 0, hi := 0 } := by
  have h := arctanAreaLoopState_zero n
  simp [positiveLoopComputeAtStage, h.1, h.2.1]

theorem arctanIntegralRectangleRaw_equiv_arctanGeom
    {x : Rat} (hx : 0 <= x) :
    (arctanIntegralRectangleRaw x).Equiv (arctanGeom x) := by
  intro n
  apply (RealCompute.compareAt_overlap_iff
    (arctanIntegralRectangleRaw x) (arctanGeom x) n n).2
  by_cases hzero : x = 0
  · subst x
    have hover := arctanAreaLoop_integralSum_overlaps_positiveLoop
      (x := 0) (by decide +kernel) n
    rw [positiveLoopComputeAtStage_zero n] at hover
    simpa [arctanIntegralRectangleRaw, arctanIntegralRectangleCompute,
      arctanGeom, RealCompute.ofRat] using hover
  · change QInterval.Overlaps
      (integralSumInterval (arctanAreaLoopState x n).intervals)
      ((arctanGeom x).compute n)
    rw [arctanGeom_nonneg_compute_eq hzero hx n]
    exact arctanAreaLoop_integralSum_overlaps_positiveLoop hx n

/-- Bounded rational tangent addition for the geometric arctangent.

The proof is wholly at the raw-interval level.  It transports the midpoint
rectangle construction across the chart, identifies the transported bracket
with the difference of the two canonical endpoint brackets by finite covers,
and then uses the already verified rectangle--geometric comparisons. -/
theorem arctanGeom_chartAdd_add_of_half
    {u x : Rat} (hu0 : 0 <= u) (huHalf : u <= (1 : Rat) / 2)
    (hx0 : 0 <= x) (hx1 : x <= 1)
    (himage : RationalCircle.Trigonometry.chartAddParameter u x <= 1) :
    (arctanGeom u + arctanGeom x).Equiv
      (arctanGeom (RationalCircle.Trigonometry.chartAddParameter u x)) := by
  have hu1 : u < 1 := by
    have hhalf : (1 : Rat) / 2 < 1 := by decide +kernel
    grind
  have huUnit : u <= 1 :=
    Rat.le_trans huHalf (by decide +kernel : (1 : Rat) / 2 <= 1)
  let v : Rat := RationalCircle.Trigonometry.chartAddParameter u x
  have hcover : CoversInterval u v
      (chartAddIntervals u (arctanAreaLoopState x 0).intervals) := by
    dsimp [v]
    simpa only [RationalCircle.Trigonometry.chartAddParameter_zero_right] using
      (chartAddAreaLoop_covers hu0 hu1 hx0 hx1 0)
  have huv : u <= v := CoversInterval.start_le_end hcover
  have hv0 : 0 <= v := Rat.le_trans hu0 huv
  have hgeomU : (arctanGeom u).Valid :=
    arctanGeom_valid_on_unit hu0 huUnit
  have hgeomX : (arctanGeom x).Valid :=
    arctanGeom_valid_on_unit hx0 hx1
  have hgeomV : (arctanGeom v).Valid := by
    dsimp [v]
    exact arctanGeom_valid_on_unit hv0 himage
  have hrectU : (arctanIntegralRectangleRaw u).Valid :=
    arctanIntegralRectangleRaw_valid hu0 huUnit
  have hrectX : (arctanIntegralRectangleRaw x).Valid :=
    arctanIntegralRectangleRaw_valid hx0 hx1
  have hrectV : (arctanIntegralRectangleRaw v).Valid := by
    dsimp [v]
    exact arctanIntegralRectangleRaw_valid hv0 himage
  have hchart : (chartAddAreaLoopRaw u x).Valid :=
    chartAddAreaLoopRaw_valid hu0 huHalf hx0 hx1 himage
  have hrectSub :
      (arctanIntegralRectangleRaw v - arctanIntegralRectangleRaw u).Valid :=
    RealCompute.sub_valid hrectV hrectU
  have hgeomSub : (arctanGeom v - arctanGeom u).Valid :=
    RealCompute.sub_valid hgeomV hgeomU
  have hrectXChart :
      (arctanIntegralRectangleRaw x).Equiv (chartAddAreaLoopRaw u x) :=
    arctanIntegralRectangleRaw_equiv_chartAddAreaLoopRaw hu0 hu1 hx0 hx1
  have hchartRectSub :
      (chartAddAreaLoopRaw u x).Equiv
        (arctanIntegralRectangleRaw v - arctanIntegralRectangleRaw u) := by
    dsimp [v]
    exact chartAddAreaLoopRaw_equiv_rectangleSub hu0 huHalf hx0 hx1
  have hrectSubGeomSub :
      (arctanIntegralRectangleRaw v - arctanIntegralRectangleRaw u).Equiv
        (arctanGeom v - arctanGeom u) :=
    RealCompute.sub_equiv hrectV hgeomV hrectU hgeomU
      (arctanIntegralRectangleRaw_equiv_arctanGeom hv0)
      (arctanIntegralRectangleRaw_equiv_arctanGeom hu0)
  have hrectXSub :
      (arctanIntegralRectangleRaw x).Equiv
        (arctanIntegralRectangleRaw v - arctanIntegralRectangleRaw u) :=
    RealCompute.equiv_trans hrectX hchart hrectSub hrectXChart hchartRectSub
  have hgeomXRectSub :
      (arctanGeom x).Equiv
        (arctanIntegralRectangleRaw v - arctanIntegralRectangleRaw u) :=
    RealCompute.equiv_trans hgeomX hrectX hrectSub
      (RealCompute.equiv_symm (arctanIntegralRectangleRaw_equiv_arctanGeom hx0))
      hrectXSub
  have hgeomXSub :
      (arctanGeom x).Equiv (arctanGeom v - arctanGeom u) :=
    RealCompute.equiv_trans hgeomX hrectSub hgeomSub
      hgeomXRectSub hrectSubGeomSub
  have hleft : (arctanGeom u + arctanGeom x).Valid :=
    RealCompute.add_valid hgeomU hgeomX
  have hmiddle : (arctanGeom u + (arctanGeom v - arctanGeom u)).Valid :=
    RealCompute.add_valid hgeomU hgeomSub
  have hright : ((arctanGeom v - arctanGeom u) + arctanGeom u).Valid :=
    RealCompute.add_valid hgeomSub hgeomU
  have hreplace :
      (arctanGeom u + arctanGeom x).Equiv
        (arctanGeom u + (arctanGeom v - arctanGeom u)) :=
    RealCompute.add_equiv hgeomU hgeomU hgeomX hgeomSub
      (RealCompute.equiv_refl (arctanGeom u) hgeomU) hgeomXSub
  have hcomm :
      (arctanGeom u + (arctanGeom v - arctanGeom u)).Equiv
        ((arctanGeom v - arctanGeom u) + arctanGeom u) :=
    RealCompute.add_comm_equiv (arctanGeom u) (arctanGeom v - arctanGeom u)
      hgeomU hgeomSub
  exact RealCompute.equiv_trans hleft hmiddle hgeomV hreplace
    (RealCompute.equiv_trans hmiddle hright hgeomV hcomm
      (RealCompute.sub_add_cancel_equiv hgeomV hgeomU))

/-- The tangent-chart coordinate which turns an ordinary increment `h` at
`x` into a chart increment based at zero. -/
def tangentChartIncrement (x h : Rat) : Rat :=
  h / (1 + x * (x + h))

/- The following experimental half-chart transport was intentionally removed
from the active API.  It is not used by the unit-branch derivative proof;
the local pole-margin transport below is both shorter and fully checked.
/-- The inverse tangent-addition coordinate based at the half-unit slope.
It maps the right half of the unit branch back into the first half. -/
def halfChartCoordinate (x : Rat) : Rat :=
  (x - (1 : Rat) / 2) / (1 + x / 2)

theorem halfChartCoordinate_den_pos {x : Rat} (hx0 : 0 <= x) :
    0 < 1 + x / 2 := by
  have hxhalf : 0 <= x / 2 := by
    rw [Rat.div_def]
    exact Rat.mul_nonneg hx0 (Rat.le_of_lt ((Rat.inv_pos).2 (by decide +kernel)))
  grind

theorem halfChartCoordinate_nonneg {x : Rat}
    (hxHalf : (1 : Rat) / 2 <= x) :
    0 <= halfChartCoordinate x := by
  have hx0 : 0 <= x := by grind
  unfold halfChartCoordinate
  rw [Rat.div_def]
  exact Rat.mul_nonneg (by grind)
    (Rat.le_of_lt ((Rat.inv_pos).2 (halfChartCoordinate_den_pos hx0)))

theorem halfChartCoordinate_le_half {x : Rat}
    (hxHalf : (1 : Rat) / 2 <= x) (hx1 : x <= 1) :
    halfChartCoordinate x <= (1 : Rat) / 2 := by
  have hx0 : 0 <= x := by grind
  let d : Rat := 1 + x / 2
  have hdpos : 0 < d := by
    dsimp [d]
    exact halfChartCoordinate_den_pos hx0
  have hnum : x - (1 : Rat) / 2 <= ((1 : Rat) / 2) * d := by
    dsimp [d]
    grind [Rat.sub_eq_add_neg, Rat.mul_add]
  apply Rat.le_of_mul_le_mul_right (c := d)
  · calc
      halfChartCoordinate x * d = x - (1 : Rat) / 2 := by
        unfold halfChartCoordinate
        rw [Rat.div_def]
        have hcancel : d⁻¹ * d = 1 := Rat.inv_mul_cancel d (Rat.ne_of_gt hdpos)
        grind [Rat.mul_assoc, Rat.mul_comm]
      _ <= ((1 : Rat) / 2) * d := hnum
  · exact hdpos

theorem chartAddParameter_half_halfChartCoordinate {x : Rat}
    (hx0 : 0 <= x) :
    RationalCircle.Trigonometry.chartAddParameter ((1 : Rat) / 2)
      (halfChartCoordinate x) = x := by
  let d : Rat := 1 + x / 2
  have hdpos : 0 < d := by
    dsimp [d]
    exact halfChartCoordinate_den_pos hx0
  have hdne : d ≠ 0 := Rat.ne_of_gt hdpos
  have hdenEq :
      1 - ((1 : Rat) / 2) * ((x - (1 : Rat) / 2) / d) =
        ((5 : Rat) / 4) / d := by
    rw [Rat.div_def, Rat.div_def]
    have hcancel : d * d⁻¹ = 1 := Rat.mul_inv_cancel d hdne
    dsimp [d] at hcancel ⊢
    grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
      Rat.mul_assoc, Rat.mul_comm]
  have hnumEq :
      (1 : Rat) / 2 + (x - (1 : Rat) / 2) / d =
        (((5 : Rat) / 4) * x) / d := by
    rw [Rat.div_def, Rat.div_def]
    have hcancel : d * d⁻¹ = 1 := Rat.mul_inv_cancel d hdne
    dsimp [d] at hcancel ⊢
    grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
      Rat.mul_assoc, Rat.mul_comm]
  have hfivepos : 0 < (5 : Rat) / 4 := by decide +kernel
  have hfactorne : (5 : Rat) / 4 ≠ 0 := Rat.ne_of_gt hfivepos
  unfold RationalCircle.Trigonometry.chartAddParameter
    RationalCircle.Trigonometry.chartAddNum
    RationalCircle.Trigonometry.chartAddDen halfChartCoordinate
  change ((1 : Rat) / 2 + (x - (1 : Rat) / 2) / d) /
      (1 - ((1 : Rat) / 2) * ((x - (1 : Rat) / 2) / d)) = x
  rw [hnumEq, hdenEq]
  simp only [Rat.div_def]
  rw [Rat.inv_mul_rev]
  have hcancelD : d * d⁻¹ = 1 := Rat.mul_inv_cancel d hdne
  have hcancelF : ((5 : Rat) / 4) * ((5 : Rat) / 4)⁻¹ = 1 :=
    Rat.mul_inv_cancel _ hfactorne
  grind [Rat.mul_assoc, Rat.mul_comm]

/-- The right-half chart has an exact rational forward difference quotient.
This is the coordinate-scale factor needed to transport a derivative from the
first-half parameter back to the original unit-slope coordinate. -/
theorem halfChartCoordinate_differenceQuotient
    {x h : Rat} (hx0 : 0 <= x) (hpos : 0 < h) :
    (halfChartCoordinate (x + h) - halfChartCoordinate x) / h =
      ((5 : Rat) / 4) /
        ((1 + x / 2) * (1 + (x + h) / 2)) := by
  let d0 : Rat := 1 + x / 2
  let d1 : Rat := 1 + (x + h) / 2
  have hd0pos : 0 < d0 := by
    dsimp [d0]
    exact halfChartCoordinate_den_pos hx0
  have hxh0 : 0 <= x + h := by grind
  have hd1pos : 0 < d1 := by
    dsimp [d1]
    exact halfChartCoordinate_den_pos hxh0
  have hhne : h ≠ 0 := Rat.ne_of_gt hpos
  have hd0ne : d0 ≠ 0 := Rat.ne_of_gt hd0pos
  have hd1ne : d1 ≠ 0 := Rat.ne_of_gt hd1pos
  apply rat_eq_of_mul_eq_mul_pos (c := h * d0 * d1)
  · exact Rat.mul_pos (Rat.mul_pos hpos hd0pos) hd1pos
  · unfold halfChartCoordinate
    change (((x + h - (1 : Rat) / 2) / d1 -
        (x - (1 : Rat) / 2) / d0) / h) * (h * d0 * d1) =
        (((5 : Rat) / 4) / (d0 * d1)) * (h * d0 * d1)
    rw [Rat.div_def]
    have hcancelH : h⁻¹ * h = 1 := Rat.inv_mul_cancel h hhne
    have hcancelD0 : d0⁻¹ * d0 = 1 := Rat.inv_mul_cancel d0 hd0ne
    have hcancelD1 : d1⁻¹ * d1 = 1 := Rat.inv_mul_cancel d1 hd1ne
    dsimp [d0, d1] at hcancelD0 hcancelD1 ⊢
    field_simp
    ring

/-- Exact denominator transformation for the inverse half-unit tangent chart. -/
theorem one_add_square_halfChartCoordinate {x : Rat} (hx0 : 0 <= x) :
    1 + halfChartCoordinate x * halfChartCoordinate x =
      (((5 : Rat) / 4) * (1 + x * x)) /
        ((1 + x / 2) * (1 + x / 2)) := by
  let d : Rat := 1 + x / 2
  have hdpos : 0 < d := by
    dsimp [d]
    exact halfChartCoordinate_den_pos hx0
  have hdne : d ≠ 0 := Rat.ne_of_gt hdpos
  have hdsqpos : 0 < d * d := Rat.mul_pos hdpos hdpos
  apply rat_eq_of_mul_eq_mul_pos (c := d * d)
  · exact hdsqpos
  · unfold halfChartCoordinate
    change (1 + ((x - (1 : Rat) / 2) / d) *
        ((x - (1 : Rat) / 2) / d)) * (d * d) =
        ((((5 : Rat) / 4) * (1 + x * x)) / (d * d)) * (d * d)
    rw [Rat.div_def]
    have hcancelD : d⁻¹ * d = 1 := Rat.inv_mul_cancel d hdne
    have hcancelD' : d * d⁻¹ = 1 := Rat.mul_inv_cancel d hdne
    field_simp
    ring

/-- The inverse half-unit chart transports the arctangent kernel by its exact
rational coordinate derivative. -/
theorem halfChartCoordinate_scale_mul_integralKernel {x : Rat}
    (hx0 : 0 <= x) :
    (((5 : Rat) / 4) / ((1 + x / 2) * (1 + x / 2))) *
        integralKernel (halfChartCoordinate x) = integralKernel x := by
  let d : Rat := 1 + x / 2
  let a : Rat := (5 : Rat) / 4
  let k : Rat := 1 + x * x
  have hdpos : 0 < d := by
    dsimp [d]
    exact halfChartCoordinate_den_pos hx0
  have hapos : 0 < a := by
    dsimp [a]
    decide +kernel
  have hkpos : 0 < k := by
    dsimp [k]
    exact RationalCircle.Stage.one_add_square_pos x
  have hdne : d ≠ 0 := Rat.ne_of_gt hdpos
  have hane : a ≠ 0 := Rat.ne_of_gt hapos
  have hkne : k ≠ 0 := Rat.ne_of_gt hkpos
  have hden : 1 + halfChartCoordinate x * halfChartCoordinate x =
      (a * k) / (d * d) := by
    dsimp [a, k, d]
    exact one_add_square_halfChartCoordinate hx0
  unfold integralKernel
  rw [hden]
  dsimp [a, d, k] at hane hkne hdne ⊢
  rw [Rat.div_def, Rat.inv_mul_rev]
  have hcancelD : (1 + x / 2) * (1 + x / 2)⁻¹ = 1 :=
    Rat.mul_inv_cancel _ hdne
  have hcancelA : ((5 : Rat) / 4) * ((5 : Rat) / 4)⁻¹ = 1 :=
    Rat.mul_inv_cancel _ hane
  have hcancelK : (1 + x * x) * (1 + x * x)⁻¹ = 1 :=
    Rat.mul_inv_cancel _ hkne
  grind [Rat.mul_assoc, Rat.mul_comm]

/-- The finite right-half coordinate scale approaches its derivative scale
with a directly computable error no larger than the ordinary input step. -/
theorem halfChartCoordinate_scale_sub_differenceQuotient_le_step
    {x h : Rat} (hx0 : 0 <= x) (hpos : 0 < h) :
    0 <= ((5 : Rat) / 4) / ((1 + x / 2) * (1 + x / 2)) -
        (halfChartCoordinate (x + h) - halfChartCoordinate x) / h /\
      ((5 : Rat) / 4) / ((1 + x / 2) * (1 + x / 2)) -
        (halfChartCoordinate (x + h) - halfChartCoordinate x) / h <= h := by
  rw [halfChartCoordinate_differenceQuotient hx0 hpos]
  let d0 : Rat := 1 + x / 2
  let d1 : Rat := 1 + (x + h) / 2
  let a : Rat := (5 : Rat) / 4
  have hd0pos : 0 < d0 := by
    dsimp [d0]
    exact halfChartCoordinate_den_pos hx0
  have hxh0 : 0 <= x + h := by grind
  have hd1pos : 0 < d1 := by
    dsimp [d1]
    exact halfChartCoordinate_den_pos hxh0
  have hd0ne : d0 ≠ 0 := Rat.ne_of_gt hd0pos
  have hd1ne : d1 ≠ 0 := Rat.ne_of_gt hd1pos
  have hapos : 0 < a := by
    dsimp [a]
    decide +kernel
  have ha2 : a <= 2 := by
    dsimp [a]
    decide +kernel
  have hd0one : 1 <= d0 := by
    dsimp [d0]
    have hxhalf : 0 <= x / 2 := by
      rw [Rat.div_def]
      exact Rat.mul_nonneg hx0 (Rat.le_of_lt ((Rat.inv_pos).2 (by decide +kernel)))
    grind
  have hd1one : 1 <= d1 := by
    dsimp [d1]
    have hhalf : 0 <= (x + h) / 2 := by
      rw [Rat.div_def]
      exact Rat.mul_nonneg hxh0 (Rat.le_of_lt ((Rat.inv_pos).2 (by decide +kernel)))
    grind
  have hdprodpos : 0 < d0 * d1 := Rat.mul_pos hd0pos hd1pos
  have hdprodOne : 1 <= d0 * d1 := by
    calc
      1 = 1 * 1 := by grind
      _ <= d0 * 1 := Rat.mul_le_mul_of_nonneg_right hd0one (by decide +kernel)
      _ <= d0 * d1 := Rat.mul_le_mul_of_nonneg_left hd1one
        (Rat.le_trans (by decide +kernel) hd0one)
  have hdelta : d1 - d0 = h / 2 := by
    dsimp [d0, d1]
    grind [Rat.sub_eq_add_neg]
  have hformula : a / (d0 * d0) - a / (d0 * d1) =
      (a * (h / 2)) / (d0 * d1) := by
    rw [Rat.div_def, Rat.inv_mul_rev]
    have hcancelD0 : d0⁻¹ * d0 = 1 := Rat.inv_mul_cancel d0 hd0ne
    have hcancelD1 : d1⁻¹ * d1 = 1 := Rat.inv_mul_cancel d1 hd1ne
    field_simp
    ring
  change 0 <= a / (d0 * d0) - a / (d0 * d1) /\
    a / (d0 * d0) - a / (d0 * d1) <= h
  rw [hformula]
  have hnum0 : 0 <= a * (h / 2) := by
    rw [Rat.div_def]
    exact Rat.mul_nonneg (Rat.le_of_lt hapos)
      (Rat.mul_nonneg (Rat.le_of_lt hpos)
        (Rat.le_of_lt ((Rat.inv_pos).2 (by decide +kernel))))
  have hinv0 : 0 <= (d0 * d1)⁻¹ :=
    Rat.le_of_lt ((Rat.inv_pos).2 hdprodpos)
  have hnonneg : 0 <= (a * (h / 2)) / (d0 * d1) := by
    rw [Rat.div_def]
    exact Rat.mul_nonneg hnum0 hinv0
  have hinvLe : (d0 * d1)⁻¹ <= 1 := by
    apply Rat.le_of_mul_le_mul_right (c := d0 * d1)
    · calc
        (d0 * d1)⁻¹ * (d0 * d1) = 1 :=
          Rat.inv_mul_cancel _ (Rat.ne_of_gt hdprodpos)
        _ <= 1 * (d0 * d1) := by simpa using hdprodOne
    · exact hdprodpos
  have hhalfLe : h / 2 <= h := by
    rw [Rat.div_def]
    have htwoInv : (2 : Rat)⁻¹ <= 1 := by decide +kernel
    calc
      h * (2 : Rat)⁻¹ <= h * 1 :=
        Rat.mul_le_mul_of_nonneg_left htwoInv (Rat.le_of_lt hpos)
      _ = h := by grind
  have hupper : (a * (h / 2)) / (d0 * d1) <= h := by
    rw [Rat.div_def]
    have hhalf0 : 0 <= h / 2 := by
      rw [Rat.div_def]
      exact Rat.mul_nonneg (Rat.le_of_lt hpos)
        (Rat.le_of_lt ((Rat.inv_pos).2 (by decide +kernel)))
    calc
      (a * (h / 2)) * (d0 * d1)⁻¹ <= (2 * (h / 2)) * (d0 * d1)⁻¹ :=
        Rat.mul_le_mul_of_nonneg_right
          (Rat.mul_le_mul_of_nonneg_right ha2 hhalf0) hinv0
      _ = h * (d0 * d1)⁻¹ := by
        rw [Rat.div_def]
        have hcancel : (2 : Rat) * (2 : Rat)⁻¹ = 1 := by decide +kernel
        grind [Rat.mul_assoc, Rat.mul_comm]
      _ <= h * 1 := Rat.mul_le_mul_of_nonneg_left hinvLe (Rat.le_of_lt hpos)
      _ = h := by grind
  exact ⟨hnonneg, hupper⟩
-/

theorem tangentChartIncrement_den_pos
    {x h : Rat} (hx : 0 <= x) (hxh : 0 <= x + h) :
    0 < 1 + x * (x + h) := by
  have hprod : 0 <= x * (x + h) := Rat.mul_nonneg hx hxh
  grind

theorem tangentChartIncrement_pos
    {x h : Rat} (hx : 0 <= x) (hpos : 0 < h) :
    0 < tangentChartIncrement x h := by
  unfold tangentChartIncrement
  rw [Rat.div_def]
  apply Rat.mul_pos hpos
  apply (Rat.inv_pos).2
  exact tangentChartIncrement_den_pos hx (by grind)

theorem tangentChartIncrement_le_step
    {x h : Rat} (hx : 0 <= x) (hpos : 0 < h) :
    tangentChartIncrement x h <= h := by
  let d : Rat := 1 + x * (x + h)
  have hdpos : 0 < d := by
    dsimp [d]
    exact tangentChartIncrement_den_pos hx (by grind)
  have hd1 : 1 <= d := by
    dsimp [d]
    have hprod : 0 <= x * (x + h) := Rat.mul_nonneg hx (by grind)
    grind
  have hdinv : d⁻¹ <= 1 := by
    apply Rat.le_of_mul_le_mul_right (c := d)
    · calc
        d⁻¹ * d = d * d⁻¹ := by rw [Rat.mul_comm]
        _ = 1 := Rat.mul_inv_cancel _ (Rat.ne_of_gt hdpos)
        _ <= 1 * d := by simpa using hd1
    · exact hdpos
  unfold tangentChartIncrement
  rw [Rat.div_def]
  calc
    h * d⁻¹ <= h * 1 :=
      Rat.mul_le_mul_of_nonneg_left hdinv (Rat.le_of_lt hpos)
    _ = h := by grind

/-- On a positive step which remains in the unit branch, the tangent chart
increment stays a uniform distance from its pole even when the basepoint is
in the right half. -/
theorem tangentChartIncrement_base_mul_le_half
    {x h : Rat} (hx0 : 0 <= x) (hpos : 0 < h) (hupper : x + h <= 1) :
    x * tangentChartIncrement x h <= (1 : Rat) / 2 := by
  have hstep : tangentChartIncrement x h <= h :=
    tangentChartIncrement_le_step hx0 hpos
  have hlimit : h <= 1 - x := by
    grind [Rat.sub_eq_add_neg]
  have hquad : x * (1 - x) <= (1 : Rat) / 4 := by
    have hsquare := RationalCircle.Stage.ratSquare_nonneg
      (x - (1 : Rat) / 2)
    grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul]
  calc
    x * tangentChartIncrement x h <= x * h :=
      Rat.mul_le_mul_of_nonneg_left hstep hx0
    _ <= x * (1 - x) :=
      Rat.mul_le_mul_of_nonneg_left hlimit hx0
    _ <= (1 : Rat) / 4 := hquad
    _ <= (1 : Rat) / 2 := by decide +kernel

/-- A nonnegative chart increment no larger than a half unit remains on the
unit arctangent branch.  This is the domain gate for the local tangent-chart
derivative certificate. -/
theorem tangentChartIncrement_mem_unit_of_mem_half
    {x h : Rat} (hx : 0 <= x) (hh0 : 0 <= h) (hhhalf : h <= (1 : Rat) / 2) :
    0 <= tangentChartIncrement x h /\ tangentChartIncrement x h <= 1 := by
  by_cases hpos : 0 < h
  · constructor
    · exact Rat.le_of_lt (tangentChartIncrement_pos hx hpos)
    · calc
        tangentChartIncrement x h <= h := tangentChartIncrement_le_step hx hpos
        _ <= (1 : Rat) / 2 := hhhalf
        _ <= 1 := by decide +kernel
  · have hle : h <= 0 := by grind
    have hzero : h = 0 := Rat.le_antisymm hle hh0
    subst h
    unfold tangentChartIncrement
    rw [Rat.div_def, Rat.zero_mul]
    exact ⟨Rat.le_refl, by decide +kernel⟩

/-- The chart increment has exactly the scale factor required to compare an
ordinary difference quotient with the basepoint quotient. -/
theorem tangentChartIncrement_div_step
    {x h : Rat} (hpos : 0 < h) :
    tangentChartIncrement x h / h = 1 / (1 + x * (x + h)) := by
  have hne : h ≠ 0 := Rat.ne_of_gt hpos
  unfold tangentChartIncrement
  rw [Rat.div_def, Rat.div_def]
  have hcancel : h * h⁻¹ = 1 := Rat.mul_inv_cancel h hne
  grind [Rat.mul_assoc, Rat.mul_comm]

/-- The finite rectangle arctangent quotient at an arbitrary nonnegative
basepoint is controlled by the zero-based tangent chart.  The chart
increment is evaluated by the same rectangle construction, while the
ordinary quotient is scaled by its exact rational ratio to the input step.

This is the local finite enclosure needed for the eventual theorem that the
derivative of arctangent is one over one plus its square: the remaining
derivative proof must choose a stage whose rectangle width survives division
by h, and then compare the right endpoint scale with the derivative kernel. -/
theorem arctanIntegralRectangleCompute_tangentChart_quotient_contains
    {x h : Rat} (hx : 0 <= x) (hpos : 0 < h) (n : Nat) :
    ({ lo :=
        (1 / (1 + x * (x + h))) *
          (1 - tangentChartIncrement x h * tangentChartIncrement x h),
       hi := 1 / (1 + x * (x + h)) } : QInterval).ContainsInterval
      (QInterval.differenceQuotient
        (arctanIntegralRectangleCompute (tangentChartIncrement x h) n)
        (arctanIntegralRectangleCompute 0 n) h) := by
  let t := tangentChartIncrement x h
  let scale : Rat := 1 / (1 + x * (x + h))
  have hhne : h ≠ 0 := Rat.ne_of_gt hpos
  have hhinv : 0 <= 1 / h := by
    rw [Rat.div_def]
    simpa using Rat.le_of_lt ((Rat.inv_pos).2 hpos)
  have htpos : 0 < t := by
    dsimp [t]
    exact tangentChartIncrement_pos hx hpos
  have ht0 : 0 <= t := Rat.le_of_lt htpos
  have hbox := arctanIntegralRectangleCompute_tangent_box_contains ht0 n
  have hscale : t / h = scale := by
    dsimp [t, scale]
    exact tangentChartIncrement_div_step hpos
  have hleft :
      scale * (1 - t * t) <=
        (1 / h) * (arctanIntegralRectangleCompute t n).lo := by
    apply Rat.le_of_mul_le_mul_right (c := h)
    · calc
        (scale * (1 - t * t)) * h =
            ((t / h) * (1 - t * t)) * h := by rw [hscale]
        _ = t - t * t * t := by
          rw [Rat.div_def]
          have hcancel : h⁻¹ * h = 1 := Rat.inv_mul_cancel h hhne
          grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
            Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
        _ <= (arctanIntegralRectangleCompute t n).lo := hbox.1
        _ = ((1 / h) * (arctanIntegralRectangleCompute t n).lo) * h := by
          rw [Rat.div_def]
          have hcancel : h * h⁻¹ = 1 := Rat.mul_inv_cancel h hhne
          grind [Rat.mul_assoc, Rat.mul_comm]
    · exact hpos
  have hright :
      (1 / h) * (arctanIntegralRectangleCompute t n).hi <= scale := by
    apply Rat.le_of_mul_le_mul_right (c := h)
    · calc
        ((1 / h) * (arctanIntegralRectangleCompute t n).hi) * h =
            (arctanIntegralRectangleCompute t n).hi := by
              rw [Rat.div_def]
              have hcancel : h * h⁻¹ = 1 := Rat.mul_inv_cancel h hhne
              grind [Rat.mul_assoc, Rat.mul_comm]
        _ <= t := hbox.2
        _ = scale * h := by
          rw [← hscale, Rat.div_def]
          have hcancel : h⁻¹ * h = 1 := Rat.inv_mul_cancel h hhne
          grind [Rat.mul_assoc, Rat.mul_comm]
    · exact hpos
  unfold QInterval.ContainsInterval QInterval.differenceQuotient
    QInterval.divRat QInterval.sub QInterval.scaleRat
  rw [if_pos hhinv]
  rw [arctanIntegralRectangleCompute_zero_lower,
    arctanIntegralRectangleCompute_zero_upper]
  constructor
  · change scale * (1 - t * t) <=
      (1 / h) * ((arctanIntegralRectangleCompute t n).lo - 0)
    simpa [Rat.sub_eq_add_neg, Rat.add_zero] using hleft
  · change (1 / h) * ((arctanIntegralRectangleCompute t n).hi - 0) <= scale
    simpa [Rat.sub_eq_add_neg, Rat.add_zero] using hright

/-- The tangent-addition chart maps the derived chart increment to the
ordinary endpoint `x + h`. -/
theorem chartAddParameter_tangentChartIncrement
    {x h : Rat} (hx : 0 <= x) (hxh : 0 <= x + h) :
    RationalCircle.Trigonometry.chartAddParameter x
      (tangentChartIncrement x h) = x + h := by
  let d : Rat := 1 + x * (x + h)
  have hdpos : 0 < d := by
    dsimp [d]
    exact tangentChartIncrement_den_pos hx hxh
  have hdne : d ≠ 0 := Rat.ne_of_gt hdpos
  have hxdenpos : 0 < 1 + x * x :=
    RationalCircle.Stage.one_add_square_pos x
  have hxdenne : 1 + x * x ≠ 0 := Rat.ne_of_gt hxdenpos
  have hdenEq : 1 - x * (h * d⁻¹) = (1 + x * x) * d⁻¹ := by
    have hcancel : d * d⁻¹ = 1 := Rat.mul_inv_cancel d hdne
    dsimp [d] at hcancel ⊢
    grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
      Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
  have hnumEq : x + h * d⁻¹ = (x + h) * (1 + x * x) * d⁻¹ := by
    have hcancel : d * d⁻¹ = 1 := Rat.mul_inv_cancel d hdne
    dsimp [d] at hcancel ⊢
    grind [Rat.add_mul, Rat.mul_add, Rat.add_assoc, Rat.add_comm,
      Rat.mul_assoc, Rat.mul_comm]
  unfold RationalCircle.Trigonometry.chartAddParameter
    RationalCircle.Trigonometry.chartAddNum
    RationalCircle.Trigonometry.chartAddDen tangentChartIncrement
  change (x + h * d⁻¹) / (1 - x * (h * d⁻¹)) = x + h
  rw [hnumEq, hdenEq, Rat.div_def, Rat.inv_mul_rev]
  have hcancelD : d * d⁻¹ = 1 := Rat.mul_inv_cancel d hdne
  have hcancelX : (1 + x * x) * (1 + x * x)⁻¹ = 1 :=
    Rat.mul_inv_cancel _ hxdenne
  grind [Rat.mul_assoc, Rat.mul_comm]

/-- On the unit branch, changing from the basepoint kernel to the tangent
chart scale changes it by at most the ordinary positive increment. -/
theorem integralKernel_sub_tangentChartScale_le_step
    {x h : Rat} (hx0 : 0 <= x) (hx1 : x <= 1)
    (hpos : 0 < h) (hxh : 0 <= x + h) :
    0 <= integralKernel x - 1 / (1 + x * (x + h)) /\
      integralKernel x - 1 / (1 + x * (x + h)) <= h := by
  let d0 : Rat := 1 + x * x
  let d : Rat := 1 + x * (x + h)
  have hh0 : 0 <= h := Rat.le_of_lt hpos
  have hd0pos : 0 < d0 := by
    dsimp [d0]
    exact RationalCircle.Stage.one_add_square_pos x
  have hdpos : 0 < d := by
    dsimp [d]
    exact tangentChartIncrement_den_pos hx0 hxh
  have hd0le : d0 <= d := by
    have hterm : 0 <= x * h := Rat.mul_nonneg hx0 hh0
    dsimp [d0, d]
    grind [Rat.mul_add, Rat.add_assoc, Rat.add_comm]
  have hscale_le : 1 / d <= 1 / d0 :=
    one_div_le_one_div_of_pos_of_le hd0pos hd0le
  have hnonneg : 0 <= 1 / d0 - 1 / d := by grind
  have hd0ne : d0 ≠ 0 := Rat.ne_of_gt hd0pos
  have hdne : d ≠ 0 := Rat.ne_of_gt hdpos
  have hformula : 1 / d0 - 1 / d = (x * h) / (d0 * d) := by
    simp only [Rat.div_def, Rat.one_mul, Rat.inv_mul_rev]
    have hcancel0 : d0 * d0⁻¹ = 1 := Rat.mul_inv_cancel d0 hd0ne
    have hcancel : d * d⁻¹ = 1 := Rat.mul_inv_cancel d hdne
    dsimp [d0, d] at hcancel0 hcancel ⊢
    grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
      Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
  have hprodpos : 0 < d0 * d := Rat.mul_pos hd0pos hdpos
  have hprod1 : 1 <= d0 * d := by
    have hd01 : 1 <= d0 := by
      dsimp [d0]
      have hsq := RationalCircle.Stage.ratSquare_nonneg x
      grind
    have hd1 : 1 <= d := by
      dsimp [d]
      have hprod : 0 <= x * (x + h) := Rat.mul_nonneg hx0 hxh
      grind
    calc
      1 = 1 * 1 := by grind
      _ <= d0 * 1 := Rat.mul_le_mul_of_nonneg_right hd01 (by decide +kernel)
      _ <= d0 * d := Rat.mul_le_mul_of_nonneg_left hd1
        (Rat.le_trans (by decide +kernel) hd01)
  have hprodinv : (d0 * d)⁻¹ <= 1 := by
    apply Rat.le_of_mul_le_mul_right (c := d0 * d)
    · calc
        (d0 * d)⁻¹ * (d0 * d) = 1 :=
          Rat.inv_mul_cancel _ (Rat.ne_of_gt hprodpos)
        _ <= 1 * (d0 * d) := by simpa using hprod1
    · exact hprodpos
  have hnumle : x * h <= h := by
    calc
      x * h <= 1 * h := Rat.mul_le_mul_of_nonneg_right hx1 hh0
      _ = h := by grind
  have hprodinv0 : 0 <= (d0 * d)⁻¹ :=
    Rat.le_of_lt ((Rat.inv_pos).2 hprodpos)
  have hupper : (x * h) / (d0 * d) <= h := by
    rw [Rat.div_def]
    calc
      (x * h) * (d0 * d)⁻¹ <= h * (d0 * d)⁻¹ :=
        Rat.mul_le_mul_of_nonneg_right hnumle hprodinv0
      _ <= h * 1 := Rat.mul_le_mul_of_nonneg_left hprodinv hh0
      _ = h := by grind
  change 0 <= 1 / d0 - 1 / d /\ 1 / d0 - 1 / d <= h
  exact ⟨hnonneg, by simpa [hformula] using hupper⟩

/-- The tangent-chart quotient has a direct derivative-kernel enclosure.
The error is entirely rational and independent of the rectangle stage:
the scale changes by at most h, while the zero-based arctangent tangent box
contributes at most h squared. -/
theorem arctanIntegralRectangleCompute_tangentChart_quotient_kernel_contains
    {x h : Rat} (hx0 : 0 <= x) (hx1 : x <= 1) (hpos : 0 < h) (n : Nat) :
    ({ lo := integralKernel x - (h + h * h), hi := integralKernel x } :
      QInterval).ContainsInterval
      (QInterval.differenceQuotient
        (arctanIntegralRectangleCompute (tangentChartIncrement x h) n)
        (arctanIntegralRectangleCompute 0 n) h) := by
  let t := tangentChartIncrement x h
  let d : Rat := 1 + x * (x + h)
  let scale : Rat := 1 / d
  have hbase := arctanIntegralRectangleCompute_tangentChart_quotient_contains
    hx0 hpos n
  have hbase' :
      scale * (1 - t * t) <=
          (QInterval.differenceQuotient
            (arctanIntegralRectangleCompute t n)
            (arctanIntegralRectangleCompute 0 n) h).lo /\
        (QInterval.differenceQuotient
            (arctanIntegralRectangleCompute t n)
            (arctanIntegralRectangleCompute 0 n) h).hi <= scale := by
    simpa [t, d, scale, QInterval.ContainsInterval] using hbase
  have hxh : 0 <= x + h := by
    exact Rat.add_nonneg hx0 (Rat.le_of_lt hpos)
  have hscaleError := integralKernel_sub_tangentChartScale_le_step
    hx0 hx1 hpos hxh
  have hscaleError' :
      0 <= integralKernel x - scale /\
        integralKernel x - scale <= h := by
    simpa [d, scale] using hscaleError
  have ht0 : 0 <= t := by
    dsimp [t]
    exact Rat.le_of_lt (tangentChartIncrement_pos hx0 hpos)
  have htle : t <= h := by
    dsimp [t]
    exact tangentChartIncrement_le_step hx0 hpos
  have htsquare : t * t <= h * h := by
    calc
      t * t <= h * t :=
        Rat.mul_le_mul_of_nonneg_right htle ht0
      _ <= h * h :=
        Rat.mul_le_mul_of_nonneg_left htle (Rat.le_of_lt hpos)
  have hdpos : 0 < d := by
    dsimp [d]
    exact tangentChartIncrement_den_pos hx0 hxh
  have hd1 : 1 <= d := by
    dsimp [d]
    have hprod : 0 <= x * (x + h) := Rat.mul_nonneg hx0 hxh
    grind
  have hscaleLe : scale <= 1 := by
    have hinv : d⁻¹ <= 1 := by
      apply Rat.le_of_mul_le_mul_right (c := d)
      · calc
          d⁻¹ * d = 1 := Rat.inv_mul_cancel d (Rat.ne_of_gt hdpos)
          _ <= 1 * d := by simpa using hd1
      · exact hdpos
    dsimp [scale]
    rw [Rat.div_def, Rat.one_mul]
    exact hinv
  have hscaledSquare : scale * (t * t) <= h * h := by
    calc
      scale * (t * t) <= 1 * (t * t) :=
        Rat.mul_le_mul_of_nonneg_right hscaleLe
          (Rat.mul_nonneg ht0 ht0)
      _ = t * t := by grind
      _ <= h * h := htsquare
  have hkernelLeScalePlus : integralKernel x <= scale + h := by
    grind [Rat.sub_eq_add_neg, hscaleError'.2]
  have hlower :
      integralKernel x - (h + h * h) <= scale * (1 - t * t) := by
    calc
      integralKernel x - (h + h * h) <= scale - h * h := by
        grind [Rat.sub_eq_add_neg]
      _ <= scale - scale * (t * t) := by
        grind [Rat.sub_eq_add_neg]
      _ = scale * (1 - t * t) := by
        grind [Rat.sub_eq_add_neg, Rat.mul_add]
  have hupper : scale <= integralKernel x := by
    grind [Rat.sub_eq_add_neg, hscaleError'.1]
  exact ⟨Rat.le_trans hlower hbase'.1, Rat.le_trans hbase'.2 hupper⟩

/-- After positive scaling by `1 / h`, the finite transported chart bracket
still contains the chart-increment difference quotient.  This is the finite
substitution datum needed to transport the local tangent-chart derivative to
the ordinary rectangle arctangent. -/
theorem tangentChart_transport_scaled_contains_chartQuotient
    {x h : Rat} (hx0 : 0 <= x) (hxHalf : x <= (1 : Rat) / 2)
    (hpos : 0 < h) (hupper : x + h <= 1) (n : Nat) :
    (QInterval.scaleRat (1 / h)
      (chartAddAreaLoopCompute x (tangentChartIncrement x h) n)).ContainsInterval
      (QInterval.differenceQuotient
        (arctanIntegralRectangleCompute (tangentChartIncrement x h) n)
        (arctanIntegralRectangleCompute 0 n) h) := by
  have hx1 : x <= 1 := Rat.le_trans hxHalf (by decide +kernel)
  have hxh0 : 0 <= x + h := by grind
  have hh1 : h <= 1 := by grind
  have ht0 : 0 <= tangentChartIncrement x h :=
    Rat.le_of_lt (tangentChartIncrement_pos hx0 hpos)
  have ht1 : tangentChartIncrement x h <= 1 :=
    Rat.le_trans (tangentChartIncrement_le_step hx0 hpos) hh1
  have hxlt : x < 1 := by
    have hhalf : (1 : Rat) / 2 < 1 := by decide +kernel
    grind
  have hparam := chartAddParameter_tangentChartIncrement hx0 hxh0
  have hcontains := chartAddAreaLoop_integralSum_contains
    hx0 hxlt ht0 ht1 n
  have hinv : 0 <= 1 / h := by
    rw [Rat.div_def]
    simpa using Rat.le_of_lt ((Rat.inv_pos).2 hpos)
  have hscaled := QInterval.scaleRat_contains_of_nonneg hinv hcontains
  have hquotientEq :
      QInterval.differenceQuotient
        (arctanIntegralRectangleCompute (tangentChartIncrement x h) n)
        (arctanIntegralRectangleCompute 0 n) h =
        QInterval.scaleRat (1 / h)
          (arctanIntegralRectangleCompute (tangentChartIncrement x h) n) := by
    unfold QInterval.differenceQuotient QInterval.divRat QInterval.sub
      QInterval.scaleRat
    simp only [if_pos hinv]
    rw [arctanIntegralRectangleCompute_zero_lower,
      arctanIntegralRectangleCompute_zero_upper]
    apply (QInterval.mk.injEq _ _ _ _).mpr
    constructor <;> grind [Rat.sub_eq_add_neg]
  rw [hquotientEq]
  exact hscaled

/-- The scaled transported chart bracket overlaps the ordinary forward
difference quotient at the same finite stage. -/
theorem tangentChart_transport_scaled_overlaps_forwardQuotient
    {x h : Rat} (hx0 : 0 <= x) (hxHalf : x <= (1 : Rat) / 2)
    (hpos : 0 < h) (hupper : x + h <= 1) (n : Nat) :
    QInterval.Overlaps
      (QInterval.scaleRat (1 / h)
        (chartAddAreaLoopCompute x (tangentChartIncrement x h) n))
      (QInterval.differenceQuotient
        (arctanIntegralRectangleCompute (x + h) n)
        (arctanIntegralRectangleCompute x n) h) := by
  have hx1 : x <= 1 := Rat.le_trans hxHalf (by decide +kernel)
  have hxh0 : 0 <= x + h := by grind
  have hh1 : h <= 1 := by grind
  have ht0 : 0 <= tangentChartIncrement x h :=
    Rat.le_of_lt (tangentChartIncrement_pos hx0 hpos)
  have ht1 : tangentChartIncrement x h <= 1 :=
    Rat.le_trans (tangentChartIncrement_le_step hx0 hpos) hh1
  have hparam := chartAddParameter_tangentChartIncrement hx0 hxh0
  have hover := chartAddAreaLoopCompute_overlaps_rectangleSub
    hx0 hxHalf ht0 ht1 n
  rw [hparam] at hover
  have hinv : 0 <= 1 / h := by
    rw [Rat.div_def]
    simpa using Rat.le_of_lt ((Rat.inv_pos).2 hpos)
  have hscaled := QInterval.scaleRat_overlaps_of_nonneg hinv hover
  change QInterval.Overlaps
    (QInterval.scaleRat (1 / h)
      (chartAddAreaLoopCompute x (tangentChartIncrement x h) n))
    (QInterval.scaleRat (1 / h)
      (QInterval.subInterval
        (arctanIntegralRectangleCompute (x + h) n)
        (arctanIntegralRectangleCompute x n)))
  exact hscaled

/-- The finite tangent-chart containment applies throughout the unit branch;
the right-half case uses the local pole margin rather than a global
half-unit-base assumption. -/
theorem tangentChart_transport_scaled_contains_chartQuotient_on_unit
    {x h : Rat} (hx0 : 0 <= x) (hx1 : x <= 1)
    (hpos : 0 < h) (hupper : x + h <= 1) (n : Nat) :
    (QInterval.scaleRat (1 / h)
      (chartAddAreaLoopCompute x (tangentChartIncrement x h) n)).ContainsInterval
      (QInterval.differenceQuotient
        (arctanIntegralRectangleCompute (tangentChartIncrement x h) n)
        (arctanIntegralRectangleCompute 0 n) h) := by
  have hxh0 : 0 <= x + h := by grind
  have hh1 : h <= 1 := by grind
  have ht0 : 0 <= tangentChartIncrement x h :=
    Rat.le_of_lt (tangentChartIncrement_pos hx0 hpos)
  have ht1 : tangentChartIncrement x h <= 1 :=
    Rat.le_trans (tangentChartIncrement_le_step hx0 hpos) hh1
  have hxlt : x < 1 := by grind
  have hcontains := chartAddAreaLoop_integralSum_contains
    hx0 hxlt ht0 ht1 n
  have hinv : 0 <= 1 / h := by
    rw [Rat.div_def]
    simpa using Rat.le_of_lt ((Rat.inv_pos).2 hpos)
  have hscaled := QInterval.scaleRat_contains_of_nonneg hinv hcontains
  have hquotientEq :
      QInterval.differenceQuotient
        (arctanIntegralRectangleCompute (tangentChartIncrement x h) n)
        (arctanIntegralRectangleCompute 0 n) h =
        QInterval.scaleRat (1 / h)
          (arctanIntegralRectangleCompute (tangentChartIncrement x h) n) := by
    unfold QInterval.differenceQuotient QInterval.divRat QInterval.sub
      QInterval.scaleRat
    simp only [if_pos hinv]
    rw [arctanIntegralRectangleCompute_zero_lower,
      arctanIntegralRectangleCompute_zero_upper]
    apply (QInterval.mk.injEq _ _ _ _).mpr
    constructor <;> grind [Rat.sub_eq_add_neg]
  rw [hquotientEq]
  exact hscaled

/-- The scaled tangent chart overlaps the ordinary forward quotient throughout
the unit branch.  This is the exact finite transport needed by the global
forward arctangent derivative certificate. -/
theorem tangentChart_transport_scaled_overlaps_forwardQuotient_on_unit
    {x h : Rat} (hx0 : 0 <= x) (hx1 : x <= 1)
    (hpos : 0 < h) (hupper : x + h <= 1) (n : Nat) :
    QInterval.Overlaps
      (QInterval.scaleRat (1 / h)
        (chartAddAreaLoopCompute x (tangentChartIncrement x h) n))
      (QInterval.differenceQuotient
        (arctanIntegralRectangleCompute (x + h) n)
        (arctanIntegralRectangleCompute x n) h) := by
  have hxh0 : 0 <= x + h := by grind
  have hh1 : h <= 1 := by grind
  have ht0 : 0 <= tangentChartIncrement x h :=
    Rat.le_of_lt (tangentChartIncrement_pos hx0 hpos)
  have ht1 : tangentChartIncrement x h <= 1 :=
    Rat.le_trans (tangentChartIncrement_le_step hx0 hpos) hh1
  have hxlt : x < 1 := by grind
  have hparam := chartAddParameter_tangentChartIncrement hx0 hxh0
  have hover := chartAddAreaLoopCompute_overlaps_rectangleSub_of_lt
    hx0 hxlt ht0 ht1 n
  rw [hparam] at hover
  have hinv : 0 <= 1 / h := by
    rw [Rat.div_def]
    simpa using Rat.le_of_lt ((Rat.inv_pos).2 hpos)
  have hscaled := QInterval.scaleRat_overlaps_of_nonneg hinv hover
  change QInterval.Overlaps
    (QInterval.scaleRat (1 / h)
      (chartAddAreaLoopCompute x (tangentChartIncrement x h) n))
    (QInterval.scaleRat (1 / h)
      (QInterval.subInterval
        (arctanIntegralRectangleCompute (x + h) n)
        (arctanIntegralRectangleCompute x n)))
  exact hscaled

/-- On the whole rational unit branch, a forward difference of the canonical
rectangle arctangent is equivalent to the rectangle construction at its
tangent-chart increment.  The proof is entirely finite: the transported
partition computes the same short interval, while the local product margin
certifies the raw transport itself. -/
theorem arctanIntegralRectangleRaw_forward_difference_equiv_tangentChartIncrement
    {x h : Rat} (hx0 : 0 <= x) (hx1 : x <= 1)
    (hpos : 0 < h) (hupper : x + h <= 1) :
    (arctanIntegralRectangleRaw (x + h) - arctanIntegralRectangleRaw x).Equiv
      (arctanIntegralRectangleRaw (tangentChartIncrement x h)) := by
  have hxh0 : 0 <= x + h := by grind
  have hxlt : x < 1 := by grind
  have hh1 : h <= 1 := by grind
  have ht0 : 0 <= tangentChartIncrement x h :=
    Rat.le_of_lt (tangentChartIncrement_pos hx0 hpos)
  have ht1 : tangentChartIncrement x h <= 1 :=
    Rat.le_trans (tangentChartIncrement_le_step hx0 hpos) hh1
  have hmargin : x * tangentChartIncrement x h <= (1 : Rat) / 2 :=
    tangentChartIncrement_base_mul_le_half hx0 hpos hupper
  have hchart : RationalCircle.Trigonometry.chartAddParameter x
      (tangentChartIncrement x h) = x + h :=
    chartAddParameter_tangentChartIncrement hx0 hxh0
  have himage : RationalCircle.Trigonometry.chartAddParameter x
      (tangentChartIncrement x h) <= 1 := by
    rw [hchart]
    exact hupper
  have hX : (arctanIntegralRectangleRaw x).Valid :=
    arctanIntegralRectangleRaw_valid hx0 hx1
  have hY : (arctanIntegralRectangleRaw (x + h)).Valid :=
    arctanIntegralRectangleRaw_valid hxh0 hupper
  have hT : (arctanIntegralRectangleRaw (tangentChartIncrement x h)).Valid :=
    arctanIntegralRectangleRaw_valid ht0 ht1
  have hTransport : (chartAddAreaLoopRaw x (tangentChartIncrement x h)).Valid :=
    chartAddAreaLoopRaw_valid_of_rightProduct_le_half
      hx0 hxlt hx1 ht0 ht1 hmargin himage
  have hRectTransport :
      (arctanIntegralRectangleRaw (tangentChartIncrement x h)).Equiv
        (chartAddAreaLoopRaw x (tangentChartIncrement x h)) :=
    arctanIntegralRectangleRaw_equiv_chartAddAreaLoopRaw hx0 hxlt ht0 ht1
  have hTransportDifference :
      (chartAddAreaLoopRaw x (tangentChartIncrement x h)).Equiv
        (arctanIntegralRectangleRaw (x + h) - arctanIntegralRectangleRaw x) := by
    have h := chartAddAreaLoopRaw_equiv_rectangleSub_of_lt
      (u := x) (x := tangentChartIncrement x h) hx0 hxlt ht0 ht1
    rw [hchart] at h
    exact h
  exact RealCompute.equiv_trans (RealCompute.sub_valid hY hX) hTransport hT
    (RealCompute.equiv_symm hTransportDifference)
    (RealCompute.equiv_symm hRectTransport)

/-- A common finite stage of the rectangle algorithm obeys the forward
one-Lipschitz estimate.  This is stronger than stagewise monotonicity: it
controls the lower endpoint at `x+h` by the upper endpoint at `x` plus the
literal rational step. -/
theorem arctanIntegralRectangleCompute_forward_lower_sub_upper_le_step
    {x h : Rat} (hx0 : 0 <= x) (hx1 : x <= 1)
    (hpos : 0 < h) (hupper : x + h <= 1) (n : Nat) :
    (arctanIntegralRectangleCompute (x + h) n).lo -
        (arctanIntegralRectangleCompute x n).hi <= h := by
  have hequiv := arctanIntegralRectangleRaw_forward_difference_equiv_tangentChartIncrement
    hx0 hx1 hpos hupper
  have hover := (RealCompute.compareAt_overlap_iff
    (arctanIntegralRectangleRaw (x + h) - arctanIntegralRectangleRaw x)
    (arctanIntegralRectangleRaw (tangentChartIncrement x h)) n n).1
      (hequiv n)
  change QInterval.Overlaps
      (QInterval.subInterval
        (arctanIntegralRectangleCompute (x + h) n)
        (arctanIntegralRectangleCompute x n))
      (arctanIntegralRectangleCompute (tangentChartIncrement x h) n) at hover
  calc
    (arctanIntegralRectangleCompute (x + h) n).lo -
        (arctanIntegralRectangleCompute x n).hi =
        (QInterval.subInterval
          (arctanIntegralRectangleCompute (x + h) n)
          (arctanIntegralRectangleCompute x n)).lo := rfl
    _ <= (arctanIntegralRectangleCompute (tangentChartIncrement x h) n).hi :=
      hover.1
    _ <= tangentChartIncrement x h :=
      arctanIntegralRectangleCompute_upper_le_input
        (Rat.le_of_lt (tangentChartIncrement_pos hx0 hpos)) n
    _ <= h := tangentChartIncrement_le_step hx0 hpos

/-- A tangent increment based anywhere on the unit branch has the same
explicit chart-width precision schedule as the earlier first-half proof. -/
theorem tangentChartAreaLoopCompute_width_le_eps_on_unit
    {x h : Rat} (hx0 : 0 <= x) (hx1 : x <= 1)
    (hpos : 0 < h) (hupper : x + h <= 1)
    (eps : QPos) (n : Nat) (hn : 256 * (eps.val.den + 1) <= n) :
    (chartAddAreaLoopCompute x (tangentChartIncrement x h) n).width <= eps.val := by
  have hxh0 : 0 <= x + h := by grind
  have hh1 : h <= 1 := by grind
  have hxlt : x < 1 := by grind
  have ht0 : 0 <= tangentChartIncrement x h :=
    Rat.le_of_lt (tangentChartIncrement_pos hx0 hpos)
  have ht1 : tangentChartIncrement x h <= 1 :=
    Rat.le_trans (tangentChartIncrement_le_step hx0 hpos) hh1
  have hmargin : x * tangentChartIncrement x h <= (1 : Rat) / 2 :=
    tangentChartIncrement_base_mul_le_half hx0 hpos hupper
  have hchart := chartAddParameter_tangentChartIncrement hx0 hxh0
  have himage : RationalCircle.Trigonometry.chartAddParameter x
      (tangentChartIncrement x h) <= 1 := by
    rw [hchart]
    exact hupper
  exact chartAddAreaLoopCompute_width_le_eps_of_rightProduct_le_half
    hx0 hxlt hx1 ht0 ht1 hmargin himage eps n hn

/-- Tangent addition expresses an ordinary forward increment by the chart
increment based at zero on the first half of the unit branch. -/
theorem arctanGeom_add_tangentChartIncrement_equiv
    {x h : Rat} (hx0 : 0 <= x) (hxHalf : x <= (1 : Rat) / 2)
    (hpos : 0 < h) (hupper : x + h <= 1) :
    (arctanGeom x + arctanGeom (tangentChartIncrement x h)).Equiv
      (arctanGeom (x + h)) := by
  have hxh : 0 <= x + h := by grind
  have ht0 : 0 <= tangentChartIncrement x h :=
    Rat.le_of_lt (tangentChartIncrement_pos hx0 hpos)
  have hh1 : h <= 1 := by grind
  have ht1 : tangentChartIncrement x h <= 1 :=
    Rat.le_trans (tangentChartIncrement_le_step hx0 hpos) hh1
  have hchart := chartAddParameter_tangentChartIncrement hx0 hxh
  have himage : RationalCircle.Trigonometry.chartAddParameter x
      (tangentChartIncrement x h) <= 1 := by
    rw [hchart]
    exact hupper
  have hadd := arctanGeom_chartAdd_add_of_half hx0 hxHalf ht0 ht1 himage
  rw [hchart] at hadd
  exact hadd

/-- Subtracting the basepoint turns the tangent-chart addition theorem into
an ordinary forward endpoint-difference equivalence. -/
theorem arctanGeom_forward_difference_equiv_tangentChartIncrement
    {x h : Rat} (hx0 : 0 <= x) (hxHalf : x <= (1 : Rat) / 2)
    (hpos : 0 < h) (hupper : x + h <= 1) :
    (arctanGeom (x + h) - arctanGeom x).Equiv
      (arctanGeom (tangentChartIncrement x h)) := by
  have hxh : 0 <= x + h := by grind
  have hx1 : x <= 1 := Rat.le_trans hxHalf (by decide +kernel)
  have ht0 : 0 <= tangentChartIncrement x h :=
    Rat.le_of_lt (tangentChartIncrement_pos hx0 hpos)
  have hh1 : h <= 1 := by grind
  have ht1 : tangentChartIncrement x h <= 1 :=
    Rat.le_trans (tangentChartIncrement_le_step hx0 hpos) hh1
  have hX : (arctanGeom x).Valid := arctanGeom_valid_on_unit hx0 hx1
  have hT : (arctanGeom (tangentChartIncrement x h)).Valid :=
    arctanGeom_valid_on_unit ht0 ht1
  have hY : (arctanGeom (x + h)).Valid :=
    arctanGeom_valid_on_unit hxh hupper
  have hsum : (arctanGeom x + arctanGeom (tangentChartIncrement x h)).Valid :=
    RealCompute.add_valid hX hT
  have hadd := arctanGeom_add_tangentChartIncrement_equiv
    hx0 hxHalf hpos hupper
  have hsub :
      (arctanGeom (x + h) - arctanGeom x).Equiv
        ((arctanGeom x + arctanGeom (tangentChartIncrement x h)) -
          arctanGeom x) :=
    RealCompute.sub_equiv hY hsum hX hX (RealCompute.equiv_symm hadd)
      (RealCompute.equiv_refl (arctanGeom x) hX)
  exact RealCompute.equiv_trans (RealCompute.sub_valid hY hX)
    (RealCompute.sub_valid hsum hX) hT hsub
    (RealCompute.add_sub_cancel_left_equiv hX hT)

/-- Three bounded rational chart additions compose at the level of geometric
arctangent intervals.  This packages the reassociation needed by rational
three-term arctangent formulae while keeping every branch and image bound
explicit. -/
theorem arctanGeom_chartAdd_add_three_of_half
    {u v w : Rat}
    (hu0 : 0 <= u) (huHalf : u <= (1 : Rat) / 2)
    (hv0 : 0 <= v) (hvHalf : v <= (1 : Rat) / 2)
    (hw0 : 0 <= w) (hw1 : w <= 1)
    (hvw0 : 0 <= RationalCircle.Trigonometry.chartAddParameter v w)
    (hvw1 : RationalCircle.Trigonometry.chartAddParameter v w <= 1)
    (huvw0 : 0 <= RationalCircle.Trigonometry.chartAddParameter u
      (RationalCircle.Trigonometry.chartAddParameter v w))
    (huvw1 : RationalCircle.Trigonometry.chartAddParameter u
      (RationalCircle.Trigonometry.chartAddParameter v w) <= 1) :
    ((arctanGeom u + arctanGeom v) + arctanGeom w).Equiv
      (arctanGeom (RationalCircle.Trigonometry.chartAddParameter u
        (RationalCircle.Trigonometry.chartAddParameter v w))) := by
  have hu1 : u <= 1 :=
    Rat.le_trans huHalf (by decide +kernel : (1 : Rat) / 2 <= 1)
  have hv1 : v <= 1 :=
    Rat.le_trans hvHalf (by decide +kernel : (1 : Rat) / 2 <= 1)
  have hU : (arctanGeom u).Valid :=
    arctanGeom_valid_on_unit hu0 hu1
  have hV : (arctanGeom v).Valid :=
    arctanGeom_valid_on_unit hv0 hv1
  have hW : (arctanGeom w).Valid :=
    arctanGeom_valid_on_unit hw0 hw1
  have hVW :
      (arctanGeom (RationalCircle.Trigonometry.chartAddParameter v w)).Valid :=
    arctanGeom_valid_on_unit hvw0 hvw1
  have hUVW :
      (arctanGeom (RationalCircle.Trigonometry.chartAddParameter u
        (RationalCircle.Trigonometry.chartAddParameter v w))).Valid :=
    arctanGeom_valid_on_unit huvw0 huvw1
  have hVWAdd :
      (arctanGeom v + arctanGeom w).Equiv
        (arctanGeom (RationalCircle.Trigonometry.chartAddParameter v w)) :=
    arctanGeom_chartAdd_add_of_half hv0 hvHalf hw0 hw1 hvw1
  have hUVWAdd :
      (arctanGeom u +
        arctanGeom (RationalCircle.Trigonometry.chartAddParameter v w)).Equiv
        (arctanGeom (RationalCircle.Trigonometry.chartAddParameter u
          (RationalCircle.Trigonometry.chartAddParameter v w))) :=
    arctanGeom_chartAdd_add_of_half hu0 huHalf hvw0 hvw1 huvw1
  have hleft : ((arctanGeom u + arctanGeom v) + arctanGeom w).Valid :=
    RealCompute.add_valid (RealCompute.add_valid hU hV) hW
  have hassoc : (arctanGeom u + (arctanGeom v + arctanGeom w)).Valid :=
    RealCompute.add_valid hU (RealCompute.add_valid hV hW)
  have hmid :
      (arctanGeom u +
        arctanGeom (RationalCircle.Trigonometry.chartAddParameter v w)).Valid :=
    RealCompute.add_valid hU hVW
  have hregroup :
      ((arctanGeom u + arctanGeom v) + arctanGeom w).Equiv
        (arctanGeom u + (arctanGeom v + arctanGeom w)) :=
    RealCompute.add_assoc_equiv (arctanGeom u) (arctanGeom v) (arctanGeom w)
      hU hV hW
  have hreplace :
      (arctanGeom u + (arctanGeom v + arctanGeom w)).Equiv
        (arctanGeom u +
          arctanGeom (RationalCircle.Trigonometry.chartAddParameter v w)) :=
    RealCompute.add_equiv hU hU (RealCompute.add_valid hV hW) hVW
      (RealCompute.equiv_refl (arctanGeom u) hU) hVWAdd
  exact RealCompute.equiv_trans hleft hassoc hUVW hregroup
    (RealCompute.equiv_trans hassoc hmid hUVW hreplace hUVWAdd)

theorem arctanIntegralRectangleRawAtOne_equiv_arctanGeom_one :
    arctanIntegralRectangleRawAtOne.Equiv (arctanGeom 1) := by
  intro n
  apply (RealCompute.compareAt_overlap_iff
    arctanIntegralRectangleRawAtOne (arctanGeom 1) n n).2
  change QInterval.Overlaps
    (integralSumInterval (arctanAreaLoopState 1 n).intervals)
    ((arctanGeom 1).compute n)
  rw [arctanGeom_one_compute_eq n]
  exact arctanAreaLoop_integralSum_overlaps_positiveLoop
    (x := 1) (by decide +kernel) n

theorem arctanGeom_zero :
    arctanGeom 0 = RealCompute.ofRat 0 := by
  simp [arctanGeom]

def toPiAreaLoopState (state : AreaLoopState) : AreaBoundsLoopState :=
  { lo := state.lo, hi := state.hi, intervals := state.intervals }

theorem refineAux_toPiAreaLoopState
    (lo hi : Rat) (intervals : List (Rat × Rat)) :
    AreaBoundsLoopState.refineAux lo hi intervals =
      toPiAreaLoopState (AreaLoopState.refineAux lo hi intervals) := by
  induction intervals generalizing lo hi with
  | nil =>
      simp [AreaBoundsLoopState.refineAux, AreaLoopState.refineAux,
        toPiAreaLoopState]
  | cons pq rest ih =>
      rcases pq with ⟨p, r⟩
      let q := (p + r) / 2
      simp [AreaBoundsLoopState.refineAux, AreaLoopState.refineAux,
        toPiAreaLoopState, arctanAreaIncrement, circleAreaIncrement,
        arctanAreaDecrement, circleAreaDecrement]
      rw [ih]
      simp [toPiAreaLoopState]

theorem refineAreaBounds_toPiAreaLoopState (state : AreaLoopState) :
    refineAreaBounds (toPiAreaLoopState state) =
      toPiAreaLoopState (refineAreaLoopState state) := by
  cases state with
  | mk lo hi intervals =>
      exact refineAux_toPiAreaLoopState lo hi intervals

theorem iterateAreaBounds_toPiAreaLoopState (n : Nat)
    (state : AreaLoopState) :
    iterateAreaBounds n (toPiAreaLoopState state) =
      toPiAreaLoopState (iterateAreaLoopState n state) := by
  induction n generalizing state with
  | zero => rfl
  | succ n ih =>
      simp [iterateAreaBounds, iterateAreaLoopState]
      rw [refineAreaBounds_toPiAreaLoopState]
      exact ih (refineAreaLoopState state)

theorem piCircleAreaInitial_eq_arctanAreaLoopInitial_one :
    piCircleAreaInitial =
      toPiAreaLoopState (arctanAreaLoopInitial 1) := by
  decide +kernel

theorem piCircleAreaState_eq_arctanAreaLoopState_one
    (n : Nat) :
    piCircleAreaState n =
      toPiAreaLoopState (arctanAreaLoopState 1 n) := by
  unfold piCircleAreaState arctanAreaLoopState
  rw [piCircleAreaInitial_eq_arctanAreaLoopInitial_one]
  exact iterateAreaBounds_toPiAreaLoopState n (arctanAreaLoopInitial 1)

/-!
The public area loop and the polygon-stage computation use the same dyadic
parameter mesh.  The following finite bridge identifies their endpoints
exactly: chord and tangent polygon cross sums are the same geometric cell sums
carried by the update loop.  This is all rational finite algebra, not a limit
or a completeness argument.
-/

private theorem geometricLower_eq_cross_half (u v : Rat) :
    geometricLowerStep u v =
      RationalCircle.Stage.cross
        (RationalCircle.Stage.point u) (RationalCircle.Stage.point v) / 2 := by
  rw [RationalCircle.Stage.point_cross_formula]
  unfold geometricLowerStep
  rw [Rat.div_def, Rat.div_def]
  have htwo : (2 : Rat) ≠ 0 := by decide +kernel
  grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]

private theorem repeated_ratio (d h D : Rat)
    (hd : d ≠ 0) (hD : D ≠ 0) :
    (2 * d * d / D) / (2 * d * h / D) = d / h := by
  rw [Rat.div_def, Rat.div_def, Rat.div_def]
  rw [Rat.inv_mul_rev]
  rw [Rat.inv_mul_rev]
  rw [Rat.inv_mul_rev]
  have htwo : (2 : Rat) ≠ 0 := by decide +kernel
  grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]

private def innerCrossSum (S : RationalCircle.Stage) (k : Nat) : Nat -> Rat
  | 0 => 0
  | count + 1 =>
      RationalCircle.Stage.cross (S.samplePoint k) (S.samplePoint (k + 1)) +
        innerCrossSum S (k + 1) count

private theorem innerCrossSum_nonneg (S : RationalCircle.Stage)
    (hS : 0 < S.subdivisions) (k count : Nat) :
    0 <= innerCrossSum S k count := by
  induction count generalizing k with
  | zero => simp [innerCrossSum]
  | succ count ih =>
      simp only [innerCrossSum]
      exact Rat.add_nonneg
        (Rat.le_of_lt (RationalCircle.Stage.samplePoint_cross_pos_adjacent S hS k))
        (ih (k + 1))

private theorem inner_boundary_aux (S : RationalCircle.Stage)
    (k count : Nat) :
    piCircleAreaPolygon.twiceSignedAreaAux RationalCircle.Stage.cross
      RationalCircle.Stage.origin (S.samplePoint k)
      (S.innerBoundaryFrom (k + 1) count) =
      innerCrossSum S k count := by
  induction count generalizing k with
  | zero =>
      change RationalCircle.Stage.cross (S.samplePoint k)
        RationalCircle.Stage.origin = 0
      exact RationalCircle.Stage.cross_origin_right _
  | succ count ih =>
      change RationalCircle.Stage.cross (S.samplePoint k) (S.samplePoint (k + 1)) +
          piCircleAreaPolygon.twiceSignedAreaAux RationalCircle.Stage.cross
            RationalCircle.Stage.origin (S.samplePoint (k + 1))
            (S.innerBoundaryFrom (k + 1 + 1) count) =
          RationalCircle.Stage.cross (S.samplePoint k) (S.samplePoint (k + 1)) +
            innerCrossSum S (k + 1) count
      rw [ih (k + 1)]

private theorem inner_twiceSignedArea (S : RationalCircle.Stage) :
    RationalCircle.Stage.twiceSignedArea
      (RationalCircle.Stage.origin :: S.innerBoundary) =
      innerCrossSum S 0 S.subdivisions := by
  change piCircleAreaPolygon.twiceSignedAreaAux RationalCircle.Stage.cross
    RationalCircle.Stage.origin RationalCircle.Stage.origin
    (S.samplePoint 0 :: S.innerBoundaryFrom 1 S.subdivisions) = _
  simp only [piCircleAreaPolygon.twiceSignedAreaAux]
  rw [RationalCircle.Stage.cross_origin_left]
  rw [Rat.zero_add]
  simpa [innerCrossSum] using inner_boundary_aux S 0 S.subdivisions

private theorem innerQuarterArea_eq_innerCrossSum_half
    (S : RationalCircle.Stage) (hS : 0 < S.subdivisions) :
    S.innerQuarterArea = innerCrossSum S 0 S.subdivisions / 2 := by
  unfold RationalCircle.Stage.innerQuarterArea
  rw [RationalCircle.Stage.polygonArea]
  rw [inner_twiceSignedArea S]
  unfold qabs
  by_cases hneg : innerCrossSum S 0 S.subdivisions / 2 < 0
  · have hnonneg : 0 <= innerCrossSum S 0 S.subdivisions / 2 := by
      rw [Rat.div_def]
      exact Rat.mul_nonneg (innerCrossSum_nonneg S hS 0 S.subdivisions)
        (by decide +kernel)
    grind
  · simp [hneg]

private def outerCrossSum (S : RationalCircle.Stage) (k : Nat) : Nat -> Rat
  | 0 => 0
  | count + 1 =>
      RationalCircle.Stage.cross (S.samplePoint k) (S.tangentPoint k) +
        RationalCircle.Stage.cross (S.tangentPoint k) (S.samplePoint (k + 1)) +
          outerCrossSum S (k + 1) count

private theorem outerCrossSum_nonneg (S : RationalCircle.Stage)
    (hS : 0 < S.subdivisions) (k count : Nat) :
    0 <= outerCrossSum S k count := by
  induction count generalizing k with
  | zero => simp [outerCrossSum]
  | succ count ih =>
      simp only [outerCrossSum]
      exact Rat.add_nonneg
        (Rat.add_nonneg
          (RationalCircle.Stage.adjacentEntryTangentCross_nonneg S hS k)
          (RationalCircle.Stage.adjacentExitTangentCross_nonneg S hS k)
        ) (ih (k + 1))

private theorem outer_boundary_aux (S : RationalCircle.Stage)
    (k count : Nat) :
    piCircleAreaPolygon.twiceSignedAreaAux RationalCircle.Stage.cross
      RationalCircle.Stage.origin (S.samplePoint k)
      (S.outerBoundaryFrom k count) =
      outerCrossSum S k count := by
  induction count generalizing k with
  | zero =>
      change RationalCircle.Stage.cross (S.samplePoint k)
        RationalCircle.Stage.origin = 0
      exact RationalCircle.Stage.cross_origin_right _
  | succ count ih =>
      simp only [RationalCircle.Stage.outerBoundaryFrom,
        piCircleAreaPolygon.outerBoundaryFrom, outerCrossSum,
        piCircleAreaPolygon.twiceSignedAreaAux]
      change RationalCircle.Stage.cross (S.samplePoint k) (S.tangentPoint k) +
          (RationalCircle.Stage.cross (S.tangentPoint k) (S.samplePoint (k + 1)) +
            piCircleAreaPolygon.twiceSignedAreaAux RationalCircle.Stage.cross
              RationalCircle.Stage.origin (S.samplePoint (k + 1))
              (S.outerBoundaryFrom (k + 1) count)) =
          RationalCircle.Stage.cross (S.samplePoint k) (S.tangentPoint k) +
            RationalCircle.Stage.cross (S.tangentPoint k) (S.samplePoint (k + 1)) +
              outerCrossSum S (k + 1) count
      rw [ih (k + 1)]
      grind [Rat.add_assoc]

private theorem outer_twiceSignedArea (S : RationalCircle.Stage) :
    RationalCircle.Stage.twiceSignedArea
      (RationalCircle.Stage.origin :: S.outerBoundary) =
      outerCrossSum S 0 S.subdivisions := by
  change piCircleAreaPolygon.twiceSignedAreaAux RationalCircle.Stage.cross
    RationalCircle.Stage.origin RationalCircle.Stage.origin
    (S.samplePoint 0 :: S.outerBoundaryFrom 0 S.subdivisions) = _
  simp only [piCircleAreaPolygon.twiceSignedAreaAux]
  rw [RationalCircle.Stage.cross_origin_left, Rat.zero_add]
  exact outer_boundary_aux S 0 S.subdivisions

private theorem outerQuarterArea_eq_outerCrossSum_half
    (S : RationalCircle.Stage) (hS : 0 < S.subdivisions) :
    S.outerQuarterArea = outerCrossSum S 0 S.subdivisions / 2 := by
  unfold RationalCircle.Stage.outerQuarterArea
  rw [RationalCircle.Stage.polygonArea]
  rw [outer_twiceSignedArea S]
  unfold qabs
  by_cases hneg : outerCrossSum S 0 S.subdivisions / 2 < 0
  · have hnonneg : 0 <= outerCrossSum S 0 S.subdivisions / 2 := by
      rw [Rat.div_def]
      exact Rat.mul_nonneg (outerCrossSum_nonneg S hS 0 S.subdivisions)
        (by decide +kernel)
    grind
  · simp [hneg]

private theorem geometricUpper_eq_tangentCross_half (u v : Rat) :
    geometricUpperStep u v =
      (RationalCircle.Stage.cross
        (RationalCircle.Stage.point u)
        (RationalCircle.Stage.tangentIntersection
          (RationalCircle.Stage.point u) (RationalCircle.Stage.point v)) +
        RationalCircle.Stage.cross
          (RationalCircle.Stage.tangentIntersection
            (RationalCircle.Stage.point u) (RationalCircle.Stage.point v))
          (RationalCircle.Stage.point v)) / 2 := by
  rw [RationalCircle.Stage.cross_left_tangentIntersection
    (RationalCircle.Stage.point_normSq_unit u)]
  rw [RationalCircle.Stage.cross_tangentIntersection_right
    (RationalCircle.Stage.point_normSq_unit v)]
  rw [RationalCircle.Stage.one_sub_point_dot_formula,
    RationalCircle.Stage.point_cross_formula]
  unfold geometricUpperStep
  by_cases hdiff : v - u = 0
  · have huv : v = u := by grind [Rat.sub_eq_add_neg]
    subst v
    simp [Rat.div_def]
    grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.add_assoc,
      Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
  · by_cases huv : 1 + u * v = 0
    · simp [huv, Rat.div_def]
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.add_assoc,
        Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]
    · have hD : (1 + u * u) * (1 + v * v) ≠ 0 := by
        exact Rat.ne_of_gt (Rat.mul_pos
          (RationalCircle.Stage.one_add_square_pos u)
          (RationalCircle.Stage.one_add_square_pos v))
      have hratio := repeated_ratio (v - u) (1 + u * v)
        ((1 + u * u) * (1 + v * v)) hdiff hD
      rw [hratio]
      grind [Rat.div_def, Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]

private def stageIntervals (S : RationalCircle.Stage) (k : Nat) : Nat ->
    List (Rat × Rat)
  | 0 => []
  | count + 1 =>
      (S.parameter k, S.parameter (k + 1)) :: stageIntervals S (k + 1) count

private theorem innerCrossSum_half_eq_geometricLowerSum
    (S : RationalCircle.Stage) (k count : Nat) :
    innerCrossSum S k count / 2 =
      geometricLowerSum (stageIntervals S k count) := by
  induction count generalizing k with
  | zero =>
      simp [innerCrossSum, stageIntervals,
        geometricLowerSum, Rat.div_def]
  | succ count ih =>
      rw [show innerCrossSum S k (count + 1) =
        RationalCircle.Stage.cross (S.samplePoint k) (S.samplePoint (k + 1)) +
          innerCrossSum S (k + 1) count by rfl]
      rw [show stageIntervals S k (count + 1) =
        (S.parameter k, S.parameter (k + 1)) ::
          stageIntervals S (k + 1) count by rfl]
      rw [geometricLowerSum]
      rw [← ih (k + 1)]
      calc
        (RationalCircle.Stage.cross (S.samplePoint k) (S.samplePoint (k + 1)) +
            innerCrossSum S (k + 1) count) / 2 =
            RationalCircle.Stage.cross (S.samplePoint k) (S.samplePoint (k + 1)) / 2 +
              innerCrossSum S (k + 1) count / 2 := by
              rw [Rat.div_def]
              grind [Rat.add_mul]
        _ = geometricLowerStep
              (S.parameter k) (S.parameter (k + 1)) +
              innerCrossSum S (k + 1) count / 2 := by
              change RationalCircle.Stage.cross
                    (RationalCircle.Stage.point (S.parameter k))
                    (RationalCircle.Stage.point (S.parameter (k + 1))) / 2 +
                  innerCrossSum S (k + 1) count / 2 = _
              rw [← geometricLower_eq_cross_half]

private theorem outerCrossSum_half_eq_geometricUpperSum
    (S : RationalCircle.Stage) (k count : Nat) :
    outerCrossSum S k count / 2 =
      geometricUpperSum (stageIntervals S k count) := by
  induction count generalizing k with
  | zero =>
      simp [outerCrossSum, stageIntervals,
        geometricUpperSum, Rat.div_def]
  | succ count ih =>
      rw [show outerCrossSum S k (count + 1) =
        RationalCircle.Stage.cross (S.samplePoint k) (S.tangentPoint k) +
          RationalCircle.Stage.cross (S.tangentPoint k) (S.samplePoint (k + 1)) +
            outerCrossSum S (k + 1) count by rfl]
      rw [show stageIntervals S k (count + 1) =
        (S.parameter k, S.parameter (k + 1)) ::
          stageIntervals S (k + 1) count by rfl]
      rw [geometricUpperSum]
      rw [← ih (k + 1)]
      calc
        (RationalCircle.Stage.cross (S.samplePoint k) (S.tangentPoint k) +
            RationalCircle.Stage.cross (S.tangentPoint k) (S.samplePoint (k + 1)) +
              outerCrossSum S (k + 1) count) / 2 =
            (RationalCircle.Stage.cross (S.samplePoint k) (S.tangentPoint k) +
              RationalCircle.Stage.cross (S.tangentPoint k) (S.samplePoint (k + 1))) / 2 +
              outerCrossSum S (k + 1) count / 2 := by
              rw [Rat.div_def]
              grind [Rat.add_mul]
        _ = geometricUpperStep
              (S.parameter k) (S.parameter (k + 1)) +
              outerCrossSum S (k + 1) count / 2 := by
              change (RationalCircle.Stage.cross
                    (RationalCircle.Stage.point (S.parameter k))
                    (RationalCircle.Stage.tangentIntersection
                      (RationalCircle.Stage.point (S.parameter k))
                      (RationalCircle.Stage.point (S.parameter (k + 1))) ) +
                  RationalCircle.Stage.cross
                    (RationalCircle.Stage.tangentIntersection
                      (RationalCircle.Stage.point (S.parameter k))
                      (RationalCircle.Stage.point (S.parameter (k + 1))))
                    (RationalCircle.Stage.point (S.parameter (k + 1)))) / 2 +
                  outerCrossSum S (k + 1) count / 2 = _
              rw [← geometricUpper_eq_tangentCross_half]

private def midpointRefineIntervals : List (Rat × Rat) -> List (Rat × Rat)
  | [] => []
  | (p, r) :: rest =>
      (p, (p + r) / 2) :: ((p + r) / 2, r) :: midpointRefineIntervals rest

private theorem areaLoop_refineAux_intervals_eq_midpoint
    (lo hi : Rat) (intervals : List (Rat × Rat)) :
    (AreaLoopState.refineAux lo hi intervals).intervals =
      midpointRefineIntervals intervals := by
  induction intervals generalizing lo hi with
  | nil => rfl
  | cons interval rest ih =>
      rcases interval with ⟨p, r⟩
      simp [AreaLoopState.refineAux, midpointRefineIntervals, ih]

private theorem refineAreaLoopState_intervals_eq_midpoint
    (state : AreaLoopState) :
    (refineAreaLoopState state).intervals =
      midpointRefineIntervals state.intervals := by
  cases state with
  | mk lo hi intervals =>
      exact areaLoop_refineAux_intervals_eq_midpoint lo hi intervals

private theorem parameter_insertedIndex_of_refinement
    {coarse fine : RationalCircle.Stage}
    (href : RationalCircle.Stage.RefinesByDoubling coarse fine) (k : Nat) :
    fine.parameter (RationalCircle.Stage.insertedIndex k) =
      (coarse.parameter k + coarse.parameter (k + 1)) / 2 := by
  unfold RationalCircle.Stage.parameter RationalCircle.Stage.insertedIndex
    RationalCircle.Stage.RefinesByDoubling at *
  rw [href]
  rw [Rat.div_def, Rat.div_def, Rat.div_def, Rat.div_def]
  have htwo : (2 : Rat) ≠ 0 := by decide +kernel
  grind [Rat.inv_mul_rev, Rat.add_mul, Rat.mul_add, Rat.add_assoc,
    Rat.add_comm, Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]

private theorem stageIntervals_refineByDoubling
    {coarse fine : RationalCircle.Stage}
    (href : RationalCircle.Stage.RefinesByDoubling coarse fine)
    (k count : Nat) :
    stageIntervals fine (RationalCircle.Stage.refineIndex k) (2 * count) =
      midpointRefineIntervals (stageIntervals coarse k count) := by
  induction count generalizing k with
  | zero => rfl
  | succ count ih =>
      have heven0 := RationalCircle.Stage.parameter_refineIndex_of_refinement
        href k
      have hodd := parameter_insertedIndex_of_refinement href k
      have heven1 := RationalCircle.Stage.parameter_refineIndex_of_refinement
        href (k + 1)
      simp only [stageIntervals, midpointRefineIntervals]
      change
        (fine.parameter (2 * k), fine.parameter (2 * k + 1)) ::
            (fine.parameter (2 * k + 1), fine.parameter (2 * k + 1 + 1)) ::
              stageIntervals fine (2 * k + 1 + 1) (2 * count) =
          (coarse.parameter k, (coarse.parameter k + coarse.parameter (k + 1)) / 2) ::
            ((coarse.parameter k + coarse.parameter (k + 1)) / 2,
              coarse.parameter (k + 1)) ::
              midpointRefineIntervals (stageIntervals coarse (k + 1) count)
      simp only [RationalCircle.Stage.refineIndex,
        RationalCircle.Stage.insertedIndex] at heven0 heven1 hodd
      rw [heven0, hodd]
      have hindex : 2 * k + 1 + 1 = 2 * (k + 1) := by omega
      rw [hindex, heven1]
      have hnext := ih (k + 1)
      simpa [RationalCircle.Stage.refineIndex, Nat.mul_add, Nat.add_assoc,
        Nat.add_comm, Nat.mul_comm] using hnext

/-- The consecutive parameter cells of a rational circle stage are the
ordinary finite uniform mesh, written with `List.range'` so that its starting
index is explicit. -/
private theorem stageIntervals_eq_uniformRange
    (S : RationalCircle.Stage) (k count : Nat) :
    stageIntervals S k count =
      (List.range' k count).map
        (fun j => (S.parameter j, S.parameter (j + 1))) := by
  induction count generalizing k with
  | zero => simp [stageIntervals]
  | succ count ih =>
      simp only [stageIntervals, List.range'_succ, List.map_cons]
      rw [ih (k + 1)]

private theorem arctanAreaLoopIntervals_one_eq_stageIntervals (n : Nat) :
    (arctanAreaLoopState (1 : Rat) n).intervals =
      stageIntervals (RationalCircle.dyadicStage n) 0
        (RationalCircle.dyadicStage n).subdivisions := by
  induction n with
  | zero => decide +kernel
  | succ n ih =>
      rw [arctanAreaLoopState_succ,
        refineAreaLoopState_intervals_eq_midpoint, ih]
      have href := RationalCircle.dyadicStage_refinesByDoubling n
      have hsub : (RationalCircle.dyadicStage (n + 1)).subdivisions =
          2 * (RationalCircle.dyadicStage n).subdivisions := href
      rw [hsub]
      simpa [RationalCircle.Stage.refineIndex] using
        (stageIntervals_refineByDoubling href 0
          (RationalCircle.dyadicStage n).subdivisions).symm

/-- The midpoint-refined area loop at `1` has exactly the usual `2^n`
uniform rational cells of `[0,1]`.  This makes its mesh available to general
Riemann-sum theorems without exposing the circle-specific polygon machinery. -/
theorem arctanAreaLoopState_one_intervals_eq_uniform (n : Nat) :
    (arctanAreaLoopState (1 : Rat) n).intervals =
      (List.range (2 ^ n)).map
        (fun (k : Nat) =>
          ((k : Rat) / ((2 ^ n : Nat) : Rat),
            ((Nat.succ k : Nat) : Rat) / ((2 ^ n : Nat) : Rat))) := by
  rw [arctanAreaLoopIntervals_one_eq_stageIntervals,
    stageIntervals_eq_uniformRange]
  rw [← List.range_eq_range']
  simp [RationalCircle.dyadicStage, RationalCircle.dyadicSubdivisions,
    RationalCircle.Stage.parameter]

private theorem stage_innerQuarterArea_eq_geometricLowerSum (n : Nat) :
    (RationalCircle.dyadicStage n).innerQuarterArea =
      geometricLowerSum
        (arctanAreaLoopState (1 : Rat) n).intervals := by
  rw [innerQuarterArea_eq_innerCrossSum_half
    (RationalCircle.dyadicStage n) (RationalCircle.dyadicStage_positive n)]
  rw [innerCrossSum_half_eq_geometricLowerSum]
  rw [← arctanAreaLoopIntervals_one_eq_stageIntervals n]

private theorem stage_outerQuarterArea_eq_geometricUpperSum (n : Nat) :
    (RationalCircle.dyadicStage n).outerQuarterArea =
      geometricUpperSum
        (arctanAreaLoopState (1 : Rat) n).intervals := by
  rw [outerQuarterArea_eq_outerCrossSum_half
    (RationalCircle.dyadicStage n) (RationalCircle.dyadicStage_positive n)]
  rw [outerCrossSum_half_eq_geometricUpperSum]
  rw [← arctanAreaLoopIntervals_one_eq_stageIntervals n]

/-- The public area update loop and the polygonal area computation have exactly
the same rational interval at every dyadic stage. -/
theorem piCircleArea_compute_eq_piCircleAreaPolygon_compute (n : Nat) :
    piCircleArea.compute n = piCircleAreaPolygon.compute n := by
  rw [piCircleArea_compute_eq,
    RationalCircle.piCircleAreaPolygon_compute_eq_stage]
  change piCircleAreaCompute n = RationalCircle.areaIntervalAt n
  unfold piCircleAreaCompute RationalCircle.areaIntervalAt
    RationalCircle.Stage.areaInterval
  dsimp
  rw [piCircleAreaState_eq_arctanAreaLoopState_one]
  simp only [toPiAreaLoopState]
  rw [arctanAreaLoopState_hi_eq_geometricUpperSum
    (x := (1 : Rat)) (by decide +kernel) n]
  simp [arctanAreaLoopState_lo_eq_geometricLowerSum,
    stage_innerQuarterArea_eq_geometricLowerSum,
    stage_outerQuarterArea_eq_geometricUpperSum]

/-- The comparison target saying that the loop definition of pi agrees stage by
stage with four times the geometric arctangent at `1`. -/
def PiAreaCompatibility : Prop :=
  forall n : Nat,
    (((4 : Nat) * arctanGeom (1 : Rat) : RealCompute).compute n) =
      piCircleArea.compute n

theorem piAreaCompatibility : PiAreaCompatibility := by
  intro n
  have hnonneg : (0 : Rat) <= 4 := by decide +kernel
  have hstate := piCircleAreaState_eq_arctanAreaLoopState_one n
  change (RealCompute.scaleRat (4 : Rat) (arctanGeom (1 : Rat))).compute n =
    piCircleArea.compute n
  simp [RealCompute.scaleRat, RealCompute.scaleRatCompute, hnonneg,
    arctanGeom_one_compute_eq, positiveLoopComputeAtStage,
    piCircleArea, piCircleAreaCompute, hstate,
    toPiAreaLoopState]

/-- The geometric unit-sector computation, multiplied by four, has exactly
the same rational box as the circle-area pi computation at every stage.
This lives beside the two finite algorithms, so later consumers do not need
the larger pi-presentation registry merely to use the geometric bridge. -/
theorem four_arctanGeom_one_compute_eq_piCircleArea_compute (n : Nat) :
    (((4 : Nat) * arctanGeom (1 : Rat) : RealCompute).compute n) =
      piCircleArea.compute n :=
  piAreaCompatibility n

/-- The unit-slope geometric arctangent is a valid raw real. -/
theorem arctanGeom_one_valid : (arctanGeom (1 : Rat)).Valid :=
  arctanGeom_valid_on_unit (by decide +kernel) (by decide +kernel)

/-- Four times the unit-slope geometric arctangent is a valid raw real. -/
theorem four_arctanGeom_one_valid :
    (((4 : Nat) * arctanGeom (1 : Rat) : RealCompute).Valid) :=
  RealCompute.natScale_valid 4 arctanGeom_one_valid

/-- The geometric arctangent definition of pi agrees with the circle-area
definition.  The proof uses the stronger stagewise equality above and the
ordered boxes supplied by the geometric sector computation. -/
theorem four_arctanGeom_one_equiv_piCircleArea :
    (((4 : Nat) * arctanGeom (1 : Rat) : RealCompute).Equiv piCircleArea) := by
  intro n
  apply (RealCompute.compareAt_overlap_iff
    ((4 : Nat) * arctanGeom (1 : Rat) : RealCompute) piCircleArea n n).2
  rw [four_arctanGeom_one_compute_eq_piCircleArea_compute n]
  have horder := RealCompute.interval_order_of_valid
    ((4 : Nat) * arctanGeom (1 : Rat) : RealCompute)
    four_arctanGeom_one_valid n
  rw [four_arctanGeom_one_compute_eq_piCircleArea_compute n] at horder
  exact ⟨horder, horder⟩

/-- The symmetric form of the geometric arctangent pi bridge. -/
theorem piCircleArea_equiv_four_arctanGeom_one :
    piCircleArea.Equiv (((4 : Nat) * arctanGeom (1 : Rat) : RealCompute)) :=
  RealCompute.equiv_symm four_arctanGeom_one_equiv_piCircleArea

def functionRaw : PartialRealFunRaw where
  definedAt := fun _ => True
  compute := fun x _ => (arctanGeom x).compute

def representation : Elementary.Arctan.FunctionRepresentation where
  name := "arctan.geom"
  raw := functionRaw

def Valid : Prop :=
  forall x h, RealCompute.ValidCompute (functionRaw.compute x h)

def PowerSeriesAgreesOnUnit : Prop :=
  Elementary.Arctan.Equivalent Elementary.Arctan.powerSeries representation

def PowerSeriesAgreesAt (x : Rat) : Prop :=
  (arctan x).Equiv (arctanGeom x)

theorem powerSeries_equiv_geometric_of_agreement
    (h : PowerSeriesAgreesOnUnit) {x : Rat}
    (hx : Elementary.Arctan.powerSeriesDomain x) :
    (arctan x).Equiv (arctanGeom x) := by
  have hgeom : representation.raw.definedAt x := by
    simp [representation, functionRaw]
  have hagree := h x hx hgeom
  change (arctan x).Equiv (arctanGeom x) at hagree
  exact hagree

theorem geometric_equiv_powerSeries_of_agreement
    (h : PowerSeriesAgreesOnUnit) {x : Rat}
    (hx : Elementary.Arctan.powerSeriesDomain x) :
    (arctanGeom x).Equiv (arctan x) :=
  RealCompute.equiv_symm
    (powerSeries_equiv_geometric_of_agreement h hx)

theorem powerSeriesAgreesAt_of_agreement
    (h : PowerSeriesAgreesOnUnit) {x : Rat}
    (hx : Elementary.Arctan.powerSeriesDomain x) :
    PowerSeriesAgreesAt x :=
  powerSeries_equiv_geometric_of_agreement h hx

/-- The endpoint of the unit-slope arctangent branch in half-angle form.

The branch computes unit-sector area, so the slope `1` gives `pi / 4`, not
the full normalized quarter-turn `pi / 2`. -/
theorem arctanGeom_one_equiv_piCircleArea_quarter :
    (arctanGeom (1 : Rat)).Equiv
      (RationalCircle.GeometricTrig.halfQuarterTurnRaw (1 : Rat)) := by
  intro n
  apply (RealCompute.compareAt_overlap_iff
    (arctanGeom (1 : Rat))
    (RationalCircle.GeometricTrig.halfQuarterTurnRaw (1 : Rat)) n n).2
  change QInterval.Overlaps
    ((arctanGeom (1 : Rat)).compute n)
    ((RealCompute.scaleRat ((1 : Rat) / 4) piCircleArea).compute n)
  unfold RealCompute.scaleRat RealCompute.scaleRatCompute
  simp only [if_pos (by decide +kernel : (0 : Rat) <= (1 : Rat) / 4)]
  rw [← piAreaCompatibility n]
  have hvalid : (arctanGeom (1 : Rat)).Valid :=
    arctanGeom_valid_on_unit (by decide +kernel) (by decide +kernel)
  have horder := RealCompute.interval_order_of_valid
    (arctanGeom (1 : Rat)) hvalid n
  unfold QInterval.Overlaps
  change
    ((arctanGeom (1 : Rat)).compute n).lo <=
        ((1 : Rat) / 4) * (4 * ((arctanGeom (1 : Rat)).compute n).hi) /\
      ((1 : Rat) / 4) * (4 * ((arctanGeom (1 : Rat)).compute n).lo) <=
        ((arctanGeom (1 : Rat)).compute n).hi
  have hquarter_four : ((1 : Rat) / 4) * 4 = 1 := by decide +kernel
  have hcancel (q : Rat) : ((1 : Rat) / 4) * (4 * q) = q := by
    calc
      ((1 : Rat) / 4) * (4 * q) = (((1 : Rat) / 4) * 4) * q :=
        (Rat.mul_assoc _ _ _).symm
      _ = q := by rw [hquarter_four, Rat.one_mul]
  constructor
  · rw [hcancel]
    exact horder
  · rw [hcancel]
    exact horder

/-- Doubling the unit-slope sector computation and taking the geometric
quarter turn produce literally the same rational interval at every stage. -/
theorem two_arctanGeom_one_compute_eq_quarterTurnRaw_one_compute (n : Nat) :
    (((2 : Nat) * arctanGeom (1 : Rat) : RealCompute).compute n) =
      ((RationalCircle.GeometricTrig.quarterTurnRaw (1 : Rat)).compute n) := by
  change
    ((RealCompute.scaleRat (2 : Rat) (arctanGeom (1 : Rat))).compute n)
      = ((RealCompute.scaleRat ((1 : Rat) / 2) piCircleArea).compute n)
  unfold RealCompute.scaleRat RealCompute.scaleRatCompute
  simp only [if_pos (by decide +kernel : (0 : Rat) <= 2),
    if_pos (by decide +kernel : (0 : Rat) <= (1 : Rat) / 2)]
  rw [← piAreaCompatibility n]
  have hhalfFour : ((1 : Rat) / 2) * 4 = 2 := by decide +kernel
  have hscale (q : Rat) : ((1 : Rat) / 2) * (4 * q) = 2 * q := by
    calc
      ((1 : Rat) / 2) * (4 * q) = (((1 : Rat) / 2) * 4) * q :=
        (Rat.mul_assoc _ _ _).symm
      _ = 2 * q := by rw [hhalfFour]
  change
    ({ lo := 2 * ((arctanGeom (1 : Rat)).compute n).lo,
       hi := 2 * ((arctanGeom (1 : Rat)).compute n).hi } : QInterval)
      = ({ lo := ((1 : Rat) / 2) *
          (4 * ((arctanGeom (1 : Rat)).compute n).lo),
           hi := ((1 : Rat) / 2) *
           (4 * ((arctanGeom (1 : Rat)).compute n).hi) } : QInterval)
  rw [hscale, hscale]

/-- Doubling the unit-slope sector computation gives the normalized geometric
quarter turn.  This derives raw equivalence from the stronger stage equality. -/
theorem two_arctanGeom_one_equiv_quarterTurnRaw_one :
    (((2 : Nat) * arctanGeom (1 : Rat) : RealCompute).Equiv
      (RationalCircle.GeometricTrig.quarterTurnRaw (1 : Rat))) := by
  intro n
  apply (RealCompute.compareAt_overlap_iff
    ((2 : Nat) * arctanGeom (1 : Rat) : RealCompute)
    (RationalCircle.GeometricTrig.quarterTurnRaw (1 : Rat)) n n).2
  rw [← two_arctanGeom_one_compute_eq_quarterTurnRaw_one_compute]
  have hvalid : (arctanGeom (1 : Rat)).Valid :=
    arctanGeom_valid_on_unit (by decide +kernel) (by decide +kernel)
  have hscaledValid : ((2 : Nat) * arctanGeom (1 : Rat) : RealCompute).Valid :=
    RealCompute.natScale_valid 2 hvalid
  have horder := RealCompute.interval_order_of_valid
    ((2 : Nat) * arctanGeom (1 : Rat) : RealCompute) hscaledValid n
  exact ⟨horder, horder⟩

/-! The next certificate is a chart-relative orientation statement.  It
combines the exact endpoint displacement of the tangent-addition chart with
the rational circle cross-product formula.  Thus the orientation of the
translated chord is controlled by the finite rational increment `v`, without
introducing an angle-valued quantity. -/

theorem chartAdd_cross_orientation_certificate {u v : Rat}
    (hden : RationalCircle.Trigonometry.chartAddDen u v ≠ 0) :
    RationalCircle.Stage.cross
        (RationalCircle.Trigonometry.point u)
        (RationalCircle.Trigonometry.point
          (RationalCircle.Trigonometry.chartAddParameter u v)) =
      (2 * v) / (1 + v * v) := by
  rw [← RationalCircle.Trigonometry.composedPoint_eq_point_chartAdd hden]
  unfold RationalCircle.Trigonometry.composedPoint
  unfold RationalCircle.Stage.cross RationalCircle.Trigonometry.pointMul
  unfold RationalCircle.Trigonometry.point RationalCircle.Stage.point
  simp [Rat.div_def]
  have hu : 1 + u * u ≠ 0 :=
    Rat.ne_of_gt (RationalCircle.Stage.one_add_square_pos u)
  have hv : 1 + v * v ≠ 0 :=
    Rat.ne_of_gt (RationalCircle.Stage.one_add_square_pos v)
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.add_assoc,
    Rat.add_comm, Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]

end ArctanGeometry

namespace RationalCircle

namespace GeometricTrig

/-- A first-quadrant angle exhibited by a rational slope in the circle chart.

The certificate is intentionally phrased in terms of the sector-area
arctangent: if the normalized quarter-turn angle is `t * pi / 2`, the
arctangent of its stereographic slope is the *half-angle* `t * pi / 4`.
The attached coordinates are therefore exactly the rational-circle sine and
cosine coordinates selected by that arctangent identity.  A later raw-slope
extension will use the same interface with interval coordinates. -/
structure FirstQuadrantArctanWitness (t : QuarterTurn) where
  slope : Rat
  slope_nonneg : 0 <= slope
  slope_le_one : slope <= 1
  arctan_geom_eq_half_angle :
    (ArctanGeometry.arctanGeom slope).Equiv (halfQuarterTurnRaw t)

namespace FirstQuadrantArctanWitness

/-- The rational-circle cosine coordinate selected by an arctangent witness. -/
def cosine {t : QuarterTurn} (W : FirstQuadrantArctanWitness t) : Rat :=
  Trigonometry.cos W.slope

/-- The rational-circle sine coordinate selected by an arctangent witness. -/
def sine {t : QuarterTurn} (W : FirstQuadrantArctanWitness t) : Rat :=
  Trigonometry.sin W.slope

theorem slope_mem_unit {t : QuarterTurn} (W : FirstQuadrantArctanWitness t) :
    0 <= W.slope /\ W.slope <= 1 :=
  ⟨W.slope_nonneg, W.slope_le_one⟩

/-- The general arctangent-to-coordinate bridge.

It is deliberately independent of any individual special-value calculation:
once a slope is shown to have sector area `t*pi/4`, its sine and cosine are
the two coordinates of the same rational-circle point. -/
theorem arctan_to_sine_cosine_coordinates
    {t : QuarterTurn} (W : FirstQuadrantArctanWitness t) :
    (ArctanGeometry.arctanGeom W.slope).Equiv (halfQuarterTurnRaw t) /\
      W.cosine = (1 - W.slope * W.slope) / (1 + W.slope * W.slope) /\
      W.sine = (2 * W.slope) / (1 + W.slope * W.slope) /\
      sq W.sine + sq W.cosine = 1 := by
  refine ⟨W.arctan_geom_eq_half_angle, ?_, ?_, ?_⟩
  · exact Trigonometry.cos_eq W.slope
  · exact Trigonometry.sin_eq W.slope
  · exact Trigonometry.sin_sq_add_cos_sq W.slope

/-- The zero-degree endpoint of the arctangent half-angle construction. -/
theorem arctanGeom_zero_equiv_halfQuarterTurnRaw_zero :
    (ArctanGeometry.arctanGeom (0 : Rat)).Equiv
      (halfQuarterTurnRaw (0 : QuarterTurn)) := by
  rw [ArctanGeometry.arctanGeom_zero]
  intro n
  apply (RealCompute.compareAt_overlap_iff
    (RealCompute.ofRat (0 : Rat)) (halfQuarterTurnRaw (0 : QuarterTurn)) n n).2
  unfold halfQuarterTurnRaw RealCompute.scaleRat RealCompute.scaleRatCompute
  change ({ lo := 0, hi := 0 } : QInterval).Overlaps
    (if 0 <= (0 : Rat) / 4 then
      ({ lo := (0 : Rat) / 4 * (piCircleArea.compute n).lo,
         hi := (0 : Rat) / 4 * (piCircleArea.compute n).hi } : QInterval)
    else
      ({ lo := (0 : Rat) / 4 * (piCircleArea.compute n).hi,
         hi := (0 : Rat) / 4 * (piCircleArea.compute n).lo } : QInterval))
  rw [if_pos (by decide +kernel : (0 : Rat) <= 0 / 4)]
  unfold QInterval.Overlaps
  have hzero : (0 : Rat) / 4 = 0 := by decide +kernel
  rw [hzero]
  simp

/-- A reusable witness for the zero-degree special-value row. -/
def zero : FirstQuadrantArctanWitness (0 : QuarterTurn) where
  slope := 0
  slope_nonneg := by decide +kernel
  slope_le_one := by decide +kernel
  arctan_geom_eq_half_angle := arctanGeom_zero_equiv_halfQuarterTurnRaw_zero

/-- A reusable witness for the ninety-degree special-value row. -/
def one : FirstQuadrantArctanWitness (1 : QuarterTurn) where
  slope := 1
  slope_nonneg := by decide +kernel
  slope_le_one := by decide +kernel
  arctan_geom_eq_half_angle :=
    ArctanGeometry.arctanGeom_one_equiv_piCircleArea_quarter

/-- Exact coordinate values selected by the zero-degree arctangent witness. -/
theorem zero_coordinates :
    zero.cosine = 1 /\ zero.sine = 0 /\
      sq zero.sine + sq zero.cosine = 1 := by
  decide +kernel

/-- Exact coordinate values selected by the ninety-degree arctangent witness. -/
theorem one_coordinates :
    one.cosine = 0 /\ one.sine = 1 /\
      sq one.sine + sq one.cosine = 1 := by
  decide +kernel

theorem cosine_eq_chart_cosine
    {t : QuarterTurn} (W : FirstQuadrantArctanWitness t) :
    W.cosine = Trigonometry.cos W.slope := rfl

theorem sine_eq_chart_sine
    {t : QuarterTurn} (W : FirstQuadrantArctanWitness t) :
    W.sine = Trigonometry.sin W.slope := rfl

end FirstQuadrantArctanWitness

end GeometricTrig

end RationalCircle

end ComputableAnalysis


