-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Analysis_ComplexMultiplication
-- name    : liuyao_ca_fd889115_k1_Analysis_ComplexMultiplication
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T17:51:24.280211+00:00
-- url     : https://prove2.me/theorems/ed09b63e-bf7f-41b7-ac24-e14d63e186a2
-- title:
--   Computable analysis · ComplexMultiplication · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableAnalysis/ComplexMultiplication.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_ComplexAffine

set_option autoImplicit true

/-!
# Finite interval multiplication for complex boxes

This module proves the order and containment facts for the literal four-corner
rational interval product used by `QBox.mul`.  It is deliberately only the
finite-box layer: turning a product of arbitrary `ComplexCompute` values into a
valid shrinking raw computation still needs its own width-modulus theorem.

No completed complex plane or imported real-analysis library is used here.
-/

namespace ComputableAnalysis

namespace QBox

private theorem minRat_le_left (a b : Rat) : minRat a b <= a := by
  unfold minRat
  split <;> grind

private theorem minRat_le_right (a b : Rat) : minRat a b <= b := by
  unfold minRat
  split <;> grind

private theorem le_minRat {x a b : Rat}
    (hxa : x <= a) (hxb : x <= b) : x <= minRat a b := by
  unfold minRat
  split <;> assumption

private theorem le_maxRat2_left (a b : Rat) : a <= maxRat2 a b := by
  unfold maxRat2
  split <;> grind

private theorem le_maxRat2_right (a b : Rat) : b <= maxRat2 a b := by
  unfold maxRat2
  split <;> grind

private theorem maxRat2_le {a b x : Rat}
    (hax : a <= x) (hbx : b <= x) : maxRat2 a b <= x := by
  unfold maxRat2
  split <;> assumption

private theorem min4_le_first (a b c d : Rat) : min4 a b c d <= a := by
  exact Rat.le_trans (minRat_le_left _ _) (minRat_le_left _ _)

private theorem min4_le_second (a b c d : Rat) : min4 a b c d <= b := by
  exact Rat.le_trans (minRat_le_left _ _) (minRat_le_right _ _)

private theorem min4_le_third (a b c d : Rat) : min4 a b c d <= c := by
  exact Rat.le_trans (minRat_le_right _ _) (minRat_le_left _ _)

private theorem min4_le_fourth (a b c d : Rat) : min4 a b c d <= d := by
  exact Rat.le_trans (minRat_le_right _ _) (minRat_le_right _ _)

private theorem first_le_max4 (a b c d : Rat) : a <= max4 a b c d := by
  exact Rat.le_trans (le_maxRat2_left a b)
    (le_maxRat2_left (maxRat2 a b) (maxRat2 c d))

private theorem second_le_max4 (a b c d : Rat) : b <= max4 a b c d := by
  exact Rat.le_trans (le_maxRat2_right a b)
    (le_maxRat2_left (maxRat2 a b) (maxRat2 c d))

private theorem third_le_max4 (a b c d : Rat) : c <= max4 a b c d := by
  exact Rat.le_trans (le_maxRat2_left c d)
    (le_maxRat2_right (maxRat2 a b) (maxRat2 c d))

private theorem fourth_le_max4 (a b c d : Rat) : d <= max4 a b c d := by
  exact Rat.le_trans (le_maxRat2_right c d)
    (le_maxRat2_right (maxRat2 a b) (maxRat2 c d))

private theorem le_min4 {x a b c d : Rat}
    (hxa : x <= a) (hxb : x <= b) (hxc : x <= c) (hxd : x <= d) :
    x <= min4 a b c d := by
  exact le_minRat (le_minRat hxa hxb) (le_minRat hxc hxd)

private theorem max4_le {a b c d x : Rat}
    (hax : a <= x) (hbx : b <= x) (hcx : c <= x) (hdx : d <= x) :
    max4 a b c d <= x := by
  exact maxRat2_le (maxRat2_le hax hbx) (maxRat2_le hcx hdx)

private theorem mul_le_mul_of_nonpos_left {a b c : Rat}
    (hab : a <= b) (hc : c <= 0) : c * b <= c * a := by
  have hnc : 0 <= -c := by grind
  have h := Rat.mul_le_mul_of_nonneg_left hab hnc
  grind [Rat.neg_mul]

private theorem mul_le_mul_of_nonpos_right {a b c : Rat}
    (hab : a <= b) (hc : c <= 0) : b * c <= a * c := by
  have h := mul_le_mul_of_nonpos_left hab hc
  simpa [Rat.mul_comm] using h

private theorem mul_nonpos_of_nonneg_of_nonpos {x y : Rat}
    (hx : 0 <= x) (hy : y <= 0) : x * y <= 0 := by
  have hny : 0 <= -y := by grind
  have h : 0 <= x * (-y) := Rat.mul_nonneg hx hny
  grind [Rat.mul_neg]

private theorem mul_nonneg_of_nonpos {x y : Rat}
    (hx : x <= 0) (hy : y <= 0) : 0 <= x * y := by
  have hnx : 0 <= -x := by grind
  have hny : 0 <= -y := by grind
  have h : 0 <= (-x) * (-y) := Rat.mul_nonneg hnx hny
  grind [Rat.neg_mul, Rat.mul_neg, Rat.neg_neg]

private theorem min4_transpose (a b c d : Rat) :
    min4 a b c d = min4 a c b d := by
  apply Rat.le_antisymm
  · apply le_min4
    · exact Rat.le_trans (minRat_le_left _ _)
        (minRat_le_left _ _)
    · exact Rat.le_trans (minRat_le_right _ _)
        (minRat_le_left _ _)
    · exact Rat.le_trans (minRat_le_left _ _)
        (minRat_le_right _ _)
    · exact Rat.le_trans (minRat_le_right _ _)
        (minRat_le_right _ _)
  · apply le_min4
    · exact Rat.le_trans (minRat_le_left _ _)
        (minRat_le_left _ _)
    · exact Rat.le_trans (minRat_le_right _ _)
        (minRat_le_left _ _)
    · exact Rat.le_trans (minRat_le_left _ _)
        (minRat_le_right _ _)
    · exact Rat.le_trans (minRat_le_right _ _)
        (minRat_le_right _ _)

private theorem max4_transpose (a b c d : Rat) :
    max4 a b c d = max4 a c b d := by
  apply Rat.le_antisymm
  · apply max4_le
    · exact Rat.le_trans (le_maxRat2_left _ _)
        (le_maxRat2_left _ _)
    · exact Rat.le_trans (le_maxRat2_left _ _)
        (le_maxRat2_right _ _)
    · exact Rat.le_trans (le_maxRat2_right _ _)
        (le_maxRat2_left _ _)
    · exact Rat.le_trans (le_maxRat2_right _ _)
        (le_maxRat2_right _ _)
  · apply max4_le
    · exact Rat.le_trans (le_maxRat2_left _ _)
        (le_maxRat2_left _ _)
    · exact Rat.le_trans (le_maxRat2_left _ _)
        (le_maxRat2_right _ _)
    · exact Rat.le_trans (le_maxRat2_right _ _)
        (le_maxRat2_left _ _)
    · exact Rat.le_trans (le_maxRat2_right _ _)
        (le_maxRat2_right _ _)

/-- The literal four-corner interval product is symmetric in its two input
intervals. -/
theorem mulRealInterval_comm (a b c d : Rat) :
    mulRealInterval a b c d = mulRealInterval c d a b := by
  unfold mulRealInterval
  simp only [Rat.mul_comm]
  rw [min4_transpose, max4_transpose]

/-- Multiplication by the exact zero interval is the exact zero interval. -/
theorem mulRealInterval_zero_left (c d : Rat) :
    mulRealInterval 0 0 c d = { lo := 0, hi := 0 } := by
  simp [mulRealInterval, min4, max4, minRat, maxRat2]

/-- If the left complex box lies on the real axis, the real coordinate of
its complex product is exactly the ordinary real interval product. -/
theorem mul_realPart_of_real_left (A B : QBox)
    (hlo : A.lo.im = 0) (hhi : A.hi.im = 0) :
    ({ lo := (QBox.mul A B).lo.re,
       hi := (QBox.mul A B).hi.re } : QInterval) =
      mulRealInterval A.lo.re A.hi.re B.lo.re B.hi.re := by
  unfold QBox.mul
  rw [hlo, hhi, mulRealInterval_zero_left]
  let R := mulRealInterval A.lo.re A.hi.re B.lo.re B.hi.re
  change ({ lo := R.lo - 0, hi := R.hi - 0 } : QInterval) = R
  cases R
  congr <;> grind

/-- The literal four-corner product contains every product of two rational
points enclosed by its input intervals. -/
theorem mulRealInterval_contains {a b c d x y : Rat}
    (hax : a <= x) (hxb : x <= b)
    (hcy : c <= y) (hyd : y <= d) :
    (mulRealInterval a b c d).lo <= x * y /\
      x * y <= (mulRealInterval a b c d).hi := by
  unfold mulRealInterval
  constructor
  · by_cases hx : 0 <= x
    · by_cases hy : 0 <= y
      · by_cases hc : 0 <= c
        · calc
            min4 (a * c) (a * d) (b * c) (b * d) <= a * c :=
              min4_le_first _ _ _ _
            _ <= x * c := Rat.mul_le_mul_of_nonneg_right hax hc
            _ <= x * y := Rat.mul_le_mul_of_nonneg_left hcy hx
        · have hc0 : c <= 0 := by grind
          calc
            min4 (a * c) (a * d) (b * c) (b * d) <= b * c :=
              min4_le_third _ _ _ _
            _ <= x * c := mul_le_mul_of_nonpos_right hxb hc0
            _ <= x * y := Rat.mul_le_mul_of_nonneg_left hcy hx
      · have hy0 : y <= 0 := by grind
        have hc0 : c <= 0 := Rat.le_trans hcy hy0
        calc
          min4 (a * c) (a * d) (b * c) (b * d) <= b * c :=
            min4_le_third _ _ _ _
          _ <= x * c := mul_le_mul_of_nonpos_right hxb hc0
          _ <= x * y := Rat.mul_le_mul_of_nonneg_left hcy hx
    · have hx0 : x <= 0 := by grind
      by_cases hy : 0 <= y
      · have hd0 : 0 <= d := Rat.le_trans hy hyd
        calc
          min4 (a * c) (a * d) (b * c) (b * d) <= a * d :=
            min4_le_second _ _ _ _
          _ <= x * d := Rat.mul_le_mul_of_nonneg_right hax hd0
          _ <= x * y := mul_le_mul_of_nonpos_left hyd hx0
      · have hy0 : y <= 0 := by grind
        by_cases hd : 0 <= d
        · have hdx : d * x <= 0 := mul_nonpos_of_nonneg_of_nonpos hd hx0
          have hxd : x * d <= 0 := by
            simpa [Rat.mul_comm] using hdx
          have hxy : 0 <= x * y := mul_nonneg_of_nonpos hx0 hy0
          calc
            min4 (a * c) (a * d) (b * c) (b * d) <= a * d :=
              min4_le_second _ _ _ _
            _ <= x * d := Rat.mul_le_mul_of_nonneg_right hax hd
            _ <= 0 := hxd
            _ <= x * y := hxy
        · have hd0 : d <= 0 := by grind
          calc
            min4 (a * c) (a * d) (b * c) (b * d) <= b * d :=
              min4_le_fourth _ _ _ _
            _ <= x * d := mul_le_mul_of_nonpos_right hxb hd0
            _ <= x * y := mul_le_mul_of_nonpos_left hyd hx0
  · by_cases hx : 0 <= x
    · by_cases hy : 0 <= y
      · calc
          x * y <= b * y := Rat.mul_le_mul_of_nonneg_right hxb hy
          _ <= b * d := Rat.mul_le_mul_of_nonneg_left hyd (by grind)
          _ <= max4 (a * c) (a * d) (b * c) (b * d) :=
            fourth_le_max4 _ _ _ _
      · have hy0 : y <= 0 := by grind
        by_cases ha : 0 <= a
        · calc
            x * y <= a * y := mul_le_mul_of_nonpos_right hax hy0
            _ <= a * d := Rat.mul_le_mul_of_nonneg_left hyd ha
            _ <= max4 (a * c) (a * d) (b * c) (b * d) :=
              second_le_max4 _ _ _ _
        · by_cases hd : 0 <= d
          · have hxy : x * y <= 0 := mul_nonpos_of_nonneg_of_nonpos hx hy0
            have hb0 : 0 <= b := Rat.le_trans hx hxb
            have hbd : 0 <= b * d := Rat.mul_nonneg hb0 hd
            calc
              x * y <= 0 := hxy
              _ <= b * d := hbd
              _ <= max4 (a * c) (a * d) (b * c) (b * d) :=
                fourth_le_max4 _ _ _ _
          · have hd0 : d <= 0 := by grind
            calc
              x * y <= x * d := Rat.mul_le_mul_of_nonneg_left hyd hx
              _ <= a * d := mul_le_mul_of_nonpos_right hax hd0
              _ <= max4 (a * c) (a * d) (b * c) (b * d) :=
                second_le_max4 _ _ _ _
    · have hx0 : x <= 0 := by grind
      by_cases hy : 0 <= y
      · by_cases hc : 0 <= c
        · calc
            x * y <= x * c := mul_le_mul_of_nonpos_left hcy hx0
            _ <= b * c := Rat.mul_le_mul_of_nonneg_right hxb hc
            _ <= max4 (a * c) (a * d) (b * c) (b * d) :=
              third_le_max4 _ _ _ _
        · have hc0 : c <= 0 := by grind
          have hyx : y * x <= 0 := mul_nonpos_of_nonneg_of_nonpos hy hx0
          have hxy : x * y <= 0 := by
            simpa [Rat.mul_comm] using hyx
          have hac : 0 <= a * c :=
            mul_nonneg_of_nonpos (Rat.le_trans hax hx0) hc0
          calc
            x * y <= 0 := hxy
            _ <= a * c := hac
            _ <= max4 (a * c) (a * d) (b * c) (b * d) :=
              first_le_max4 _ _ _ _
      · have hy0 : y <= 0 := by grind
        calc
          x * y <= a * y := mul_le_mul_of_nonpos_right hax hy0
          _ <= a * c :=
            mul_le_mul_of_nonpos_left hcy (Rat.le_trans hax hx0)
          _ <= max4 (a * c) (a * d) (b * c) (b * d) :=
            first_le_max4 _ _ _ _

/-- A four-corner product interval is ordered whenever its two input
intervals are ordered. -/
theorem mulRealInterval_ordered {a b c d : Rat}
    (hab : a <= b) (hcd : c <= d) :
    (mulRealInterval a b c d).lo <= (mulRealInterval a b c d).hi := by
  have h := mulRealInterval_contains (a := a) (b := b) (c := c) (d := d)
    (x := a) (y := c) Rat.le_refl hab Rat.le_refl hcd
  exact Rat.le_trans h.1 h.2

/-- Refining both input intervals refines their literal four-corner product
interval.  This is the finite nesting fact required before a raw complex
product can be made valid. -/
theorem mulRealInterval_nested
    {a b c d a' b' c' d' : Rat}
    (haa' : a <= a') (ha'b' : a' <= b') (hb'b : b' <= b)
    (hcc' : c <= c') (hc'd' : c' <= d') (hd'd : d' <= d) :
    (mulRealInterval a b c d).lo <= (mulRealInterval a' b' c' d').lo /\
      (mulRealInterval a' b' c' d').hi <= (mulRealInterval a b c d).hi := by
  have h_ac := mulRealInterval_contains
    (a := a) (b := b) (c := c) (d := d) (x := a') (y := c')
    haa' (Rat.le_trans ha'b' hb'b) hcc' (Rat.le_trans hc'd' hd'd)
  have h_ad := mulRealInterval_contains
    (a := a) (b := b) (c := c) (d := d) (x := a') (y := d')
    haa' (Rat.le_trans ha'b' hb'b) (Rat.le_trans hcc' hc'd') hd'd
  have h_bc := mulRealInterval_contains
    (a := a) (b := b) (c := c) (d := d) (x := b') (y := c')
    (Rat.le_trans haa' ha'b') hb'b hcc' (Rat.le_trans hc'd' hd'd)
  have h_bd := mulRealInterval_contains
    (a := a) (b := b) (c := c) (d := d) (x := b') (y := d')
    (Rat.le_trans haa' ha'b') hb'b (Rat.le_trans hcc' hc'd') hd'd
  unfold mulRealInterval
  exact ⟨le_min4 h_ac.1 h_ad.1 h_bc.1 h_bd.1,
    max4_le h_ac.2 h_ad.2 h_bc.2 h_bd.2⟩

/-- Every coordinate of a rational complex box is bounded in absolute value
by the supplied rational radius.  This is the finite hypothesis used by the
product-width estimate below. -/
def CoordinateBounded (A : QBox) (B : Rat) : Prop :=
  qabs A.lo.re <= B /\ qabs A.hi.re <= B /\
    qabs A.lo.im <= B /\ qabs A.hi.im <= B

/-- A strictly positive rational radius containing all four coordinates of a
box.  Adding one is intentional: it gives a nonzero denominator in the
eventual product-width schedule without any case distinction. -/
def coordinateRadius (A : QBox) : Rat :=
  1 + max4 (qabs A.lo.re) (qabs A.hi.re) (qabs A.lo.im) (qabs A.hi.im)

theorem coordinateRadius_pos (A : QBox) : 0 < A.coordinateRadius := by
  unfold coordinateRadius
  have hmax : 0 <= max4 (qabs A.lo.re) (qabs A.hi.re)
      (qabs A.lo.im) (qabs A.hi.im) :=
    Rat.le_trans (qabs_nonneg A.lo.re)
      (first_le_max4 _ _ _ _)
  grind

theorem coordinateBounded_radius (A : QBox) :
    A.CoordinateBounded A.coordinateRadius := by
  unfold CoordinateBounded coordinateRadius
  constructor
  · have hfirst : qabs A.lo.re <=
        max4 (qabs A.lo.re) (qabs A.hi.re) (qabs A.lo.im) (qabs A.hi.im) :=
      first_le_max4 _ _ _ _
    exact Rat.le_trans hfirst (by grind)
  constructor
  · have hsecond : qabs A.hi.re <=
        max4 (qabs A.lo.re) (qabs A.hi.re) (qabs A.lo.im) (qabs A.hi.im) :=
      second_le_max4 _ _ _ _
    exact Rat.le_trans hsecond (by grind)
  constructor
  · have hthird : qabs A.lo.im <=
        max4 (qabs A.lo.re) (qabs A.hi.re) (qabs A.lo.im) (qabs A.hi.im) :=
      third_le_max4 _ _ _ _
    exact Rat.le_trans hthird (by grind)
  · have hfourth : qabs A.hi.im <=
        max4 (qabs A.lo.re) (qabs A.hi.re) (qabs A.lo.im) (qabs A.hi.im) :=
      fourth_le_max4 _ _ _ _
    exact Rat.le_trans hfourth (by grind)

theorem CoordinateBounded.mono {A : QBox} {B C : Rat}
    (hA : A.CoordinateBounded B) (hBC : B <= C) :
    A.CoordinateBounded C := by
  exact ⟨Rat.le_trans hA.1 hBC, Rat.le_trans hA.2.1 hBC,
    Rat.le_trans hA.2.2.1 hBC, Rat.le_trans hA.2.2.2 hBC⟩

private theorem qabs_le_of_endpoint_bounds {a b x B : Rat}
    (ha : qabs a <= B) (hb : qabs b <= B)
    (hax : a <= x) (hxb : x <= b) : qabs x <= B := by
  apply qabs_le_of_neg_le_le
  · calc
      -B <= -qabs a := Rat.neg_le_neg ha
      _ <= a := neg_qabs_le_self a
      _ <= x := hax
  · calc
      x <= b := hxb
      _ <= qabs b := self_le_qabs b
      _ <= B := hb

/-- A box nested in an ordered coordinate-bounded box inherits that rational
coordinate bound. -/
theorem coordinateBounded_of_nested {inner outer : QBox} {B : Rat}
    (hinner : inner.Ordered) (hnested : inner.NestedIn outer)
    (houter : outer.CoordinateBounded B) : inner.CoordinateBounded B := by
  rcases houter with ⟨horelo, horehi, hoimlo, hoimhi⟩
  constructor
  · apply qabs_le_of_endpoint_bounds horelo horehi
    · exact hnested.1.1
    · exact Rat.le_trans hinner.1 hnested.2.1
  constructor
  · apply qabs_le_of_endpoint_bounds horelo horehi
    · exact Rat.le_trans hnested.1.1 hinner.1
    · exact hnested.2.1
  constructor
  · apply qabs_le_of_endpoint_bounds hoimlo hoimhi
    · exact hnested.1.2
    · exact Rat.le_trans hinner.2 hnested.2.2
  · apply qabs_le_of_endpoint_bounds hoimlo hoimhi
    · exact Rat.le_trans hnested.1.2 hinner.2
    · exact hnested.2.2

/-- The rational center of an ordered complex box is an enclosed rational
point. -/
theorem center_mem {A : QBox} (hA : A.Ordered) :
    A.lo <= A.center /\ A.center <= A.hi := by
  have hre := QInterval.midpoint_mem
    (I := { lo := A.lo.re, hi := A.hi.re }) hA.1
  have him := QInterval.midpoint_mem
    (I := { lo := A.lo.im, hi := A.hi.im }) hA.2
  simp only [QBox.center, QComplex.le_def]
  exact ⟨⟨by simpa [QInterval.midpoint] using hre.1,
      by simpa [QInterval.midpoint] using him.1⟩,
    ⟨by simpa [QInterval.midpoint] using hre.2,
      by simpa [QInterval.midpoint] using him.2⟩⟩

/-- Coordinatewise addition of boxes contains the sum of any enclosed
rational complex points. -/
theorem add_contains {A C : QBox} {x y : QComplex}
    (hxlo : A.lo <= x) (hxhi : x <= A.hi)
    (hylo : C.lo <= y) (hyhi : y <= C.hi) :
    (add A C).lo <= QComplex.add x y /\
      QComplex.add x y <= (add A C).hi := by
  change
    (A.lo.re + C.lo.re <= x.re + y.re /\
      A.lo.im + C.lo.im <= x.im + y.im) /\
    (x.re + y.re <= A.hi.re + C.hi.re /\
      x.im + y.im <= A.hi.im + C.hi.im)
  exact ⟨⟨rat_add_le_add hxlo.1 hylo.1,
      rat_add_le_add hxlo.2 hylo.2⟩,
    ⟨rat_add_le_add hxhi.1 hyhi.1,
      rat_add_le_add hxhi.2 hyhi.2⟩⟩

/-- Scaling a box by an exact rational contains the scaled enclosed point,
with endpoint reversal handled in the negative case. -/
theorem scaleRat_contains {r : Rat} {A : QBox} {x : QComplex}
    (hxlo : A.lo <= x) (hxhi : x <= A.hi) :
    (scaleRat r A).lo <= QComplex.scaleRat r x /\
      QComplex.scaleRat r x <= (scaleRat r A).hi := by
  by_cases hr : 0 <= r
  · simp only [scaleRat, QComplex.scaleRat, if_pos hr]
    exact ⟨
      ⟨Rat.mul_le_mul_of_nonneg_left hxlo.1 hr,
        Rat.mul_le_mul_of_nonneg_left hxlo.2 hr⟩,
      ⟨Rat.mul_le_mul_of_nonneg_left hxhi.1 hr,
        Rat.mul_le_mul_of_nonneg_left hxhi.2 hr⟩⟩
  · have hr0 : r <= 0 := by grind
    simp only [scaleRat, QComplex.scaleRat, if_neg hr]
    exact ⟨
      ⟨mul_le_mul_of_nonpos_left hxhi.1 hr0,
        mul_le_mul_of_nonpos_left hxhi.2 hr0⟩,
      ⟨mul_le_mul_of_nonpos_left hxlo.1 hr0,
        mul_le_mul_of_nonpos_left hxlo.2 hr0⟩⟩

private theorem product_deviation_bound
    {a b c d x y B : Rat}
    (hab : a <= b) (hcd : c <= d)
    (ha : qabs a <= B)
    (hc : qabs c <= B) (hd : qabs d <= B)
    (hax : a <= x) (hxb : x <= b)
    (hcy : c <= y) (hyd : y <= d) :
    qabs (x * y - a * c) <= B * ((b - a) + (d - c)) := by
  have hxgap : qabs (x - a) <= b - a :=
    qabs_sub_le_of_common_bounds hax hxb Rat.le_refl hab
  have hygap : qabs (y - c) <= d - c :=
    qabs_sub_le_of_common_bounds hcy hyd Rat.le_refl hcd
  have hyabs : qabs y <= B :=
    qabs_le_of_endpoint_bounds hc hd hcy hyd
  have hwidthx : 0 <= b - a := by grind [Rat.sub_eq_add_neg]
  have hwidthy : 0 <= d - c := by grind [Rat.sub_eq_add_neg]
  have hleft : qabs (x - a) * qabs y <= (b - a) * B := by
    calc
      qabs (x - a) * qabs y <= (b - a) * qabs y :=
        Rat.mul_le_mul_of_nonneg_right hxgap (qabs_nonneg y)
      _ <= (b - a) * B :=
        Rat.mul_le_mul_of_nonneg_left hyabs hwidthx
  have hright : qabs a * qabs (y - c) <= B * (d - c) := by
    calc
      qabs a * qabs (y - c) <= qabs a * (d - c) :=
        Rat.mul_le_mul_of_nonneg_left hygap (qabs_nonneg a)
      _ <= B * (d - c) :=
        Rat.mul_le_mul_of_nonneg_right ha hwidthy
  have hdecompose :
      x * y - a * c = (x - a) * y + a * (y - c) := by
    grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul, Rat.mul_assoc,
      Rat.add_assoc, Rat.add_comm, Rat.mul_comm]
  calc
    qabs (x * y - a * c) = qabs ((x - a) * y + a * (y - c)) := by
      rw [hdecompose]
    _ <= qabs ((x - a) * y) + qabs (a * (y - c)) :=
      qabs_add_le _ _
    _ = qabs (x - a) * qabs y + qabs a * qabs (y - c) := by
      rw [qabs_mul, qabs_mul]
    _ <= (b - a) * B + B * (d - c) := rat_add_le_add hleft hright
    _ = B * ((b - a) + (d - c)) := by
      grind [Rat.mul_add, Rat.mul_assoc, Rat.mul_comm]

private theorem product_deviation_bounds
    {a c p E : Rat} (h : qabs (p - a * c) <= E) :
    a * c - E <= p /\ p <= a * c + E := by
  constructor
  · have hneg : -E <= p - a * c :=
      Rat.le_trans (Rat.neg_le_neg h) (neg_qabs_le_self _)
    grind [Rat.sub_eq_add_neg]
  · have hpos : p - a * c <= E :=
      Rat.le_trans (self_le_qabs _) h
    grind [Rat.sub_eq_add_neg]

/-- The width of a literal four-corner product is bounded by a finite
rational Lipschitz estimate.  Both input intervals are assumed coordinatewise
bounded by the same rational `B`; no ambient real multiplication is used. -/
theorem mulRealInterval_width_le_of_abs_bounded {a b c d B : Rat}
    (hab : a <= b) (hcd : c <= d)
    (ha : qabs a <= B)
    (hc : qabs c <= B) (hd : qabs d <= B) :
    (mulRealInterval a b c d).width <=
      2 * B * ((b - a) + (d - c)) := by
  let E : Rat := B * ((b - a) + (d - c))
  have hac := product_deviation_bounds
    (a := a) (c := c) (E := E)
    (product_deviation_bound hab hcd ha hc hd
      Rat.le_refl hab Rat.le_refl hcd)
  have had := product_deviation_bounds
    (a := a) (c := c) (E := E)
    (product_deviation_bound hab hcd ha hc hd
      Rat.le_refl hab hcd Rat.le_refl)
  have hbc := product_deviation_bounds
    (a := a) (c := c) (E := E)
    (product_deviation_bound hab hcd ha hc hd
      hab Rat.le_refl Rat.le_refl hcd)
  have hbd := product_deviation_bounds
    (a := a) (c := c) (E := E)
    (product_deviation_bound hab hcd ha hc hd
      hab Rat.le_refl hcd Rat.le_refl)
  have hlow : a * c - E <= min4 (a * c) (a * d) (b * c) (b * d) :=
    le_min4 hac.1 had.1 hbc.1 hbd.1
  have hhigh : max4 (a * c) (a * d) (b * c) (b * d) <= a * c + E :=
    max4_le hac.2 had.2 hbc.2 hbd.2
  unfold mulRealInterval QInterval.width
  calc
    max4 (a * c) (a * d) (b * c) (b * d) -
        min4 (a * c) (a * d) (b * c) (b * d) <=
        (a * c + E) - (a * c - E) := by grind [Rat.sub_eq_add_neg]
    _ = 2 * B * ((b - a) + (d - c)) := by
      dsimp [E]
      grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.mul_assoc, Rat.mul_comm]

/-- A coordinatewise-bounded complex-box product has both coordinate widths
controlled by the four input coordinate widths. -/
theorem mul_width_height_le_of_coordinateBounded {A C : QBox} {B : Rat}
    (hA : A.Ordered) (hC : C.Ordered)
    (hAbound : A.CoordinateBounded B) (hCbound : C.CoordinateBounded B) :
    (mul A C).width <= 2 * B * (A.width + A.height + C.width + C.height) /\
      (mul A C).height <= 2 * B * (A.width + A.height + C.width + C.height) := by
  rcases hAbound with ⟨hArelo, _, hAimlo, _⟩
  rcases hCbound with ⟨hCrelo, hCrehi, hCimlo, hCimhi⟩
  have hrr := mulRealInterval_width_le_of_abs_bounded hA.1 hC.1
    hArelo hCrelo hCrehi
  have hii := mulRealInterval_width_le_of_abs_bounded hA.2 hC.2
    hAimlo hCimlo hCimhi
  have hri := mulRealInterval_width_le_of_abs_bounded hA.1 hC.2
    hArelo hCimlo hCimhi
  have hir := mulRealInterval_width_le_of_abs_bounded hA.2 hC.1
    hAimlo hCrelo hCrehi
  constructor
  · change
      (mulRealInterval A.lo.re A.hi.re C.lo.re C.hi.re).hi -
          (mulRealInterval A.lo.im A.hi.im C.lo.im C.hi.im).lo -
        ((mulRealInterval A.lo.re A.hi.re C.lo.re C.hi.re).lo -
          (mulRealInterval A.lo.im A.hi.im C.lo.im C.hi.im).hi) <= _
    calc
      (mulRealInterval A.lo.re A.hi.re C.lo.re C.hi.re).hi -
            (mulRealInterval A.lo.im A.hi.im C.lo.im C.hi.im).lo -
          ((mulRealInterval A.lo.re A.hi.re C.lo.re C.hi.re).lo -
            (mulRealInterval A.lo.im A.hi.im C.lo.im C.hi.im).hi) =
          (mulRealInterval A.lo.re A.hi.re C.lo.re C.hi.re).width +
            (mulRealInterval A.lo.im A.hi.im C.lo.im C.hi.im).width := by
              unfold QInterval.width
              grind [Rat.sub_eq_add_neg]
      _ <= 2 * B * ((A.hi.re - A.lo.re) + (C.hi.re - C.lo.re)) +
          2 * B * ((A.hi.im - A.lo.im) + (C.hi.im - C.lo.im)) :=
        rat_add_le_add hrr hii
      _ = 2 * B * (A.width + A.height + C.width + C.height) := by
        unfold QBox.width QBox.height
        grind [Rat.mul_add, Rat.mul_assoc, Rat.add_assoc, Rat.add_comm,
          Rat.mul_comm]
  · change
      (mulRealInterval A.lo.re A.hi.re C.lo.im C.hi.im).hi +
          (mulRealInterval A.lo.im A.hi.im C.lo.re C.hi.re).hi -
        ((mulRealInterval A.lo.re A.hi.re C.lo.im C.hi.im).lo +
          (mulRealInterval A.lo.im A.hi.im C.lo.re C.hi.re).lo) <= _
    calc
      (mulRealInterval A.lo.re A.hi.re C.lo.im C.hi.im).hi +
            (mulRealInterval A.lo.im A.hi.im C.lo.re C.hi.re).hi -
          ((mulRealInterval A.lo.re A.hi.re C.lo.im C.hi.im).lo +
            (mulRealInterval A.lo.im A.hi.im C.lo.re C.hi.re).lo) =
          (mulRealInterval A.lo.re A.hi.re C.lo.im C.hi.im).width +
            (mulRealInterval A.lo.im A.hi.im C.lo.re C.hi.re).width := by
              unfold QInterval.width
              grind [Rat.sub_eq_add_neg]
      _ <= 2 * B * ((A.hi.re - A.lo.re) + (C.hi.im - C.lo.im)) +
          2 * B * ((A.hi.im - A.lo.im) + (C.hi.re - C.lo.re)) :=
        rat_add_le_add hri hir
      _ = 2 * B * (A.width + A.height + C.width + C.height) := by
        unfold QBox.width QBox.height
        grind [Rat.mul_add, Rat.mul_assoc, Rat.add_assoc, Rat.add_comm,
          Rat.mul_comm]

/-- A rational point selected from the coordinatewise intersection of two
overlapping boxes.  It is a finite witness for product-overlap transport. -/
private def overlapPoint (A C : QBox) : QComplex :=
  { re := maxRat2 A.lo.re C.lo.re, im := maxRat2 A.lo.im C.lo.im }

private theorem overlapPoint_mem_left {A C : QBox}
    (hA : A.Ordered) (hover : A.Overlaps C) :
    A.lo <= overlapPoint A C /\ overlapPoint A C <= A.hi := by
  constructor
  · exact ⟨le_maxRat2_left _ _, le_maxRat2_left _ _⟩
  · exact ⟨maxRat2_le hA.1 hover.2.1, maxRat2_le hA.2 hover.2.2⟩

private theorem overlapPoint_mem_right {A C : QBox}
    (hC : C.Ordered) (hover : A.Overlaps C) :
    C.lo <= overlapPoint A C /\ overlapPoint A C <= C.hi := by
  constructor
  · exact ⟨le_maxRat2_right _ _, le_maxRat2_right _ _⟩
  · exact ⟨maxRat2_le hover.1.1 hC.1, maxRat2_le hover.1.2 hC.2⟩

/-- The literal complex box product contains the ordinary rational complex
product of any two rational points enclosed by its input boxes. -/
theorem mul_contains {A B : QBox} {z w : QComplex}
    (hzlo : A.lo <= z) (hzhi : z <= A.hi)
    (hwlo : B.lo <= w) (hwhi : w <= B.hi) :
    (mul A B).lo <= QComplex.mul z w /\
      QComplex.mul z w <= (mul A B).hi := by
  have hrr := mulRealInterval_contains
    (a := A.lo.re) (b := A.hi.re) (c := B.lo.re) (d := B.hi.re)
    hzlo.1 hzhi.1 hwlo.1 hwhi.1
  have hii := mulRealInterval_contains
    (a := A.lo.im) (b := A.hi.im) (c := B.lo.im) (d := B.hi.im)
    hzlo.2 hzhi.2 hwlo.2 hwhi.2
  have hri := mulRealInterval_contains
    (a := A.lo.re) (b := A.hi.re) (c := B.lo.im) (d := B.hi.im)
    hzlo.1 hzhi.1 hwlo.2 hwhi.2
  have hir := mulRealInterval_contains
    (a := A.lo.im) (b := A.hi.im) (c := B.lo.re) (d := B.hi.re)
    hzlo.2 hzhi.2 hwlo.1 hwhi.1
  change
    ((mulRealInterval A.lo.re A.hi.re B.lo.re B.hi.re).lo -
        (mulRealInterval A.lo.im A.hi.im B.lo.im B.hi.im).hi <=
      z.re * w.re - z.im * w.im /\
    (mulRealInterval A.lo.re A.hi.re B.lo.im B.hi.im).lo +
        (mulRealInterval A.lo.im A.hi.im B.lo.re B.hi.re).lo <=
      z.re * w.im + z.im * w.re) /\
    (z.re * w.re - z.im * w.im <=
      (mulRealInterval A.lo.re A.hi.re B.lo.re B.hi.re).hi -
        (mulRealInterval A.lo.im A.hi.im B.lo.im B.hi.im).lo /\
    z.re * w.im + z.im * w.re <=
      (mulRealInterval A.lo.re A.hi.re B.lo.im B.hi.im).hi +
        (mulRealInterval A.lo.im A.hi.im B.lo.re B.hi.re).hi)
  constructor
  · constructor <;> grind [Rat.sub_eq_add_neg]
  · constructor <;> grind [Rat.sub_eq_add_neg]

/-- Literal four-corner multiplication carries two pairs of overlapping,
ordered input boxes to overlapping output boxes.  The proof names rational
points in the two finite intersections, so it requires neither a completed
complex plane nor a choice principle. -/
theorem mul_overlaps_of_overlaps {A A' C C' : QBox}
    (hA : A.Ordered) (hA' : A'.Ordered)
    (hC : C.Ordered) (hC' : C'.Ordered)
    (hAA' : A.Overlaps A') (hCC' : C.Overlaps C') :
    (mul A C).Overlaps (mul A' C') := by
  let x := overlapPoint A A'
  let y := overlapPoint C C'
  have hxA := overlapPoint_mem_left hA hAA'
  have hxA' := overlapPoint_mem_right hA' hAA'
  have hyC := overlapPoint_mem_left hC hCC'
  have hyC' := overlapPoint_mem_right hC' hCC'
  have hleft := mul_contains (A := A) (B := C) (z := x) (w := y)
    hxA.1 hxA.2 hyC.1 hyC.2
  have hright := mul_contains (A := A') (B := C') (z := x) (w := y)
    hxA'.1 hxA'.2 hyC'.1 hyC'.2
  exact ⟨
    ⟨Rat.le_trans hleft.1.1 hright.2.1,
      Rat.le_trans hleft.1.2 hright.2.2⟩,
    ⟨Rat.le_trans hright.1.1 hleft.2.1,
      Rat.le_trans hright.1.2 hleft.2.2⟩⟩

/-- The literal product of two ordered complex boxes is ordered. -/
theorem mul_ordered {A B : QBox}
    (hA : A.Ordered) (hB : B.Ordered) : (mul A B).Ordered := by
  have hrr := mulRealInterval_ordered hA.1 hB.1
  have hii := mulRealInterval_ordered hA.2 hB.2
  have hri := mulRealInterval_ordered hA.1 hB.2
  have hir := mulRealInterval_ordered hA.2 hB.1
  change
    (mulRealInterval A.lo.re A.hi.re B.lo.re B.hi.re).lo -
        (mulRealInterval A.lo.im A.hi.im B.lo.im B.hi.im).hi <=
      (mulRealInterval A.lo.re A.hi.re B.lo.re B.hi.re).hi -
        (mulRealInterval A.lo.im A.hi.im B.lo.im B.hi.im).lo /\
    (mulRealInterval A.lo.re A.hi.re B.lo.im B.hi.im).lo +
        (mulRealInterval A.lo.im A.hi.im B.lo.re B.hi.re).lo <=
      (mulRealInterval A.lo.re A.hi.re B.lo.im B.hi.im).hi +
        (mulRealInterval A.lo.im A.hi.im B.lo.re B.hi.re).hi
  constructor <;> grind [Rat.sub_eq_add_neg]

/-- Refining two ordered complex boxes refines their literal product box. -/
theorem mul_nested {A B A' B' : QBox}
    (hA' : A'.Ordered) (hB' : B'.Ordered)
    (hA : A'.NestedIn A) (hB : B'.NestedIn B) :
    (mul A' B').NestedIn (mul A B) := by
  have hrr := mulRealInterval_nested
    hA.1.1 hA'.1 hA.2.1 hB.1.1 hB'.1 hB.2.1
  have hii := mulRealInterval_nested
    hA.1.2 hA'.2 hA.2.2 hB.1.2 hB'.2 hB.2.2
  have hri := mulRealInterval_nested
    hA.1.1 hA'.1 hA.2.1 hB.1.2 hB'.2 hB.2.2
  have hir := mulRealInterval_nested
    hA.1.2 hA'.2 hA.2.2 hB.1.1 hB'.1 hB.2.1
  change
    ((mulRealInterval A.lo.re A.hi.re B.lo.re B.hi.re).lo -
        (mulRealInterval A.lo.im A.hi.im B.lo.im B.hi.im).hi <=
      (mulRealInterval A'.lo.re A'.hi.re B'.lo.re B'.hi.re).lo -
        (mulRealInterval A'.lo.im A'.hi.im B'.lo.im B'.hi.im).hi /\
    (mulRealInterval A.lo.re A.hi.re B.lo.im B.hi.im).lo +
        (mulRealInterval A.lo.im A.hi.im B.lo.re B.hi.re).lo <=
      (mulRealInterval A'.lo.re A'.hi.re B'.lo.im B'.hi.im).lo +
        (mulRealInterval A'.lo.im A'.hi.im B'.lo.re B'.hi.re).lo) /\
    ((mulRealInterval A'.lo.re A'.hi.re B'.lo.re B'.hi.re).hi -
        (mulRealInterval A'.lo.im A'.hi.im B'.lo.im B'.hi.im).lo <=
      (mulRealInterval A.lo.re A.hi.re B.lo.re B.hi.re).hi -
        (mulRealInterval A.lo.im A.hi.im B.lo.im B.hi.im).lo /\
    (mulRealInterval A'.lo.re A'.hi.re B'.lo.im B'.hi.im).hi +
        (mulRealInterval A'.lo.im A'.hi.im B'.lo.re B'.hi.re).hi <=
      (mulRealInterval A.lo.re A.hi.re B.lo.im B.hi.im).hi +
        (mulRealInterval A.lo.im A.hi.im B.lo.re B.hi.re).hi)
  constructor
  · constructor <;> grind [Rat.sub_eq_add_neg]
  · constructor <;> grind [Rat.sub_eq_add_neg]

end QBox

namespace QInterval

theorem inv_of_pos {I : QInterval} (hpos : 0 < I.lo) :
    I.inv = { lo := 1 / I.hi, hi := 1 / I.lo } := by
  simp [QInterval.inv, hpos]

theorem one_div_le_one_div_of_pos {a b : Rat}
    (ha : 0 < a) (hab : a <= b) : 1 / b <= 1 / a := by
  rw [Rat.div_def, Rat.div_def]
  simp only [Rat.one_mul]
  have hb : 0 < b := by grind
  have hprod : 0 < a * b := Rat.mul_pos ha hb
  apply Rat.le_of_mul_le_mul_right (c := a * b)
  · have ha0 : a ≠ 0 := Rat.ne_of_gt ha
    have hb0 : b ≠ 0 := Rat.ne_of_gt hb
    calc
      b⁻¹ * (a * b) = a := by
        grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel,
          Rat.inv_mul_cancel]
      _ <= b := hab
      _ = a⁻¹ * (a * b) := by
        grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel,
          Rat.inv_mul_cancel]
  · exact hprod

theorem inv_overlaps_of_pos {I J : QInterval}
    (hIpos : 0 < I.lo) (hJpos : 0 < J.lo)
    (hIJ : I.Overlaps J) : I.inv.Overlaps J.inv := by
  rw [inv_of_pos hIpos, inv_of_pos hJpos]
  unfold QInterval.Overlaps at hIJ ⊢
  constructor
  · exact one_div_le_one_div_of_pos hJpos hIJ.2
  · exact one_div_le_one_div_of_pos hIpos hIJ.1

theorem inv_ordered_of_pos {I : QInterval}
    (hpos : 0 < I.lo) (hI : I.lo <= I.hi) :
    I.inv.lo <= I.inv.hi := by
  rw [inv_of_pos hpos]
  change 1 / I.hi <= 1 / I.lo
  rw [Rat.div_def, Rat.div_def]
  simp only [Rat.one_mul]
  have hIhi : 0 < I.hi := by grind
  have hprod : 0 < I.lo * I.hi := Rat.mul_pos hpos hIhi
  apply Rat.le_of_mul_le_mul_right (c := I.lo * I.hi)
  · have hlo : I.lo ≠ 0 := Rat.ne_of_gt hpos
    have hhi : I.hi ≠ 0 := Rat.ne_of_gt hIhi
    calc
      I.hi⁻¹ * (I.lo * I.hi) = I.lo * (I.hi * I.hi⁻¹) := by
        grind [Rat.mul_assoc, Rat.mul_comm]
      _ = I.lo := by rw [Rat.mul_inv_cancel _ hhi, Rat.mul_one]
      _ <= I.hi := hI
      _ = I.hi * (I.lo * I.lo⁻¹) := by
        rw [Rat.mul_inv_cancel _ hlo, Rat.mul_one]
      _ = I.lo⁻¹ * (I.lo * I.hi) := by
        grind [Rat.mul_assoc, Rat.mul_comm]
  · exact hprod

theorem inv_width_eq_width_div_product_of_pos {I : QInterval}
    (hpos : 0 < I.lo) (hI : I.lo <= I.hi) :
    I.inv.width = I.width / (I.lo * I.hi) := by
  rw [inv_of_pos hpos]
  unfold QInterval.width
  rw [Rat.div_def]
  have hhi : 0 < I.hi := by grind
  have hline : 1 / I.lo - 1 / I.hi =
      (I.hi - I.lo) * (I.lo * I.hi)⁻¹ := by
    rw [Rat.div_def, Rat.div_def]
    have hlo0 : I.lo ≠ 0 := Rat.ne_of_gt hpos
    have hhi0 : I.hi ≠ 0 := Rat.ne_of_gt hhi
    grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
      Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel,
      Rat.inv_mul_cancel]
  exact hline

theorem inv_width_le_width_div_sq_of_lower_bound {I : QInterval} {a : Rat}
    (ha : 0 < a) (haI : a <= I.lo) (hI : I.lo <= I.hi) :
    I.inv.width <= I.width / (a * a) := by
  have hpos : 0 < I.lo := by grind
  have hhi : 0 < I.hi := by grind
  have hlohi : 0 < I.lo * I.hi := Rat.mul_pos hpos hhi
  have haa : 0 < a * a := Rat.mul_pos ha ha
  have hwidth : 0 <= I.width := by
    unfold QInterval.width
    grind
  rw [inv_width_eq_width_div_product_of_pos hpos hI]
  rw [Rat.div_def, Rat.div_def]
  apply Rat.le_of_mul_le_mul_right
    (c := (I.lo * I.hi) * (a * a))
  · have hlo0 : I.lo ≠ 0 := Rat.ne_of_gt hpos
    have hhi0 : I.hi ≠ 0 := Rat.ne_of_gt hhi
    have ha0 : a ≠ 0 := Rat.ne_of_gt ha
    calc
      I.width * (I.lo * I.hi)⁻¹ * ((I.lo * I.hi) * (a * a)) =
          I.width * (a * a) := by
        grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel,
          Rat.inv_mul_cancel]
      _ <= I.width * (I.lo * I.hi) := by
        have hsq : a * a <= I.lo * I.hi := by
          have hleft := Rat.mul_le_mul_of_nonneg_right haI
            (Rat.le_of_lt ha)
          have hright := Rat.mul_le_mul_of_nonneg_left
            (Rat.le_trans haI hI) (Rat.le_of_lt hpos)
          exact Rat.le_trans hleft hright
        exact Rat.mul_le_mul_of_nonneg_left
          hsq
          hwidth
      _ = I.width * (a * a)⁻¹ * ((I.lo * I.hi) * (a * a)) := by
        grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel,
          Rat.inv_mul_cancel]
  · exact Rat.mul_pos hlohi haa

theorem inv_nested_of_pos {I J : QInterval}
    (hIpos : 0 < I.lo) (hJpos : 0 < J.lo)
    (hIJ : I.lo <= J.lo) (hJord : J.lo <= J.hi)
    (hhiJ : J.hi <= I.hi) :
    I.inv.ContainsInterval J.inv := by
  rw [inv_of_pos hIpos, inv_of_pos hJpos]
  change 1 / I.hi <= 1 / J.hi /\ 1 / J.lo <= 1 / I.lo
  · constructor
    · rw [Rat.div_def, Rat.div_def]
      simp only [Rat.one_mul]
      have hIhi : 0 < I.hi := by grind
      have hJhi : 0 < J.hi := by grind
      have hprod : 0 < J.hi * I.hi := Rat.mul_pos hJhi hIhi
      apply Rat.le_of_mul_le_mul_right (c := J.hi * I.hi)
      · have hIhi0 : I.hi ≠ 0 := Rat.ne_of_gt hIhi
        have hJhi0 : J.hi ≠ 0 := Rat.ne_of_gt hJhi
        calc
          I.hi⁻¹ * (J.hi * I.hi) = J.hi := by
            grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
          _ <= I.hi := hhiJ
          _ = J.hi⁻¹ * (J.hi * I.hi) := by
            grind [Rat.mul_assoc, Rat.mul_comm]
      · exact hprod
    · rw [Rat.div_def, Rat.div_def]
      simp only [Rat.one_mul]
      have hIlo0 : 0 < I.lo := hIpos
      have hJlo0 : 0 < J.lo := hJpos
      have hprod : 0 < J.lo * I.lo := Rat.mul_pos hJlo0 hIlo0
      apply Rat.le_of_mul_le_mul_right (c := J.lo * I.lo)
      · have hIlo : I.lo ≠ 0 := Rat.ne_of_gt hIlo0
        have hJlo : J.lo ≠ 0 := Rat.ne_of_gt hJlo0
        calc
          J.lo⁻¹ * (J.lo * I.lo) = I.lo := by
            grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
          _ <= J.lo := hIJ
          _ = I.lo⁻¹ * (J.lo * I.lo) := by
            grind [Rat.mul_assoc, Rat.mul_comm]
      · exact hprod

end QInterval

namespace RealCompute

def positiveInvCompute (x : RealCompute) (N : Nat) : Nat -> QInterval :=
  fun n =>
    if n < N then
      { lo := 0, hi := 1 / (x.compute N).lo }
    else
      QInterval.inv (x.compute n)

def positiveInv (x : RealCompute) (N : Nat) : RealCompute where
  compute := positiveInvCompute x N

theorem positiveInv_compute_ordered {x : RealCompute} {N n : Nat}
    (hx : x.Valid) (hpos : 0 < (x.compute N).lo) :
    ((positiveInv x N).compute n).lo <=
      ((positiveInv x N).compute n).hi := by
  by_cases hn : n < N
  · simp [positiveInv, positiveInvCompute, hn]
    change 0 <= 1 / (x.compute N).lo
    rw [Rat.div_def]
    exact Rat.le_of_lt (Rat.mul_pos (by decide +kernel) ((Rat.inv_pos).2 hpos))
  · simp [positiveInv, positiveInvCompute, hn]
    change (QInterval.inv (x.compute n)).lo <=
      (QInterval.inv (x.compute n)).hi
    apply QInterval.inv_ordered_of_pos
    · have hNn := hx.2.1 N n (by omega)
      grind
    · exact interval_order_of_valid x hx n

theorem positiveInv_compute_nested {x : RealCompute} {N n m : Nat}
    (hx : x.Valid) (hpos : 0 < (x.compute N).lo) (hnm : n <= m) :
    QInterval.ContainsInterval ((positiveInv x N).compute n)
      ((positiveInv x N).compute m) := by
  by_cases hn : n < N
  · by_cases hm : m < N
    · simp [positiveInv, positiveInvCompute, hn, hm]
      change 0 <= 0 /\ 1 / (x.compute N).lo <= 1 / (x.compute N).lo
      exact ⟨Rat.le_refl, Rat.le_refl⟩
    · simp [positiveInv, positiveInvCompute, hn, hm]
      change 0 <= (QInterval.inv (x.compute m)).lo /\
        (QInterval.inv (x.compute m)).hi <= 1 / (x.compute N).lo
      have hNm : N <= m := by omega
      have hN := hx.2.1 N m hNm
      have hmpos : 0 < (x.compute m).lo := by grind
      have hmh : 0 < (x.compute m).hi := by grind
      rw [QInterval.inv_of_pos hmpos]
      change 0 <= 1 / (x.compute m).hi /\
        1 / (x.compute m).lo <= 1 / (x.compute N).lo
      constructor
      · rw [Rat.div_def]
        exact Rat.le_of_lt (Rat.mul_pos (by decide +kernel) ((Rat.inv_pos).2 hmh))
      · apply QInterval.one_div_le_one_div_of_pos
          hpos hN.1
  · have hNn : N <= n := by omega
    have hNm : N <= m := by omega
    have hNn' := hx.2.1 N n hNn
    have hNm' := hx.2.1 N m hNm
    have hnpos : 0 < (x.compute n).lo := by grind
    have hmp : 0 < (x.compute m).lo := by grind
    have hm : ¬m < N := by omega
    simp [positiveInv, positiveInvCompute, hn, hm]
    apply QInterval.inv_nested_of_pos hnpos hmp
    · exact (hx.2.1 n m hnm).1
    · exact interval_order_of_valid x hx m
    · exact (hx.2.1 n m hnm).2.2

theorem positiveInv_valid {x : RealCompute} {N : Nat}
    (hx : x.Valid) (hpos : 0 < (x.compute N).lo) :
    (positiveInv x N).Valid := by
  constructor
  · intro n
    unfold QInterval.width
    have ho := positiveInv_compute_ordered hx hpos (n := n)
    grind
  · constructor
    · intro n m hnm
      have hnest := positiveInv_compute_nested hx hpos hnm
      exact ⟨hnest.1, ⟨positiveInv_compute_ordered hx hpos, hnest.2⟩⟩
    · intro eps
      let a : Rat := (x.compute N).lo
      let delta : QPos := ⟨eps.val * (a * a), by
        dsimp [a]
        exact Rat.mul_pos eps.property
          (Rat.mul_pos hpos hpos)⟩
      obtain ⟨Nx, hNx⟩ := hx.2.2 delta
      refine ⟨Nat.max N Nx, ?_⟩
      intro n hn
      have hnN : N <= n := Nat.le_trans (Nat.le_max_left _ _) hn
      have hnx : Nx <= n := Nat.le_trans (Nat.le_max_right _ _) hn
      have hsmall := hNx n hnx
      have hNn := hx.2.1 N n hnN
      have hposn : 0 < (x.compute n).lo := by
        grind [hNn.1]
      have hinv := QInterval.inv_width_le_width_div_sq_of_lower_bound
        hpos (by simpa [a] using hNn.1) (interval_order_of_valid x hx n)
      have hquot : (x.compute n).width / (a * a) <= eps.val := by
        rw [Rat.div_def]
        apply Rat.le_of_mul_le_mul_right (c := a * a)
        · have haa0 : a * a ≠ 0 := Rat.ne_of_gt (Rat.mul_pos hpos hpos)
          calc
            (x.compute n).width * (a * a)⁻¹ * (a * a) =
                (x.compute n).width := by
              grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel,
                Rat.inv_mul_cancel]
            _ <= eps.val * (a * a) := by
              dsimp [delta] at hsmall
              exact hsmall
        · exact Rat.mul_pos hpos hpos
      simp [positiveInv, positiveInvCompute, Nat.not_lt_of_ge hnN]
      exact Rat.le_trans hinv hquot

theorem positiveInv_equiv_of_stages {x : RealCompute} {N M : Nat}
    (hx : x.Valid) (hNpos : 0 < (x.compute N).lo)
    (hMpos : 0 < (x.compute M).lo) :
    (positiveInv x N).Equiv (positiveInv x M) := by
  intro n
  apply (compareAt_overlap_iff (positiveInv x N) (positiveInv x M) n n).2
  change QInterval.Overlaps
    ((positiveInv x N).compute n) ((positiveInv x M).compute n)
  by_cases hnN : n < N
  · by_cases hnM : n < M
    · simp [positiveInv, positiveInvCompute, hnN, hnM,
        QInterval.Overlaps]
      constructor
      · exact (by
          rw [Rat.div_def]
          exact Rat.le_of_lt (Rat.mul_pos (by decide +kernel)
            ((Rat.inv_pos).2 hMpos)))
      · exact (by
          rw [Rat.div_def]
          exact Rat.le_of_lt (Rat.mul_pos (by decide +kernel)
            ((Rat.inv_pos).2 hNpos)))
    · have hMn : M <= n := by omega
      have hMn' := hx.2.1 M n hMn
      have hnpos : 0 < (x.compute n).lo := by
        apply (Rat.lt_iff_le_and_ne).2
        constructor
        · exact Rat.le_trans (Rat.le_of_lt hMpos) hMn'.1
        · intro hz
          have hmzero : (x.compute M).lo = 0 :=
            Rat.le_antisymm (by simpa [hz] using hMn'.1)
              (Rat.le_of_lt hMpos)
          exact (Rat.ne_of_gt hMpos) hmzero
      simp [positiveInv, positiveInvCompute, hnN, hnM,
        QInterval.Overlaps]
      rw [QInterval.inv_of_pos hnpos]
      change 0 ≤ 1 / (x.compute n).lo ∧
        1 / (x.compute n).hi ≤ 1 / (x.compute N).lo
      constructor
      · rw [Rat.div_def]
        exact Rat.le_of_lt (Rat.mul_pos (by decide +kernel)
          ((Rat.inv_pos).2 hnpos))
      · have hnN' := hx.2.1 n N (by omega)
        exact QInterval.one_div_le_one_div_of_pos hNpos
          (Rat.le_trans (interval_order_of_valid x hx N) hnN'.2.2)
  · have hNn : N <= n := by omega
    by_cases hnM : n < M
    · have hNn' := hx.2.1 N n hNn
      have hnpos : 0 < (x.compute n).lo := by
        have hNn' := hx.2.1 N n hNn
        apply (Rat.lt_iff_le_and_ne).2
        constructor
        · exact Rat.le_trans (Rat.le_of_lt hNpos) hNn'.1
        · intro hz
          have hnzero : (x.compute N).lo = 0 :=
            Rat.le_antisymm (by simpa [hz] using hNn'.1)
              (Rat.le_of_lt hNpos)
          exact (Rat.ne_of_gt hNpos) hnzero
      simp [positiveInv, positiveInvCompute, hnN, hnM,
        QInterval.Overlaps]
      rw [QInterval.inv_of_pos hnpos]
      change 1 / (x.compute n).hi ≤ 1 / (x.compute M).lo ∧
        0 ≤ 1 / (x.compute n).lo
      constructor
      · have hnM' := hx.2.1 n M (by omega)
        exact QInterval.one_div_le_one_div_of_pos hMpos
          (Rat.le_trans (interval_order_of_valid x hx M) hnM'.2.2)
      · rw [Rat.div_def]
        exact Rat.le_of_lt (Rat.mul_pos (by decide +kernel)
          ((Rat.inv_pos).2 hnpos))
    · have hMn : M <= n := by omega
      have hnpos : 0 < (x.compute n).lo := by
        have hNn' := hx.2.1 N n hNn
        apply (Rat.lt_iff_le_and_ne).2
        constructor
        · exact Rat.le_trans (Rat.le_of_lt hNpos) hNn'.1
        · intro hz
          have hnzero : (x.compute N).lo = 0 :=
            Rat.le_antisymm (by simpa [hz] using hNn'.1)
              (Rat.le_of_lt hNpos)
          exact (Rat.ne_of_gt hNpos) hnzero
      simp [positiveInv, positiveInvCompute, hnN, hnM,
        QInterval.Overlaps]
      rw [QInterval.inv_of_pos hnpos]
      change 1 / (x.compute n).hi ≤ 1 / (x.compute n).lo
      exact QInterval.one_div_le_one_div_of_pos hnpos
        (interval_order_of_valid x hx n)

theorem positiveInv_equiv_of_input {x y : RealCompute} {N : Nat}
    (hx : x.Valid) (hy : y.Valid) (hxy : x.Equiv y)
    (hXpos : 0 < (x.compute N).lo)
    (hYpos : 0 < (y.compute N).lo) :
    (positiveInv x N).Equiv (positiveInv y N) := by
  intro n
  apply (compareAt_overlap_iff (positiveInv x N) (positiveInv y N) n n).2
  change QInterval.Overlaps
    ((positiveInv x N).compute n) ((positiveInv y N).compute n)
  by_cases hn : n < N
  · simp [positiveInv, positiveInvCompute, hn, QInterval.Overlaps]
    constructor
    · rw [Rat.div_def]
      exact Rat.le_of_lt (Rat.mul_pos (by decide +kernel)
        ((Rat.inv_pos).2 hYpos))
    · rw [Rat.div_def]
      exact Rat.le_of_lt (Rat.mul_pos (by decide +kernel)
        ((Rat.inv_pos).2 hXpos))
  · have hNn : N <= n := by omega
    have hXn := hx.2.1 N n hNn
    have hYn := hy.2.1 N n hNn
    have hXnpos : 0 < (x.compute n).lo := by
      apply (Rat.lt_iff_le_and_ne).2
      constructor
      · exact Rat.le_trans (Rat.le_of_lt hXpos) hXn.1
      · intro hz
        have hzero : (x.compute N).lo = 0 :=
          Rat.le_antisymm (by simpa [hz] using hXn.1)
            (Rat.le_of_lt hXpos)
        exact (Rat.ne_of_gt hXpos) hzero
    have hYnpos : 0 < (y.compute n).lo := by
      apply (Rat.lt_iff_le_and_ne).2
      constructor
      · exact Rat.le_trans (Rat.le_of_lt hYpos) hYn.1
      · intro hz
        have hzero : (y.compute N).lo = 0 :=
          Rat.le_antisymm (by simpa [hz] using hYn.1)
            (Rat.le_of_lt hYpos)
        exact (Rat.ne_of_gt hYpos) hzero
    simp [positiveInv, positiveInvCompute, hn, QInterval.Overlaps]
    exact QInterval.inv_overlaps_of_pos hXnpos hYnpos
      ((compareAt_overlap_iff x y n n).1 (hxy n))

theorem positiveInv_mul_self_equiv_one {x : RealCompute} {N : Nat}
    (hx : x.Valid) (hpos : 0 < (x.compute N).lo) :
    (mul x (positiveInv x N)).Equiv one := by
  intro n
  apply (compareAt_overlap_iff (mul x (positiveInv x N)) one n n).2
  change QInterval.Overlaps
    (QBox.mulRealInterval
      (x.compute n).lo (x.compute n).hi
      ((positiveInv x N).compute n).lo
      ((positiveInv x N).compute n).hi)
    ({ lo := 1, hi := 1 } : QInterval)
  unfold QInterval.Overlaps
  by_cases hn : n < N
  · have hnn := hx.2.1 n N (by omega)
    simp [positiveInv, positiveInvCompute, hn]
    have ha_mem : (x.compute n).lo <= (x.compute N).lo /\
        (x.compute N).lo <= (x.compute n).hi :=
      ⟨hnn.1, Rat.le_trans (interval_order_of_valid x hx N) hnn.2.2⟩
    have hrec_mem : (0 : Rat) <= 1 / (x.compute N).lo /\
        1 / (x.compute N).lo <= 1 / (x.compute N).lo := by
      constructor
      · rw [Rat.div_def]
        exact Rat.le_of_lt (Rat.mul_pos (by decide +kernel)
          ((Rat.inv_pos).2 hpos))
      · exact Rat.le_refl
    have hprod := QBox.mulRealInterval_contains
      ha_mem.1 ha_mem.2 hrec_mem.1 hrec_mem.2
    have hprod_eq : (x.compute N).lo * (1 / (x.compute N).lo) = 1 := by
      rw [Rat.div_def]
      simp only [Rat.one_mul]
      exact Rat.mul_inv_cancel _ (Rat.ne_of_gt hpos)
    rw [hprod_eq] at hprod
    exact ⟨hprod.1, hprod.2⟩
  · have hNn : N <= n := by omega
    have hNn' := hx.2.1 N n hNn
    have hposn : 0 < (x.compute n).lo := by grind
    simp [positiveInv, positiveInvCompute, hn]
    rw [QInterval.inv_of_pos hposn]
    have hrec_order := QInterval.inv_ordered_of_pos hposn
      (interval_order_of_valid x hx n)
    have hprod := QBox.mulRealInterval_contains
      (Rat.le_refl) (interval_order_of_valid x hx n)
      (QInterval.one_div_le_one_div_of_pos hposn
        (interval_order_of_valid x hx n))
      (Rat.le_refl)
    have hprod_eq : (x.compute n).lo * (1 / (x.compute n).lo) = 1 := by
      rw [Rat.div_def]
      simp only [Rat.one_mul]
      exact Rat.mul_inv_cancel _ (Rat.ne_of_gt hposn)
    rw [hprod_eq] at hprod
    exact ⟨hprod.1, hprod.2⟩

theorem neg_neg_equiv {x : RealCompute} (hx : x.Valid) : (-(-x)).Equiv x := by
  intro n
  apply (compareAt_overlap_iff (-(-x)) x n n).2
  change QInterval.Overlaps (negCompute (neg x) n) (x.compute n)
  simp [RealCompute.neg, negCompute, QInterval.Overlaps]
  exact interval_order_of_valid x hx n

theorem mul_neg_neg_equiv {x y : RealCompute}
    (hx : x.Valid) (hy : y.Valid) :
    (mul (-x) (-y)).Equiv (mul x y) := by
  intro n
  apply (compareAt_overlap_iff (mul (-x) (-y)) (mul x y) n n).2
  change QInterval.Overlaps
    (QBox.mulRealInterval
      (-(x.compute n).hi) (-(x.compute n).lo)
      (-(y.compute n).hi) (-(y.compute n).lo))
    (QBox.mulRealInterval
      (x.compute n).lo (x.compute n).hi
      (y.compute n).lo (y.compute n).hi)
  have hxord := interval_order_of_valid x hx n
  have hyord := interval_order_of_valid y hy n
  have hxp := QInterval.midpoint_mem hxord
  have hyp := QInterval.midpoint_mem hyord
  let p : Rat := QInterval.midpoint (x.compute n)
  let q : Rat := QInterval.midpoint (y.compute n)
  have hnegx : -(x.compute n).hi <= -p /\
      -p <= -(x.compute n).lo := by
    exact ⟨Rat.neg_le_neg hxp.2, Rat.neg_le_neg hxp.1⟩
  have hnegy : -(y.compute n).hi <= -q /\
      -q <= -(y.compute n).lo := by
    exact ⟨Rat.neg_le_neg hyp.2, Rat.neg_le_neg hyp.1⟩
  have hleft := QBox.mulRealInterval_contains
    hnegx.1 hnegx.2 hnegy.1 hnegy.2
  have hright := QBox.mulRealInterval_contains
    hxp.1 hxp.2 hyp.1 hyp.2
  have hpoint : (-p) * (-q) = p * q := by
    grind [Rat.neg_mul, Rat.mul_neg, Rat.neg_neg]
  rw [hpoint] at hleft
  exact ⟨Rat.le_trans hleft.1 hright.2,
    Rat.le_trans hright.1 hleft.2⟩

def negativeInv (x : RealCompute) (N : Nat) : RealCompute :=
  -(positiveInv (-x) N)

theorem negativeInv_valid {x : RealCompute} {N : Nat}
    (hx : x.Valid) (hneg : (x.compute N).hi < 0) :
    (negativeInv x N).Valid := by
  unfold negativeInv
  apply neg_valid
  apply positiveInv_valid (neg_valid hx)
  change 0 < -(x.compute N).hi
  grind

theorem negativeInv_equiv_of_stages {x : RealCompute} {N M : Nat}
    (hx : x.Valid)
    (hNneg : (x.compute N).hi < 0)
    (hMneg : (x.compute M).hi < 0) :
    (negativeInv x N).Equiv (negativeInv x M) := by
  unfold negativeInv
  apply neg_equiv
  apply positiveInv_equiv_of_stages (neg_valid hx)
  · change 0 < -(x.compute N).hi
    grind
  · change 0 < -(x.compute M).hi
    grind

theorem negativeInv_equiv_of_input {x y : RealCompute} {N : Nat}
    (hx : x.Valid) (hy : y.Valid) (hxy : x.Equiv y)
    (hXneg : (x.compute N).hi < 0)
    (hYneg : (y.compute N).hi < 0) :
    (negativeInv x N).Equiv (negativeInv y N) := by
  unfold negativeInv
  apply neg_equiv
  apply positiveInv_equiv_of_input (neg_valid hx) (neg_valid hy)
    (neg_equiv hxy)
  · change 0 < -(x.compute N).hi
    grind
  · change 0 < -(y.compute N).hi
    grind

private theorem qabs_le_of_interval_bounds {a b x B : Rat}
    (ha : qabs a <= B) (hb : qabs b <= B)
    (hax : a <= x) (hxb : x <= b) : qabs x <= B := by
  apply qabs_le_of_neg_le_le
  · calc
      -B <= -qabs a := Rat.neg_le_neg ha
      _ <= a := neg_qabs_le_self a
      _ <= x := hax
  · calc
      x <= b := hxb
      _ <= qabs b := self_le_qabs b
      _ <= B := hb

theorem mul_compute_ordered {x y : RealCompute}
    (hx : x.Valid) (hy : y.Valid) (n : Nat) :
    ((mul x y).compute n).lo <= ((mul x y).compute n).hi := by
  change (QBox.mulRealInterval
      (x.compute n).lo (x.compute n).hi
      (y.compute n).lo (y.compute n).hi).lo <=
    (QBox.mulRealInterval
      (x.compute n).lo (x.compute n).hi
      (y.compute n).lo (y.compute n).hi).hi
  exact QBox.mulRealInterval_ordered
    (interval_order_of_valid x hx n)
    (interval_order_of_valid y hy n)

theorem mul_compute_nested {x y : RealCompute}
    (hx : x.Valid) (hy : y.Valid) {n m : Nat} (hnm : n <= m) :
    QInterval.ContainsInterval ((mul x y).compute n) ((mul x y).compute m) := by
  change QInterval.ContainsInterval
    (QBox.mulRealInterval
      (x.compute n).lo (x.compute n).hi
      (y.compute n).lo (y.compute n).hi)
    (QBox.mulRealInterval
      (x.compute m).lo (x.compute m).hi
      (y.compute m).lo (y.compute m).hi)
  exact QBox.mulRealInterval_nested
    (hx.2.1 n m hnm).1
    (interval_order_of_valid x hx m)
    (hx.2.1 n m hnm).2.2
    (hy.2.1 n m hnm).1
    (interval_order_of_valid y hy m)
    (hy.2.1 n m hnm).2.2

theorem mul_valid_of_widthsShrink {x y : RealCompute}
    (hx : x.Valid) (hy : y.Valid)
    (hshrink : RealCompute.WidthsShrinkToZero (mul x y).compute) :
    (mul x y).Valid := by
  constructor
  · intro n
    change 0 <= ((mul x y).compute n).hi - ((mul x y).compute n).lo
    exact by grind [mul_compute_ordered hx hy n]
  · constructor
    · intro n m hnm
      have hnest := mul_compute_nested hx hy hnm
      exact ⟨hnest.1, ⟨mul_compute_ordered hx hy m, hnest.2⟩⟩
    · exact hshrink

/-- Arbitrary signed valid raw reals are closed under the literal four-corner
product.  The proof uses only rational interval arithmetic: later stages are
anchored inside the finite stage-zero intervals, and the product width is
controlled by the resulting finite rational bound. -/
theorem mul_valid {x y : RealCompute}
    (hx : x.Valid) (hy : y.Valid) :
    (mul x y).Valid := by
  apply mul_valid_of_widthsShrink hx hy
  intro eps
  let Bx : Rat := 1 + qabs (x.compute 0).lo + qabs (x.compute 0).hi
  let By : Rat := 1 + qabs (y.compute 0).lo + qabs (y.compute 0).hi
  let B : Rat := Bx + By
  have hBxpos : 0 < Bx := by
    dsimp [Bx]
    have h0 : 0 <= qabs (x.compute 0).lo := qabs_nonneg _
    have h1 : 0 <= qabs (x.compute 0).hi := qabs_nonneg _
    grind
  have hBypos : 0 < By := by
    dsimp [By]
    have h0 : 0 <= qabs (y.compute 0).lo := qabs_nonneg _
    have h1 : 0 <= qabs (y.compute 0).hi := qabs_nonneg _
    grind
  have hBpos : 0 < B := by
    dsimp [B]
    grind
  have hdenpos : 0 < (4 : Rat) * B := Rat.mul_pos (by decide +kernel) hBpos
  let delta : QPos := ⟨eps.val / ((4 : Rat) * B), by
    rw [Rat.div_def]
    exact Rat.mul_pos eps.property ((Rat.inv_pos).2 hdenpos)⟩
  obtain ⟨Nx, hNx⟩ := hx.2.2 delta
  obtain ⟨Ny, hNy⟩ := hy.2.2 delta
  refine ⟨Nat.max Nx Ny, ?_⟩
  intro n hn
  have hnx : Nx <= n := Nat.le_trans (Nat.le_max_left _ _) hn
  have hny : Ny <= n := Nat.le_trans (Nat.le_max_right _ _) hn
  have hxsmall := hNx n hnx
  have hysmall := hNy n hny
  have hx0 := hx.2.1 0 n (Nat.zero_le n)
  have hy0 := hy.2.1 0 n (Nat.zero_le n)
  have hxlo0 : qabs (x.compute 0).lo <= Bx := by
    dsimp [Bx]
    grind [qabs_nonneg (x.compute 0).lo, qabs_nonneg (x.compute 0).hi]
  have hxhi0 : qabs (x.compute 0).hi <= Bx := by
    dsimp [Bx]
    grind [qabs_nonneg (x.compute 0).lo, qabs_nonneg (x.compute 0).hi]
  have hylo0 : qabs (y.compute 0).lo <= By := by
    dsimp [By]
    grind [qabs_nonneg (y.compute 0).lo, qabs_nonneg (y.compute 0).hi]
  have hyhi0 : qabs (y.compute 0).hi <= By := by
    dsimp [By]
    grind [qabs_nonneg (y.compute 0).lo, qabs_nonneg (y.compute 0).hi]
  have hxlob : qabs (x.compute n).lo <= Bx := by
    apply qabs_le_of_interval_bounds
    · exact hxlo0
    · exact hxhi0
    · exact hx0.1
    · exact Rat.le_trans (interval_order_of_valid x hx n) hx0.2.2
  have hxhib : qabs (x.compute n).hi <= Bx := by
    apply qabs_le_of_interval_bounds
    · exact hxlo0
    · exact hxhi0
    · exact Rat.le_trans hx0.1 (interval_order_of_valid x hx n)
    · exact hx0.2.2
  have hylob : qabs (y.compute n).lo <= By := by
    apply qabs_le_of_interval_bounds
    · exact hylo0
    · exact hyhi0
    · exact hy0.1
    · exact Rat.le_trans (interval_order_of_valid y hy n) hy0.2.2
  have hyhib : qabs (y.compute n).hi <= By := by
    apply qabs_le_of_interval_bounds
    · exact hylo0
    · exact hyhi0
    · exact Rat.le_trans hy0.1 (interval_order_of_valid y hy n)
    · exact hy0.2.2
  have hBxle : Bx <= B := by
    dsimp [B]
    grind
  have hByle : By <= B := by
    dsimp [B]
    grind
  have hwidth := QBox.mulRealInterval_width_le_of_abs_bounded
    (interval_order_of_valid x hx n)
    (interval_order_of_valid y hy n)
    (Rat.le_trans hxlob hBxle)
    (Rat.le_trans hylob hByle)
    (Rat.le_trans hyhib hByle)
  have hsum :
      (x.compute n).width + (y.compute n).width <= 2 * delta.val := by
    grind
  have hscaled :
      2 * B * ((x.compute n).width + (y.compute n).width) <= eps.val := by
    calc
      2 * B * ((x.compute n).width + (y.compute n).width) <=
          2 * B * (2 * delta.val) :=
        Rat.mul_le_mul_of_nonneg_left hsum (by
          exact Rat.le_of_lt (Rat.mul_pos (by decide +kernel) hBpos))
      _ = eps.val := by
        dsimp [delta]
        rw [Rat.div_def]
        have hne : (4 : Rat) * B ≠ 0 := Rat.ne_of_gt hdenpos
        grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
  exact Rat.le_trans hwidth hscaled

/-- Equivalent raw-real representatives remain equivalent after the literal
four-corner product.  The witness is constructive: at each stage take the
midpoint of the explicit intersection of the two input intervals, then use
the finite product enclosure for the common rational product. -/
theorem mul_equiv {x x' y y' : RealCompute}
    (hx : x.Valid) (hx' : x'.Valid)
    (hy : y.Valid) (hy' : y'.Valid)
    (hxx' : x.Equiv x') (hyy' : y.Equiv y') :
    (mul x y).Equiv (mul x' y') := by
  intro n
  have hxx := (compareAt_overlap_iff x x' n n).1 (hxx' n)
  have hyy := (compareAt_overlap_iff y y' n n).1 (hyy' n)
  have hxord : (QInterval.intersection (x.compute n) (x'.compute n)).lo <=
      (QInterval.intersection (x.compute n) (x'.compute n)).hi := by
    apply QInterval.intersection_ordered_of_overlaps
      (interval_order_of_valid x hx n)
      (interval_order_of_valid x' hx' n)
    exact hxx
  have hyord : (QInterval.intersection (y.compute n) (y'.compute n)).lo <=
      (QInterval.intersection (y.compute n) (y'.compute n)).hi := by
    apply QInterval.intersection_ordered_of_overlaps
      (interval_order_of_valid y hy n)
      (interval_order_of_valid y' hy' n)
    exact hyy
  let p : Rat := QInterval.midpoint
    (QInterval.intersection (x.compute n) (x'.compute n))
  let q : Rat := QInterval.midpoint
    (QInterval.intersection (y.compute n) (y'.compute n))
  have hp :
      (QInterval.intersection (x.compute n) (x'.compute n)).lo <= p /\
      p <= (QInterval.intersection (x.compute n) (x'.compute n)).hi := by
    exact QInterval.midpoint_mem hxord
  have hq :
      (QInterval.intersection (y.compute n) (y'.compute n)).lo <= q /\
      q <= (QInterval.intersection (y.compute n) (y'.compute n)).hi := by
    exact QInterval.midpoint_mem hyord
  have hxp : (x.compute n).lo <= p /\ p <= (x.compute n).hi := by
    have hleft := QInterval.intersection_contained_left
      (x.compute n) (x'.compute n)
    have hright := QInterval.intersection_contained_left
      (x.compute n) (x'.compute n)
    exact ⟨Rat.le_trans hleft.1 hp.1, Rat.le_trans hp.2 hright.2⟩
  have hxp' : (x'.compute n).lo <= p /\ p <= (x'.compute n).hi := by
    have hleft := QInterval.intersection_contained_right
      (x.compute n) (x'.compute n)
    have hright := QInterval.intersection_contained_right
      (x.compute n) (x'.compute n)
    exact ⟨Rat.le_trans hleft.1 hp.1, Rat.le_trans hp.2 hright.2⟩
  have hyp : (y.compute n).lo <= q /\ q <= (y.compute n).hi := by
    have hleft := QInterval.intersection_contained_left
      (y.compute n) (y'.compute n)
    have hright := QInterval.intersection_contained_left
      (y.compute n) (y'.compute n)
    exact ⟨Rat.le_trans hleft.1 hq.1, Rat.le_trans hq.2 hright.2⟩
  have hyp' : (y'.compute n).lo <= q /\ q <= (y'.compute n).hi := by
    have hleft := QInterval.intersection_contained_right
      (y.compute n) (y'.compute n)
    have hright := QInterval.intersection_contained_right
      (y.compute n) (y'.compute n)
    exact ⟨Rat.le_trans hleft.1 hq.1, Rat.le_trans hq.2 hright.2⟩
  apply (compareAt_overlap_iff (mul x y) (mul x' y') n n).2
  change QInterval.Overlaps
    (QBox.mulRealInterval
      (x.compute n).lo (x.compute n).hi
      (y.compute n).lo (y.compute n).hi)
    (QBox.mulRealInterval
      (x'.compute n).lo (x'.compute n).hi
      (y'.compute n).lo (y'.compute n).hi)
  have hprod := QBox.mulRealInterval_contains hxp.1 hxp.2 hyp.1 hyp.2
  have hprod' := QBox.mulRealInterval_contains hxp'.1 hxp'.2 hyp'.1 hyp'.2
  exact ⟨Rat.le_trans hprod.1 hprod'.2, Rat.le_trans hprod'.1 hprod.2⟩

def divByPositive (x y : RealCompute) (N : Nat) : RealCompute :=
  mul x (positiveInv y N)

def divByNegative (x y : RealCompute) (N : Nat) : RealCompute :=
  mul x (negativeInv y N)

theorem divByPositive_valid {x y : RealCompute} {N : Nat}
    (hx : x.Valid) (hy : y.Valid) (hpos : 0 < (y.compute N).lo) :
    (divByPositive x y N).Valid := by
  unfold divByPositive
  exact mul_valid hx (positiveInv_valid hy hpos)

theorem divByPositive_equiv_of_stages {x y : RealCompute} {N M : Nat}
    (hx : x.Valid) (hy : y.Valid)
    (hNpos : 0 < (y.compute N).lo)
    (hMpos : 0 < (y.compute M).lo) :
    (divByPositive x y N).Equiv (divByPositive x y M) := by
  unfold divByPositive
  apply mul_equiv hx hx
    (positiveInv_valid hy hNpos)
    (positiveInv_valid hy hMpos)
    (equiv_refl _ hx)
  exact positiveInv_equiv_of_stages hy hNpos hMpos

theorem divByPositive_equiv_of_inputs
    {x x' y y' : RealCompute} {N : Nat}
    (hx : x.Valid) (hx' : x'.Valid) (hy : y.Valid) (hy' : y'.Valid)
    (hxx' : x.Equiv x') (hyy' : y.Equiv y')
    (hYpos : 0 < (y.compute N).lo)
    (hY'pos : 0 < (y'.compute N).lo) :
    (divByPositive x y N).Equiv (divByPositive x' y' N) := by
  unfold divByPositive
  apply mul_equiv hx hx'
    (positiveInv_valid hy hYpos)
    (positiveInv_valid hy' hY'pos)
    hxx'
  exact positiveInv_equiv_of_input hy hy' hyy' hYpos hY'pos

theorem divByNegative_valid {x y : RealCompute} {N : Nat}
    (hx : x.Valid) (hy : y.Valid) (hneg : (y.compute N).hi < 0) :
    (divByNegative x y N).Valid := by
  unfold divByNegative
  exact mul_valid hx (negativeInv_valid hy hneg)

theorem divByNegative_equiv_of_stages {x y : RealCompute} {N M : Nat}
    (hx : x.Valid) (hy : y.Valid)
    (hNneg : (y.compute N).hi < 0)
    (hMneg : (y.compute M).hi < 0) :
    (divByNegative x y N).Equiv (divByNegative x y M) := by
  unfold divByNegative
  apply mul_equiv hx hx
    (negativeInv_valid hy hNneg)
    (negativeInv_valid hy hMneg)
    (equiv_refl _ hx)
  exact negativeInv_equiv_of_stages hy hNneg hMneg

theorem divByNegative_equiv_of_inputs
    {x x' y y' : RealCompute} {N : Nat}
    (hx : x.Valid) (hx' : x'.Valid) (hy : y.Valid) (hy' : y'.Valid)
    (hxx' : x.Equiv x') (hyy' : y.Equiv y')
    (hYneg : (y.compute N).hi < 0)
    (hY'neg : (y'.compute N).hi < 0) :
    (divByNegative x y N).Equiv (divByNegative x' y' N) := by
  unfold divByNegative
  apply mul_equiv hx hx'
    (negativeInv_valid hy hYneg)
    (negativeInv_valid hy' hY'neg)
    hxx'
  exact negativeInv_equiv_of_input hy hy' hyy' hYneg hY'neg

theorem negativeInv_mul_self_equiv_one {x : RealCompute} {N : Nat}
    (hx : x.Valid) (hneg : (x.compute N).hi < 0) :
    (mul x (negativeInv x N)).Equiv one := by
  have hnx : (-x).Valid := neg_valid hx
  have hpos : 0 < ((-x).compute N).lo := by
    change 0 < -(x.compute N).hi
    grind
  have hp : (positiveInv (-x) N).Valid := positiveInv_valid hnx hpos
  have hfirst := mul_equiv
    hx (neg_valid (neg_valid hx))
    (neg_valid hp) (neg_valid hp)
    (equiv_symm (neg_neg_equiv hx))
    (equiv_refl _ (neg_valid hp))
  have hsecond := mul_neg_neg_equiv (neg_valid hx) hp
  have hthird := positiveInv_mul_self_equiv_one hnx hpos
  unfold negativeInv
  have hA : (mul x (-positiveInv (-x) N)).Valid :=
    mul_valid hx (neg_valid hp)
  have hB : (mul (-(-x)) (-positiveInv (-x) N)).Valid :=
    mul_valid (neg_valid (neg_valid hx)) (neg_valid hp)
  have hC : (mul (-x) (positiveInv (-x) N)).Valid :=
    mul_valid (neg_valid hx) hp
  have hone : one.Valid := by
    exact ofRat_valid 1
  exact equiv_trans hA hC hone
    (equiv_trans hA hB hC hfirst hsecond) hthird

end RealCompute

namespace ComplexCompute

/-- The literal product of two valid complex raw stages is an ordered box.
This supplies the first component of raw-product validity. -/
theorem mul_compute_ordered {z w : ComplexCompute}
    (hz : z.Valid) (hw : w.Valid) (n : Nat) :
    ((mul z w).compute n).Ordered := by
  change QBox.Ordered (QBox.mul (z.compute n) (w.compute n))
  exact QBox.mul_ordered (valid_ordered hz n) (valid_ordered hw n)

/-- The literal product boxes of two valid raw inputs refine stage by stage.
This supplies the nesting component of raw-product validity. -/
theorem mul_compute_nested {z w : ComplexCompute}
    (hz : z.Valid) (hw : w.Valid) {n m : Nat} (hnm : n <= m) :
    QBox.NestedIn ((mul z w).compute m) ((mul z w).compute n) := by
  change QBox.NestedIn (QBox.mul (z.compute m) (w.compute m))
    (QBox.mul (z.compute n) (w.compute n))
  exact QBox.mul_nested
    (valid_ordered hz m) (valid_ordered hw m)
    (valid_nestedIn hz hnm) (valid_nestedIn hw hnm)

/-- Once a concrete product algorithm supplies its rational width modulus,
the already-proved order and nesting facts assemble a valid raw complex
product.  The premise is the remaining general multiplication obligation. -/
theorem mul_valid_of_widthsShrink {z w : ComplexCompute}
    (hz : z.Valid) (hw : w.Valid)
    (hshrink : ComplexCompute.WidthsShrinkToZero (mul z w).compute) :
    (mul z w).Valid := by
  constructor
  · intro n
    exact (QBox.ordered_iff_width_height_nonneg _).1
      (mul_compute_ordered hz hw n)
  · constructor
    · intro n m hnm
      have hnest := mul_compute_nested hz hw hnm
      exact ⟨hnest.1.1, hnest.2.1, hnest.1.2, hnest.2.2⟩
    · exact hshrink

/-- Arbitrary valid complex raw algorithms are closed under the literal
four-corner complex product.  The width schedule is obtained constructively
from the two finite stage-zero boxes: validity nests every later coordinate
inside those boxes, whose explicit rational radii bound multiplication.

This is a raw-box theorem, not an appeal to multiplication in a completed
complex plane. -/
theorem mul_valid {z w : ComplexCompute}
    (hz : z.Valid) (hw : w.Valid) :
    (mul z w).Valid := by
  apply mul_valid_of_widthsShrink hz hw
  intro eps
  let Bz : Rat := (z.compute 0).coordinateRadius
  let Bw : Rat := (w.compute 0).coordinateRadius
  let B : Rat := Bz + Bw
  have hBzpos : 0 < Bz := by
    dsimp [Bz]
    exact QBox.coordinateRadius_pos _
  have hBwpos : 0 < Bw := by
    dsimp [Bw]
    exact QBox.coordinateRadius_pos _
  have hBpos : 0 < B := by
    dsimp [B]
    grind
  have height : 0 < (8 : Rat) * B :=
    Rat.mul_pos (by decide +kernel) hBpos
  let delta : QPos := ⟨eps.val / ((8 : Rat) * B), by
    rw [Rat.div_def]
    exact Rat.mul_pos eps.property ((Rat.inv_pos).2 height)⟩
  obtain ⟨Nz, hNz⟩ := hz.2.2 delta
  obtain ⟨Nw, hNw⟩ := hw.2.2 delta
  refine ⟨Nat.max Nz Nw, ?_⟩
  intro n hn
  have hnz : Nz <= n := Nat.le_trans (Nat.le_max_left _ _) hn
  have hnw : Nw <= n := Nat.le_trans (Nat.le_max_right _ _) hn
  have hznarrow := hNz n hnz
  have hwnarrow := hNw n hnw
  have hzradius : (z.compute n).CoordinateBounded Bz := by
    apply QBox.coordinateBounded_of_nested
      (valid_ordered hz n) (valid_nestedIn hz (Nat.zero_le n))
    exact QBox.coordinateBounded_radius _
  have hwradius : (w.compute n).CoordinateBounded Bw := by
    apply QBox.coordinateBounded_of_nested
      (valid_ordered hw n) (valid_nestedIn hw (Nat.zero_le n))
    exact QBox.coordinateBounded_radius _
  have hBzle : Bz <= B := by
    dsimp [B]
    have hBw0 : 0 <= Bw := Rat.le_of_lt hBwpos
    grind
  have hBwle : Bw <= B := by
    dsimp [B]
    have hBz0 : 0 <= Bz := Rat.le_of_lt hBzpos
    grind
  have hzbound : (z.compute n).CoordinateBounded B :=
    hzradius.mono hBzle
  have hwbound : (w.compute n).CoordinateBounded B :=
    hwradius.mono hBwle
  have hproduct := QBox.mul_width_height_le_of_coordinateBounded
    (valid_ordered hz n) (valid_ordered hw n) hzbound hwbound
  have hsum :
      (z.compute n).width + (z.compute n).height +
          (w.compute n).width + (w.compute n).height <= 4 * delta.val := by
    grind
  have hconstant_nonneg : 0 <= 2 * B := by
    have hB0 : 0 <= B := Rat.le_of_lt hBpos
    grind
  have hscaled :
      2 * B * ((z.compute n).width + (z.compute n).height +
          (w.compute n).width + (w.compute n).height) <= eps.val := by
    calc
      2 * B * ((z.compute n).width + (z.compute n).height +
            (w.compute n).width + (w.compute n).height) <=
          2 * B * (4 * delta.val) :=
        Rat.mul_le_mul_of_nonneg_left hsum hconstant_nonneg
      _ = eps.val := by
        dsimp [delta]
        rw [Rat.div_def]
        have hne : (8 : Rat) * B ≠ 0 := Rat.ne_of_gt height
        grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
  exact ⟨Rat.le_trans hproduct.1 hscaled,
    Rat.le_trans hproduct.2 hscaled⟩

/-- Multiplication respects the project's overlap equality on valid complex
raw algorithms.  At each stage, the finite overlap witnesses for the two
input boxes provide rational points in their intersections; the four-corner
product boxes both contain the product of those points. -/
theorem mul_equiv {z z' w w' : ComplexCompute}
    (hz : z.Valid) (hz' : z'.Valid) (hw : w.Valid) (hw' : w'.Valid)
    (hzz' : z.Equiv z') (hww' : w.Equiv w') :
    (mul z w).Equiv (mul z' w') := by
  intro n
  have hzz := (compareAt_overlap_iff z z' n n).1 (hzz' n)
  have hww := (compareAt_overlap_iff w w' n n).1 (hww' n)
  apply (compareAt_overlap_iff (mul z w) (mul z' w') n n).2
  change QBox.Overlaps (QBox.mul (z.compute n) (w.compute n))
    (QBox.mul (z'.compute n) (w'.compute n))
  exact QBox.mul_overlaps_of_overlaps
    (valid_ordered hz n) (valid_ordered hz' n)
    (valid_ordered hw n) (valid_ordered hw' n) hzz hww

private theorem mulI_contains_rotation_point {z : ComplexCompute} {p : QComplex}
    (n : Nat) (hp : (z.compute n).lo <= p /\ p <= (z.compute n).hi) :
    ((mulI z).compute n).lo <= { re := -p.im, im := p.re } /\
      { re := -p.im, im := p.re } <= ((mulI z).compute n).hi := by
  change
    (-((z.compute n).hi.im) <= -p.im /\ (z.compute n).lo.re <= p.re) /\
      (-p.im <= -((z.compute n).lo.im) /\ p.re <= (z.compute n).hi.re)
  exact ⟨⟨Rat.neg_le_neg hp.2.2, hp.1.1⟩,
    ⟨Rat.neg_le_neg hp.1.2, hp.2.1⟩⟩

private theorem qcomplex_mul_as_affine_rotation (c p : QComplex) :
    QComplex.add (QComplex.scaleRat c.re p)
      (QComplex.scaleRat c.im { re := -p.im, im := p.re }) =
      QComplex.mul c p := by
  cases c
  cases p
  simp only [QComplex.add, QComplex.scaleRat, QComplex.mul]
  congr 1 <;> grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
    Rat.mul_assoc, Rat.mul_comm]

/-- Exact rational complex scalar multiplication agrees with the general
four-corner product.  The affine representation remains a convenient exact
evaluator, while this bridge lets later theorems use ordinary raw-complex
multiplication without selecting a special scalar implementation. -/
theorem qcomplexLeftMul_equiv_mul_ofQComplex (c : QComplex) {z : ComplexCompute}
    (hz : z.Valid) :
    (qcomplexLeftMul c z).Equiv (mul (ofQComplex c) z) := by
  intro n
  let p := (z.compute n).center
  have hp : (z.compute n).lo <= p /\ p <= (z.compute n).hi :=
    QBox.center_mem (valid_ordered hz n)
  have hrotate := mulI_contains_rotation_point n hp
  have hscale := QBox.scaleRat_contains (r := c.re) hp.1 hp.2
  have hrotateScale := QBox.scaleRat_contains (r := c.im) hrotate.1 hrotate.2
  have haffine := QBox.add_contains hscale.1 hscale.2
    hrotateScale.1 hrotateScale.2
  have hformula := qcomplex_mul_as_affine_rotation c p
  have haffine' :
      ((qcomplexLeftMul c z).compute n).lo <= QComplex.mul c p /\
        QComplex.mul c p <= ((qcomplexLeftMul c z).compute n).hi := by
    change
      (QBox.add (QBox.scaleRat c.re (z.compute n))
        (QBox.scaleRat c.im ((mulI z).compute n))).lo <= QComplex.mul c p /\
      QComplex.mul c p <=
        (QBox.add (QBox.scaleRat c.re (z.compute n))
          (QBox.scaleRat c.im ((mulI z).compute n))).hi
    rw [← hformula]
    exact haffine
  have hproduct :
      ((mul (ofQComplex c) z).compute n).lo <= QComplex.mul c p /\
        QComplex.mul c p <= ((mul (ofQComplex c) z).compute n).hi := by
    change (QBox.mul (QBox.point c) (z.compute n)).lo <= QComplex.mul c p /\
      QComplex.mul c p <= (QBox.mul (QBox.point c) (z.compute n)).hi
    exact QBox.mul_contains (QComplex.le_refl c) (QComplex.le_refl c) hp.1 hp.2
  apply (compareAt_overlap_iff (qcomplexLeftMul c z) (mul (ofQComplex c) z)
    n n).2
  exact ⟨QComplex.le_trans haffine'.1 hproduct.2,
    QComplex.le_trans hproduct.1 haffine'.2⟩

end ComplexCompute

end ComputableAnalysis


