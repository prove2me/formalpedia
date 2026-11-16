-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Analysis_RealMultiplication
-- name    : liuyao_ca_fd889115_k1_Analysis_RealMultiplication
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T17:54:37.791221+00:00
-- url     : https://prove2.me/theorems/3215ad77-c393-4ed8-9070-ae22f39acb4c
-- title:
--   Computable analysis · RealMultiplication · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableAnalysis/RealMultiplication.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_ComplexMultiplication
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_Differential

set_option autoImplicit true

/-!
# General multiplication of raw interval reals

`RealCompute.mul` is the literal four-corner interval product already defined in
`Basic`.  The early API certified it only under nonnegativity hypotheses.
This file proves the general signed closure theorem directly from finite
rational interval estimates.  No completed real multiplication is used.
-/

namespace ComputableAnalysis

namespace QInterval

/-- Both endpoints of a rational interval are bounded in absolute value. -/
def AbsBounded (I : QInterval) (B : Rat) : Prop :=
  qabs I.lo <= B /\ qabs I.hi <= B

/-- A strictly positive rational bound for both endpoints. -/
def absRadius (I : QInterval) : Rat :=
  1 + qabs I.lo + qabs I.hi

theorem absRadius_pos (I : QInterval) : 0 < I.absRadius := by
  unfold absRadius
  grind [qabs_nonneg I.lo, qabs_nonneg I.hi]

theorem absBounded_absRadius (I : QInterval) :
    I.AbsBounded I.absRadius := by
  unfold AbsBounded absRadius
  constructor
  · grind [qabs_nonneg I.hi]
  · grind [qabs_nonneg I.lo]

theorem AbsBounded.mono {I : QInterval} {B C : Rat}
    (hI : I.AbsBounded B) (hBC : B <= C) : I.AbsBounded C := by
  exact ⟨Rat.le_trans hI.1 hBC, Rat.le_trans hI.2 hBC⟩

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

/-- An ordered interval contained in an absolute-bounded interval inherits
the same bound. -/
theorem absBounded_of_contains {inner outer : QInterval} {B : Rat}
    (hinner : inner.lo <= inner.hi)
    (hcontains : outer.ContainsInterval inner)
    (houter : outer.AbsBounded B) : inner.AbsBounded B := by
  constructor
  · exact qabs_le_of_endpoint_bounds houter.1 houter.2
      hcontains.1 (Rat.le_trans hinner hcontains.2)
  · exact qabs_le_of_endpoint_bounds houter.1 houter.2
      (Rat.le_trans hcontains.1 hinner) hcontains.2

/-- Every rational point in an absolute-bounded interval inherits the same
absolute bound. -/
theorem qabs_le_of_mem_absBounded {I : QInterval} {x B : Rat}
    (hI : I.AbsBounded B) (hx : I.lo <= x /\ x <= I.hi) :
    qabs x <= B :=
  qabs_le_of_endpoint_bounds hI.1 hI.2 hx.1 hx.2

/-- Products of two pairs of overlapping ordered intervals overlap. -/
theorem mulRealInterval_overlaps_of_overlaps
    {A A' B B' : QInterval}
    (hA : A.lo <= A.hi) (hA' : A'.lo <= A'.hi)
    (hB : B.lo <= B.hi) (hB' : B'.lo <= B'.hi)
    (hAA' : A.Overlaps A') (hBB' : B.Overlaps B') :
    (QBox.mulRealInterval A.lo A.hi B.lo B.hi).Overlaps
      (QBox.mulRealInterval A'.lo A'.hi B'.lo B'.hi) := by
  unfold Overlaps at hAA' hBB'
  let x : Rat := if A.lo <= A'.lo then A'.lo else A.lo
  let y : Rat := if B.lo <= B'.lo then B'.lo else B.lo
  have hxA : A.lo <= x := by dsimp [x]; split <;> grind
  have hxA' : A'.lo <= x := by dsimp [x]; split <;> grind
  have hxAh : x <= A.hi := by
    dsimp [x]
    split <;> grind
  have hxA'h : x <= A'.hi := by
    dsimp [x]
    split <;> grind
  have hyB : B.lo <= y := by dsimp [y]; split <;> grind
  have hyB' : B'.lo <= y := by dsimp [y]; split <;> grind
  have hyBh : y <= B.hi := by
    dsimp [y]
    split <;> grind
  have hyB'h : y <= B'.hi := by
    dsimp [y]
    split <;> grind
  have hp := QBox.mulRealInterval_contains hxA hxAh hyB hyBh
  have hp' := QBox.mulRealInterval_contains hxA' hxA'h hyB' hyB'h
  exact ⟨Rat.le_trans hp.1 hp'.2, Rat.le_trans hp'.1 hp.2⟩

private theorem qabs_minRat_le {a b R : Rat}
    (ha : qabs a <= R) (hb : qabs b <= R) :
    qabs (minRat a b) <= R := by
  unfold minRat
  split <;> assumption

private theorem qabs_maxRat2_le {a b R : Rat}
    (ha : qabs a <= R) (hb : qabs b <= R) :
    qabs (maxRat2 a b) <= R := by
  unfold maxRat2
  split <;> assumption

private theorem qabs_min4_le {a b c d R : Rat}
    (ha : qabs a <= R) (hb : qabs b <= R)
    (hc : qabs c <= R) (hd : qabs d <= R) :
    qabs (min4 a b c d) <= R := by
  exact qabs_minRat_le (qabs_minRat_le ha hb) (qabs_minRat_le hc hd)

private theorem qabs_max4_le {a b c d R : Rat}
    (ha : qabs a <= R) (hb : qabs b <= R)
    (hc : qabs c <= R) (hd : qabs d <= R) :
    qabs (max4 a b c d) <= R := by
  exact qabs_maxRat2_le (qabs_maxRat2_le ha hb) (qabs_maxRat2_le hc hd)

/-- The endpoints selected by the four-corner product inherit the product of
two supplied absolute endpoint bounds. -/
theorem mulRealInterval_absBounded
    {I J : QInterval} {A B : Rat}
    (hI : I.AbsBounded A) (hJ : J.AbsBounded B) :
    (QBox.mulRealInterval I.lo I.hi J.lo J.hi).AbsBounded (A * B) := by
  have hll : qabs (I.lo * J.lo) <= A * B := by
    rw [qabs_mul]
    exact rat_mul_le_mul_of_nonneg (qabs_nonneg _) hI.1
      (qabs_nonneg _) hJ.1
  have hlh : qabs (I.lo * J.hi) <= A * B := by
    rw [qabs_mul]
    exact rat_mul_le_mul_of_nonneg (qabs_nonneg _) hI.1
      (qabs_nonneg _) hJ.2
  have hhl : qabs (I.hi * J.lo) <= A * B := by
    rw [qabs_mul]
    exact rat_mul_le_mul_of_nonneg (qabs_nonneg _) hI.2
      (qabs_nonneg _) hJ.1
  have hhh : qabs (I.hi * J.hi) <= A * B := by
    rw [qabs_mul]
    exact rat_mul_le_mul_of_nonneg (qabs_nonneg _) hI.2
      (qabs_nonneg _) hJ.2
  change qabs (min4 (I.lo * J.lo) (I.lo * J.hi)
      (I.hi * J.lo) (I.hi * J.hi)) <= A * B /\
    qabs (max4 (I.lo * J.lo) (I.lo * J.hi)
      (I.hi * J.lo) (I.hi * J.hi)) <= A * B
  exact ⟨qabs_min4_le hll hlh hhl hhh,
    qabs_max4_le hll hlh hhl hhh⟩

end QInterval

namespace RealCompute

/-! The public signed multiplication laws now live in `ComplexMultiplication`.
Retain these earlier proof bodies privately for the interval-function assembly
below, without redeclaring the imported public theorem names. -/

/-- Every stage of the literal product of valid raw reals is ordered. -/
private theorem legacyMulComputeOrdered {x y : RealCompute}
    (hx : x.Valid) (hy : y.Valid) (n : Nat) :
    0 <= ((mul x y).compute n).width := by
  change 0 <= (QBox.mulRealInterval
    (x.compute n).lo (x.compute n).hi
    (y.compute n).lo (y.compute n).hi).width
  have hordered := QBox.mulRealInterval_ordered
    (interval_order_of_valid x hx n) (interval_order_of_valid y hy n)
  unfold QInterval.width
  grind [Rat.sub_eq_add_neg]

/-- Literal product intervals refine whenever both input intervals refine. -/
private theorem legacyMulComputeNested {x y : RealCompute}
    (hx : x.Valid) (hy : y.Valid) {n m : Nat} (hnm : n <= m) :
    ((mul x y).compute n).ContainsInterval ((mul x y).compute m) := by
  have hxn := hx.2.1 n m hnm
  have hyn := hy.2.1 n m hnm
  change (QBox.mulRealInterval
      (x.compute n).lo (x.compute n).hi
      (y.compute n).lo (y.compute n).hi).ContainsInterval
    (QBox.mulRealInterval
      (x.compute m).lo (x.compute m).hi
      (y.compute m).lo (y.compute m).hi)
  exact QBox.mulRealInterval_nested
    hxn.1 hxn.2.1 hxn.2.2 hyn.1 hyn.2.1 hyn.2.2

/-- Order, nesting, and a supplied width-shrink proof assemble general
raw-real product validity. -/
private theorem legacyMulValidOfWidthsShrink {x y : RealCompute}
    (hx : x.Valid) (hy : y.Valid)
    (hshrink : WidthsShrinkToZero (mul x y).compute) :
    (mul x y).Valid := by
  constructor
  · exact legacyMulComputeOrdered hx hy
  · constructor
    · intro n m hnm
      have hnest := legacyMulComputeNested hx hy hnm
      have horderWidth := legacyMulComputeOrdered hx hy m
      have horder : ((mul x y).compute m).lo <=
          ((mul x y).compute m).hi := by
        unfold QInterval.width at horderWidth
        grind [Rat.sub_eq_add_neg]
      exact ⟨hnest.1, horder, hnest.2⟩
    · exact hshrink

/-- Arbitrary valid raw interval reals are closed under the signed
four-corner product. -/
private theorem legacyMulValid {x y : RealCompute}
    (hx : x.Valid) (hy : y.Valid) : (mul x y).Valid := by
  apply legacyMulValidOfWidthsShrink hx hy
  intro eps
  let Bx : Rat := (x.compute 0).absRadius
  let By : Rat := (y.compute 0).absRadius
  let B : Rat := Bx + By
  have hBxpos : 0 < Bx := QInterval.absRadius_pos _
  have hBypos : 0 < By := QInterval.absRadius_pos _
  have hBpos : 0 < B := by dsimp [B]; grind
  have h4B : 0 < (4 : Rat) * B :=
    Rat.mul_pos (by decide +kernel) hBpos
  let delta : QPos :=
    { val := eps.val / ((4 : Rat) * B)
      property := by
        rw [Rat.div_def]
        exact Rat.mul_pos eps.property ((Rat.inv_pos).2 h4B) }
  obtain ⟨Nx, hNx⟩ := hx.2.2 delta
  obtain ⟨Ny, hNy⟩ := hy.2.2 delta
  refine ⟨Nat.max Nx Ny, ?_⟩
  intro n hn
  have hxw := hNx n (Nat.le_trans (Nat.le_max_left _ _) hn)
  have hyw := hNy n (Nat.le_trans (Nat.le_max_right _ _) hn)
  have hxb : (x.compute n).AbsBounded B := by
    apply QInterval.AbsBounded.mono
      (QInterval.absBounded_of_contains
        (interval_order_of_valid x hx n)
        ⟨(hx.2.1 0 n (Nat.zero_le n)).1,
          (hx.2.1 0 n (Nat.zero_le n)).2.2⟩
        (QInterval.absBounded_absRadius _))
    dsimp [B, Bx, By]
    grind [Rat.le_of_lt hBypos]
  have hyb : (y.compute n).AbsBounded B := by
    apply QInterval.AbsBounded.mono
      (QInterval.absBounded_of_contains
        (interval_order_of_valid y hy n)
        ⟨(hy.2.1 0 n (Nat.zero_le n)).1,
          (hy.2.1 0 n (Nat.zero_le n)).2.2⟩
        (QInterval.absBounded_absRadius _))
    dsimp [B, Bx, By]
    grind [Rat.le_of_lt hBxpos]
  have hp := QBox.mulRealInterval_width_le_of_abs_bounded
    (interval_order_of_valid x hx n) (interval_order_of_valid y hy n)
    hxb.1 hyb.1 hyb.2
  have hsum :
      (x.compute n).width + (y.compute n).width <= 2 * delta.val := by
    grind
  calc
    ((mul x y).compute n).width <=
        2 * B * ((x.compute n).width + (y.compute n).width) := hp
    _ <= 2 * B * (2 * delta.val) :=
      Rat.mul_le_mul_of_nonneg_left hsum (by grind [Rat.le_of_lt hBpos])
    _ = eps.val := by
      dsimp [delta]
      rw [Rat.div_def]
      have hne : (4 : Rat) * B ≠ 0 := Rat.ne_of_gt h4B
      grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]

/-- General signed multiplication respects overlap equality. -/
private theorem legacyMulEquiv {x x' y y' : RealCompute}
    (hx : x.Valid) (hx' : x'.Valid) (hy : y.Valid) (hy' : y'.Valid)
    (hxx' : x.Equiv x') (hyy' : y.Equiv y') :
    (mul x y).Equiv (mul x' y') := by
  intro n
  have hxx := (compareAt_overlap_iff x x' n n).1
    (sameStageOverlap_of_equiv hx hx' hxx' n)
  have hyy := (compareAt_overlap_iff y y' n n).1
    (sameStageOverlap_of_equiv hy hy' hyy' n)
  apply (compareAt_overlap_iff (mul x y) (mul x' y') n n).2
  exact QInterval.mulRealInterval_overlaps_of_overlaps
    (interval_order_of_valid x hx n) (interval_order_of_valid x' hx' n)
    (interval_order_of_valid y hy n) (interval_order_of_valid y' hy' n)
    hxx hyy

end RealCompute

namespace RealFunRaw

/-- Pointwise multiplication of arbitrary valid interval-real functions is
valid.  Stage-zero enclosures provide the finite local bounds automatically. -/
theorem mul_valid {f g : RealFunRaw} (hf : f.Valid) (hg : g.Valid) :
    (mul f g).Valid := by
  intro x hx
  let X : RealCompute := { compute := f.compute x }
  let Y : RealCompute := { compute := g.compute x }
  have hX : X.Valid := by
    simpa [X, RealCompute.Valid, RealFunRaw.applyCompute] using hf x hx.1
  have hY : Y.Valid := by
    simpa [Y, RealCompute.Valid, RealFunRaw.applyCompute] using hg x hx.2
  have hproduct : (RealCompute.mul X Y).Valid := RealCompute.mul_valid hX hY
  change RealCompute.ValidCompute (RealCompute.mulCompute X Y) at hproduct
  change RealCompute.ValidCompute (RealCompute.mulCompute X Y)
  exact hproduct

end RealFunRaw

namespace FunctionOnInterval

/-- A uniform finite rational absolute bound for every endpoint produced by
an interval function on its chart.  This is executable quantitative metadata,
not a compactness theorem: clients provide the radius and its endpoint proof. -/
structure UniformAbsBound (F : FunctionOnInterval) where
  radius : Rat
  radius_pos : 0 < radius
  endpoints : forall x (hx : inDomainInterval F.lower F.upper x) n,
    (F.compute x hx n).AbsBounded radius

namespace UniformAbsBound

/-- Enlarge a uniform bound to any larger strictly positive rational radius. -/
def mono {F : FunctionOnInterval} (B : UniformAbsBound F)
    (radius : Rat) (hradius : 0 < radius) (hle : B.radius <= radius) :
    UniformAbsBound F where
  radius := radius
  radius_pos := hradius
  endpoints := fun x hx n => (B.endpoints x hx n).mono hle

end UniformAbsBound

/-- Pointwise multiplication of arbitrary valid functions on a common
rational interval.  Unlike the earlier positive-bounded constructor, no sign
or externally supplied range bound is required. -/
def mul
    (F G : FunctionOnInterval)
    (same_lower : F.lower = G.lower)
    (same_upper : F.upper = G.upper) : FunctionOnInterval where
  raw :=
    { definedAt := fun x =>
        inDomainInterval F.lower F.upper x /\
          F.raw.definedAt x /\ G.raw.definedAt x
      compute := fun x hx n =>
        QBox.mulRealInterval
          (F.raw.compute x hx.2.1 n).lo (F.raw.compute x hx.2.1 n).hi
          (G.raw.compute x hx.2.2 n).lo (G.raw.compute x hx.2.2 n).hi }
  lower := F.lower
  upper := F.upper
  defined_on := by
    intro x hx
    refine ⟨hx, F.defined_on x hx, G.defined_on x ?_⟩
    constructor
    · rw [← same_lower]
      exact hx.1
    · rw [← same_upper]
      exact hx.2
  valid_on := by
    intro x hx
    let X : RealCompute := { compute := F.raw.compute x hx.2.1 }
    let Y : RealCompute := { compute := G.raw.compute x hx.2.2 }
    have hX : X.Valid := by
      simpa [X, RealCompute.Valid] using F.valid_on x hx.2.1
    have hY : Y.Valid := by
      simpa [Y, RealCompute.Valid] using G.valid_on x hx.2.2
    have hproduct := RealCompute.mul_valid hX hY
    change RealCompute.ValidCompute
      (fun n => QBox.mulRealInterval
        (F.raw.compute x hx.2.1 n).lo (F.raw.compute x hx.2.1 n).hi
        (G.raw.compute x hx.2.2 n).lo (G.raw.compute x hx.2.2 n).hi)
    change RealCompute.ValidCompute (RealCompute.mulCompute X Y) at hproduct
    exact hproduct

@[simp] theorem mul_compute
    (F G : FunctionOnInterval)
    (same_lower : F.lower = G.lower)
    (same_upper : F.upper = G.upper)
    (x : Rat) (hx : inDomainInterval F.lower F.upper x) (n : Nat) :
    (mul F G same_lower same_upper).compute x
      (by simpa [mul] using
        (show inDomainInterval F.lower F.upper x from hx)) n =
      QBox.mulRealInterval
        (F.compute x hx n).lo (F.compute x hx n).hi
        (G.compute x (by
          constructor
          · rw [← same_lower]
            exact hx.1
          · rw [← same_upper]
            exact hx.2) n).lo
        (G.compute x (by
          constructor
          · rw [← same_lower]
            exact hx.1
          · rw [← same_upper]
            exact hx.2) n).hi := by
  rfl

namespace UniformAbsBound

/-- The pointwise product of uniformly bounded interval functions is
uniformly bounded by the product of their radii. -/
def mul {F G : FunctionOnInterval}
    (same_lower : F.lower = G.lower) (same_upper : F.upper = G.upper)
    (BF : UniformAbsBound F) (BG : UniformAbsBound G) :
    UniformAbsBound (FunctionOnInterval.mul F G same_lower same_upper) where
  radius := BF.radius * BG.radius
  radius_pos := Rat.mul_pos BF.radius_pos BG.radius_pos
  endpoints := by
    intro x hx n
    have hFx : inDomainInterval F.lower F.upper x := by
      simpa [FunctionOnInterval.mul] using hx
    have hGx : inDomainInterval G.lower G.upper x := by
      constructor
      · rw [← same_lower]
        exact hFx.1
      · rw [← same_upper]
        exact hFx.2
    change (QBox.mulRealInterval
      (F.compute x hFx n).lo (F.compute x hFx n).hi
      (G.compute x hGx n).lo (G.compute x hGx n).hi).AbsBounded
        (BF.radius * BG.radius)
    exact QInterval.mulRealInterval_absBounded
      (BF.endpoints x hFx n) (BG.endpoints x hGx n)

end UniformAbsBound

/-- General signed pointwise multiplication transports along the local
representation graph. -/
theorem equivalent_mul
    (F F' G G' : FunctionOnInterval)
    (hFF' : Equivalent F F') (hGG' : Equivalent G G')
    (same_lower_FG : F.lower = G.lower) (same_upper_FG : F.upper = G.upper)
    (same_lower_F'G' : F'.lower = G'.lower)
    (same_upper_F'G' : F'.upper = G'.upper) :
    Equivalent
      (FunctionOnInterval.mul F G same_lower_FG same_upper_FG)
      (FunctionOnInterval.mul F' G' same_lower_F'G' same_upper_F'G') := by
  refine ⟨hFF'.1, hFF'.2.1, ?_⟩
  intro x hx hx'
  let hxG : inDomainInterval G.lower G.upper x :=
    ⟨by rw [← same_lower_FG]; exact hx.1,
      by rw [← same_upper_FG]; exact hx.2⟩
  let hxG' : inDomainInterval G'.lower G'.upper x :=
    ⟨by rw [← same_lower_F'G']; exact hx'.1,
      by rw [← same_upper_F'G']; exact hx'.2⟩
  have hXF : (PartialRealFunRaw.apply F.raw F.valid_on x
      (F.defined_on x hx)).Valid := by
    change RealCompute.ValidCompute (F.raw.compute x (F.defined_on x hx))
    exact F.valid_on x (F.defined_on x hx)
  have hXG : (PartialRealFunRaw.apply G.raw G.valid_on x
      (G.defined_on x hxG)).Valid := by
    change RealCompute.ValidCompute (G.raw.compute x (G.defined_on x hxG))
    exact G.valid_on x (G.defined_on x hxG)
  have hXF' : (PartialRealFunRaw.apply F'.raw F'.valid_on x
      (F'.defined_on x hx')).Valid := by
    change RealCompute.ValidCompute (F'.raw.compute x (F'.defined_on x hx'))
    exact F'.valid_on x (F'.defined_on x hx')
  have hXG' : (PartialRealFunRaw.apply G'.raw G'.valid_on x
      (G'.defined_on x hxG')).Valid := by
    change RealCompute.ValidCompute (G'.raw.compute x (G'.defined_on x hxG'))
    exact G'.valid_on x (G'.defined_on x hxG')
  change (RealCompute.mul
      (PartialRealFunRaw.apply F.raw F.valid_on x (F.defined_on x hx))
      (PartialRealFunRaw.apply G.raw G.valid_on x
        (G.defined_on x hxG))).Equiv
    (RealCompute.mul
      (PartialRealFunRaw.apply F'.raw F'.valid_on x
        (F'.defined_on x hx'))
      (PartialRealFunRaw.apply G'.raw G'.valid_on x
        (G'.defined_on x hxG')))
  exact RealCompute.mul_equiv hXF hXF' hXG hXG'
    (hFF'.2.2 x hx hx') (hGG'.2.2 x hxG hxG')

end FunctionOnInterval

end ComputableAnalysis


