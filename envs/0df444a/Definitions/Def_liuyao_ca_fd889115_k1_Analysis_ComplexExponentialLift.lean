-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Analysis_ComplexExponentialLift
-- name    : liuyao_ca_fd889115_k1_Analysis_ComplexExponentialLift
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T17:59:16.748396+00:00
-- url     : https://prove2.me/theorems/4fb1e300-8bd8-4f8c-968d-8bd9db6e569a
-- title:
--   Computable analysis · ComplexExponentialLift · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableAnalysis/ComplexExponentialLift.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_ComplexPowerCalculus

set_option autoImplicit true

/-!
# Exponential of a bounded represented complex number

This module lifts the rational-complex Taylor evaluator to nested rational
box representations.  At stage `n` it evaluates a finite Taylor prefix at
the center of the input's `n`th box.  A single rational radius budgets both
the movement of that center and the remaining factorial tail; finite-prefix
intersection then produces a valid `ComplexCompute`.
-/

namespace ComputableAnalysis
namespace ComplexExponentialLift

open ComplexExponentialApproximation

namespace QBox

/-- If one ordered rational complex box is nested in another, the distance
between their centers is bounded by the outer coordinate widths. -/
theorem center_sub_center_normBound_le_width_add_height_of_nested
    {outer inner : QBox} (hOuter : outer.Ordered)
    (hInner : inner.Ordered) (hNested : inner.NestedIn outer) :
    QComplex.normBound (QComplex.sub outer.center inner.center) <=
      outer.width + outer.height := by
  have hOuterCenter := QBox.center_mem hOuter
  have hInnerCenter0 := QBox.center_mem hInner
  have hInnerCenter :
      outer.lo <= inner.center /\ inner.center <= outer.hi :=
    ⟨QComplex.le_trans hNested.1 hInnerCenter0.1,
      QComplex.le_trans hInnerCenter0.2 hNested.2⟩
  have hre : qabs (outer.center.re - inner.center.re) <= outer.width :=
    qabs_sub_le_of_common_bounds hOuterCenter.1.1 hOuterCenter.2.1
      hInnerCenter.1.1 hInnerCenter.2.1
  have him : qabs (outer.center.im - inner.center.im) <= outer.height :=
    qabs_sub_le_of_common_bounds hOuterCenter.1.2 hOuterCenter.2.2
      hInnerCenter.1.2 hInnerCenter.2.2
  simpa only [QComplex.normBound, QComplex.sub, QComplex.add, QComplex.neg,
    Rat.sub_eq_add_neg] using rat_add_le_add hre him

end QBox

/-- A represented complex input together with one rational norm ball
containing every sampled center. -/
structure BoundedInput (C : Rat) where
  raw : ComplexCompute
  valid : raw.Valid
  radius_nonneg : 0 <= C
  center_normBound : forall n : Nat,
    QComplex.normBound (raw.compute n).center <= C

namespace BoundedInput

def ofQComplex (z : QComplex) (C : Rat) (hC : 0 <= C)
    (hz : QComplex.normBound z <= C) : BoundedInput C where
  raw := ComplexCompute.ofQComplex z
  valid := ComplexCompute.ofQComplex_valid z
  radius_nonneg := hC
  center_normBound := by
    intro n
    have hcenter : ((ComplexCompute.ofQComplex z).compute n).center = z := by
      cases z
      simp only [ComplexCompute.ofQComplex, QBox.center]
      congr 1 <;>
        rw [Rat.div_def] <;>
        grind [Rat.add_mul, Rat.mul_assoc, Rat.mul_comm,
          Rat.mul_inv_cancel]
    rw [hcenter]
    exact hz

theorem ofQComplex_center (z : QComplex) (C : Rat) (hC : 0 <= C)
    (hz : QComplex.normBound z <= C) (n : Nat) :
    ((ofQComplex z C hC hz).raw.compute n).center = z := by
  cases z
  simp only [ofQComplex, ComplexCompute.ofQComplex, QBox.center]
  congr 1 <;>
    rw [Rat.div_def] <;>
    grind [Rat.add_mul, Rat.mul_assoc, Rat.mul_comm,
      Rat.mul_inv_cancel]

theorem center_sub_normBound_le_width_add_height
    {C : Rat} (A : BoundedInput C) (k n : Nat) (hkn : k <= n) :
    QComplex.normBound
        (QComplex.sub (A.raw.compute n).center
          (A.raw.compute k).center) <=
      (A.raw.compute k).width + (A.raw.compute k).height := by
  have hkordered := ComplexCompute.valid_ordered A.valid k
  have hnordered := ComplexCompute.valid_ordered A.valid n
  have hkcenter := QBox.center_mem hkordered
  have hncenter0 := QBox.center_mem hnordered
  have hnest := ComplexCompute.valid_nestedIn A.valid hkn
  have hncenter :
      (A.raw.compute k).lo <= (A.raw.compute n).center /\
        (A.raw.compute n).center <= (A.raw.compute k).hi :=
    ⟨QComplex.le_trans hnest.1 hncenter0.1,
      QComplex.le_trans hncenter0.2 hnest.2⟩
  have hre :
      qabs ((A.raw.compute n).center.re -
          (A.raw.compute k).center.re) <=
        (A.raw.compute k).hi.re - (A.raw.compute k).lo.re :=
    qabs_sub_le_of_common_bounds hncenter.1.1 hncenter.2.1
      hkcenter.1.1 hkcenter.2.1
  have him :
      qabs ((A.raw.compute n).center.im -
          (A.raw.compute k).center.im) <=
        (A.raw.compute k).hi.im - (A.raw.compute k).lo.im :=
    qabs_sub_le_of_common_bounds hncenter.1.2 hncenter.2.2
      hkcenter.1.2 hkcenter.2.2
  simpa only [QComplex.normBound, QComplex.sub, QComplex.add, QComplex.neg,
    QBox.width, QBox.height, Rat.sub_eq_add_neg] using rat_add_le_add hre him

/-- The Taylor degree sampled at a represented-input stage. -/
def terms (C : Rat) (stage : Nat) : Nat :=
  RationalMajorant.factorialTailStart C + stage

/-- Direct point-valued Taylor candidates at moving rational centers. -/
def candidate {C : Rat} (A : BoundedInput C) : ComplexCompute where
  compute := fun stage => QBox.point
    (expPrefix (A.raw.compute stage).center (terms C stage))

@[simp] theorem candidate_center {C : Rat} (A : BoundedInput C)
    (stage : Nat) :
    ((candidate A).compute stage).center =
      expPrefix (A.raw.compute stage).center (terms C stage) := by
  let z := expPrefix (A.raw.compute stage).center (terms C stage)
  change (QBox.point z).center = z
  cases z
  simp only [QBox.point, QBox.center]
  congr 1 <;>
        rw [Rat.div_def] <;>
        grind [Rat.add_mul, Rat.mul_assoc, Rat.mul_comm,
          Rat.mul_inv_cancel]

/-- Every moving Taylor candidate has a computable norm bound depending
only on the declared input ball.  The deliberately coarse `1` covers both
the empty prefix and the constant term; the remaining displacement from
zero is controlled by the common derivative majorant. -/
theorem candidate_center_normBound_le
    {C : Rat} (A : BoundedInput C) (stage : Nat) :
    QComplex.normBound ((candidate A).compute stage).center <=
      1 + derivativeMajorant C * C := by
  let z := (A.raw.compute stage).center
  let p := expPrefix z (terms C stage)
  let p0 := expPrefix QComplex.zero (terms C stage)
  have hzeroNorm : QComplex.normBound QComplex.zero <= C := by
    rw [QComplex.normBound_zero]
    exact A.radius_nonneg
  have hdiff := expPrefix_difference_normBound_le_uniform
    A.radius_nonneg (A.center_normBound stage) hzeroNorm (terms C stage)
  have hzdist : QComplex.normBound (QComplex.sub z QComplex.zero) <= C := by
    have hsub : QComplex.sub z QComplex.zero = z := by
      cases z
      simp [QComplex.sub, QComplex.add, QComplex.neg, QComplex.zero]
      constructor <;> grind
    rw [hsub]
    exact A.center_normBound stage
  have hdiff' : QComplex.normBound (QComplex.sub p p0) <=
      derivativeMajorant C * C :=
    Rat.le_trans (by simpa [p, p0, z] using hdiff)
      (Rat.mul_le_mul_of_nonneg_left hzdist
        (derivativeMajorant_nonneg A.radius_nonneg))
  have hp0 : QComplex.normBound p0 <= 1 := by
    have hterm : forall k : Nat,
        term QComplex.zero (k + 1) = QComplex.zero := by
      intro k
      simp [term, ComplexSeries.expTerm, QComplex.pow, QComplex.divRat,
        QComplex.mul, QComplex.zero]
      constructor <;> grind [Rat.div_def]
    have hprefix : forall k : Nat,
        expPrefix QComplex.zero (k + 1) = QComplex.one := by
      intro k
      induction k with
      | zero => decide +kernel
      | succ k ih =>
          rw [expPrefix_succ, ih, hterm]
          decide +kernel
    dsimp [p0]
    cases hterms : terms C stage with
    | zero => decide +kernel
    | succ k =>
        rw [hprefix k]
        decide +kernel
  have hsplit : p = QComplex.add (QComplex.sub p p0) p0 := by
    cases p
    cases p0
    simp [QComplex.add, QComplex.sub, QComplex.neg]
    constructor <;> grind
  rw [candidate_center]
  change QComplex.normBound p <= _
  rw [hsplit]
  exact Rat.le_trans (QComplex.normBound_add_le _ _)
    (by have := rat_add_le_add hdiff' hp0; grind)

/-- Finite input stability for two moving Taylor candidates.  No equivalence
between the represented inputs is required: a supplied rational distance
between their current centers is transported by the explicit prefix
derivative majorant. -/
theorem candidate_center_sub_normBound_le
    {C delta : Rat} (A B : BoundedInput C) (stage : Nat)
    (hdelta : QComplex.normBound
      (QComplex.sub (A.raw.compute stage).center
        (B.raw.compute stage).center) <= delta) :
    QComplex.normBound
      (QComplex.sub ((candidate A).compute stage).center
        ((candidate B).compute stage).center) <=
      derivativeMajorant C * delta := by
  have hprefix := expPrefix_difference_normBound_le_uniform
    A.radius_nonneg (A.center_normBound stage) (B.center_normBound stage)
    (terms C stage)
  have hmajorant : 0 <= derivativeMajorant C :=
    derivativeMajorant_nonneg A.radius_nonneg
  exact Rat.le_trans (by
    simpa only [candidate_center] using hprefix)
    (Rat.mul_le_mul_of_nonneg_left hdelta hmajorant)

/-- A positive Lipschitz coefficient.  The added one avoids a special case
when the exponential-prefix derivative majorant is zero. -/
def inputCoefficient (C : Rat) : Rat := derivativeMajorant C + 1

theorem inputCoefficient_pos {C : Rat} (hC : 0 <= C) :
    0 < inputCoefficient C := by
  have hmajorant := derivativeMajorant_nonneg hC
  unfold inputCoefficient
  grind

/-- The joint input-motion and Taylor-tail budget. -/
def radius {C : Rat} (A : BoundedInput C) (stage : Nat) : Rat :=
  inputCoefficient C *
      ((A.raw.compute stage).width + (A.raw.compute stage).height) +
    stageRadius C stage

theorem candidate_ordered {C : Rat} (A : BoundedInput C) (stage : Nat) :
    ((candidate A).compute stage).Ordered :=
  QComplex.le_refl _

theorem candidate_widths_shrink {C : Rat} (A : BoundedInput C) :
    ComplexCompute.WidthsShrinkToZero (candidate A).compute := by
  intro eps
  refine ⟨0, ?_⟩
  intro stage _
  constructor <;>
    simpa [candidate, QBox.point, QBox.width, QBox.height,
      Rat.sub_self] using (Rat.le_of_lt eps.property)

private theorem add_difference_tail (x y tail : QComplex) :
    QComplex.add y
      (QComplex.add (QComplex.sub x (QComplex.add y tail)) tail) = x := by
  cases x
  cases y
  cases tail
  simp [QComplex.add, QComplex.sub, QComplex.neg]
  constructor <;> grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm]

theorem candidate_future_contained_expand
    {C : Rat} (A : BoundedInput C) (k n : Nat) (hkn : k <= n) :
    ((candidate A).compute n).NestedIn
      (QBox.expand ((candidate A).compute k) (radius A k)) := by
  let extra := n - k
  have hterms : terms C n = terms C k + extra := by
    dsimp [terms, extra]
    omega
  let zn := (A.raw.compute n).center
  let zk := (A.raw.compute k).center
  let tail := tailPartial zk (terms C k) extra
  let movingError := QComplex.sub
    (expPrefix zn (terms C n)) (expPrefix zk (terms C n))
  let error := QComplex.add movingError tail
  have hprefixK :
      expPrefix zk (terms C n) =
        QComplex.add (expPrefix zk (terms C k)) tail := by
    rw [hterms]
    exact expPrefix_add zk (terms C k) extra
  have hvalue :
      expPrefix zn (terms C n) =
        QComplex.add (expPrefix zk (terms C k)) error := by
    dsimp [error, movingError]
    rw [hprefixK]
    exact (add_difference_tail
      (expPrefix zn (terms C n)) (expPrefix zk (terms C k)) tail).symm
  have hcenter := center_sub_normBound_le_width_add_height A k n hkn
  have hmoving : QComplex.normBound movingError <=
      derivativeMajorant C *
        ((A.raw.compute k).width + (A.raw.compute k).height) := by
    dsimp [movingError, zn, zk]
    exact Rat.le_trans
      (expPrefix_difference_normBound_le_uniform A.radius_nonneg
        (A.center_normBound n) (A.center_normBound k) (terms C n))
      (Rat.mul_le_mul_of_nonneg_left hcenter
        (derivativeMajorant_nonneg A.radius_nonneg))
  have htail0 := tailPartial_normBound_le A.radius_nonneg
    (A.center_normBound k) (terms C k) extra
  have htail1 := RationalMajorant.factorialTailPartial_bound
    A.radius_nonneg
    (RationalMajorant.factorialTailStart_mono C
      (RationalMajorant.factorialTailStart C) k
      (RationalMajorant.factorialTailStart_satisfies C)) extra
  have htail : QComplex.normBound tail <= stageRadius C k := by
    exact Rat.le_trans htail0 (by
      simpa [tail, terms, stageRadius] using htail1)
  have hsum0 :
      0 <= (A.raw.compute k).width + (A.raw.compute k).height :=
    Rat.add_nonneg (A.valid.1 k).1 (A.valid.1 k).2
  have hcoefficient :
      derivativeMajorant C <= inputCoefficient C := by
    unfold inputCoefficient
    grind
  have herror : QComplex.normBound error <= radius A k := by
    calc
      QComplex.normBound error <=
          QComplex.normBound movingError + QComplex.normBound tail :=
        QComplex.normBound_add_le _ _
      _ <= derivativeMajorant C *
            ((A.raw.compute k).width + (A.raw.compute k).height) +
          stageRadius C k := rat_add_le_add hmoving htail
      _ <= inputCoefficient C *
            ((A.raw.compute k).width + (A.raw.compute k).height) +
          stageRadius C k :=
        rat_add_le_add
          (Rat.mul_le_mul_of_nonneg_right hcoefficient hsum0) Rat.le_refl
      _ = radius A k := rfl
  change (QBox.point (expPrefix zn (terms C n))).NestedIn
    (QBox.expand (QBox.point (expPrefix zk (terms C k))) (radius A k))
  rw [hvalue]
  exact point_add_error_nested_expand _ _ herror

theorem radius_shrinks {C : Rat} (A : BoundedInput C) :
    ShrinksToZero (radius A) := by
  intro eps
  let K := inputCoefficient C
  have hK : 0 < K := inputCoefficient_pos A.radius_nonneg
  let inputEps : QPos :=
    ⟨eps.val / (4 * K), by
      rw [Rat.div_def]
      exact Rat.mul_pos eps.property ((Rat.inv_pos).2
        (Rat.mul_pos (by decide +kernel) hK))⟩
  let tailEps : QPos :=
    ⟨eps.val / 2, by
      rw [Rat.div_def]
      exact Rat.mul_pos eps.property
        ((Rat.inv_pos).2 (by decide +kernel))⟩
  obtain ⟨Ni, hNi⟩ := A.valid.2.2 inputEps
  obtain ⟨Nt, hNt⟩ := stageRadius_shrinks A.radius_nonneg tailEps
  refine ⟨Nat.max Ni Nt, ?_⟩
  intro n hn
  have hni : Ni <= n := Nat.le_trans (Nat.le_max_left _ _) hn
  have hnt : Nt <= n := Nat.le_trans (Nat.le_max_right _ _) hn
  have hwidths := hNi n hni
  have htail := hNt n hnt
  have hsum :
      (A.raw.compute n).width + (A.raw.compute n).height <=
        2 * inputEps.val := by
    exact Rat.le_trans (rat_add_le_add hwidths.1 hwidths.2) (by
      grind)
  have hK0 : 0 <= K := Rat.le_of_lt hK
  have hinput :
      K * ((A.raw.compute n).width + (A.raw.compute n).height) <=
        eps.val / 2 := by
    calc
      K * ((A.raw.compute n).width + (A.raw.compute n).height) <=
      K * (2 * inputEps.val) :=
        Rat.mul_le_mul_of_nonneg_left hsum hK0
      _ = eps.val / 2 := by
        dsimp [inputEps, K]
        rw [Rat.div_def, Rat.div_def]
        have h4K : (4 : Rat) * inputCoefficient C ≠ 0 :=
          Rat.ne_of_gt (Rat.mul_pos (by decide +kernel)
            (inputCoefficient_pos A.radius_nonneg))
        grind [Rat.mul_add, Rat.add_mul, Rat.mul_assoc, Rat.mul_comm,
          Rat.mul_inv_cancel ((4 : Rat) * inputCoefficient C) h4K,
          Rat.mul_inv_cancel 2 (by decide +kernel : (2 : Rat) ≠ 0)]
  unfold radius
  dsimp [K] at hinput
  exact Rat.le_trans (rat_add_le_add hinput htail) (by
    rw [Rat.div_def]
    grind [Rat.mul_add, Rat.add_assoc, Rat.add_comm,
      Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel])

/-- Exponential of a bounded represented complex number, computed by finite
Taylor prefixes and finite rational-box intersections. -/
def exponential {C : Rat} (A : BoundedInput C) : ComplexCompute :=
  ComplexCompute.cauchyStabilize (candidate A) (radius A)

theorem exponential_valid {C : Rat} (A : BoundedInput C) :
    (exponential A).Valid := by
  unfold exponential
  exact ComplexCompute.cauchyStabilize_valid
    (candidate_ordered A) (candidate_widths_shrink A)
    (candidate_future_contained_expand A) (radius_shrinks A)

/-- The stabilized represented exponential retains its current exact moving
Taylor candidate. -/
theorem exponential_contains_current_candidate
    {C : Rat} (A : BoundedInput C) (stage : Nat) :
    ((candidate A).compute stage).NestedIn
      ((exponential A).compute stage) := by
  unfold exponential
  exact ComplexCompute.cauchyStabilize_contains_current
    (candidate_future_contained_expand A) stage

/-- The stabilized exponential center differs from its retained exact Taylor
candidate by at most the two coordinate widths of the stabilized box. -/
theorem exponential_center_sub_candidate_center_normBound_le
    {C : Rat} (A : BoundedInput C) (stage : Nat) :
    QComplex.normBound
      (QComplex.sub ((exponential A).compute stage).center
        ((candidate A).compute stage).center) <=
      ((exponential A).compute stage).width +
        ((exponential A).compute stage).height :=
  QBox.center_sub_center_normBound_le_width_add_height_of_nested
    (ComplexCompute.valid_ordered (exponential_valid A) stage)
    (candidate_ordered A stage)
    (exponential_contains_current_candidate A stage)

private theorem normBound_sub_comm (z w : QComplex) :
    QComplex.normBound (QComplex.sub z w) =
      QComplex.normBound (QComplex.sub w z) := by
  cases z with
  | mk zr zi =>
    cases w with
    | mk wr wi =>
      have hre : zr + -wr = -(wr + -zr) := by grind
      have him : zi + -wi = -(wi + -zi) := by grind
      simp only [QComplex.normBound, QComplex.sub, QComplex.add, QComplex.neg]
      rw [hre, him, qabs_neg, qabs_neg]

/-- Stability of the actual stabilized exponential centers for two nearby
finite inputs.  The bound separates the two runtime output widths from the
Taylor-prefix response to the supplied input-center distance. -/
theorem exponential_center_sub_center_normBound_le
    {C delta : Rat} (A B : BoundedInput C) (stage : Nat)
    (hdelta : QComplex.normBound
      (QComplex.sub (A.raw.compute stage).center
        (B.raw.compute stage).center) <= delta) :
    QComplex.normBound
      (QComplex.sub ((exponential A).compute stage).center
        ((exponential B).compute stage).center) <=
      (((exponential A).compute stage).width +
          ((exponential A).compute stage).height) +
        derivativeMajorant C * delta +
      (((exponential B).compute stage).width +
        ((exponential B).compute stage).height) := by
  let ea := ((exponential A).compute stage).center
  let ca := ((candidate A).compute stage).center
  let cb := ((candidate B).compute stage).center
  let eb := ((exponential B).compute stage).center
  have hidentity : QComplex.sub ea eb =
      QComplex.add (QComplex.add (QComplex.sub ea ca)
        (QComplex.sub ca cb)) (QComplex.sub cb eb) := by
    cases ea
    cases ca
    cases cb
    cases eb
    simp only [QComplex.sub, QComplex.add, QComplex.neg]
    congr 1 <;> grind
  have hA := exponential_center_sub_candidate_center_normBound_le A stage
  have hCandidates := candidate_center_sub_normBound_le A B stage hdelta
  have hB0 := exponential_center_sub_candidate_center_normBound_le B stage
  have hB : QComplex.normBound (QComplex.sub cb eb) <=
      ((exponential B).compute stage).width +
        ((exponential B).compute stage).height := by
    rw [normBound_sub_comm]
    exact hB0
  have hleft :
      QComplex.normBound
          (QComplex.add (QComplex.sub ea ca) (QComplex.sub ca cb)) <=
        (((exponential A).compute stage).width +
            ((exponential A).compute stage).height) +
          derivativeMajorant C * delta :=
    Rat.le_trans
      (QComplex.normBound_add_le (QComplex.sub ea ca)
        (QComplex.sub ca cb))
      (rat_add_le_add hA hCandidates)
  rw [hidentity]
  exact Rat.le_trans
    (QComplex.normBound_add_le
      (QComplex.add (QComplex.sub ea ca) (QComplex.sub ca cb))
      (QComplex.sub cb eb))
    (rat_add_le_add hleft hB)

/-! ## Independence of the chosen bounded representative -/

def variation {C : Rat} (A : BoundedInput C) (stage : Nat) : Rat :=
  (A.raw.compute stage).width + (A.raw.compute stage).height

theorem variation_nonneg {C : Rat} (A : BoundedInput C) (stage : Nat) :
    0 <= variation A stage :=
  Rat.add_nonneg (A.valid.1 stage).1 (A.valid.1 stage).2

theorem variation_antitone {C : Rat} (A : BoundedInput C)
    (k n : Nat) (hkn : k <= n) : variation A n <= variation A k := by
  have hnest := ComplexCompute.valid_nestedIn A.valid hkn
  have hwh := QBox.width_height_le_of_nested hnest
  exact rat_add_le_add hwh.1 hwh.2

theorem center_sub_normBound_le_variation_add_of_equiv
    {C : Rat} (A B : BoundedInput C) (hAB : A.raw.Equiv B.raw)
    (m n : Nat) :
    QComplex.normBound
        (QComplex.sub (A.raw.compute m).center
          (B.raw.compute n).center) <=
      variation A m + variation B n := by
  have hAo := ComplexCompute.valid_ordered A.valid m
  have hBo := ComplexCompute.valid_ordered B.valid n
  have hAc := QBox.center_mem hAo
  have hBc := QBox.center_mem hBo
  have hover := (ComplexCompute.compareAt_overlap_iff A.raw B.raw m n).1
    (ComplexCompute.allStagesOverlap_of_equiv A.valid B.valid hAB m n)
  simp only [QComplex.le_def] at hAc hBc
  unfold QBox.Overlaps at hover
  simp only [QComplex.le_def] at hover
  have hre :
      qabs ((A.raw.compute m).center.re -
          (B.raw.compute n).center.re) <=
        (A.raw.compute m).width + (B.raw.compute n).width := by
    apply qabs_le_of_neg_le_le
    · have hupper :
          (B.raw.compute n).center.re - (A.raw.compute m).center.re <=
            (B.raw.compute n).hi.re - (A.raw.compute m).lo.re := by
        grind [Rat.sub_eq_add_neg]
      have hbound :
          (B.raw.compute n).hi.re - (A.raw.compute m).lo.re <=
            (A.raw.compute m).width + (B.raw.compute n).width := by
        unfold QBox.width
        grind [QBox.Overlaps, QComplex.le_def, Rat.sub_eq_add_neg]
      have := Rat.le_trans hupper hbound
      grind [Rat.sub_eq_add_neg]
    · have hupper :
          (A.raw.compute m).center.re - (B.raw.compute n).center.re <=
            (A.raw.compute m).hi.re - (B.raw.compute n).lo.re := by
        grind [Rat.sub_eq_add_neg]
      have hbound :
          (A.raw.compute m).hi.re - (B.raw.compute n).lo.re <=
            (A.raw.compute m).width + (B.raw.compute n).width := by
        unfold QBox.width
        grind [QBox.Overlaps, QComplex.le_def, Rat.sub_eq_add_neg]
      exact Rat.le_trans hupper hbound
  have him :
      qabs ((A.raw.compute m).center.im -
          (B.raw.compute n).center.im) <=
        (A.raw.compute m).height + (B.raw.compute n).height := by
    apply qabs_le_of_neg_le_le
    · have hupper :
          (B.raw.compute n).center.im - (A.raw.compute m).center.im <=
            (B.raw.compute n).hi.im - (A.raw.compute m).lo.im := by
        grind [Rat.sub_eq_add_neg]
      have hbound :
          (B.raw.compute n).hi.im - (A.raw.compute m).lo.im <=
            (A.raw.compute m).height + (B.raw.compute n).height := by
        unfold QBox.height
        grind [QBox.Overlaps, QComplex.le_def, Rat.sub_eq_add_neg]
      have := Rat.le_trans hupper hbound
      grind [Rat.sub_eq_add_neg]
    · have hupper :
          (A.raw.compute m).center.im - (B.raw.compute n).center.im <=
            (A.raw.compute m).hi.im - (B.raw.compute n).lo.im := by
        grind [Rat.sub_eq_add_neg]
      have hbound :
          (A.raw.compute m).hi.im - (B.raw.compute n).lo.im <=
            (A.raw.compute m).height + (B.raw.compute n).height := by
        unfold QBox.height
        grind [QBox.Overlaps, QComplex.le_def, Rat.sub_eq_add_neg]
      exact Rat.le_trans hupper hbound
  have hadd := rat_add_le_add hre him
  simpa only [QComplex.normBound, QComplex.sub, QComplex.add, QComplex.neg,
    Rat.sub_eq_add_neg, variation] using (Rat.le_trans hadd (by grind))

/-- Symmetric radius used to compare two equivalent bounded inputs. -/
def crossRadius {C : Rat} (A B : BoundedInput C) (stage : Nat) : Rat :=
  inputCoefficient C * (variation A stage + variation B stage) +
    stageRadius C stage

theorem radius_le_crossRadius {C : Rat} (A B : BoundedInput C)
    (stage : Nat) : radius A stage <= crossRadius A B stage := by
  have hK := Rat.le_of_lt (inputCoefficient_pos A.radius_nonneg)
  have hB := variation_nonneg B stage
  unfold radius crossRadius
  change inputCoefficient C * variation A stage + stageRadius C stage <=
    inputCoefficient C * (variation A stage + variation B stage) +
      stageRadius C stage
  exact rat_add_le_add
    (Rat.mul_le_mul_of_nonneg_left (by grind) hK) Rat.le_refl

theorem crossRadius_shrinks {C : Rat} (A B : BoundedInput C) :
    ShrinksToZero (crossRadius A B) := by
  intro eps
  let K := inputCoefficient C
  have hK : 0 < K := inputCoefficient_pos A.radius_nonneg
  let inputEps : QPos :=
    ⟨eps.val / (8 * K), by
      rw [Rat.div_def]
      exact Rat.mul_pos eps.property ((Rat.inv_pos).2
        (Rat.mul_pos (by decide +kernel) hK))⟩
  let tailEps : QPos :=
    ⟨eps.val / 2, by
      rw [Rat.div_def]
      exact Rat.mul_pos eps.property
        ((Rat.inv_pos).2 (by decide +kernel))⟩
  obtain ⟨NA, hNA⟩ := A.valid.2.2 inputEps
  obtain ⟨NB, hNB⟩ := B.valid.2.2 inputEps
  obtain ⟨Nt, hNt⟩ := stageRadius_shrinks A.radius_nonneg tailEps
  refine ⟨Nat.max (Nat.max NA NB) Nt, ?_⟩
  intro n hn
  have hnAB : Nat.max NA NB <= n :=
    Nat.le_trans (Nat.le_max_left _ _) hn
  have hnA : NA <= n := Nat.le_trans (Nat.le_max_left _ _) hnAB
  have hnB : NB <= n := Nat.le_trans (Nat.le_max_right _ _) hnAB
  have hnt : Nt <= n := Nat.le_trans (Nat.le_max_right _ _) hn
  have hA := hNA n hnA
  have hB := hNB n hnB
  have ht := hNt n hnt
  have hvariations :
      variation A n + variation B n <= 4 * inputEps.val := by
    unfold variation
    have := rat_add_le_add (rat_add_le_add hA.1 hA.2)
      (rat_add_le_add hB.1 hB.2)
    exact Rat.le_trans this (by grind)
  have hinput :
      K * (variation A n + variation B n) <= eps.val / 2 := by
    calc
      K * (variation A n + variation B n) <= K * (4 * inputEps.val) :=
        Rat.mul_le_mul_of_nonneg_left hvariations (Rat.le_of_lt hK)
      _ = eps.val / 2 := by
        dsimp [inputEps, K]
        rw [Rat.div_def, Rat.div_def]
        have h8K : (8 : Rat) * inputCoefficient C ≠ 0 :=
          Rat.ne_of_gt (Rat.mul_pos (by decide +kernel)
            (inputCoefficient_pos A.radius_nonneg))
        grind [Rat.mul_add, Rat.add_mul, Rat.mul_assoc, Rat.mul_comm,
          Rat.mul_inv_cancel ((8 : Rat) * inputCoefficient C) h8K,
          Rat.mul_inv_cancel 2 (by decide +kernel : (2 : Rat) ≠ 0)]
  unfold crossRadius
  dsimp [K] at hinput
  exact Rat.le_trans (rat_add_le_add hinput ht) (by
    rw [Rat.div_def]
    grind [Rat.mul_add, Rat.add_assoc, Rat.add_comm,
      Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel])

theorem candidate_future_contained_cross_expand_of_equiv
    {C : Rat} (A B : BoundedInput C) (hAB : A.raw.Equiv B.raw)
    (k n : Nat) (hkn : k <= n) :
    ((candidate A).compute n).NestedIn
      (QBox.expand ((candidate B).compute k) (crossRadius A B k)) := by
  let extra := n - k
  have hterms : terms C n = terms C k + extra := by
    dsimp [terms, extra]
    omega
  let za := (A.raw.compute n).center
  let zb := (B.raw.compute k).center
  let tail := tailPartial zb (terms C k) extra
  let movingError := QComplex.sub
    (expPrefix za (terms C n)) (expPrefix zb (terms C n))
  let error := QComplex.add movingError tail
  have hprefixB :
      expPrefix zb (terms C n) =
        QComplex.add (expPrefix zb (terms C k)) tail := by
    rw [hterms]
    exact expPrefix_add zb (terms C k) extra
  have hvalue :
      expPrefix za (terms C n) =
        QComplex.add (expPrefix zb (terms C k)) error := by
    dsimp [error, movingError]
    rw [hprefixB]
    exact (add_difference_tail
      (expPrefix za (terms C n)) (expPrefix zb (terms C k)) tail).symm
  have hcenter0 :=
    center_sub_normBound_le_variation_add_of_equiv A B hAB n k
  have hcenter : QComplex.normBound (QComplex.sub za zb) <=
      variation A k + variation B k := by
    exact Rat.le_trans hcenter0
      (rat_add_le_add (variation_antitone A k n hkn) Rat.le_refl)
  have hmoving : QComplex.normBound movingError <=
      derivativeMajorant C * (variation A k + variation B k) := by
    dsimp [movingError, za, zb]
    exact Rat.le_trans
      (expPrefix_difference_normBound_le_uniform A.radius_nonneg
        (A.center_normBound n) (B.center_normBound k) (terms C n))
      (Rat.mul_le_mul_of_nonneg_left hcenter
        (derivativeMajorant_nonneg A.radius_nonneg))
  have htail0 := tailPartial_normBound_le A.radius_nonneg
    (B.center_normBound k) (terms C k) extra
  have htail1 := RationalMajorant.factorialTailPartial_bound
    A.radius_nonneg
    (RationalMajorant.factorialTailStart_mono C
      (RationalMajorant.factorialTailStart C) k
      (RationalMajorant.factorialTailStart_satisfies C)) extra
  have htail : QComplex.normBound tail <= stageRadius C k := by
    exact Rat.le_trans htail0 (by
      simpa [tail, terms, stageRadius] using htail1)
  have hvar0 : 0 <= variation A k + variation B k :=
    Rat.add_nonneg (variation_nonneg A k) (variation_nonneg B k)
  have hcoefficient : derivativeMajorant C <= inputCoefficient C := by
    unfold inputCoefficient
    grind
  have herror : QComplex.normBound error <= crossRadius A B k := by
    calc
      QComplex.normBound error <=
          QComplex.normBound movingError + QComplex.normBound tail :=
        QComplex.normBound_add_le _ _
      _ <= derivativeMajorant C * (variation A k + variation B k) +
          stageRadius C k := rat_add_le_add hmoving htail
      _ <= inputCoefficient C * (variation A k + variation B k) +
          stageRadius C k := rat_add_le_add
            (Rat.mul_le_mul_of_nonneg_right hcoefficient hvar0) Rat.le_refl
      _ = crossRadius A B k := rfl
  change (QBox.point (expPrefix za (terms C n))).NestedIn
    (QBox.expand (QBox.point (expPrefix zb (terms C k)))
      (crossRadius A B k))
  rw [hvalue]
  exact point_add_error_nested_expand _ _ herror

def crossExponential {C : Rat} (A B : BoundedInput C) : ComplexCompute :=
  ComplexCompute.cauchyStabilize (candidate A) (crossRadius A B)

theorem crossExponential_valid {C : Rat} (A B : BoundedInput C) :
    (crossExponential A B).Valid := by
  unfold crossExponential
  apply ComplexCompute.cauchyStabilize_valid
  · exact candidate_ordered A
  · exact candidate_widths_shrink A
  · intro k n hkn
    apply QBox.nested_trans (candidate_future_contained_expand A k n hkn)
    exact QBox.expand_mono_radius _ (radius_le_crossRadius A B k)
  · exact crossRadius_shrinks A B

theorem exponential_equiv_crossExponential
    {C : Rat} (A B : BoundedInput C) :
    (exponential A).Equiv (crossExponential A B) := by
  unfold exponential crossExponential
  apply ComplexCompute.cauchyStabilize_equiv_of_common_candidate
  · exact candidate_ordered A
  · exact candidate_future_contained_expand A
  · intro k n hkn
    apply QBox.nested_trans (candidate_future_contained_expand A k n hkn)
    exact QBox.expand_mono_radius _ (radius_le_crossRadius A B k)

theorem crossRadius_comm {C : Rat} (A B : BoundedInput C) (n : Nat) :
    crossRadius A B n = crossRadius B A n := by
  simp [crossRadius, Rat.add_comm]

theorem crossExponential_equiv_of_input_equiv
    {C : Rat} (A B : BoundedInput C) (hAB : A.raw.Equiv B.raw) :
    (crossExponential A B).Equiv (crossExponential B A) := by
  intro n
  apply (ComplexCompute.compareAt_overlap_iff
    (crossExponential A B) (crossExponential B A) n n).2
  have hleft : ((candidate A).compute n).NestedIn
      ((crossExponential A B).compute n) := by
    unfold crossExponential
    apply ComplexCompute.cauchyStabilize_contains_external
      (external := fun m => (candidate A).compute m)
    intro k m hkm
    apply QBox.nested_trans (candidate_future_contained_expand A k m hkm)
    exact QBox.expand_mono_radius _ (radius_le_crossRadius A B k)
    exact Nat.le_refl n
  have hright : ((candidate A).compute n).NestedIn
      ((crossExponential B A).compute n) := by
    unfold crossExponential
    apply ComplexCompute.cauchyStabilize_contains_external
      (external := fun m => (candidate A).compute m)
    intro k m hkm
    simpa [crossRadius_comm] using
      candidate_future_contained_cross_expand_of_equiv A B hAB k m hkm
    exact Nat.le_refl n
  exact ⟨
    QComplex.le_trans hleft.1
      (QComplex.le_trans (candidate_ordered A n) hright.2),
    QComplex.le_trans hright.1
      (QComplex.le_trans (candidate_ordered A n) hleft.2)⟩

/-- The bounded represented exponential respects equivalence of its input
box computations. -/
theorem exponential_equiv_of_input_equiv
    {C : Rat} (A B : BoundedInput C) (hAB : A.raw.Equiv B.raw) :
    (exponential A).Equiv (exponential B) := by
  exact ComplexCompute.equiv_trans
    (exponential_valid A) (crossExponential_valid A B) (exponential_valid B)
    (exponential_equiv_crossExponential A B)
    (ComplexCompute.equiv_trans
      (crossExponential_valid A B) (crossExponential_valid B A)
      (exponential_valid B)
      (crossExponential_equiv_of_input_equiv A B hAB)
      (ComplexCompute.equiv_symm (exponential_equiv_crossExponential B A)))

theorem exponential_ofQComplex_compute_eq
    (z : QComplex) (C : Rat) (hC : 0 <= C)
    (hz : QComplex.normBound z <= C) (n : Nat) :
    (exponential (ofQComplex z C hC hz)).compute n =
      (exponentialRawAt z C).compute n := by
  let A := ofQComplex z C hC hz
  have hcand : forall stage,
      (candidate A).compute stage = (directCandidate z C).compute stage := by
    intro stage
    simp only [candidate, directCandidate, terms]
    rw [show (A.raw.compute stage).center = z by
      exact ofQComplex_center z C hC hz stage]
  have hradius : forall stage, radius A stage = stageRadius C stage := by
    intro stage
    unfold radius
    have hwidth : (A.raw.compute stage).width = 0 := by
      simp only [A, ofQComplex, ComplexCompute.ofQComplex, QBox.width]
      grind
    have hheight : (A.raw.compute stage).height = 0 := by
      simp only [A, ofQComplex, ComplexCompute.ofQComplex, QBox.height]
      grind
    rw [hwidth, hheight, Rat.zero_add, Rat.mul_zero, Rat.zero_add]
  unfold exponential exponentialRawAt ComplexCompute.cauchyStabilize
  change ComplexCompute.cauchyStabilizeCompute
      (candidate A).compute (radius A) n =
    ComplexCompute.cauchyStabilizeCompute
      (directCandidate z C).compute (stageRadius C) n
  induction n with
  | zero => simp [ComplexCompute.cauchyStabilizeCompute, hcand, hradius]
  | succ n ih =>
      rw [ComplexCompute.cauchyStabilizeCompute,
        ComplexCompute.cauchyStabilizeCompute, ih, hcand, hradius]

/-- On exact rational-complex inputs, the represented-input lift agrees with
the original rational-point exponential construction. -/
theorem exponential_ofQComplex_equiv_exponentialRawAt
    (z : QComplex) (C : Rat) (hC : 0 <= C)
    (hz : QComplex.normBound z <= C) :
    (exponential (ofQComplex z C hC hz)).Equiv (exponentialRawAt z C) := by
  intro n
  have href := (ComplexCompute.equiv_refl (exponentialRawAt z C)
    (exponentialRawAt_valid hC hz)) n
  unfold ComplexCompute.compareAt at href ⊢
  rw [exponential_ofQComplex_compute_eq z C hC hz n]
  exact href

end BoundedInput
end ComplexExponentialLift
end ComputableAnalysis


