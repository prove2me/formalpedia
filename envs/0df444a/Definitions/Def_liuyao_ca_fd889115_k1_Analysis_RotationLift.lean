-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Analysis_RotationLift
-- name    : liuyao_ca_fd889115_k1_Analysis_RotationLift
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T17:58:05.896999+00:00
-- url     : https://prove2.me/theorems/4a78e2b5-dbc4-4fca-8331-71f95b2654d0
-- title:
--   Computable analysis · RotationLift · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableAnalysis/RotationLift.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_RotationSeries

set_option autoImplicit true

/-!
# Lifting a bounded represented angle through the rotation series

The factorial rotation evaluator in `RotationSeries` takes a rational input.
This module packages the finite information needed to apply one common
evaluator to the successive rational midpoints of a represented angle.  It
does not assume a completed real or complex plane: the result is a valid
`ComplexCompute`, obtained by finite prefix stabilization.

The bounds `[1, 2]` and modulus `2 / (n + 1)` are chosen for the later
input `pi / 2`.  Keeping this lifting step generic means that the complex
calculation is checked without importing a particular pi registry.
-/

namespace ComputableAnalysis

namespace RotationLift

/-- A represented angle suitable for the common imaginary-axis rotation
series.  Its finite boxes are nested by `valid`, lie in `[1,2]`, and carry the
explicit modulus used to budget the error caused by replacing the represented
input with a rational midpoint. -/
structure HalfPiInput where
  raw : RealCompute
  valid : raw.Valid
  bounds : forall n : Nat,
    (1 : Rat) <= (raw.compute n).lo /\
      (raw.compute n).hi <= 2
  width_le_two_div_succ : forall n : Nat,
    (raw.compute n).width <= 2 / (((n + 1 : Nat) : Rat))

namespace HalfPiInput

/-- The exact rational input on the bounded half-angle chart.  This is the
compatibility witness between the represented-angle lift and the original
rational factorial evaluator. -/
def rationalInput (T : Rat) (hlo : (1 : Rat) <= T) (hhi : T <= 2) :
    HalfPiInput where
  raw := RealCompute.ofRat T
  valid := RealCompute.ofRat_valid T
  bounds := by
    intro _
    change (1 : Rat) <= T /\ T <= 2
    exact ⟨hlo, hhi⟩
  width_le_two_div_succ := by
    intro n
    change T - T <= 2 / (((n + 1 : Nat) : Rat))
    rw [Rat.sub_self]
    apply Rat.le_of_lt
    rw [Rat.div_def]
    exact Rat.mul_pos (by decide +kernel)
      ((Rat.inv_pos).2 ((Rat.natCast_pos).2 (Nat.succ_pos n)))

/-- A rational input has its own value as every midpoint sample. -/
theorem rationalInput_midpoint (T : Rat) (hlo : (1 : Rat) <= T) (hhi : T <= 2)
    (n : Nat) :
    ((rationalInput T hlo hhi).raw.compute n).midpoint = T := by
  change (({ lo := T, hi := T } : QInterval).midpoint) = T
  unfold QInterval.midpoint
  rw [Rat.div_def]
  have htwo : (2 : Rat) * (2 : Rat)⁻¹ = 1 :=
    Rat.mul_inv_cancel 2 (by decide +kernel)
  calc
    (T + T) * (2 : Rat)⁻¹ = T * (2 * (2 : Rat)⁻¹) := by
      grind [Rat.add_mul, Rat.mul_assoc, Rat.mul_comm]
    _ = T := by rw [htwo, Rat.mul_one]

/-- Every rational midpoint of the input boxes has absolute value at most
two, so it lies in the uniform factorial domain. -/
theorem midpoint_qabs_le_two (A : HalfPiInput) (n : Nat) :
    qabs ((A.raw.compute n).midpoint) <= 2 := by
  have hwidth := A.valid.1 n
  have hordered : (A.raw.compute n).lo <= (A.raw.compute n).hi := by
    unfold QInterval.width at hwidth
    grind [Rat.sub_eq_add_neg]
  have hmid := QInterval.midpoint_mem hordered
  have hbounds := A.bounds n
  have hnonneg : 0 <= (A.raw.compute n).midpoint :=
    Rat.le_trans (Rat.le_of_lt (by decide +kernel : (0 : Rat) < 1))
      (Rat.le_trans hbounds.1 hmid.1)
  rw [qabs_eq_self_of_nonneg hnonneg]
  exact Rat.le_trans hmid.2 hbounds.2

/-- Later midpoint samples remain in the earlier certified input box. -/
theorem midpoint_sub_le_width (A : HalfPiInput) (k n : Nat) (hkn : k <= n) :
    qabs ((A.raw.compute n).midpoint - (A.raw.compute k).midpoint) <=
      (A.raw.compute k).width := by
  have hkwidth := A.valid.1 k
  have hkordered : (A.raw.compute k).lo <= (A.raw.compute k).hi := by
    unfold QInterval.width at hkwidth
    grind [Rat.sub_eq_add_neg]
  have hnwidth := A.valid.1 n
  have hnordered : (A.raw.compute n).lo <= (A.raw.compute n).hi := by
    unfold QInterval.width at hnwidth
    grind [Rat.sub_eq_add_neg]
  have hmidk := QInterval.midpoint_mem hkordered
  have hmidn := QInterval.midpoint_mem hnordered
  have hnest := A.valid.2.1 k n hkn
  apply qabs_sub_le_of_common_bounds
  · exact Rat.le_trans hnest.1 hmidn.1
  · exact Rat.le_trans hmidn.2 hnest.2.2
  · exact hmidk.1
  · exact hmidk.2

/-- Equivalent represented angles have rational midpoint samples that differ
by at most the sum of their two interval widths.  This is a finite interval
calculation: validity promotes same-stage raw overlap to cross-stage overlap,
and no completed-real continuity principle is used. -/
theorem midpoint_sub_le_width_add_width_of_equiv
    (A B : HalfPiInput) (hAB : A.raw.Equiv B.raw) (m n : Nat) :
    qabs ((A.raw.compute m).midpoint - (B.raw.compute n).midpoint) <=
      (A.raw.compute m).width + (B.raw.compute n).width := by
  have hAwidth := A.valid.1 m
  have hAordered : (A.raw.compute m).lo <= (A.raw.compute m).hi := by
    unfold QInterval.width at hAwidth
    grind [Rat.sub_eq_add_neg]
  have hBwidth := B.valid.1 n
  have hBordered : (B.raw.compute n).lo <= (B.raw.compute n).hi := by
    unfold QInterval.width at hBwidth
    grind [Rat.sub_eq_add_neg]
  have hAmid := QInterval.midpoint_mem hAordered
  have hBmid := QInterval.midpoint_mem hBordered
  have hover := (RealCompute.compareAt_overlap_iff A.raw B.raw m n).1
    (RealCompute.allStagesOverlap_of_equiv A.valid B.valid hAB m n)
  have hAlo_le_Bhi : (A.raw.compute m).lo <= (B.raw.compute n).hi :=
    hover.1
  have hBlo_le_Ahi : (B.raw.compute n).lo <= (A.raw.compute m).hi :=
    hover.2
  apply qabs_le_of_neg_le_le
  · have hupper : (B.raw.compute n).midpoint - (A.raw.compute m).midpoint <=
        (B.raw.compute n).hi - (A.raw.compute m).lo := by
      grind [Rat.sub_eq_add_neg]
    have hupperBound :
        (B.raw.compute n).hi - (A.raw.compute m).lo <=
          (A.raw.compute m).width + (B.raw.compute n).width := by
      unfold QInterval.width
      grind [Rat.sub_eq_add_neg]
    have hbound := Rat.le_trans hupper hupperBound
    grind [Rat.sub_eq_add_neg]
  · have hupper : (A.raw.compute m).midpoint - (B.raw.compute n).midpoint <=
        (A.raw.compute m).hi - (B.raw.compute n).lo := by
      grind [Rat.sub_eq_add_neg]
    have hupperBound :
        (A.raw.compute m).hi - (B.raw.compute n).lo <=
          (A.raw.compute m).width + (B.raw.compute n).width := by
      unfold QInterval.width
      grind [Rat.sub_eq_add_neg]
    exact Rat.le_trans hupper hupperBound

/-- The direct rational-midpoint factorial candidate. -/
def rotationCandidate (A : HalfPiInput) : ComplexCompute where
  compute := fun n => RotationSeries.uniformRotationBox (A.raw.compute n).midpoint n

theorem rotationCandidate_compute (A : HalfPiInput) (n : Nat) :
    (rotationCandidate A).compute n =
      RotationSeries.uniformRotationBox (A.raw.compute n).midpoint n := rfl

/-- At an exact rational input, the direct represented-angle candidate is
literally the existing common-schedule factorial box. -/
theorem rationalInput_rotationCandidate_compute
    (T : Rat) (hlo : (1 : Rat) <= T) (hhi : T <= 2) (n : Nat) :
    (rotationCandidate (rationalInput T hlo hhi)).compute n =
      RotationSeries.uniformRotationBox T n := by
  rw [rotationCandidate_compute, rationalInput_midpoint T hlo hhi]

theorem rotationCandidate_ordered (A : HalfPiInput) (n : Nat) :
    ((rotationCandidate A).compute n).Ordered := by
  rw [rotationCandidate_compute]
  have hvalid := RotationSeries.uniformRotationExpRaw_valid _
    (midpoint_qabs_le_two A n)
  exact ComplexCompute.valid_ordered hvalid n

theorem rotationCandidate_widths_shrink (A : HalfPiInput) :
    ComplexCompute.WidthsShrinkToZero (rotationCandidate A).compute := by
  intro eps
  obtain ⟨N, hN⟩ := RotationSeries.uniformRotationBox_widths_shrink 0 eps
  refine ⟨N, ?_⟩
  intro n hn
  have h := hN n hn
  rw [rotationCandidate_compute,
    RotationSeries.uniformRotationBox_width,
    RotationSeries.uniformRotationBox_height]
  rw [RotationSeries.uniformRotationBox_width,
    RotationSeries.uniformRotationBox_height] at h
  exact h

/-- The joint finite Lipschitz radius for two equivalent represented-angle
inputs at one factorial stage. -/
def crossRadius (A B : HalfPiInput) (n : Nat) : Rat :=
  16 * ((A.raw.compute n).width + (B.raw.compute n).width)

/-- The joint cross-input radius has the executable `64/(n+1)` modulus. -/
theorem crossRadius_shrinks (A B : HalfPiInput) :
    ShrinksToZero (crossRadius A B) := by
  apply shrinksToZero_of_natOverSuccBound (C := 64)
  intro n
  have hA := A.width_le_two_div_succ n
  have hB := B.width_le_two_div_succ n
  have hsum :
      (A.raw.compute n).width + (B.raw.compute n).width <=
        4 / (((n + 1 : Nat) : Rat)) := by
    calc
      (A.raw.compute n).width + (B.raw.compute n).width <=
          2 / (((n + 1 : Nat) : Rat)) + 2 / (((n + 1 : Nat) : Rat)) :=
        rat_add_le_add hA hB
      _ = 4 / (((n + 1 : Nat) : Rat)) := by
        rw [Rat.div_def]
        grind [Rat.mul_add, Rat.mul_assoc, Rat.mul_comm]
  unfold crossRadius
  calc
    16 * ((A.raw.compute n).width + (B.raw.compute n).width) <=
        16 * (4 / (((n + 1 : Nat) : Rat))) :=
      Rat.mul_le_mul_of_nonneg_left hsum (by decide +kernel)
    _ = 64 / (((n + 1 : Nat) : Rat)) := by
      rw [Rat.div_def]
      grind [Rat.mul_assoc, Rat.mul_comm]

/-- Later input boxes have no larger width than earlier ones. -/
theorem width_antitone (A : HalfPiInput) (k n : Nat) (hkn : k <= n) :
    (A.raw.compute n).width <= (A.raw.compute k).width := by
  apply QInterval.width_le_of_contains
  have hnest := A.valid.2.1 k n hkn
  exact ⟨hnest.1, hnest.2.2⟩

/-- At a common factorial-prefix stage, equivalent represented-angle inputs
produce boxes related by the explicit finite Lipschitz enlargement determined
by the two input widths.  This is the same-stage core of the
representative-respecting stabilization theorem proved below. -/
theorem rotationCandidate_sameStage_contained_expand_of_equiv
    (A B : HalfPiInput) (hAB : A.raw.Equiv B.raw) (n : Nat) :
    QBox.NestedIn ((rotationCandidate A).compute n)
      (QBox.expand ((rotationCandidate B).compute n)
        (crossRadius A B n)) := by
  simpa [rotationCandidate, crossRadius] using
    RotationSeries.uniformRotationBox_contained_expand_of_input_near
      ((A.raw.compute n).midpoint) ((B.raw.compute n).midpoint)
      ((A.raw.compute n).width + (B.raw.compute n).width)
      (midpoint_qabs_le_two A n) (midpoint_qabs_le_two B n) n
      (midpoint_sub_le_width_add_width_of_equiv A B hAB n n)

/-- The explicit input-error radius: the checked finite-prefix Lipschitz
budget is sixteen times the input-box width. -/
def rotationRadius (A : HalfPiInput) (n : Nat) : Rat :=
  16 * (A.raw.compute n).width

theorem rotationRadius_shrinks (A : HalfPiInput) :
    ShrinksToZero (rotationRadius A) := by
  apply shrinksToZero_of_natOverSuccBound (C := 32)
  intro n
  have hwidth := A.width_le_two_div_succ n
  unfold rotationRadius
  calc
    16 * (A.raw.compute n).width <=
        16 * (2 / (((n + 1 : Nat) : Rat))) :=
      Rat.mul_le_mul_of_nonneg_left hwidth (by decide +kernel)
    _ = 32 / (((n + 1 : Nat) : Rat)) := by
      rw [Rat.div_def]
      grind [Rat.mul_assoc, Rat.mul_comm]

/-- The ordinary one-input radius is contained in the joint cross-input
radius at the same stage. -/
theorem rotationRadius_le_crossRadius (A B : HalfPiInput) (n : Nat) :
    rotationRadius A n <= crossRadius A B n := by
  have hBnonneg : 0 <= (B.raw.compute n).width := B.valid.1 n
  unfold rotationRadius crossRadius
  apply Rat.mul_le_mul_of_nonneg_left
  · grind [Rat.sub_eq_add_neg]
  · decide +kernel

/-- A later direct candidate for one represented angle fits in an earlier
candidate box widened by the ordinary one-input radius. -/
theorem rotationCandidate_future_contained_expand
    (A : HalfPiInput) (k n : Nat) (hkn : k <= n) :
    QBox.NestedIn ((rotationCandidate A).compute n)
      (QBox.expand ((rotationCandidate A).compute k)
        (rotationRadius A k)) := by
  have hfuture := RotationSeries.uniformRotationBox_future_contained_expand_of_input_near
    (A.raw.compute n).midpoint (A.raw.compute k).midpoint
    (A.raw.compute k).width
    (midpoint_qabs_le_two A n) (midpoint_qabs_le_two A k)
    k n hkn (midpoint_sub_le_width A k n hkn)
  simpa [rotationCandidate_compute, rotationRadius] using hfuture

/-- A later candidate from an equivalent represented angle fits in an earlier
candidate box of the other evaluator, with the joint rational cross radius. -/
theorem rotationCandidate_future_contained_expand_of_equiv
    (A B : HalfPiInput) (hAB : A.raw.Equiv B.raw)
    (k n : Nat) (hkn : k <= n) :
    QBox.NestedIn ((rotationCandidate A).compute n)
      (QBox.expand ((rotationCandidate B).compute k)
        (crossRadius A B k)) := by
  have hnear0 := midpoint_sub_le_width_add_width_of_equiv A B hAB n k
  have hAw := width_antitone A k n hkn
  have hnear :
      qabs ((A.raw.compute n).midpoint - (B.raw.compute k).midpoint) <=
        (A.raw.compute k).width + (B.raw.compute k).width :=
    Rat.le_trans hnear0 (rat_add_le_add hAw Rat.le_refl)
  have hfuture := RotationSeries.uniformRotationBox_future_contained_expand_of_input_near
    (A.raw.compute n).midpoint (B.raw.compute k).midpoint
    ((A.raw.compute k).width + (B.raw.compute k).width)
    (midpoint_qabs_le_two A n) (midpoint_qabs_le_two B k)
    k n hkn hnear
  simpa [rotationCandidate_compute, crossRadius] using hfuture

/-- The stabilized represented-angle rotation.  It intersects a finite
prefix of widened midpoint candidates, so its validity is constructive. -/
def rotation (A : HalfPiInput) : ComplexCompute :=
  ComplexCompute.cauchyStabilize (rotationCandidate A) (rotationRadius A)

theorem rotation_valid (A : HalfPiInput) : (rotation A).Valid := by
  unfold rotation
  apply ComplexCompute.cauchyStabilize_valid
  · exact rotationCandidate_ordered A
  · exact rotationCandidate_widths_shrink A
  · exact rotationCandidate_future_contained_expand A
  · exact rotationRadius_shrinks A

/-- The specialized half-angle lift and the general represented-input
rotation evaluator use the same rational midpoint factorial candidates.
Their different widening budgets give equivalent stabilized values, so the
generic evaluator is a representation-independent extension of this existing
half-pi construction. -/
theorem rotation_equiv_representedRotationExpRaw (A : HalfPiInput) :
    (rotation A).Equiv (RotationSeries.representedRotationExpRaw A.raw) := by
  have hbound : forall n,
      -2 <= (A.raw.compute n).lo /\ (A.raw.compute n).hi <= 2 := by
    intro n
    have h := A.bounds n
    exact ⟨Rat.le_trans (by decide : (-2 : Rat) <= 1) h.1, h.2⟩
  have hnew := RotationSeries.representedRotationCandidate_future
    A.raw A.valid hbound
  have hnew' : forall k n, k <= n ->
      ((rotationCandidate A).compute n).NestedIn
        (QBox.expand ((rotationCandidate A).compute k)
          (rotationRadius A k)) :=
    rotationCandidate_future_contained_expand A
  have hwide : forall k n, k <= n ->
      ((rotationCandidate A).compute n).NestedIn
        (QBox.expand ((rotationCandidate A).compute k)
          (RotationSeries.representedRotationRadius A.raw k)) := by
    intro k n hkn
    simpa [rotationCandidate, RotationSeries.representedRotationCandidate,
      rotationRadius, RotationSeries.representedRotationRadius] using
        hnew k n hkn
  unfold rotation RotationSeries.representedRotationExpRaw
  exact ComplexCompute.cauchyStabilize_equiv_of_common_candidate
    (rotationCandidate_ordered A) hnew' hwide

/-- The same direct candidate, stabilized with the joint cross-input radius.
This makes the representative-change modulus part of the executable
stabilization data. -/
def crossRotation (A B : HalfPiInput) : ComplexCompute :=
  ComplexCompute.cauchyStabilize (rotationCandidate A) (crossRadius A B)

/-- The joint radius is large enough to preserve the ordinary one-input
future-containment certificate. -/
theorem crossRotation_future_contained_expand
    (A B : HalfPiInput) (k n : Nat) (hkn : k <= n) :
    QBox.NestedIn ((rotationCandidate A).compute n)
      (QBox.expand ((rotationCandidate A).compute k)
        (crossRadius A B k)) := by
  apply QBox.nested_trans
    (rotationCandidate_future_contained_expand A k n hkn)
  exact QBox.expand_mono_radius _ (rotationRadius_le_crossRadius A B k)

theorem crossRotation_valid (A B : HalfPiInput) :
    (crossRotation A B).Valid := by
  unfold crossRotation
  apply ComplexCompute.cauchyStabilize_valid
  · exact rotationCandidate_ordered A
  · exact rotationCandidate_widths_shrink A
  · exact crossRotation_future_contained_expand A B
  · exact crossRadius_shrinks A B

/-- Replacing the ordinary radius by the joint cross-input radius does not
change the represented rotation, because both finite intersections retain the
same ordered rational candidate at every stage. -/
theorem rotation_equiv_crossRotation (A B : HalfPiInput) :
    (rotation A).Equiv (crossRotation A B) := by
  unfold rotation crossRotation
  exact ComplexCompute.cauchyStabilize_equiv_of_common_candidate
    (rotationCandidate_ordered A)
    (rotationCandidate_future_contained_expand A)
    (crossRotation_future_contained_expand A B)

/-- The joint radius is symmetric in the two equivalent input widths. -/
theorem crossRadius_comm (A B : HalfPiInput) (n : Nat) :
    crossRadius A B n = crossRadius B A n := by
  simp [crossRadius, Rat.add_comm]

/-- Jointly stabilized factorial rotations agree whenever their represented
half-angle inputs agree.  The proof uses the `A` candidate at a common future
stage as a finite rational box contained in both prefix intersections. -/
theorem crossRotation_equiv_of_input_equiv
    (A B : HalfPiInput) (hAB : A.raw.Equiv B.raw) :
    (crossRotation A B).Equiv (crossRotation B A) := by
  intro n
  apply (ComplexCompute.compareAt_overlap_iff
    (crossRotation A B) (crossRotation B A) n n).2
  have hleft : QBox.NestedIn ((rotationCandidate A).compute n)
      ((crossRotation A B).compute n) := by
    unfold crossRotation
    exact ComplexCompute.cauchyStabilize_contains_external
      (candidate := rotationCandidate A) (radius := crossRadius A B)
      (external := fun m => (rotationCandidate A).compute m)
      (crossRotation_future_contained_expand A B) n n (Nat.le_refl n)
  have hright : QBox.NestedIn ((rotationCandidate A).compute n)
      ((crossRotation B A).compute n) := by
    unfold crossRotation
    apply ComplexCompute.cauchyStabilize_contains_external
      (candidate := rotationCandidate B) (radius := crossRadius B A)
      (external := fun m => (rotationCandidate A).compute m)
    intro k m hkm
    simpa [crossRadius_comm] using
      rotationCandidate_future_contained_expand_of_equiv A B hAB k m hkm
    exact Nat.le_refl n
  exact ⟨
    QComplex.le_trans hleft.1
      (QComplex.le_trans (rotationCandidate_ordered A n) hright.2),
    QComplex.le_trans hright.1
      (QComplex.le_trans (rotationCandidate_ordered A n) hleft.2)⟩

/-- The represented factorial rotation respects raw-real equivalence of its
bounded half-angle input.  This is a computation-level continuity theorem for
the lift, proved with finite boxes and explicit shrinking radii only. -/
theorem rotation_equiv_of_input_equiv
    (A B : HalfPiInput) (hAB : A.raw.Equiv B.raw) :
    (rotation A).Equiv (rotation B) := by
  exact ComplexCompute.equiv_trans
    (rotation_valid A) (crossRotation_valid A B) (rotation_valid B)
    (rotation_equiv_crossRotation A B)
    (ComplexCompute.equiv_trans
      (crossRotation_valid A B) (crossRotation_valid B A) (rotation_valid B)
      (crossRotation_equiv_of_input_equiv A B hAB)
      (ComplexCompute.equiv_symm (rotation_equiv_crossRotation B A)))

/-- The stabilized box contains the direct rational-midpoint factorial box
at the same stage.  This is the finite enclosure used by a later
quarter-turn identification. -/
theorem rotation_contains_current_candidate (A : HalfPiInput) (n : Nat) :
    QBox.NestedIn ((rotationCandidate A).compute n)
      ((rotation A).compute n) := by
  unfold rotation
  apply ComplexCompute.cauchyStabilize_contains_current
  intro k m hkm
  have hfuture := RotationSeries.uniformRotationBox_future_contained_expand_of_input_near
    (A.raw.compute m).midpoint (A.raw.compute k).midpoint
    (A.raw.compute k).width
    (midpoint_qabs_le_two A m) (midpoint_qabs_le_two A k)
    k m hkm (midpoint_sub_le_width A k m hkm)
  simpa [rotationCandidate_compute, rotationRadius] using hfuture

/-- The represented-angle evaluator extends the original rational factorial
rotation exactly on the bounded chart.  Thus lifting an already exact input
does not introduce a second complex-exponential notion; stabilization merely
reboxes the same nested rational factorial candidates. -/
theorem rationalInput_rotation_equiv_uniformRotationExpRaw
    (T : Rat) (hlo : (1 : Rat) <= T) (hhi : T <= 2) :
    (rotation (rationalInput T hlo hhi)).Equiv
      (RotationSeries.uniformRotationExpRaw T) := by
  intro n
  apply (ComplexCompute.compareAt_overlap_iff
    (rotation (rationalInput T hlo hhi))
    (RotationSeries.uniformRotationExpRaw T) n n).2
  have hcontains := rotation_contains_current_candidate
    (rationalInput T hlo hhi) n
  rw [rationalInput_rotationCandidate_compute T hlo hhi n] at hcontains
  have hTnonneg : (0 : Rat) <= T :=
    Rat.le_trans (by decide +kernel) hlo
  have hTbound : qabs T <= 2 := by
    rw [qabs_eq_self_of_nonneg hTnonneg]
    exact hhi
  have hordered := ComplexCompute.valid_ordered
    (RotationSeries.uniformRotationExpRaw_valid T hTbound) n
  exact ⟨QComplex.le_trans hcontains.1 hordered,
    QComplex.le_trans hordered hcontains.2⟩

/-- Any bounded represented input that is certified equal to a rational
angle has the original rational factorial rotation as its result.  This is
the representation-independent compatibility law used when a later analytic
construction happens to collapse to an exact rational parameter. -/
theorem rotation_equiv_uniformRotationExpRaw_of_equiv_ofRat
    (A : HalfPiInput) (T : Rat) (hlo : (1 : Rat) <= T) (hhi : T <= 2)
    (hAT : A.raw.Equiv (RealCompute.ofRat T)) :
    (rotation A).Equiv (RotationSeries.uniformRotationExpRaw T) := by
  have hInput : A.raw.Equiv (rationalInput T hlo hhi).raw := by
    simpa [rationalInput] using hAT
  have hTnonneg : (0 : Rat) <= T :=
    Rat.le_trans (by decide +kernel) hlo
  have hTbound : qabs T <= 2 := by
    rw [qabs_eq_self_of_nonneg hTnonneg]
    exact hhi
  exact ComplexCompute.equiv_trans
    (rotation_valid A)
    (rotation_valid (rationalInput T hlo hhi))
    (RotationSeries.uniformRotationExpRaw_valid T hTbound)
    (rotation_equiv_of_input_equiv A (rationalInput T hlo hhi) hInput)
    (rationalInput_rotation_equiv_uniformRotationExpRaw T hlo hhi)

end HalfPiInput

end RotationLift

end ComputableAnalysis


