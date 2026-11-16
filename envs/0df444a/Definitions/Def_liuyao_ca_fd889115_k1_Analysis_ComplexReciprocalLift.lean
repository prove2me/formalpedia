-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Analysis_ComplexReciprocalLift
-- name    : liuyao_ca_fd889115_k1_Analysis_ComplexReciprocalLift
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T18:00:29.281554+00:00
-- url     : https://prove2.me/theorems/be211821-552a-42c5-a9a3-d52747e2d85b
-- title:
--   Computable analysis · ComplexReciprocalLift · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableAnalysis/ComplexReciprocalLift.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_ComplexReciprocalCalculus
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_ComplexExponentialLift
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_ComplexComputeQuotientAlgebra
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_ComplexComputeQuotient

set_option autoImplicit true

/-!
# Reciprocal of a represented complex number away from zero

The input carries rational bounds on every sampled center: an upper
`normBound` and a positive lower `normSq` margin.  Finite inverse values at
those centers form a rational Cauchy family by the checked reciprocal
Lipschitz estimate.  Finite-prefix intersection produces the nested output.
-/

namespace ComputableAnalysis
namespace ComplexReciprocalLift

/-- A represented complex input uniformly separated from zero at its sampled
rational centers. -/
structure AwayInput (C margin : Rat) where
  raw : ComplexCompute
  valid : raw.Valid
  bound_nonneg : 0 <= C
  margin_pos : 0 < margin
  center_normBound : forall n,
    QComplex.normBound (raw.compute n).center <= C
  center_normSq_ge : forall n,
    margin <= QComplex.normSq (raw.compute n).center

namespace AwayInput

def toBoundedInput {C margin : Rat} (A : AwayInput C margin) :
    ComplexExponentialLift.BoundedInput C where
  raw := A.raw
  valid := A.valid
  radius_nonneg := A.bound_nonneg
  center_normBound := A.center_normBound

def ofQComplex (z : QComplex) (C margin : Rat)
    (hC : 0 <= C) (hmargin : 0 < margin)
    (hzC : QComplex.normBound z <= C)
    (hzsep : margin <= QComplex.normSq z) : AwayInput C margin where
  raw := ComplexCompute.ofQComplex z
  valid := ComplexCompute.ofQComplex_valid z
  bound_nonneg := hC
  margin_pos := hmargin
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
    exact hzC
  center_normSq_ge := by
    intro n
    have hcenter : ((ComplexCompute.ofQComplex z).compute n).center = z := by
      cases z
      simp only [ComplexCompute.ofQComplex, QBox.center]
      congr 1 <;>
        rw [Rat.div_def] <;>
        grind [Rat.add_mul, Rat.mul_assoc, Rat.mul_comm,
          Rat.mul_inv_cancel]
    rw [hcenter]
    exact hzsep

def variation {C margin : Rat} (A : AwayInput C margin) (stage : Nat) : Rat :=
  ComplexExponentialLift.BoundedInput.variation A.toBoundedInput stage

theorem variation_nonneg {C margin : Rat} (A : AwayInput C margin)
    (stage : Nat) : 0 <= variation A stage :=
  ComplexExponentialLift.BoundedInput.variation_nonneg A.toBoundedInput stage

theorem variation_antitone {C margin : Rat} (A : AwayInput C margin)
    (k n : Nat) (hkn : k <= n) : variation A n <= variation A k :=
  ComplexExponentialLift.BoundedInput.variation_antitone
    A.toBoundedInput k n hkn

def inverseBound (C margin : Rat) : Rat := C * margin⁻¹

def coefficient (C margin : Rat) : Rat := (inverseBound C margin) ^ 2 + 1

theorem coefficient_pos {C margin : Rat} (A : AwayInput C margin) :
    0 < coefficient C margin := by
  have hbase : 0 <= inverseBound C margin :=
    Rat.mul_nonneg A.bound_nonneg
      (Rat.le_of_lt ((Rat.inv_pos).2 A.margin_pos))
  have hsquare : 0 <= (inverseBound C margin) ^ 2 :=
    Rat.pow_nonneg hbase
  unfold coefficient
  grind

def candidate {C margin : Rat} (A : AwayInput C margin) : ComplexCompute where
  compute := fun stage =>
    QBox.point (QComplex.inverse (A.raw.compute stage).center)

def radius {C margin : Rat} (A : AwayInput C margin) (stage : Nat) : Rat :=
  coefficient C margin * variation A stage

theorem candidate_ordered {C margin : Rat} (A : AwayInput C margin)
    (stage : Nat) : ((candidate A).compute stage).Ordered :=
  QComplex.le_refl _

theorem candidate_widths_shrink {C margin : Rat} (A : AwayInput C margin) :
    ComplexCompute.WidthsShrinkToZero (candidate A).compute := by
  intro eps
  refine ⟨0, ?_⟩
  intro stage _
  constructor <;>
    simpa [candidate, QBox.point, QBox.width, QBox.height,
      Rat.sub_self] using (Rat.le_of_lt eps.property)

private theorem add_sub_cancel_right (x y : QComplex) :
    QComplex.add y (QComplex.sub x y) = x := by
  cases x
  cases y
  simp [QComplex.add, QComplex.sub, QComplex.neg]
  congr 1 <;> grind [Rat.sub_eq_add_neg]

theorem candidate_future_contained_expand
    {C margin : Rat} (A : AwayInput C margin)
    (k n : Nat) (hkn : k <= n) :
    ((candidate A).compute n).NestedIn
      (QBox.expand ((candidate A).compute k) (radius A k)) := by
  let zn := (A.raw.compute n).center
  let zk := (A.raw.compute k).center
  let error := QComplex.sub (QComplex.inverse zn) (QComplex.inverse zk)
  have hcenter :=
    ComplexExponentialLift.BoundedInput.center_sub_normBound_le_width_add_height
      A.toBoundedInput k n hkn
  have hraw := QComplex.inverse_difference_normBound_le
    A.bound_nonneg A.margin_pos
    (A.center_normBound n) (A.center_normBound k)
    (A.center_normSq_ge n) (A.center_normSq_ge k)
  have hbase0 : 0 <= (inverseBound C margin) ^ 2 := by
    apply Rat.pow_nonneg
    exact Rat.mul_nonneg A.bound_nonneg
      (Rat.le_of_lt ((Rat.inv_pos).2 A.margin_pos))
  have herror0 : QComplex.normBound error <=
      (inverseBound C margin) ^ 2 * variation A k := by
    exact Rat.le_trans hraw
      (Rat.mul_le_mul_of_nonneg_left hcenter hbase0)
  have hcoeff : (inverseBound C margin) ^ 2 <= coefficient C margin := by
    unfold coefficient
    grind
  have herror : QComplex.normBound error <= radius A k := by
    exact Rat.le_trans herror0
      (Rat.mul_le_mul_of_nonneg_right hcoeff (variation_nonneg A k))
  change (QBox.point (QComplex.inverse zn)).NestedIn
    (QBox.expand (QBox.point (QComplex.inverse zk)) (radius A k))
  rw [show QComplex.inverse zn =
      QComplex.add (QComplex.inverse zk) error by
    exact (add_sub_cancel_right (QComplex.inverse zn)
      (QComplex.inverse zk)).symm]
  exact ComplexExponentialApproximation.point_add_error_nested_expand _ _ herror

theorem radius_shrinks {C margin : Rat} (A : AwayInput C margin) :
    ShrinksToZero (radius A) := by
  intro eps
  let K := coefficient C margin
  have hK : 0 < K := coefficient_pos A
  let inputEps : QPos :=
    ⟨eps.val / (2 * K), by
      rw [Rat.div_def]
      exact Rat.mul_pos eps.property ((Rat.inv_pos).2
        (Rat.mul_pos (by decide +kernel) hK))⟩
  obtain ⟨N, hN⟩ := A.valid.2.2 inputEps
  refine ⟨N, ?_⟩
  intro n hn
  have hwh := hN n hn
  have hvariation : variation A n <= 2 * inputEps.val := by
    unfold variation ComplexExponentialLift.BoundedInput.variation
    exact Rat.le_trans (rat_add_le_add hwh.1 hwh.2) (by grind)
  unfold radius
  calc
    coefficient C margin * variation A n <=
        coefficient C margin * (2 * inputEps.val) :=
      Rat.mul_le_mul_of_nonneg_left hvariation (Rat.le_of_lt hK)
    _ = eps.val := by
      dsimp [inputEps, K]
      rw [Rat.div_def]
      have h2K : (2 : Rat) * coefficient C margin ≠ 0 :=
        Rat.ne_of_gt (Rat.mul_pos (by decide +kernel) (coefficient_pos A))
      grind [Rat.mul_assoc, Rat.mul_comm,
        Rat.mul_inv_cancel ((2 : Rat) * coefficient C margin) h2K]

/-- The stabilized represented reciprocal. -/
def reciprocal {C margin : Rat} (A : AwayInput C margin) : ComplexCompute :=
  ComplexCompute.cauchyStabilize (candidate A) (radius A)

theorem reciprocal_valid {C margin : Rat} (A : AwayInput C margin) :
    A.reciprocal.Valid := by
  unfold reciprocal
  exact ComplexCompute.cauchyStabilize_valid
    (candidate_ordered A) (candidate_widths_shrink A)
    (candidate_future_contained_expand A) (radius_shrinks A)

theorem reciprocal_contains_current_candidate
    {C margin : Rat} (A : AwayInput C margin) (stage : Nat) :
    ((candidate A).compute stage).NestedIn (A.reciprocal.compute stage) := by
  unfold reciprocal
  exact ComplexCompute.cauchyStabilize_contains_current
    (candidate_future_contained_expand A) stage

/-- The certified away-from-zero input times its constructed reciprocal
represents one.  At each finite stage, the product box contains the exact
product of the input-box center and its rational-complex inverse. -/
theorem mul_reciprocal_equiv_one
    {C margin : Rat} (A : AwayInput C margin) :
    (ComplexCompute.mul A.raw A.reciprocal).Equiv ComplexCompute.one := by
  intro stage
  apply (ComplexCompute.compareAt_overlap_iff
    (ComplexCompute.mul A.raw A.reciprocal) ComplexCompute.one stage stage).2
  let z := (A.raw.compute stage).center
  have hzmem :
      (A.raw.compute stage).lo <= z /\ z <= (A.raw.compute stage).hi :=
    QBox.center_mem (ComplexCompute.valid_ordered A.valid stage)
  have hcandidate := A.reciprocal_contains_current_candidate stage
  have hinvmem :
      (A.reciprocal.compute stage).lo <= QComplex.inverse z /\
        QComplex.inverse z <= (A.reciprocal.compute stage).hi := by
    change (A.reciprocal.compute stage).lo <=
        (QBox.point (QComplex.inverse z)).lo /\
      (QBox.point (QComplex.inverse z)).hi <=
        (A.reciprocal.compute stage).hi
    exact hcandidate
  have hproduct := QBox.mul_contains hzmem.1 hzmem.2
    hinvmem.1 hinvmem.2
  have hnorm : QComplex.normSq z ≠ 0 := by
    intro hzero
    have hsep := A.center_normSq_ge stage
    have hmargin := A.margin_pos
    dsimp [z] at hzero
    rw [hzero] at hsep
    grind
  have hone : QComplex.mul z (QComplex.inverse z) = QComplex.one :=
    QComplex.mul_inverse_of_normSq_ne_zero z hnorm
  rw [hone] at hproduct
  exact QBox.overlaps_of_common_point hproduct
    ⟨QComplex.le_refl QComplex.one, QComplex.le_refl QComplex.one⟩

theorem quotient_mul_reciprocal_eq_one
    {C margin : Rat} (A : AwayInput C margin) :
    ComplexComputeQuotient.ofRaw A.raw A.valid *
        ComplexComputeQuotient.ofRaw A.reciprocal A.reciprocal_valid = 1 :=
  ComplexComputeQuotient.ofRaw_eq_ofRaw (A.mul_reciprocal_equiv_one)

/-! ## Representative invariance -/

def crossRadius {C margin : Rat} (A B : AwayInput C margin)
    (stage : Nat) : Rat :=
  coefficient C margin * (variation A stage + variation B stage)

theorem radius_le_crossRadius {C margin : Rat}
    (A B : AwayInput C margin) (stage : Nat) :
    radius A stage <= crossRadius A B stage := by
  unfold radius crossRadius
  exact Rat.mul_le_mul_of_nonneg_left
    (by have := variation_nonneg B stage; grind)
    (Rat.le_of_lt (coefficient_pos A))

theorem crossRadius_shrinks {C margin : Rat}
    (A B : AwayInput C margin) : ShrinksToZero (crossRadius A B) := by
  intro eps
  let K := coefficient C margin
  have hK : 0 < K := coefficient_pos A
  let inputEps : QPos :=
    ⟨eps.val / (4 * K), by
      rw [Rat.div_def]
      exact Rat.mul_pos eps.property ((Rat.inv_pos).2
        (Rat.mul_pos (by decide +kernel) hK))⟩
  obtain ⟨NA, hNA⟩ := A.valid.2.2 inputEps
  obtain ⟨NB, hNB⟩ := B.valid.2.2 inputEps
  refine ⟨Nat.max NA NB, ?_⟩
  intro n hn
  have hnA : NA <= n := Nat.le_trans (Nat.le_max_left _ _) hn
  have hnB : NB <= n := Nat.le_trans (Nat.le_max_right _ _) hn
  have hA := hNA n hnA
  have hB := hNB n hnB
  have hvariation : variation A n + variation B n <=
      4 * inputEps.val := by
    unfold variation ComplexExponentialLift.BoundedInput.variation
    have := rat_add_le_add (rat_add_le_add hA.1 hA.2)
      (rat_add_le_add hB.1 hB.2)
    exact Rat.le_trans this (by grind)
  unfold crossRadius
  calc
    coefficient C margin * (variation A n + variation B n) <=
        coefficient C margin * (4 * inputEps.val) :=
      Rat.mul_le_mul_of_nonneg_left hvariation (Rat.le_of_lt hK)
    _ = eps.val := by
      dsimp [inputEps, K]
      rw [Rat.div_def]
      have h4K : (4 : Rat) * coefficient C margin ≠ 0 :=
        Rat.ne_of_gt (Rat.mul_pos (by decide +kernel) (coefficient_pos A))
      grind [Rat.mul_assoc, Rat.mul_comm,
        Rat.mul_inv_cancel ((4 : Rat) * coefficient C margin) h4K]

theorem candidate_future_contained_cross_expand_of_equiv
    {C margin : Rat} (A B : AwayInput C margin)
    (hAB : A.raw.Equiv B.raw) (k n : Nat) (hkn : k <= n) :
    ((candidate A).compute n).NestedIn
      (QBox.expand ((candidate B).compute k) (crossRadius A B k)) := by
  let za := (A.raw.compute n).center
  let zb := (B.raw.compute k).center
  let error := QComplex.sub (QComplex.inverse za) (QComplex.inverse zb)
  have hcenter0 :=
    ComplexExponentialLift.BoundedInput.center_sub_normBound_le_variation_add_of_equiv
      A.toBoundedInput B.toBoundedInput hAB n k
  have hcenter : QComplex.normBound (QComplex.sub za zb) <=
      variation A k + variation B k := by
    exact Rat.le_trans hcenter0
      (rat_add_le_add (variation_antitone A k n hkn) Rat.le_refl)
  have hraw := QComplex.inverse_difference_normBound_le
    A.bound_nonneg A.margin_pos
    (A.center_normBound n) (B.center_normBound k)
    (A.center_normSq_ge n) (B.center_normSq_ge k)
  have hbase0 : 0 <= (inverseBound C margin) ^ 2 := by
    apply Rat.pow_nonneg
    exact Rat.mul_nonneg A.bound_nonneg
      (Rat.le_of_lt ((Rat.inv_pos).2 A.margin_pos))
  have herror0 : QComplex.normBound error <=
      (inverseBound C margin) ^ 2 *
        (variation A k + variation B k) :=
    Rat.le_trans hraw (Rat.mul_le_mul_of_nonneg_left hcenter hbase0)
  have hcoeff : (inverseBound C margin) ^ 2 <= coefficient C margin := by
    unfold coefficient
    grind
  have hvar0 : 0 <= variation A k + variation B k :=
    Rat.add_nonneg (variation_nonneg A k) (variation_nonneg B k)
  have herror : QComplex.normBound error <= crossRadius A B k :=
    Rat.le_trans herror0
      (Rat.mul_le_mul_of_nonneg_right hcoeff hvar0)
  change (QBox.point (QComplex.inverse za)).NestedIn
    (QBox.expand (QBox.point (QComplex.inverse zb)) (crossRadius A B k))
  rw [show QComplex.inverse za = QComplex.add (QComplex.inverse zb) error by
    exact (add_sub_cancel_right (QComplex.inverse za)
      (QComplex.inverse zb)).symm]
  exact ComplexExponentialApproximation.point_add_error_nested_expand _ _ herror

def crossReciprocal {C margin : Rat} (A B : AwayInput C margin) : ComplexCompute :=
  ComplexCompute.cauchyStabilize (candidate A) (crossRadius A B)

theorem crossReciprocal_valid {C margin : Rat}
    (A B : AwayInput C margin) : (crossReciprocal A B).Valid := by
  unfold crossReciprocal
  apply ComplexCompute.cauchyStabilize_valid
  · exact candidate_ordered A
  · exact candidate_widths_shrink A
  · intro k n hkn
    apply QBox.nested_trans (candidate_future_contained_expand A k n hkn)
    exact QBox.expand_mono_radius _ (radius_le_crossRadius A B k)
  · exact crossRadius_shrinks A B

theorem reciprocal_equiv_crossReciprocal {C margin : Rat}
    (A B : AwayInput C margin) :
    A.reciprocal.Equiv (crossReciprocal A B) := by
  unfold reciprocal crossReciprocal
  apply ComplexCompute.cauchyStabilize_equiv_of_common_candidate
  · exact candidate_ordered A
  · exact candidate_future_contained_expand A
  · intro k n hkn
    apply QBox.nested_trans (candidate_future_contained_expand A k n hkn)
    exact QBox.expand_mono_radius _ (radius_le_crossRadius A B k)

theorem crossRadius_comm {C margin : Rat}
    (A B : AwayInput C margin) (n : Nat) :
    crossRadius A B n = crossRadius B A n := by
  simp [crossRadius, Rat.add_comm]

theorem crossReciprocal_equiv_of_input_equiv
    {C margin : Rat} (A B : AwayInput C margin)
    (hAB : A.raw.Equiv B.raw) :
    (crossReciprocal A B).Equiv (crossReciprocal B A) := by
  intro n
  apply (ComplexCompute.compareAt_overlap_iff
    (crossReciprocal A B) (crossReciprocal B A) n n).2
  have hleft : ((candidate A).compute n).NestedIn
      ((crossReciprocal A B).compute n) := by
    unfold crossReciprocal
    apply ComplexCompute.cauchyStabilize_contains_external
      (external := fun m => (candidate A).compute m)
    intro k m hkm
    apply QBox.nested_trans (candidate_future_contained_expand A k m hkm)
    exact QBox.expand_mono_radius _ (radius_le_crossRadius A B k)
    exact Nat.le_refl n
  have hright : ((candidate A).compute n).NestedIn
      ((crossReciprocal B A).compute n) := by
    unfold crossReciprocal
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

theorem reciprocal_equiv_of_input_equiv
    {C margin : Rat} (A B : AwayInput C margin)
    (hAB : A.raw.Equiv B.raw) : A.reciprocal.Equiv B.reciprocal := by
  exact ComplexCompute.equiv_trans
    A.reciprocal_valid (crossReciprocal_valid A B) B.reciprocal_valid
    (reciprocal_equiv_crossReciprocal A B)
    (ComplexCompute.equiv_trans
      (crossReciprocal_valid A B) (crossReciprocal_valid B A)
      B.reciprocal_valid
      (crossReciprocal_equiv_of_input_equiv A B hAB)
      (ComplexCompute.equiv_symm (reciprocal_equiv_crossReciprocal B A)))

/-- On an exact rational-complex input, reciprocal stabilization is literally
the constant rational inverse box at every stage. -/
theorem reciprocal_ofQComplex_compute_eq
    (z : QComplex) (C margin : Rat)
    (hC : 0 <= C) (hmargin : 0 < margin)
    (hzC : QComplex.normBound z <= C)
    (hzsep : margin <= QComplex.normSq z) (n : Nat) :
    ((ofQComplex z C margin hC hmargin hzC hzsep).reciprocal).compute n =
      QBox.point (QComplex.inverse z) := by
  let A := ofQComplex z C margin hC hmargin hzC hzsep
  have hcenter : forall stage, (A.raw.compute stage).center = z := by
    intro stage
    dsimp [A, ofQComplex]
    cases z
    simp only [ComplexCompute.ofQComplex, QBox.center]
    congr 1 <;>
      rw [Rat.div_def] <;>
      grind [Rat.add_mul, Rat.mul_assoc, Rat.mul_comm,
        Rat.mul_inv_cancel]
  have hcandidate : forall stage,
      (candidate A).compute stage = QBox.point (QComplex.inverse z) := by
    intro stage
    simp only [candidate]
    rw [hcenter]
  have hvariation : forall stage, variation A stage = 0 := by
    intro stage
    unfold variation ComplexExponentialLift.BoundedInput.variation
    dsimp [A, ofQComplex, toBoundedInput]
    simp [ComplexCompute.ofQComplex, QBox.width, QBox.height,
      Rat.sub_self, Rat.zero_add]
  have hradius : forall stage, radius A stage = 0 := by
    intro stage
    unfold radius
    rw [hvariation, Rat.mul_zero]
  unfold reciprocal ComplexCompute.cauchyStabilize
  change ComplexCompute.cauchyStabilizeCompute
      (candidate A).compute (radius A) n =
    QBox.point (QComplex.inverse z)
  induction n with
  | zero =>
      rw [ComplexCompute.cauchyStabilizeCompute.eq_def, hcandidate, hradius]
      simp [QBox.expand, QBox.point, Rat.sub_eq_add_neg, Rat.add_zero]
  | succ n ih =>
      change QBox.intersection
        (ComplexCompute.cauchyStabilizeCompute (candidate A).compute (radius A) n)
        (QBox.expand ((candidate A).compute (n + 1)) (radius A (n + 1))) =
          QBox.point (QComplex.inverse z)
      rw [ih, hcandidate, hradius]
      simp [QBox.expand, QBox.intersection, QBox.point, minRat, maxRat2,
        Rat.sub_eq_add_neg, Rat.add_zero]

/-- Exact rational-complex inputs are preserved by the represented reciprocal
lift, up to inversion. -/
theorem reciprocal_ofQComplex_equiv_ofQComplex_inverse
    (z : QComplex) (C margin : Rat)
    (hC : 0 <= C) (hmargin : 0 < margin)
    (hzC : QComplex.normBound z <= C)
    (hzsep : margin <= QComplex.normSq z) :
    ((ofQComplex z C margin hC hmargin hzC hzsep).reciprocal).Equiv
      (ComplexCompute.ofQComplex (QComplex.inverse z)) := by
  intro n
  apply (ComplexCompute.compareAt_overlap_iff _ _ n n).2
  rw [reciprocal_ofQComplex_compute_eq z C margin hC hmargin hzC hzsep n]
  exact ⟨QComplex.le_refl _, QComplex.le_refl _⟩

end AwayInput
end ComplexReciprocalLift
end ComputableAnalysis


