-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Analysis_FiniteApproximateIdentity
-- name    : liuyao_ca_fd889115_k1_Analysis_FiniteApproximateIdentity
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T17:50:23.135103+00:00
-- url     : https://prove2.me/theorems/54614803-58b5-4aec-97fa-07372d5d333a
-- title:
--   Computable analysis · FiniteApproximateIdentity · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableAnalysis/FiniteApproximateIdentity.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_Basic

set_option autoImplicit true

/-!
# Finite approximate identities

This module isolates the finite algebra behind an approximate identity.  A
kernel is a finite list of rational sample points with nonnegative rational
weights of total mass one.  Its action is therefore an executable rational
weighted sum.

No integral, topology, completed real number, or limiting assertion occurs
here.  A later quadrature construction can use this theorem after proving
that its finite weights have mass one and are concentrated in a region where
the sampled function has a stated rational modulus.
-/

namespace ComputableAnalysis

/-- One rational sample point and its rational quadrature weight. -/
structure WeightedPoint where
  point : Rat
  weight : Rat
deriving DecidableEq, Repr

namespace WeightedPoint

/-- Total mass of a finite weighted sample. -/
def totalWeight : List WeightedPoint -> Rat
  | [] => 0
  | sample :: rest => sample.weight + totalWeight rest

/-- The literal finite weighted action on a rational-valued function. -/
def action (samples : List WeightedPoint) (f : Rat -> Rat) : Rat :=
  match samples with
  | [] => 0
  | sample :: rest => sample.weight * f sample.point + action rest f

theorem action_append (left right : List WeightedPoint) (f : Rat -> Rat) :
    action (left ++ right) f = action left f + action right f := by
  induction left with
  | nil =>
      change action right f = 0 + action right f
      grind
  | cons sample rest ih =>
      simp only [List.cons_append, action]
      rw [ih]
      grind [Rat.add_assoc]

theorem action_const (samples : List WeightedPoint) (constant : Rat) :
    action samples (fun _ => constant) = constant * totalWeight samples := by
  induction samples with
  | nil =>
      change (0 : Rat) = constant * 0
      grind
  | cons sample rest ih =>
      simp only [action, totalWeight]
      rw [ih]
      grind [Rat.mul_add, Rat.add_mul, Rat.mul_comm]

theorem action_add (samples : List WeightedPoint) (f g : Rat -> Rat) :
    action samples (fun x => f x + g x) = action samples f + action samples g := by
  induction samples with
  | nil =>
      change (0 : Rat) = 0 + 0
      grind
  | cons sample rest ih =>
      simp only [action]
      rw [ih]
      grind [Rat.mul_add, Rat.add_assoc, Rat.add_comm]

theorem action_scale (samples : List WeightedPoint)
    (factor : Rat) (f : Rat -> Rat) :
    action samples (fun x => factor * f x) = factor * action samples f := by
  induction samples with
  | nil =>
      change (0 : Rat) = factor * 0
      grind
  | cons sample rest ih =>
      simp only [action]
      rw [ih]
      grind [Rat.mul_add, Rat.mul_assoc, Rat.mul_comm]

/-- The same action, centered at a prescribed rational value. -/
def centeredAction (samples : List WeightedPoint)
    (f : Rat -> Rat) (center : Rat) : Rat :=
  match samples with
  | [] => 0
  | sample :: rest =>
      sample.weight * (f sample.point - center) +
        centeredAction rest f center

theorem totalWeight_append (left right : List WeightedPoint) :
    totalWeight (left ++ right) = totalWeight left + totalWeight right := by
  induction left with
  | nil =>
      change totalWeight right = 0 + totalWeight right
      grind
  | cons sample rest ih =>
      simp only [List.cons_append, totalWeight]
      rw [ih]
      grind

theorem centeredAction_append (left right : List WeightedPoint)
    (f : Rat -> Rat) (center : Rat) :
    centeredAction (left ++ right) f center =
      centeredAction left f center + centeredAction right f center := by
  induction left with
  | nil =>
      change centeredAction right f center =
        0 + centeredAction right f center
      grind
  | cons sample rest ih =>
      simp only [List.cons_append, centeredAction]
      rw [ih]
      grind

theorem action_eq_center_mul_totalWeight_add_centeredAction
    (samples : List WeightedPoint) (f : Rat -> Rat) (center : Rat) :
    action samples f = center * totalWeight samples +
      centeredAction samples f center := by
  induction samples with
  | nil =>
      change (0 : Rat) = center * 0 + 0
      grind
  | cons sample rest ih =>
      simp only [action, totalWeight, centeredAction]
      rw [ih]
      grind [Rat.mul_add, Rat.add_mul, Rat.sub_eq_add_neg,
        Rat.mul_assoc, Rat.mul_comm]

/-- A finite weighted sum inherits a common pointwise error bound. -/
theorem qabs_centeredAction_le
    (samples : List WeightedPoint) (f : Rat -> Rat)
    (center error : Rat)
    (weights_nonnegative :
      forall sample, sample ∈ samples -> 0 <= sample.weight)
    (local_error :
      forall sample, sample ∈ samples ->
        qabs (f sample.point - center) <= error) :
    qabs (centeredAction samples f center) <=
      error * totalWeight samples := by
  induction samples with
  | nil => simp [centeredAction, totalWeight, qabs]
  | cons sample rest ih =>
      have hweight : 0 <= sample.weight :=
        weights_nonnegative sample (by simp)
      have hlocal : qabs (f sample.point - center) <= error :=
        local_error sample (by simp)
      have hrestWeights :
          forall item, item ∈ rest -> 0 <= item.weight := by
        intro item hitem
        exact weights_nonnegative item (by simp [hitem])
      have hrestLocal :
          forall item, item ∈ rest ->
            qabs (f item.point - center) <= error := by
        intro item hitem
        exact local_error item (by simp [hitem])
      have htail := ih hrestWeights hrestLocal
      calc
        qabs (centeredAction (sample :: rest) f center) =
            qabs (sample.weight * (f sample.point - center) +
              centeredAction rest f center) := by rfl
        _ <= qabs (sample.weight * (f sample.point - center)) +
              qabs (centeredAction rest f center) :=
            qabs_add_le _ _
        _ = sample.weight * qabs (f sample.point - center) +
              qabs (centeredAction rest f center) := by
            rw [qabs_mul, qabs_eq_self_of_nonneg hweight]
        _ <= sample.weight * error +
              error * totalWeight rest :=
            rat_add_le_add
              (Rat.mul_le_mul_of_nonneg_left hlocal hweight) htail
        _ = error * totalWeight (sample :: rest) := by
            simp only [totalWeight]
            grind [Rat.mul_add, Rat.add_mul, Rat.mul_comm]

/-- Split a finite weighted action into a well-controlled central part and a
separately controlled tail.  This is the finite rational estimate needed by
Gaussian quadrature: the central samples use a local modulus, while distant
samples are charged against their explicit tail mass. -/
theorem qabs_centeredAction_append_le
    (central tail : List WeightedPoint) (f : Rat -> Rat)
    (center centralError tailError : Rat)
    (central_weights_nonnegative :
      forall sample, sample ∈ central -> 0 <= sample.weight)
    (tail_weights_nonnegative :
      forall sample, sample ∈ tail -> 0 <= sample.weight)
    (central_error :
      forall sample, sample ∈ central ->
        qabs (f sample.point - center) <= centralError)
    (tail_error :
      forall sample, sample ∈ tail ->
        qabs (f sample.point - center) <= tailError) :
    qabs (centeredAction (central ++ tail) f center) <=
      centralError * totalWeight central +
        tailError * totalWeight tail := by
  rw [centeredAction_append]
  exact Rat.le_trans (qabs_add_le _ _)
    (rat_add_le_add
      (qabs_centeredAction_le central f center centralError
        central_weights_nonnegative central_error)
      (qabs_centeredAction_le tail f center tailError
        tail_weights_nonnegative tail_error))

/-- Multiply every weight by the same rational factor, leaving sample points
unchanged. -/
def scaleWeights (factor : Rat) : List WeightedPoint -> List WeightedPoint
  | [] => []
  | sample :: rest =>
      { point := sample.point, weight := factor * sample.weight } ::
        scaleWeights factor rest

theorem totalWeight_scaleWeights (factor : Rat)
    (samples : List WeightedPoint) :
    totalWeight (scaleWeights factor samples) =
      factor * totalWeight samples := by
  induction samples with
  | nil => simp [scaleWeights, totalWeight]
  | cons sample rest ih =>
      simp only [scaleWeights, totalWeight]
      rw [ih]
      grind [Rat.mul_add]

theorem action_scaleWeights (factor : Rat)
    (samples : List WeightedPoint) (f : Rat -> Rat) :
    action (scaleWeights factor samples) f = factor * action samples f := by
  induction samples with
  | nil => simp [scaleWeights, action]
  | cons sample rest ih =>
      simp only [scaleWeights, action]
      rw [ih]
      grind [Rat.mul_add, Rat.mul_assoc]

theorem scaleWeights_nonnegative
    (factor : Rat) (factor_nonnegative : 0 <= factor)
    (samples : List WeightedPoint)
    (weights_nonnegative :
      forall sample, sample ∈ samples -> 0 <= sample.weight) :
    forall sample, sample ∈ scaleWeights factor samples ->
      0 <= sample.weight := by
  induction samples with
  | nil =>
      intro sample hsample
      simp [scaleWeights] at hsample
  | cons head rest ih =>
      intro sample hsample
      simp only [scaleWeights, List.mem_cons] at hsample
      rcases hsample with hsample | hsample
      · rw [hsample]
        exact Rat.mul_nonneg factor_nonnegative
          (weights_nonnegative head (by simp))
      · apply ih
        · intro item hitem
          exact weights_nonnegative item (by simp [hitem])
        · exact hsample

theorem scaleWeights_preserves_point_bound
    (factor : Rat) (samples : List WeightedPoint) (bound : Rat)
    (points_bounded :
      forall sample, sample ∈ samples -> qabs sample.point <= bound) :
    forall sample, sample ∈ scaleWeights factor samples ->
      qabs sample.point <= bound := by
  induction samples with
  | nil =>
      intro sample hsample
      simp [scaleWeights] at hsample
  | cons head rest ih =>
      intro sample hsample
      simp only [scaleWeights, List.mem_cons] at hsample
      rcases hsample with hsample | hsample
      · rw [hsample]
        exact points_bounded head (by simp)
      · apply ih
        · intro item hitem
          exact points_bounded item (by simp [hitem])
        · exact hsample

end WeightedPoint

/-! ## Stability of aligned finite quadrature rules -/

/-- One source sample paired with one target sample.  A finite list of these
pairs is an explicit coupling between two quadrature rules; no matching or
choice principle is hidden in the comparison. -/
structure WeightedPointCoupling where
  source : WeightedPoint
  target : WeightedPoint
deriving DecidableEq, Repr

namespace WeightedPointCoupling

/-- Source weighted action of a finite coupling. -/
def sourceAction : List WeightedPointCoupling -> (Rat -> Rat) -> Rat
  | [], _ => 0
  | pair :: rest, f =>
      pair.source.weight * f pair.source.point + sourceAction rest f

/-- Target weighted action of a finite coupling. -/
def targetAction : List WeightedPointCoupling -> (Rat -> Rat) -> Rat
  | [], _ => 0
  | pair :: rest, f =>
      pair.target.weight * f pair.target.point + targetAction rest f

/-- Total source mass in the coupling. -/
def sourceTotalWeight : List WeightedPointCoupling -> Rat
  | [] => 0
  | pair :: rest => pair.source.weight + sourceTotalWeight rest

/-- Total absolute discrepancy between paired source and target weights. -/
def weightDiscrepancy : List WeightedPointCoupling -> Rat
  | [] => 0
  | pair :: rest =>
      qabs (pair.target.weight - pair.source.weight) +
        weightDiscrepancy rest

/-- Source sample list extracted from an explicit coupling. -/
def sourceSamples (pairs : List WeightedPointCoupling) : List WeightedPoint :=
  pairs.map (fun pair => pair.source)

/-- Target sample list extracted from an explicit coupling. -/
def targetSamples (pairs : List WeightedPointCoupling) : List WeightedPoint :=
  pairs.map (fun pair => pair.target)

theorem sourceAction_eq_action (pairs : List WeightedPointCoupling)
    (f : Rat -> Rat) :
    sourceAction pairs f = WeightedPoint.action (sourceSamples pairs) f := by
  induction pairs with
  | nil => rfl
  | cons pair rest ih => simp [sourceAction, sourceSamples, ih,
      WeightedPoint.action]

theorem targetAction_eq_action (pairs : List WeightedPointCoupling)
    (f : Rat -> Rat) :
    targetAction pairs f = WeightedPoint.action (targetSamples pairs) f := by
  induction pairs with
  | nil => rfl
  | cons pair rest ih => simp [targetAction, targetSamples, ih,
      WeightedPoint.action]

theorem sourceTotalWeight_eq_totalWeight
    (pairs : List WeightedPointCoupling) :
    sourceTotalWeight pairs =
      WeightedPoint.totalWeight (sourceSamples pairs) := by
  induction pairs with
  | nil => rfl
  | cons pair rest ih => simp [sourceTotalWeight, sourceSamples, ih,
      WeightedPoint.totalWeight]

/-- Finite quadrature stability under simultaneous perturbation of weights
and sample points.  The first term pays for changing weights, using a bound on
target values.  The second pays for transporting source points to target
points, using the original nonnegative mass. -/
theorem qabs_targetAction_sub_sourceAction_le
    (pairs : List WeightedPointCoupling) (sourceFunction targetFunction : Rat -> Rat)
    (valueBound pointError : Rat)
    (source_weights_nonnegative : forall pair, pair ∈ pairs ->
      0 <= pair.source.weight)
    (target_values_bounded : forall pair, pair ∈ pairs ->
      qabs (targetFunction pair.target.point) <= valueBound)
    (point_transport_error : forall pair, pair ∈ pairs ->
      qabs (targetFunction pair.target.point -
        sourceFunction pair.source.point) <= pointError) :
    qabs (targetAction pairs targetFunction -
      sourceAction pairs sourceFunction) <=
        valueBound * weightDiscrepancy pairs +
          pointError * sourceTotalWeight pairs := by
  induction pairs with
  | nil =>
      change qabs (0 - 0) <= valueBound * 0 + pointError * 0
      grind [qabs]
  | cons pair rest ih =>
      have hsourceWeight : 0 <= pair.source.weight :=
        source_weights_nonnegative pair (by simp)
      have htargetValue :
          qabs (targetFunction pair.target.point) <= valueBound :=
        target_values_bounded pair (by simp)
      have hpointError :
          qabs (targetFunction pair.target.point -
            sourceFunction pair.source.point) <= pointError :=
        point_transport_error pair (by simp)
      have hrestSourceWeights : forall item, item ∈ rest ->
          0 <= item.source.weight := by
        intro item hitem
        exact source_weights_nonnegative item (by simp [hitem])
      have hrestTargetValues : forall item, item ∈ rest ->
          qabs (targetFunction item.target.point) <= valueBound := by
        intro item hitem
        exact target_values_bounded item (by simp [hitem])
      have hrestPointError : forall item, item ∈ rest ->
          qabs (targetFunction item.target.point -
            sourceFunction item.source.point) <= pointError := by
        intro item hitem
        exact point_transport_error item (by simp [hitem])
      have htail := ih hrestSourceWeights hrestTargetValues hrestPointError
      have hweightTerm :
          qabs ((pair.target.weight - pair.source.weight) *
              targetFunction pair.target.point) <=
            qabs (pair.target.weight - pair.source.weight) * valueBound := by
        rw [qabs_mul]
        exact Rat.mul_le_mul_of_nonneg_left htargetValue
          (qabs_nonneg _)
      have hpointTerm :
          qabs (pair.source.weight *
              (targetFunction pair.target.point -
                sourceFunction pair.source.point)) <=
            pair.source.weight * pointError := by
        rw [qabs_mul, qabs_eq_self_of_nonneg hsourceWeight]
        exact Rat.mul_le_mul_of_nonneg_left hpointError hsourceWeight
      have hhead :
          qabs ((pair.target.weight - pair.source.weight) *
              targetFunction pair.target.point +
            pair.source.weight *
              (targetFunction pair.target.point -
                sourceFunction pair.source.point)) <=
            qabs (pair.target.weight - pair.source.weight) * valueBound +
              pair.source.weight * pointError :=
        Rat.le_trans (qabs_add_le _ _)
          (rat_add_le_add hweightTerm hpointTerm)
      have hrearrange :
          targetAction (pair :: rest) targetFunction -
              sourceAction (pair :: rest) sourceFunction =
            ((pair.target.weight - pair.source.weight) *
                targetFunction pair.target.point +
              pair.source.weight *
                (targetFunction pair.target.point -
                  sourceFunction pair.source.point)) +
              (targetAction rest targetFunction -
                sourceAction rest sourceFunction) := by
        simp only [targetAction, sourceAction]
        grind [Rat.mul_add, Rat.add_mul, Rat.sub_eq_add_neg,
          Rat.mul_assoc, Rat.mul_comm]
      rw [hrearrange]
      calc
        qabs
            (((pair.target.weight - pair.source.weight) *
                targetFunction pair.target.point +
              pair.source.weight *
                (targetFunction pair.target.point -
                  sourceFunction pair.source.point)) +
              (targetAction rest targetFunction -
                sourceAction rest sourceFunction)) <=
            qabs ((pair.target.weight - pair.source.weight) *
                targetFunction pair.target.point +
              pair.source.weight *
                (targetFunction pair.target.point -
                  sourceFunction pair.source.point)) +
              qabs (targetAction rest targetFunction -
                sourceAction rest sourceFunction) := qabs_add_le _ _
        _ <=
            (qabs (pair.target.weight - pair.source.weight) * valueBound +
              pair.source.weight * pointError) +
              (valueBound * weightDiscrepancy rest +
                pointError * sourceTotalWeight rest) :=
          rat_add_le_add hhead htail
        _ = valueBound * weightDiscrepancy (pair :: rest) +
              pointError * sourceTotalWeight (pair :: rest) := by
          simp only [weightDiscrepancy, sourceTotalWeight]
          grind [Rat.mul_add, Rat.add_mul, Rat.mul_comm, Rat.mul_assoc]

/-- Exact-weight specialization: when paired weights agree, only transport of
sample points contributes to the quadrature error. -/
theorem qabs_targetAction_sub_sourceAction_le_of_weights_eq
    (pairs : List WeightedPointCoupling) (sourceFunction targetFunction : Rat -> Rat)
    (pointError : Rat)
    (source_weights_nonnegative : forall pair, pair ∈ pairs ->
      0 <= pair.source.weight)
    (weights_eq : forall pair, pair ∈ pairs ->
      pair.target.weight = pair.source.weight)
    (point_transport_error : forall pair, pair ∈ pairs ->
      qabs (targetFunction pair.target.point -
        sourceFunction pair.source.point) <= pointError) :
    qabs (targetAction pairs targetFunction -
      sourceAction pairs sourceFunction) <=
        pointError * sourceTotalWeight pairs := by
  induction pairs with
  | nil =>
      change qabs (0 - 0) <= pointError * 0
      grind [qabs]
  | cons pair rest ih =>
      have hsourceWeight : 0 <= pair.source.weight :=
        source_weights_nonnegative pair (by simp)
      have hweight : pair.target.weight = pair.source.weight :=
        weights_eq pair (by simp)
      have hpointError :
          qabs (targetFunction pair.target.point -
            sourceFunction pair.source.point) <= pointError :=
        point_transport_error pair (by simp)
      have htail := ih
        (fun item hitem => source_weights_nonnegative item (by simp [hitem]))
        (fun item hitem => weights_eq item (by simp [hitem]))
        (fun item hitem => point_transport_error item (by simp [hitem]))
      have hhead :
          qabs (pair.source.weight *
            (targetFunction pair.target.point -
              sourceFunction pair.source.point)) <=
            pair.source.weight * pointError := by
        rw [qabs_mul, qabs_eq_self_of_nonneg hsourceWeight]
        exact Rat.mul_le_mul_of_nonneg_left hpointError hsourceWeight
      have hrearrange :
          targetAction (pair :: rest) targetFunction -
              sourceAction (pair :: rest) sourceFunction =
            pair.source.weight *
                (targetFunction pair.target.point -
                  sourceFunction pair.source.point) +
              (targetAction rest targetFunction -
                sourceAction rest sourceFunction) := by
        simp only [targetAction, sourceAction]
        rw [hweight]
        grind [Rat.mul_add, Rat.add_mul, Rat.sub_eq_add_neg,
          Rat.mul_assoc, Rat.mul_comm]
      rw [hrearrange]
      exact Rat.le_trans (qabs_add_le _ _)
        (Rat.le_trans (rat_add_le_add hhead htail) (by
          simp only [sourceTotalWeight]
          grind [Rat.mul_add, Rat.add_mul, Rat.mul_comm]))

/-- The same stability estimate stated through the public finite weighted
action on the two sample lists extracted from the coupling. -/
theorem qabs_action_targetSamples_sub_action_sourceSamples_le
    (pairs : List WeightedPointCoupling) (sourceFunction targetFunction : Rat -> Rat)
    (valueBound pointError : Rat)
    (source_weights_nonnegative : forall pair, pair ∈ pairs ->
      0 <= pair.source.weight)
    (target_values_bounded : forall pair, pair ∈ pairs ->
      qabs (targetFunction pair.target.point) <= valueBound)
    (point_transport_error : forall pair, pair ∈ pairs ->
      qabs (targetFunction pair.target.point -
        sourceFunction pair.source.point) <= pointError) :
    qabs (WeightedPoint.action (targetSamples pairs) targetFunction -
      WeightedPoint.action (sourceSamples pairs) sourceFunction) <=
        valueBound * weightDiscrepancy pairs +
          pointError * WeightedPoint.totalWeight (sourceSamples pairs) := by
  rw [← targetAction_eq_action, ← sourceAction_eq_action,
    ← sourceTotalWeight_eq_totalWeight]
  exact qabs_targetAction_sub_sourceAction_le pairs
    sourceFunction targetFunction valueBound pointError
    source_weights_nonnegative target_values_bounded point_transport_error

/-- Public-action form of exact-weight point transport. -/
theorem qabs_action_targetSamples_sub_action_sourceSamples_le_of_weights_eq
    (pairs : List WeightedPointCoupling) (sourceFunction targetFunction : Rat -> Rat)
    (pointError : Rat)
    (source_weights_nonnegative : forall pair, pair ∈ pairs ->
      0 <= pair.source.weight)
    (weights_eq : forall pair, pair ∈ pairs ->
      pair.target.weight = pair.source.weight)
    (point_transport_error : forall pair, pair ∈ pairs ->
      qabs (targetFunction pair.target.point -
        sourceFunction pair.source.point) <= pointError) :
    qabs (WeightedPoint.action (targetSamples pairs) targetFunction -
      WeightedPoint.action (sourceSamples pairs) sourceFunction) <=
        pointError * WeightedPoint.totalWeight (sourceSamples pairs) := by
  rw [← targetAction_eq_action, ← sourceAction_eq_action,
    ← sourceTotalWeight_eq_totalWeight]
  exact qabs_targetAction_sub_sourceAction_le_of_weights_eq pairs
    sourceFunction targetFunction pointError source_weights_nonnegative
    weights_eq point_transport_error

end WeightedPointCoupling

/-- Executable finite probability data: nonnegative rational weights with
exact rational total mass one. -/
structure FiniteProbabilityKernel where
  samples : List WeightedPoint
  weights_nonnegative :
    forall sample, sample ∈ samples -> 0 <= sample.weight
  totalWeight_eq_one : WeightedPoint.totalWeight samples = 1

namespace FiniteProbabilityKernel

def action (kernel : FiniteProbabilityKernel) (f : Rat -> Rat) : Rat :=
  WeightedPoint.action kernel.samples f

/-- Finite approximate-identity theorem in its most direct form.  If every
sample seen by the normalized positive kernel is within `error` of `center`,
then the kernel action is within the same error. -/
theorem action_approximates_center
    (kernel : FiniteProbabilityKernel) (f : Rat -> Rat)
    (center error : Rat)
    (local_error :
      forall sample, sample ∈ kernel.samples ->
        qabs (f sample.point - center) <= error) :
    qabs (kernel.action f - center) <= error := by
  have hcentered := WeightedPoint.qabs_centeredAction_le
    kernel.samples f center error
    kernel.weights_nonnegative local_error
  have haction := WeightedPoint.action_eq_center_mul_totalWeight_add_centeredAction
    kernel.samples f center
  rw [kernel.totalWeight_eq_one] at haction hcentered
  have heq :
      kernel.action f - center =
        WeightedPoint.centeredAction kernel.samples f center := by
    unfold action
    rw [haction]
    grind
  rw [heq]
  simpa using hcentered

/-- Radius/Lipschitz specialization.  This is the reusable concentration
estimate used by finite quadrature approximations to a Gaussian delta family.
-/
theorem action_approximates_value_at_zero
    (kernel : FiniteProbabilityKernel) (f : Rat -> Rat)
    (lipschitz radius : Rat)
    (lipschitz_nonnegative : 0 <= lipschitz)
    (support_radius :
      forall sample, sample ∈ kernel.samples ->
        qabs sample.point <= radius)
    (lipschitz_at_zero :
      forall sample, sample ∈ kernel.samples ->
        qabs (f sample.point - f 0) <=
          lipschitz * qabs sample.point) :
    qabs (kernel.action f - f 0) <= lipschitz * radius := by
  apply kernel.action_approximates_center f (f 0) (lipschitz * radius)
  intro sample hsample
  exact Rat.le_trans (lipschitz_at_zero sample hsample)
    (Rat.mul_le_mul_of_nonneg_left
      (support_radius sample hsample) lipschitz_nonnegative)

/-- Central/tail form of the finite approximate-identity estimate.  Unlike a
single global error bound, this records the small mass of distant samples
explicitly and is therefore the useful shape for a truncated Gaussian. -/
theorem action_approximates_center_of_split
    (kernel : FiniteProbabilityKernel) (f : Rat -> Rat)
    (center centralError tailError : Rat)
    (central tail : List WeightedPoint)
    (split : kernel.samples = central ++ tail)
    (central_error :
      forall sample, sample ∈ central ->
        qabs (f sample.point - center) <= centralError)
    (tail_error :
      forall sample, sample ∈ tail ->
        qabs (f sample.point - center) <= tailError) :
    qabs (kernel.action f - center) <=
      centralError * WeightedPoint.totalWeight central +
        tailError * WeightedPoint.totalWeight tail := by
  have hcentralWeights :
      forall sample, sample ∈ central -> 0 <= sample.weight := by
    intro sample hsample
    apply kernel.weights_nonnegative sample
    rw [split]
    exact List.mem_append_left tail hsample
  have htailWeights :
      forall sample, sample ∈ tail -> 0 <= sample.weight := by
    intro sample hsample
    apply kernel.weights_nonnegative sample
    rw [split]
    exact List.mem_append_right central hsample
  have haction := WeightedPoint.action_eq_center_mul_totalWeight_add_centeredAction
    kernel.samples f center
  rw [kernel.totalWeight_eq_one] at haction
  have heq :
      kernel.action f - center =
        WeightedPoint.centeredAction kernel.samples f center := by
    unfold action
    rw [haction]
    grind
  rw [heq, split]
  exact WeightedPoint.qabs_centeredAction_append_le
    central tail f center centralError tailError
    hcentralWeights htailWeights central_error tail_error

end FiniteProbabilityKernel

/-- Unnormalized finite positive kernel data.  This is the input shape of a
rational quadrature rule before division by its computed total mass. -/
structure FinitePositiveKernelData where
  samples : List WeightedPoint
  weights_nonnegative :
    forall sample, sample ∈ samples -> 0 <= sample.weight
  totalWeight_positive : 0 < WeightedPoint.totalWeight samples

namespace FinitePositiveKernelData

/-- Exact rational normalization by the finite computed total mass. -/
def normalized (data : FinitePositiveKernelData) : FiniteProbabilityKernel where
  samples := WeightedPoint.scaleWeights
    (WeightedPoint.totalWeight data.samples)⁻¹ data.samples
  weights_nonnegative := WeightedPoint.scaleWeights_nonnegative
    (WeightedPoint.totalWeight data.samples)⁻¹
    (Rat.le_of_lt ((Rat.inv_pos).2 data.totalWeight_positive))
    data.samples data.weights_nonnegative
  totalWeight_eq_one := by
    rw [WeightedPoint.totalWeight_scaleWeights]
    have hnonzero : WeightedPoint.totalWeight data.samples ≠ 0 :=
      Rat.ne_of_gt data.totalWeight_positive
    grind [Rat.mul_comm, Rat.mul_inv_cancel _ hnonzero]

theorem normalized_action (data : FinitePositiveKernelData)
    (f : Rat -> Rat) :
    data.normalized.action f =
      (WeightedPoint.totalWeight data.samples)⁻¹ *
        WeightedPoint.action data.samples f := by
  unfold normalized FiniteProbabilityKernel.action
  exact WeightedPoint.action_scaleWeights _ _ _

theorem normalized_support
    (data : FinitePositiveKernelData) (bound : Rat)
    (points_bounded : forall sample, sample ∈ data.samples ->
      qabs sample.point <= bound) :
    forall sample, sample ∈ data.normalized.samples ->
      qabs sample.point <= bound :=
  WeightedPoint.scaleWeights_preserves_point_bound _ _ _ points_bounded

end FinitePositiveKernelData

/-- A fully scheduled finite approximate identity.  The schedule is part of
the data: asking for a positive rational radius returns a stage whose finite
kernel is supported inside that radius. -/
structure FiniteApproximateIdentity where
  kernel : Nat -> FiniteProbabilityKernel
  radius : Nat -> Rat
  radius_nonnegative : forall stage, 0 <= radius stage
  support_radius : forall stage sample,
    sample ∈ (kernel stage).samples -> qabs sample.point <= radius stage
  schedule : Rat -> Nat
  schedule_spec : forall requested,
    0 < requested -> radius (schedule requested) <= requested

namespace FiniteApproximateIdentity

/-- Explicit convergence rate on a rational Lipschitz probe. -/
theorem action_rate
    (family : FiniteApproximateIdentity) (f : Rat -> Rat)
    (lipschitz requestedError : Rat)
    (lipschitz_positive : 0 < lipschitz)
    (requestedError_positive : 0 < requestedError)
    (lipschitz_at_zero : forall sample,
      sample ∈ (family.kernel
        (family.schedule (requestedError / lipschitz))).samples ->
        qabs (f sample.point - f 0) <=
          lipschitz * qabs sample.point) :
    qabs ((family.kernel
      (family.schedule (requestedError / lipschitz))).action f - f 0) <=
        requestedError := by
  have hlipschitzNonnegative : 0 <= lipschitz := Rat.le_of_lt lipschitz_positive
  have hlipschitzNonzero : lipschitz ≠ 0 := Rat.ne_of_gt lipschitz_positive
  have hrequested : 0 < requestedError / lipschitz := by
    rw [Rat.div_def]
    exact Rat.mul_pos requestedError_positive
      ((Rat.inv_pos).2 lipschitz_positive)
  let stage := family.schedule (requestedError / lipschitz)
  have hradius := family.schedule_spec
    (requestedError / lipschitz) hrequested
  have hfinite := (family.kernel stage).action_approximates_value_at_zero
    f lipschitz (family.radius stage) hlipschitzNonnegative
    (family.support_radius stage)
    lipschitz_at_zero
  have hscaled :
      lipschitz * family.radius stage <= requestedError := by
    calc
      lipschitz * family.radius stage <=
          lipschitz * (requestedError / lipschitz) :=
        Rat.mul_le_mul_of_nonneg_left hradius hlipschitzNonnegative
      _ = requestedError := by
        rw [Rat.div_def]
        grind [Rat.mul_assoc, Rat.mul_comm,
          Rat.mul_inv_cancel _ hlipschitzNonzero]
  exact Rat.le_trans hfinite hscaled

end FiniteApproximateIdentity

/-! ## A concrete shrinking two-point family -/

/-- The positive rational radius `1/(stage+1)`. -/
def reciprocalStageRadius (stage : Nat) : Rat :=
  1 / (((stage + 1 : Nat) : Rat))

theorem reciprocalStageRadius_positive (stage : Nat) :
    0 < reciprocalStageRadius stage := by
  unfold reciprocalStageRadius
  rw [Rat.div_def, Rat.one_mul]
  exact (Rat.inv_pos).2
    ((Rat.natCast_pos).2 (Nat.succ_pos stage))

theorem reciprocalStageRadius_le_one (stage : Nat) :
    reciprocalStageRadius stage <= 1 := by
  have hden : (1 : Rat) <= ((stage + 1 : Nat) : Rat) := by
    change ((1 : Nat) : Rat) <= ((stage + 1 : Nat) : Rat)
    exact (Rat.natCast_le_natCast).2
      (Nat.succ_le_succ (Nat.zero_le stage))
  have hdenPos : (0 : Rat) < ((stage + 1 : Nat) : Rat) := by
    exact (Rat.natCast_pos).2 (Nat.succ_pos stage)
  have hdenNe : (((stage + 1 : Nat) : Rat)) ≠ 0 := Rat.ne_of_gt hdenPos
  unfold reciprocalStageRadius
  apply Rat.le_of_mul_le_mul_right (c := ((stage + 1 : Nat) : Rat))
  · calc
      (1 / (((stage + 1 : Nat) : Rat))) * (((stage + 1 : Nat) : Rat)) = 1 := by
        rw [Rat.div_def]
        grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
      _ <= ((stage + 1 : Nat) : Rat) := hden
      _ = 1 * ((stage + 1 : Nat) : Rat) := by grind
  · exact hdenPos

/-- Equal mass at the two rational points `-1/(stage+1)` and
`1/(stage+1)`. -/
def symmetricTwoPointKernel (stage : Nat) : FiniteProbabilityKernel where
  samples :=
    [ { point := -reciprocalStageRadius stage, weight := 1 / 2 },
      { point := reciprocalStageRadius stage, weight := 1 / 2 } ]
  weights_nonnegative := by
    intro sample hsample
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hsample
    rcases hsample with hsample | hsample
    · rw [hsample]
      change (0 : Rat) <= 1 / 2
      decide +kernel
    · rw [hsample]
      change (0 : Rat) <= 1 / 2
      decide +kernel
  totalWeight_eq_one := by
    simp [WeightedPoint.totalWeight]
    decide +kernel

theorem symmetricTwoPointKernel_action
    (stage : Nat) (f : Rat -> Rat) :
    (symmetricTwoPointKernel stage).action f =
      (f (-reciprocalStageRadius stage) +
        f (reciprocalStageRadius stage)) / 2 := by
  unfold symmetricTwoPointKernel FiniteProbabilityKernel.action
  simp only [WeightedPoint.action]
  grind [Rat.div_def, Rat.mul_add, Rat.add_mul, Rat.mul_comm,
    Rat.mul_assoc]

theorem symmetricTwoPointKernel_support
    (stage : Nat) (sample : WeightedPoint)
    (hsample : sample ∈ (symmetricTwoPointKernel stage).samples) :
    qabs sample.point <= reciprocalStageRadius stage := by
  have hradius : 0 <= reciprocalStageRadius stage :=
    Rat.le_of_lt (reciprocalStageRadius_positive stage)
  simp only [symmetricTwoPointKernel, List.mem_cons,
    List.not_mem_nil, or_false] at hsample
  rcases hsample with hsample | hsample
  ·
    rw [hsample]
    rw [qabs_neg, qabs_eq_self_of_nonneg hradius]
    exact Rat.le_refl
  ·
    rw [hsample]
    rw [qabs_eq_self_of_nonneg hradius]
    exact Rat.le_refl

/-- A completely executable approximate identity with denominator-based
schedule.  It is a regression model for concentration estimates, not a claim
that these two weights are Gaussian quadrature. -/
def symmetricTwoPointApproximateIdentity : FiniteApproximateIdentity where
  kernel := symmetricTwoPointKernel
  radius := reciprocalStageRadius
  radius_nonnegative := fun stage =>
    Rat.le_of_lt (reciprocalStageRadius_positive stage)
  support_radius := symmetricTwoPointKernel_support
  schedule := fun requested => requested.den
  schedule_spec := by
    intro requested hrequested
    exact one_div_den_succ_le_of_pos hrequested

theorem symmetricTwoPointApproximateIdentity_action_rate
    (f : Rat -> Rat) (lipschitz requestedError : Rat)
    (lipschitz_positive : 0 < lipschitz)
    (requestedError_positive : 0 < requestedError)
    (lipschitz_at_zero : forall x : Rat,
      qabs (f x - f 0) <= lipschitz * qabs x) :
    qabs
      ((symmetricTwoPointKernel
        ((requestedError / lipschitz).den)).action f - f 0) <=
          requestedError := by
  exact symmetricTwoPointApproximateIdentity.action_rate
    f lipschitz requestedError lipschitz_positive requestedError_positive
    (fun sample _ => lipschitz_at_zero sample.point)

end ComputableAnalysis


