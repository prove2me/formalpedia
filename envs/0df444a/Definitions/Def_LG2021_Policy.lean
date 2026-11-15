-- Prove2me | Definitions.Def_LG2021_Policy
-- name    : LG2021_Policy
-- status  : Definition
-- author  : @sim2000dg
-- created : 2026-11-14T16:23:12.16907+00:00
-- url     : https://prove2.me/theorems/5b7d5fe7-c87c-4fa8-a222-b7e369d34015
-- title:
--   Stochastic convex-bandit policy and adaptive transcript objects
-- statement:
--   Concrete implementation and model objects used to formalize Algorithms 1 and 2 of Lattimore and György (COLT 2021). These include the configuration, query policy, Gaussian candidate and observation seeds, countable rational cut histories and ellipsoid frames, actual algorithm traces, adaptive transcript measures, truncated estimators, confidence-event predicates, and numerical budgets.
--
--   The policy depends on the known action set and numerical parameters; its observations determine subsequent queries. Radial guards ensure feasible query choices, and countable cut histories support measurable ellipsoid selection. The module includes the intrinsic typing, measurability, probability-law normalization, and measure-reparameterization proofs required to construct these objects.
--
--   The proposition-valued definitions specify the confidence conditions and regret guarantees used in theorem interfaces. They define these conditions; the statistical confidence and regret results are proved in separate theorem entries.
-- source:
--   Tor Lattimore and András György, Improved Regret for Zeroth-Order Stochastic Convex Bandits, Proceedings of the 34th Conference on Learning Theory (COLT 2021), Proceedings of Machine Learning Research 134:2938–2964, 2021, Algorithms 1 and 2 and Sections 5–7. Concrete implementation and adaptive observation-model definitions.

import Mathlib
import Definitions.Def_LG2021_RegretRate
import Definitions.Def_BilateralProfitMHR_ConvexBandit
import Definitions.Def_LG2021_CanonicalBandit
import Definitions.Def_LG2021_GaussianEstimators
import Definitions.Def_LG2021_GaussianSeparation
import Definitions.Def_ModernConvex_EllipsoidMethod_EllipsoidMethod
import Definitions.Def_ModernConvex_Ellipsoids_Ellipsoid
set_option autoImplicit false
/- LG2021AlgorithmOracle -/
section
/-!
The concrete estimators and stopping rule of Algorithm 1 in Tor Lattimore and
Andras Gyorgy, "Improved regret for zeroth-order stochastic convex bandits",
Proceedings of the 34th Conference on Learning Theory, PMLR 134, 2021.
The positivity test in `eligible` makes the stopping rule total: a zero
lower confidence bound cannot trigger stopping. The moment constants remain
explicit parameters for the formal concentration estimates.
-/
noncomputable section
namespace LG2021.Algorithm
open MeasureTheory Concentration
open scoped Classical
instance instMeasurableSpaceOptionFin_theorems (u : ℕ) : MeasurableSpace (Option (Fin u)) := ⊤
instance instMeasurableSingletonClassOptionFin_theorems (u : ℕ) : MeasurableSingletonClass (Option (Fin u)) := ⟨fun _ => trivial⟩
structure OracleConfig where
  horizon : ℕ
  radius : ℝ
  lambda : ℝ
  momentConstant : ℝ
  concentrationConstant : ℝ
def confidenceLog (p : OracleConfig) (u : ℕ) : ℝ :=
  Real.log (3 * (u : ℝ) * (p.horizon : ℝ) ^ 3)
def scalarEstimate {u : ℕ} (m : ℕ) (sums : Fin u → ℝ) (s : Fin u) : ℝ :=
  sums s / (m : ℝ)
def gradientEstimate {d u : ℕ} (m : ℕ) (sums : Fin u → Space d) (s : Fin u) : Space d :=
  (m : ℝ)⁻¹ • sums s
def confidenceRadius (p : OracleConfig) (u m : ℕ) : ℝ :=
  (p.momentConstant / p.lambda + 1) *
    Real.sqrt (confidenceLog p u / (p.concentrationConstant * (m : ℝ))) +
      1 / (8 * p.radius * (p.horizon : ℝ))
def lowerBound (p : OracleConfig) {u : ℕ} (m : ℕ) (sums : Fin u → ℝ) (s : Fin u) : ℝ :=
  max 0 (scalarEstimate m sums s - confidenceRadius p u m)
def eligible (p : OracleConfig) {u : ℕ} (m : ℕ) (sums : Fin u → ℝ) (s : Fin u) : Prop :=
  0 < lowerBound p m sums s ∧
    (4 * p.momentConstant * p.radius / lowerBound p m sums s) ^ 2 *
      confidenceLog p u / p.concentrationConstant ≤ (m : ℝ)
def firstEligible (p : OracleConfig) {u : ℕ} (indices : List (Fin u))
    (m : ℕ) (sums : Fin u → ℝ) : Option (Fin u) :=
  match indices with
  | [] => none
  | i :: rest => if eligible p m sums i then some i else firstEligible p rest m sums
def winner (p : OracleConfig) {u : ℕ} (m : ℕ) (sums : Fin u → ℝ) : Option (Fin u) :=
  firstEligible p (List.finRange u) m sums
private theorem measurable_likelihoodRatio {d : ℕ} (lambda : ℝ) :
    Measurable (fun w : Space d × Space d => likelihoodRatio lambda w.1 w.2) := by
  unfold likelihoodRatio
  fun_prop
private theorem measurable_truncation {d : ℕ} (lambda r : ℝ) :
    Measurable (fun w : Space d × Space d => truncation lambda r w.1 w.2) := by
  unfold truncation
  apply Measurable.ite _ measurable_const measurable_const
  exact (measurableSet_le (measurable_likelihoodRatio lambda) measurable_const).inter
    (measurableSet_le measurable_snd.norm measurable_const)
private theorem measurable_scalarCoefficient {d : ℕ} (lambda r : ℝ) :
    Measurable (fun w : Space d × Space d => scalarCoefficient lambda r w.1 w.2) := by
  exact ((measurable_const.sub measurable_const).add
    ((measurable_likelihoodRatio lambda).div_const lambda)).mul (measurable_truncation lambda r)
private theorem measurable_gradientCoefficient {d : ℕ} (lambda r : ℝ) :
    Measurable (fun w : Space d × Space d => gradientCoefficient lambda r w.1 w.2) := by
  exact (((measurable_likelihoodRatio lambda).mul (measurable_truncation lambda r)).div_const
    ((1 - lambda) ^ 2)).smul (by fun_prop)
private theorem measurable_scalarEstimate {u : ℕ} (s : Fin u) :
    Measurable (fun w : ℕ × (Fin u → ℝ) => scalarEstimate w.1 w.2 s) := by
  unfold scalarEstimate
  fun_prop
private theorem measurable_confidenceRadius (p : OracleConfig) (u : ℕ) :
    Measurable (fun m : ℕ => confidenceRadius p u m) := measurable_of_countable _
private theorem measurable_lowerBound (p : OracleConfig) {u : ℕ} (s : Fin u) :
    Measurable (fun w : ℕ × (Fin u → ℝ) => lowerBound p w.1 w.2 s) := by
  exact measurable_const.max ((measurable_scalarEstimate s).sub
    ((measurable_confidenceRadius p u).comp measurable_fst))
private theorem measurableSet_eligible (p : OracleConfig) {u : ℕ} (s : Fin u) :
    MeasurableSet {w : ℕ × (Fin u → ℝ) | eligible p w.1 w.2 s} := by
  have hleft : Measurable (fun w : ℕ × (Fin u → ℝ) =>
      (4 * p.momentConstant * p.radius / lowerBound p w.1 w.2 s) ^ 2 *
        confidenceLog p u / p.concentrationConstant) :=
    ((((measurable_const.div (measurable_lowerBound p s)).pow_const 2).mul_const
      (confidenceLog p u)).div_const p.concentrationConstant)
  have hright : Measurable (fun w : ℕ × (Fin u → ℝ) => (w.1 : ℝ)) := by fun_prop
  exact (measurableSet_lt measurable_const (measurable_lowerBound p s)).inter
    (measurableSet_le hleft hright)
private theorem measurable_firstEligible (p : OracleConfig) {u : ℕ} (indices : List (Fin u)) :
    Measurable (fun w : ℕ × (Fin u → ℝ) => firstEligible p indices w.1 w.2) := by
  induction indices with
  | nil => exact measurable_const
  | cons i rest ih => exact Measurable.ite (measurableSet_eligible p i) measurable_const ih
private theorem measurable_winner (p : OracleConfig) {u : ℕ} :
    Measurable (fun w : ℕ × (Fin u → ℝ) => winner p w.1 w.2) :=
  measurable_firstEligible p (List.finRange u)
end LG2021.Algorithm
end
end
/- LG2021AlgorithmGeometry -/
section
noncomputable section
namespace LG2021.Algorithm
open MeasureTheory Matrix
open scoped Classical
instance instMeasurableSpaceMatrixFinReal_theorems (d : ℕ) : MeasurableSpace (Matrix (Fin d) (Fin d) ℝ) :=
  inferInstanceAs (MeasurableSpace (Fin d → Fin d → ℝ))
instance instBorelSpaceMatrixFinReal_theorems (d : ℕ) : BorelSpace (Matrix (Fin d) (Fin d) ℝ) :=
  inferInstanceAs (BorelSpace (Fin d → Fin d → ℝ))
abbrev Frame (d : ℕ) := Matrix (Fin d) (Fin d) ℝ × Space d
abbrev Cut (d : ℕ) := Space d × ℝ
def matrixAction {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) (x : Space d) : Space d :=
  (EuclideanSpace.equiv (Fin d) ℝ).symm (M *ᵥ (EuclideanSpace.equiv (Fin d) ℝ) x)
def frameApply {d : ℕ} (F : Frame d) (x : Space d) : Space d := matrixAction F.1 x + F.2
def frameUnapply {d : ℕ} (F : Frame d) (x : Space d) : Space d :=
  matrixAction F.1⁻¹ (x - F.2)
def cutSet {d : ℕ} (cut : Cut d) : Set (Space d) := {x | inner ℝ cut.1 x ≤ cut.2}
def activeBody {d p : ℕ} (K : Set (Space d)) (cuts : Fin p → Cut d) : Set (Space d) :=
  K ∩ ⋂ i, cutSet (cuts i)
def cutFromEstimate {d : ℕ} (F : Frame d) (z v : Space d) : Cut d :=
  let a := matrixAction F.1⁻¹.transpose v
  (a, inner ℝ a (frameApply F z))
@[fun_prop] private theorem continuous_matrixAction {d : ℕ} :
    Continuous (fun w : Matrix (Fin d) (Fin d) ℝ × Space d => matrixAction w.1 w.2) := by
  unfold matrixAction
  fun_prop
@[fun_prop] private theorem measurable_matrixInverse {d : ℕ} :
    Measurable (fun M : Matrix (Fin d) (Fin d) ℝ => M⁻¹) := by
  simp_rw [Matrix.inv_def, Ring.inverse_eq_inv]
  exact (continuous_id.matrix_det.measurable.inv).smul continuous_id.matrix_adjugate.measurable
@[fun_prop] private theorem continuous_frameApply {d : ℕ} :
    Continuous (fun w : Frame d × Space d => frameApply w.1 w.2) := by
  unfold frameApply
  exact (continuous_matrixAction.comp (continuous_fst.fst.prodMk continuous_snd)).add
    continuous_fst.snd
@[fun_prop] private theorem measurable_cutFromEstimate {d : ℕ} :
    Measurable (fun w : Frame d × Space d × Space d => cutFromEstimate w.1 w.2.1 w.2.2) := by
  unfold cutFromEstimate
  have hi : Measurable (fun w : Frame d × Space d × Space d => w.1.1⁻¹) :=
    (measurable_matrixInverse (d := d)).comp measurable_fst.fst
  have ht : Measurable (fun M : Matrix (Fin d) (Fin d) ℝ => M.transpose) :=
    continuous_id.matrix_transpose.measurable
  have ha : Measurable (fun w : Frame d × Space d × Space d =>
      matrixAction w.1.1⁻¹.transpose w.2.2) := by
    exact (continuous_matrixAction (d := d)).measurable.comp
      ((ht.comp hi).prodMk measurable_snd.snd)
  apply ha.prodMk
  exact continuous_inner.measurable.comp (ha.prodMk
    (continuous_frameApply.measurable.comp (measurable_fst.prodMk measurable_snd.fst)))
end LG2021.Algorithm
end
end
/- LG2021AlgorithmQuantization -/
section
/-!
An explicit countable approximation of halfspace coefficients. This is an
additional algorithm completion, not a statement asserted in Lattimore–Gyorgy.
It permits measurable canonical ellipsoid choices on countable cut histories.
-/
noncomputable section
namespace LG2021.Algorithm
open MeasureTheory
open scoped Classical
abbrev CutCode (d : ℕ) := (Fin d → ℚ) × ℚ
def decodeCut {d : ℕ} (c : CutCode d) : Cut d :=
  ((EuclideanSpace.equiv (Fin d) ℝ).symm (fun i => (c.1 i : ℝ)), (c.2 : ℝ))
private theorem continuous_decodeCut {d : ℕ} : Continuous (decodeCut (d := d)) := by
  unfold decodeCut
  fun_prop
private theorem denseRange_decodeCut {d : ℕ} : DenseRange (decodeCut (d := d)) := by
  have hv : DenseRange (fun v : Fin d → ℚ =>
      (EuclideanSpace.equiv (Fin d) ℝ).symm (fun i => (v i : ℝ))) := by
    exact (EuclideanSpace.equiv (Fin d) ℝ).symm.surjective.denseRange.comp
      (DenseRange.piMap (fun _ : Fin d => (Rat.denseRange_cast : DenseRange ((↑) : ℚ → ℝ))))
      (EuclideanSpace.equiv (Fin d) ℝ).symm.continuous
  exact hv.prodMap Rat.denseRange_cast
def enumerateCuts (d : ℕ) : ℕ → CutCode d := Classical.choose (exists_surjective_nat (CutCode d))
private theorem enumerateCuts_surjective (d : ℕ) : Function.Surjective (enumerateCuts d) :=
  Classical.choose_spec (exists_surjective_nat (CutCode d))
private theorem denseRange_enumerateCuts (d : ℕ) : DenseRange (fun n => decodeCut (enumerateCuts d n)) :=
  denseRange_decodeCut.comp (enumerateCuts_surjective d).denseRange continuous_decodeCut
def positiveRadius (ε : ℝ) : ℝ := if 0 < ε then ε else 1
private theorem positiveRadius_pos (ε : ℝ) : 0 < positiveRadius ε := by
  unfold positiveRadius
  split_ifs with h
  · exact h
  · norm_num
private theorem measurable_positiveRadius : Measurable positiveRadius := by
  exact Measurable.ite (measurableSet_lt measurable_const measurable_id)
    measurable_id measurable_const
private theorem exists_close_cut {d : ℕ} (w : Cut d × ℝ) :
    ∃ k : ℕ, dist w.1 (decodeCut (enumerateCuts d k)) < positiveRadius w.2 :=
  (denseRange_enumerateCuts d).exists_dist_lt w.1 (positiveRadius_pos w.2)
def quantizeCut {d : ℕ} (target : Cut d) (ε : ℝ) : CutCode d :=
  enumerateCuts d (Nat.find (exists_close_cut (target, ε)))
private theorem measurable_quantizeCut {d : ℕ} :
    Measurable (fun w : Cut d × ℝ => quantizeCut w.1 w.2) := by
  apply (measurable_of_countable (enumerateCuts d)).comp
  apply measurable_find (exists_close_cut (d := d))
  intro k
  exact measurableSet_lt (measurable_fst.dist measurable_const)
    (measurable_positiveRadius.comp measurable_snd)
def cutValue {d : ℕ} (c : Cut d) (x : Space d) : ℝ := inner ℝ c.1 x - c.2
def inwardCut {d : ℕ} (c : Cut d) (θ : ℝ) : Cut d := (c.1, c.2 - θ / 8)
def roundedInwardCut {d : ℕ} (c : Cut d) (θ R : ℝ) : CutCode d :=
  quantizeCut (inwardCut c θ) (θ / (32 * (R + 1)))
private theorem measurable_roundedInwardCut {d : ℕ} (R : ℝ) :
    Measurable (fun w : Cut d × ℝ => roundedInwardCut w.1 w.2 R) := by
  have htarget : Measurable (fun w : Cut d × ℝ => inwardCut w.1 w.2) :=
    measurable_fst.fst.prodMk (measurable_fst.snd.sub (measurable_snd.div_const 8))
  exact measurable_quantizeCut.comp (htarget.prodMk
    (measurable_snd.div_const (32 * (R + 1))))
end LG2021.Algorithm
end
end
/- LG2021JohnHelpers -/
section
/-! Small internal adapters reused verbatim from the accepted John-ellipsoid
solution. Their explicit inclusion avoids relying on unexposed helper names in
an external canonical theorem module. The John theorem itself is imported and
reused by its canonical statement. -/
noncomputable section
namespace LG2021.JohnHelpers
open Matrix Finset MeasureTheory ModernConvex.Ellipsoids
open scoped ENNReal
end LG2021.JohnHelpers
end
end
/- LG2021Geometry -/
section
namespace LG2021
open Set ModernConvex.Ellipsoids
open Matrix
end LG2021
end
/- LG2021AlgorithmSelector -/
section
/-!
A canonical minimum enclosing ellipsoid is chosen for each finite rational cut
history. The history space is countable, so this choice is measurable without
an additional measurable-selection principle.
The geometric existence and rounding facts reuse the proved Loewner–Fritz John
theorem. The countable-history adapter is an additional algorithm completion.
-/
noncomputable section
namespace LG2021.Algorithm
open MeasureTheory Matrix ModernConvex.Ellipsoids
open scoped Classical
abbrev NativeFrame (d : ℕ) := Matrix (Fin d) (Fin d) ℝ × (Fin d → ℝ)
def OuterFrameSpec {d : ℕ} (S : Set (Fin d → ℝ)) (F : NativeFrame d) : Prop :=
  F.1.det ≠ 0 ∧ IsMinVolCircumscribed S (ellipsoid F.1 F.2)
def chosenOuterFrame {d : ℕ} (S : Set (Fin d → ℝ)) : NativeFrame d :=
  if h : ∃ F : NativeFrame d, OuterFrameSpec S F then Classical.choose h else (1, 0)
def codedBody {d p : ℕ} (K : Set (Space d)) (cuts : Fin p → CutCode d) : Set (Space d) :=
  activeBody K (fun i => decodeCut (cuts i))
def nativeCodedBody {d p : ℕ} (K : Set (Space d)) (cuts : Fin p → CutCode d) :
    Set (Fin d → ℝ) := (EuclideanSpace.equiv (Fin d) ℝ) '' codedBody K cuts
def canonicalOuterFrame {d p : ℕ} (K : Set (Space d)) (r : ℝ)
    (cuts : Fin p → CutCode d) : Frame d :=
  let F := chosenOuterFrame (nativeCodedBody K cuts)
  (r⁻¹ • F.1, (EuclideanSpace.equiv (Fin d) ℝ).symm F.2)
private theorem measurable_canonicalOuterFrame {d p : ℕ} (K : Set (Space d)) (r : ℝ) :
    Measurable (canonicalOuterFrame (p := p) K r) := measurable_of_countable _
end LG2021.Algorithm
end
end
/- LG2021AlgorithmState -/
section
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace LG2021.Algorithm
open MeasureTheory Concentration
open scoped Classical
/-- Cuts, current affine frame, current candidates, sample count, scalar sums,
and vector sums. A zero cut is appended when the current oracle continues. -/
abbrev State (d u p : ℕ) := (Fin p → CutCode d) × Frame d × (Fin u → Space d) ×
  ℕ × (Fin u → ℝ) × (Fin u → Space d)
def updatedScalars {d u p : ℕ} (cfg : OracleConfig) (st : State d u p)
    (x : Space d) (y y' : ℝ) : Fin u → ℝ :=
  fun s => st.2.2.2.2.1 s + y * scalarCoefficient cfg.lambda cfg.radius (st.2.2.1 s) x - y'
def updatedGradients {d u p : ℕ} (cfg : OracleConfig) (st : State d u p)
    (x : Space d) (y : ℝ) : Fin u → Space d :=
  fun s => st.2.2.2.2.2 s + y • gradientCoefficient cfg.lambda cfg.radius (st.2.2.1 s) x
def continueState {d u p : ℕ} (st : State d u p) (sums : Fin u → ℝ)
    (gradients : Fin u → Space d) : State d u (p + 1) :=
  (Fin.snoc st.1 0, st.2.1, st.2.2.1, st.2.2.2.1 + 1, sums, gradients)
def restartState {d u p : ℕ} (cfg : OracleConfig) (R : ℝ)
    (rounding : (Fin (p + 1) → CutCode d) → Frame d)
    (st : State d u p) (nextCandidates : Fin u → Space d)
    (sums : Fin u → ℝ) (gradients : Fin u → Space d) (s : Fin u) : State d u (p + 1) :=
  let v := gradientEstimate (st.2.2.2.1 + 1) gradients s
  let θ := lowerBound cfg (st.2.2.2.1 + 1) sums s
  let cuts := Fin.snoc st.1 (roundedInwardCut (cutFromEstimate st.2.1 (st.2.2.1 s) v) θ R)
  (cuts, rounding cuts, nextCandidates, 0, 0, 0)
/-- One completed pair of actual observations in Algorithms 1 and 2. The
rounding function is an explicit geometric input, whose canonical measurable
construction must be supplied separately before constructing the final policy. -/
def step {d u p : ℕ} (cfg : OracleConfig) (R : ℝ)
    (rounding : (Fin (p + 1) → CutCode d) → Frame d)
    (st : State d u p) (nextCandidates : Fin u → Space d)
    (x : Space d) (y y' : ℝ) : State d u (p + 1) :=
  let sums := updatedScalars cfg st x y y'
  let gradients := updatedGradients cfg st x y
  match winner cfg (st.2.2.2.1 + 1) sums with
  | none => continueState st sums gradients
  | some s => restartState cfg R rounding st nextCandidates sums gradients s
private theorem measurable_finSnoc {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {p : ℕ} {f : α → Fin p → β} {g : α → β} (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun a => (Fin.snoc (f a) (g a) : Fin (p + 1) → β)) := by
  apply measurable_pi_lambda
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp only [Fin.snoc_last, Fin.snoc_castSucc]
  · exact hg
  · exact (measurable_pi_apply j).comp hf
private theorem measurable_optionCases {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {u : ℕ} {choice : α → Option (Fin u)} {no : α → β} {yes : Fin u → α → β}
    (hc : Measurable choice) (hn : Measurable no) (hy : ∀ s, Measurable (yes s)) :
    Measurable (fun a => match choice a with | none => no a | some s => yes s a) := by
  have hm : Measurable (fun w : Option (Fin u) × α =>
      match w.1 with | none => no w.2 | some s => yes s w.2) := by
    apply measurable_from_prod_countable_right
    intro o
    cases o with
    | none => exact hn
    | some s => exact hy s
  exact hm.comp (hc.prodMk measurable_id)
private theorem measurable_updatedScalars {α : Type*} [MeasurableSpace α] {d u p : ℕ}
    (cfg : OracleConfig) {st : α → State d u p} {x : α → Space d} {y y' : α → ℝ}
    (hst : Measurable st) (hx : Measurable x) (hy : Measurable y) (hy' : Measurable y') :
    Measurable (fun a => updatedScalars cfg (st a) (x a) (y a) (y' a)) := by
  apply measurable_pi_lambda
  intro s
  exact (((measurable_pi_apply s).comp hst.snd.snd.snd.snd.fst).add
    (hy.mul ((measurable_scalarCoefficient cfg.lambda cfg.radius).comp
      (((measurable_pi_apply s).comp hst.snd.snd.fst).prodMk hx)))).sub hy'
private theorem measurable_updatedGradients {α : Type*} [MeasurableSpace α] {d u p : ℕ}
    (cfg : OracleConfig) {st : α → State d u p} {x : α → Space d} {y : α → ℝ}
    (hst : Measurable st) (hx : Measurable x) (hy : Measurable y) :
    Measurable (fun a => updatedGradients cfg (st a) (x a) (y a)) := by
  apply measurable_pi_lambda
  intro s
  have hz : Measurable (fun a => (st a).2.2.1 s) :=
    (measurable_pi_apply s).comp hst.snd.snd.fst
  have hc : Measurable (fun a => gradientCoefficient cfg.lambda cfg.radius
      ((st a).2.2.1 s) (x a)) := by
    simpa only [Function.comp_def] using
      (measurable_gradientCoefficient (d := d) cfg.lambda cfg.radius).comp (hz.prodMk hx)
  have hp : Measurable (fun a => (st a).2.2.2.2.2 s) :=
    (measurable_pi_apply s).comp hst.snd.snd.snd.snd.snd
  exact hp.add (hy.smul hc)
private theorem measurable_continueState {α : Type*} [MeasurableSpace α] {d u p : ℕ}
    {st : α → State d u p} {sums : α → Fin u → ℝ} {grads : α → Fin u → Space d}
    (hst : Measurable st) (hs : Measurable sums) (hg : Measurable grads) :
    Measurable (fun a => continueState (st a) (sums a) (grads a)) := by
  exact (measurable_finSnoc hst.fst measurable_const).prodMk
    (hst.snd.fst.prodMk (hst.snd.snd.fst.prodMk
      ((hst.snd.snd.snd.fst.add_const 1).prodMk (hs.prodMk hg))))
private theorem measurable_restartState {α : Type*} [MeasurableSpace α] {d u p : ℕ}
    (cfg : OracleConfig) (R : ℝ)
    (rounding : (Fin (p + 1) → CutCode d) → Frame d) (hr : Measurable rounding)
    {st : α → State d u p} {next : α → Fin u → Space d}
    {sums : α → Fin u → ℝ} {grads : α → Fin u → Space d}
    (hst : Measurable st) (hn : Measurable next) (hs : Measurable sums)
    (hg : Measurable grads) (s : Fin u) :
    Measurable (fun a => restartState cfg R rounding (st a) (next a) (sums a) (grads a) s) := by
  have hv : Measurable (fun a => gradientEstimate ((st a).2.2.2.1 + 1) (grads a) s) := by
    unfold gradientEstimate
    have hm : Measurable (fun a => (((st a).2.2.2.1 + 1 : ℕ) : ℝ)) :=
      (measurable_of_countable (fun m : ℕ => (m : ℝ))).comp (hst.snd.snd.snd.fst.add_const 1)
    exact hm.inv.smul
      ((measurable_pi_apply s).comp hg)
  have hc : Measurable (fun a => (Fin.snoc (st a).1
      (roundedInwardCut (cutFromEstimate (st a).2.1 ((st a).2.2.1 s)
        (gradientEstimate ((st a).2.2.2.1 + 1) (grads a) s))
          (lowerBound cfg ((st a).2.2.2.1 + 1) (sums a) s) R) : Fin (p + 1) → CutCode d)) := by
    have hz : Measurable (fun a => (st a).2.2.1 s) :=
      (measurable_pi_apply s).comp hst.snd.snd.fst
    have hw : Measurable (fun a => ((st a).2.1, (st a).2.2.1 s,
        gradientEstimate ((st a).2.2.2.1 + 1) (grads a) s)) :=
      hst.snd.fst.prodMk (hz.prodMk hv)
    have hcut := (measurable_cutFromEstimate (d := d)).comp hw
    have hlo := (measurable_lowerBound cfg s).comp ((hst.snd.snd.snd.fst.add_const 1).prodMk hs)
    have hrounded := (measurable_roundedInwardCut (d := d) R).comp (hcut.prodMk hlo)
    exact measurable_finSnoc hst.fst hrounded
  exact hc.prodMk ((hr.comp hc).prodMk (hn.prodMk
    (measurable_const.prodMk (measurable_const.prodMk measurable_const))))
private theorem measurable_step {α : Type*} [MeasurableSpace α] {d u p : ℕ}
    (cfg : OracleConfig) (R : ℝ)
    (rounding : (Fin (p + 1) → CutCode d) → Frame d) (hr : Measurable rounding)
    {st : α → State d u p} {next : α → Fin u → Space d}
    {x : α → Space d} {y y' : α → ℝ}
    (hst : Measurable st) (hn : Measurable next) (hx : Measurable x)
    (hy : Measurable y) (hy' : Measurable y') :
    Measurable (fun a => step cfg R rounding (st a) (next a) (x a) (y a) (y' a)) := by
  have hs := measurable_updatedScalars cfg hst hx hy hy'
  have hg := measurable_updatedGradients cfg hst hx hy
  exact measurable_optionCases
    ((measurable_winner cfg).comp ((hst.snd.snd.snd.fst.add_const 1).prodMk hs))
    (measurable_continueState hst hs hg)
    (fun s => measurable_restartState cfg R rounding hr hst hn hs hg s)
end LG2021.Algorithm
end
end
/- CorollaryTransport -/
section
noncomputable section
namespace BilateralProfitMHR.CorollaryTransport
open MeasureTheory
open scoped ENNReal
end BilateralProfitMHR.CorollaryTransport
end
end
/- LG2021GaussianGeometrySphere -/
section
noncomputable section
namespace LG2021
open MeasureTheory ProbabilityTheory
private theorem measurable_gaussian_normalize (d : ℕ) (R : ℝ) :
    Measurable (fun x : Space d => (R / ‖x‖) • x) := by fun_prop
instance sphereMeasure_probability (d : ℕ) (R : ℝ) :
    IsProbabilityMeasure (sphereMeasure d R) := by
  unfold sphereMeasure
  exact Measure.isProbabilityMeasure_map (measurable_gaussian_normalize d R).aemeasurable
end LG2021
end
end
/- Normalized Gaussian norm support -/
section
noncomputable section
namespace LG2021
open MeasureTheory ProbabilityTheory
end LG2021
end
end
/- LG2021AlgorithmPolicy -/
section
noncomputable section
namespace LG2021.Algorithm
open MeasureTheory BilateralProfitMHR
open scoped Classical
/-- Independent candidate blocks and Gaussian query vectors for all possible
stages before the fixed horizon. Beyond the horizon the seed is extended by zero. -/
abbrev Seed (d u n : ℕ) := (Fin (n + 1) → Fin u → Space d) × (Fin (n + 1) → Space d)
def seedCandidates {d u n : ℕ} (seed : Seed d u n) (p : ℕ) : Fin u → Space d :=
  if h : p < n + 1 then seed.1 ⟨p, h⟩ else 0
def seedGaussian {d u n : ℕ} (seed : Seed d u n) (p : ℕ) : Space d :=
  if h : p < n + 1 then seed.2 ⟨p, h⟩ else 0
private theorem measurable_seedCandidates {d u n : ℕ} (p : ℕ) :
    Measurable (fun seed : Seed d u n => seedCandidates seed p) := by
  unfold seedCandidates
  split_ifs <;> fun_prop
private theorem measurable_seedGaussian {d u n : ℕ} (p : ℕ) :
    Measurable (fun seed : Seed d u n => seedGaussian seed p) := by
  unfold seedGaussian
  split_ifs <;> fun_prop
def initialState {d u : ℕ} (cfg : OracleConfig) (K : Set (Space d))
    (seed : Seed d u cfg.horizon) : State d u 0 :=
  (Fin.elim0, canonicalOuterFrame K cfg.radius Fin.elim0,
    seedCandidates seed 0, 0, 0, 0)
/-- The actual paired-observation recursion: each scalar/vector sum is updated
with the Gaussian query observation and the following center observation. -/
def runState {d u : ℕ} (cfg : OracleConfig) (K : Set (Space d)) (R : ℝ)
    (seed : Seed d u cfg.horizon) : (p : ℕ) → (Fin p → ℝ × ℝ) → State d u p
  | 0, _ => initialState cfg K seed
  | p + 1, ys =>
      let st := runState cfg K R seed p (fun i => ys i.castSucc)
      step cfg R (canonicalOuterFrame K cfg.radius) st
        (seedCandidates seed (p + 1)) (seedGaussian seed p)
        (ys (Fin.last p)).1 (ys (Fin.last p)).2
private theorem measurable_initialState {d u : ℕ} (cfg : OracleConfig) (K : Set (Space d)) :
    Measurable (initialState (u := u) cfg K) := by
  exact measurable_const.prodMk (measurable_const.prodMk
    ((measurable_seedCandidates 0).prodMk
      (measurable_const.prodMk (measurable_const.prodMk measurable_const))))
private theorem measurable_runState {d u : ℕ} (cfg : OracleConfig) (K : Set (Space d)) (R : ℝ)
    (p : ℕ) : Measurable (fun w : Seed d u cfg.horizon × (Fin p → ℝ × ℝ) =>
      runState cfg K R w.1 p w.2) := by
  induction p with
  | zero => exact (measurable_initialState cfg K).comp measurable_fst
  | succ p ih =>
      have hs : Measurable (fun w : Seed d u cfg.horizon × (Fin (p + 1) → ℝ × ℝ) =>
          runState cfg K R w.1 p (fun i => w.2 i.castSucc)) := by
        exact ih.comp (measurable_fst.prodMk (by fun_prop))
      exact measurable_step cfg R (canonicalOuterFrame K cfg.radius)
        (measurable_canonicalOuterFrame K cfg.radius) hs
        ((measurable_seedCandidates (p + 1)).comp measurable_fst)
        ((measurable_seedGaussian p).comp measurable_fst)
        ((measurable_pi_apply (Fin.last p)).comp measurable_snd).fst
        ((measurable_pi_apply (Fin.last p)).comp measurable_snd).snd
def pairedHistory {τ : ℕ} (ys : Fin τ → ℝ) : Fin (τ / 2) → ℝ × ℝ :=
  fun i => (ys ⟨2 * i.val, by have hi := i.isLt; omega⟩,
    ys ⟨2 * i.val + 1, by have hi := i.isLt; omega⟩)
private theorem measurable_pairedHistory (τ : ℕ) : Measurable (pairedHistory (τ := τ)) := by
  apply measurable_pi_lambda
  intro i
  exact (measurable_pi_apply _).prodMk (measurable_pi_apply _)
def proposedQuery {d u : ℕ} (cfg : OracleConfig) (K : Set (Space d)) (R : ℝ)
    (τ : ℕ) (seed : Seed d u cfg.horizon) (ys : Fin τ → ℝ) : Space d :=
  let st := runState cfg K R seed (τ / 2) (pairedHistory ys)
  let x := seedGaussian seed (τ / 2)
  if τ % 2 = 0 ∧ ‖x‖ ≤ cfg.radius / (d : ℝ)
    then frameApply st.2.1 x else frameApply st.2.1 0
private theorem measurable_proposedQuery {d u : ℕ} (cfg : OracleConfig) (K : Set (Space d)) (R : ℝ)
    (τ : ℕ) : Measurable (fun w : Seed d u cfg.horizon × (Fin τ → ℝ) =>
      proposedQuery cfg K R τ w.1 w.2) := by
  have hs : Measurable (fun w : Seed d u cfg.horizon × (Fin τ → ℝ) =>
      runState cfg K R w.1 (τ / 2) (pairedHistory w.2)) :=
    (measurable_runState cfg K R (τ / 2)).comp
      (measurable_fst.prodMk ((measurable_pairedHistory τ).comp measurable_snd))
  have hx : Measurable (fun w : Seed d u cfg.horizon × (Fin τ → ℝ) =>
      seedGaussian w.1 (τ / 2)) := (measurable_seedGaussian (τ / 2)).comp measurable_fst
  have hgood : MeasurableSet {w : Seed d u cfg.horizon × (Fin τ → ℝ) |
      τ % 2 = 0 ∧ ‖seedGaussian w.1 (τ / 2)‖ ≤ cfg.radius / (d : ℝ)} := by
    by_cases ht : τ % 2 = 0
    · simpa only [ht, true_and] using measurableSet_le hx.norm measurable_const
    · simp [ht]
  have hy : Measurable (fun w : Seed d u cfg.horizon × (Fin τ → ℝ) =>
      frameApply (runState cfg K R w.1 (τ / 2) (pairedHistory w.2)).2.1
        (seedGaussian w.1 (τ / 2))) := by
    simpa only [Function.comp_def] using
      (continuous_frameApply (d := d)).measurable.comp (hs.snd.fst.prodMk hx)
  have hn : Measurable (fun w : Seed d u cfg.horizon × (Fin τ → ℝ) =>
      frameApply (runState cfg K R w.1 (τ / 2) (pairedHistory w.2)).2.1 0) := by
    simpa only [Function.comp_def] using
      (continuous_frameApply (d := d)).measurable.comp
        (hs.snd.fst.prodMk (measurable_const (a := (0 : Space d))))
  exact Measurable.ite hgood hy hn
/-- A fully defined legal measurable policy, selected from the known body and
parameters before the loss or observation kernel. Invalid states and illegal
proposals use the fixed legal anchor; truncated Gaussian proposals use the center. -/
def policy {d u : ℕ} (cfg : OracleConfig) (K : Set (Space d)) (hK : MeasurableSet K)
    (R : ℝ) (anchor : Space d) : QueryAlg (Space d) (Seed d u cfg.horizon) where
  query τ seed ys :=
    let x := proposedQuery cfg K R τ seed ys
    if x ∈ K then x else anchor
  query_measurable τ := Measurable.ite
    (hK.preimage (measurable_proposedQuery cfg K R τ))
    (measurable_proposedQuery cfg K R τ) measurable_const
def seedMeasure (d u : ℕ) (cfg : OracleConfig) : Measure (Seed d u cfg.horizon) :=
  (Measure.pi (fun _ : Fin (cfg.horizon + 1) =>
    Measure.pi (fun _ : Fin u => sphereMeasure d (cfg.radius / (2 * (d : ℝ)))))).prod
      (Measure.pi (fun _ : Fin (cfg.horizon + 1) => gaussian d))
instance seedMeasure_probability (d u : ℕ) (cfg : OracleConfig) :
    IsProbabilityMeasure (seedMeasure d u cfg) := by
  unfold seedMeasure
  infer_instance
end LG2021.Algorithm
end
end
/- CorollaryNormalization -/
section
noncomputable section
namespace BilateralProfitMHR.CorollaryTransport
open MeasureTheory
open scoped ENNReal
end BilateralProfitMHR.CorollaryTransport
end
end
/- LG2021Process -/
section
namespace LG2021
open MeasureTheory ProbabilityTheory BilateralProfitMHR
open scoped ENNReal
private theorem pastQueries_measurable {X Ω : Type} [MeasurableSpace X] [MeasurableSpace Ω]
    (A : QueryAlg X Ω) (τ : ℕ) :
    Measurable (fun z : Ω × (Fin τ → ℝ) => A.pastQueries z.1 z.2) := by
  apply measurable_pi_lambda
  intro i
  exact (A.query_measurable i).comp
    (show Measurable (fun z : Ω × (Fin τ → ℝ) =>
      (z.1, fun j => z.2 (Fin.castLE i.isLt.le j))) from by fun_prop)
/-- The actual next-observation kernel after the policy's query has been inserted. -/
def observationKernel {X Ω : Type} [MeasurableSpace X] [MeasurableSpace Ω]
    (A : QueryAlg X Ω) (ν : ObsKernel X) (hν : ν.IsMeasurable) (τ : ℕ) :
    Kernel (Ω × (Fin τ → ℝ)) ℝ where
  toFun z := ν τ (A.pastQueries z.1 z.2) z.2 (A.query τ z.1 z.2)
  measurable' := (hν τ).comp ((pastQueries_measurable A τ).prodMk
    (measurable_snd.prodMk (A.query_measurable τ)))
private theorem measurable_history_snoc {Ω : Type} [MeasurableSpace Ω] (τ : ℕ) :
    Measurable (fun z : (Ω × (Fin τ → ℝ)) × ℝ =>
      (z.1.1, (Fin.snoc z.1.2 z.2 : Fin (τ + 1) → ℝ))) := by
  apply Measurable.prodMk (by fun_prop)
  apply measurable_pi_lambda
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp only [Fin.snoc_last, Fin.snoc_castSucc]
  · fun_prop
  · fun_prop
end LG2021
end
/- LG2021Concentration -/
section
set_option autoImplicit false
namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
end LG2021.Concentration
end
/- LG2021ConcentrationProducts -/
section
set_option autoImplicit false
namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory
end LG2021.Concentration
end
/- LG2021ConcentrationCentering -/
section
set_option autoImplicit false
namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory
end LG2021.Concentration
end
/- LG2021ConcentrationEstimators -/
section
set_option autoImplicit false
namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
end LG2021.Concentration
end
/- LG2021ConcentrationObservation -/
section
set_option autoImplicit false
namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory
end LG2021.Concentration
end
/- LG2021ConcentrationKernelMoments -/
section
set_option autoImplicit false
namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory
end LG2021.Concentration
end
/- LG2021GaussianMoments -/
section
noncomputable section
namespace LG2021
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace ENNReal NNReal
end LG2021
end
end
/- LG2021ConcentrationEstimatorMoments -/
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
end LG2021.Concentration
end
/- LG2021ConcentrationParameters -/
section
set_option autoImplicit false
namespace LG2021.Concentration
end LG2021.Concentration
end
/- LG2021ConcentrationFinite -/
section
set_option autoImplicit false
namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory
open scoped NNReal
end LG2021.Concentration
end
/- LG2021ConcentrationTruncation -/
section
set_option autoImplicit false
namespace LG2021.Concentration
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory
end LG2021.Concentration
end
/- LG2021ConcentrationGaussianTails -/
section
set_option autoImplicit false
namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal
end LG2021.Concentration
end
/- LG2021ConcentrationParameterTails -/
section
set_option autoImplicit false
namespace LG2021.Concentration
end LG2021.Concentration
end
/- LG2021GaussianGeometrySurrogate -/
section
noncomputable section
namespace LG2021
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
end LG2021
end
end
/- LG2021ConcentrationEnvelopes -/
section
set_option autoImplicit false
namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
end LG2021.Concentration
end
/- LG2021ConcentrationBias -/
section
set_option autoImplicit false
namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory
end LG2021.Concentration
end
/- LG2021GaussianGeometryTranslation -/
section
noncomputable section
namespace LG2021.GaussianTranslation
universe uX uY uι
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
end LG2021.GaussianTranslation
namespace LG2021
open MeasureTheory ProbabilityTheory
end LG2021
end
end
/- LG2021GaussianGeometryDensity -/
section
noncomputable section
namespace LG2021
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
end LG2021
end
end
/- LG2021GaussianGeometryAffine -/
section
noncomputable section
namespace LG2021
open MeasureTheory ProbabilityTheory
end LG2021
end
end
/- LG2021GaussianGeometryChangeOfMeasure -/
section
noncomputable section
namespace LG2021
open MeasureTheory ProbabilityTheory
end LG2021
end
end
/- LG2021GaussianGeometryMollification -/
section
noncomputable section
namespace LG2021
open MeasureTheory ProbabilityTheory Filter Topology
open scoped RealInnerProductSpace
/-- Gaussian regularization of an actual function on Euclidean space. -/
def gaussianMollify {d : ℕ} (epsilon : ℝ) (f : Space d → ℝ) (z : Space d) : ℝ :=
  ∫ x, f (z + epsilon • x) ∂gaussian d
end LG2021
end
end
/- LG2021GaussianGeometrySmoothingReuse -/
section
noncomputable section
namespace LG2021.ReusedSmoothing.RGF6
open MeasureTheory ProbabilityTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
end LG2021.ReusedSmoothing.RGF6
namespace LG2021
open MeasureTheory ProbabilityTheory
end LG2021
end
end
/- LG2021GaussianGeometryIntegrability -/
section
noncomputable section
namespace LG2021
open MeasureTheory ProbabilityTheory
end LG2021
end
end
/- LG2021GaussianGeometryGradient -/
section
noncomputable section
namespace LG2021
open MeasureTheory ProbabilityTheory
end LG2021
end
end
/- LG2021ConcentrationSurrogateBias -/
section
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory
end LG2021.Concentration
end
/- LG2021ConcentrationLemma4 -/
section
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory
end LG2021.Concentration
end
/- LG2021ConcentrationConditional -/
section
set_option autoImplicit false
namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory
end LG2021.Concentration
end
/- LG2021ConcentrationOracleMoments -/
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory
end LG2021.Concentration
end
/- LG2021ConcentrationOracleGradient -/
section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory
end LG2021.Concentration
end
/- LG2021ConcentrationPathLaw -/
section
noncomputable section
namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory BilateralProfitMHR
open scoped ENNReal
/-- The actual finite observation history law, retaining the original private seed.
Fresh-coordinate concentration requires a smaller revealed-history sigma algebra. -/
def historyMeasure {X Ω : Type} [MeasurableSpace X] [MeasurableSpace Ω]
    (A : QueryAlg X Ω) (P : Measure Ω) (ν : ObsKernel X) (hνm : ν.IsMeasurable) :
    (τ : ℕ) → Measure (Ω × (Fin τ → ℝ))
  | 0 => P.map (fun ω => (ω, Fin.elim0))
  | τ + 1 => ((historyMeasure A P ν hνm τ) ⊗ₘ observationKernel A ν hνm τ).map
      (fun z => (z.1.1, Fin.snoc z.1.2 z.2))
/-- The realized sum of query costs on a finite observation path. -/
def pathCost {X Ω : Type} [MeasurableSpace X] [MeasurableSpace Ω]
    (A : QueryAlg X Ω) (g : X → ℝ≥0∞) {τ : ℕ} (w : Ω × (Fin τ → ℝ)) : ℝ≥0∞ :=
  ∑ i : Fin τ, g (A.pastQueries w.1 w.2 i)
end LG2021.Concentration
end
end
/- LG2021ConcentrationFreshSeed -/
section
noncomputable section
namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory BilateralProfitMHR
open scoped ENNReal
/-- Adjoin an independent seed component which the policy has not used. -/
def ignoreSeedRight {X Ω : Type} [MeasurableSpace X] [MeasurableSpace Ω]
    (B : Type) [MeasurableSpace B] (A : QueryAlg X Ω) : QueryAlg X (Ω × B) where
  query τ w ys := A.query τ w.1 ys
  query_measurable τ := (A.query_measurable τ).comp
    (f := fun w : (Ω × B) × (Fin τ → ℝ) => (w.1.1, w.2))
    (measurable_fst.fst.prodMk measurable_snd)
/-- Measurable reparameterization of the learner's private seed. -/
def reparametrizeSeed {X Ω Ω' : Type} [MeasurableSpace X] [MeasurableSpace Ω]
    [MeasurableSpace Ω'] (A : QueryAlg X Ω) (f : Ω' → Ω) (hf : Measurable f) :
    QueryAlg X Ω' where
  query τ ω ys := A.query τ (f ω) ys
  query_measurable τ := (A.query_measurable τ).comp
    (f := fun w : Ω' × (Fin τ → ℝ) => (f w.1, w.2))
    ((hf.comp measurable_fst).prodMk measurable_snd)
/-- Freeze one unrevealed private coordinate at a fixed value. -/
def freezeCoordinatePolicy {X Ω W B : Type} [MeasurableSpace X] [MeasurableSpace Ω]
    [MeasurableSpace W] [MeasurableSpace B] (A : QueryAlg X Ω)
    (encode : W × B → Ω) (he : Measurable encode) (b0 : B) : QueryAlg X W :=
  reparametrizeSeed A (fun w => encode (w, b0)) (he.comp (measurable_id.prodMk measurable_const))
end LG2021.Concentration
end
end
/- LG2021ConcentrationNoAnticipation -/
section
noncomputable section
namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory BilateralProfitMHR Algorithm
open scoped Classical
end LG2021.Concentration
end
end
/- LG2021ConcentrationSeedCoordinates -/
section
noncomputable section
namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory BilateralProfitMHR Algorithm
open scoped ENNReal
/-- All private coordinates other than one Gaussian vector. -/
abbrev GaussianRemainder (d u n : ℕ) :=
  (Fin (n + 1) → Fin u → Space d) × (Fin n → Space d)
def gaussianRemainderMeasure (d u : ℕ) (cfg : OracleConfig) :
    Measure (GaussianRemainder d u cfg.horizon) :=
  (Measure.pi (fun _ : Fin (cfg.horizon + 1) =>
    Measure.pi (fun _ : Fin u => sphereMeasure d (cfg.radius / (2 * (d : ℝ)))))).prod
      (Measure.pi (fun _ : Fin cfg.horizon => gaussian d))
instance gaussianRemainderMeasure_probability (d u : ℕ) (cfg : OracleConfig) :
    IsProbabilityMeasure (gaussianRemainderMeasure d u cfg) := by
  unfold gaussianRemainderMeasure
  infer_instance
/-- Insert the fresh Gaussian coordinate into the original finite seed. -/
def insertGaussianSeed {d u n : ℕ} (i : Fin (n + 1))
    (w : GaussianRemainder d u n × Space d) : Seed d u n :=
  (w.1.1, Fin.insertNth i w.2 w.1.2)
/-- The Gaussian coordinate extraction preserves the exact original seed probability law. -/
private theorem insertGaussianSeed_measurePreserving {d u : ℕ} (cfg : OracleConfig)
    (i : Fin (cfg.horizon + 1)) :
    MeasurePreserving (insertGaussianSeed (d := d) (u := u) i)
      ((gaussianRemainderMeasure d u cfg).prod (gaussian d)) (seedMeasure d u cfg) := by
  let μC := Measure.pi (fun _ : Fin (cfg.horizon + 1) =>
    Measure.pi (fun _ : Fin u => sphereMeasure d (cfg.radius / (2 * (d : ℝ)))))
  let μG := Measure.pi (fun _ : Fin cfg.horizon => gaussian d)
  have h1 := measurePreserving_prodAssoc μC μG (gaussian d)
  have h2 := (MeasurePreserving.id μC).prod
    (Measure.measurePreserving_swap (μ := μG) (ν := gaussian d))
  have h3 := (MeasurePreserving.id μC).prod
    (measurePreserving_piFinSuccAbove (fun _ : Fin (cfg.horizon + 1) => gaussian d) i).symm
  convert h3.comp (h2.comp h1) using 1 <;> rfl
private theorem measurable_insertGaussianSeed {d u : ℕ} (cfg : OracleConfig)
    (i : Fin (cfg.horizon + 1)) : Measurable (insertGaussianSeed (d := d) (u := u) i) :=
  (insertGaussianSeed_measurePreserving cfg i).measurable
end LG2021.Concentration
end
end
/- LG2021ConcentrationPairPath -/
section
noncomputable section
namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory BilateralProfitMHR
open scoped ENNReal
def firstHistoryMap {Ω W B : Type} (encode : W × B → Ω) {T : ℕ}
    (w : W × (Fin T → ℝ)) (x : B) : Ω × (Fin T → ℝ) := (encode (w.1, x), w.2)
private theorem measurable_firstHistoryMap {Ω W B : Type} [MeasurableSpace Ω] [MeasurableSpace W]
    [MeasurableSpace B] (encode : W × B → Ω) (he : Measurable encode) {T : ℕ}
    (w : W × (Fin T → ℝ)) : Measurable (firstHistoryMap encode w) :=
  (he.comp (measurable_const.prodMk measurable_id)).prodMk measurable_const
def secondHistoryMap {Ω W B : Type} (encode : W × B → Ω) {T : ℕ}
    (w : W × (Fin T → ℝ)) (p : B × ℝ) : Ω × (Fin (T + 1) → ℝ) :=
  (encode (w.1, p.1), Fin.snoc w.2 p.2)
private theorem measurable_secondHistoryMap {Ω W B : Type} [MeasurableSpace Ω] [MeasurableSpace W]
    [MeasurableSpace B] (encode : W × B → Ω) (he : Measurable encode) {T : ℕ}
    (w : W × (Fin T → ℝ)) : Measurable (secondHistoryMap encode w) :=
  (measurable_history_snoc T).comp
    (((measurable_firstHistoryMap encode he w).comp measurable_fst).prodMk measurable_snd)
def pairHistoryMap {Ω W B : Type} (encode : W × B → Ω) {T : ℕ}
    (w : W × (Fin T → ℝ)) (p : (B × ℝ) × ℝ) : Ω × (Fin (T + 2) → ℝ) :=
  (encode (w.1, p.1.1), Fin.snoc (Fin.snoc w.2 p.1.2) p.2)
/-- First actual observation after revealing a fresh private coordinate. -/
def coordinateFirstKernel {X Ω W B : Type} [MeasurableSpace X] [MeasurableSpace Ω]
    [MeasurableSpace W] [MeasurableSpace B] (A : QueryAlg X Ω)
    (ν : ObsKernel X) (hνm : ν.IsMeasurable) (encode : W × B → Ω) (he : Measurable encode)
    {T : ℕ} (w : W × (Fin T → ℝ)) : Kernel B ℝ :=
  (observationKernel A ν hνm T).comap (firstHistoryMap encode w)
    (measurable_firstHistoryMap encode he w)
/-- The second actual observation kernel may depend on both the fresh coordinate and first observation. -/
def coordinateSecondKernel {X Ω W B : Type} [MeasurableSpace X] [MeasurableSpace Ω]
    [MeasurableSpace W] [MeasurableSpace B] (A : QueryAlg X Ω)
    (ν : ObsKernel X) (hνm : ν.IsMeasurable) (encode : W × B → Ω) (he : Measurable encode)
    {T : ℕ} (w : W × (Fin T → ℝ)) : Kernel (B × ℝ) ℝ :=
  (observationKernel A ν hνm (T + 1)).comap (secondHistoryMap encode w)
    (measurable_secondHistoryMap encode he w)
/-- The law of one actual sequential observation pair, conditional on the previously revealed history. -/
def coordinatePairMeasure {X Ω W B : Type} [MeasurableSpace X] [MeasurableSpace Ω]
    [MeasurableSpace W] [MeasurableSpace B] (A : QueryAlg X Ω) (Q : Measure B)
    (ν : ObsKernel X) (hνm : ν.IsMeasurable) (encode : W × B → Ω) (he : Measurable encode)
    {T : ℕ} (w : W × (Fin T → ℝ)) : Measure ((B × ℝ) × ℝ) :=
  (Q ⊗ₘ coordinateFirstKernel A ν hνm encode he w) ⊗ₘ coordinateSecondKernel A ν hνm encode he w
end LG2021.Concentration
end
end
/- LG2021ConcentrationPairKernel -/
section
noncomputable section
namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory BilateralProfitMHR
private theorem measurable_firstHistoryMap_joint {Ω W B : Type} [MeasurableSpace Ω] [MeasurableSpace W]
    [MeasurableSpace B] (encode : W × B → Ω) (he : Measurable encode) (T : ℕ) :
    Measurable (fun p : (W × (Fin T → ℝ)) × B => firstHistoryMap encode p.1 p.2) :=
  (he.comp (measurable_fst.fst.prodMk measurable_snd)).prodMk measurable_fst.snd
private theorem measurable_secondHistoryMap_joint {Ω W B : Type} [MeasurableSpace Ω] [MeasurableSpace W]
    [MeasurableSpace B] (encode : W × B → Ω) (he : Measurable encode) (T : ℕ) :
    Measurable (fun p : (W × (Fin T → ℝ)) × (B × ℝ) => secondHistoryMap encode p.1 p.2) :=
  (measurable_history_snoc T).comp
    (((measurable_firstHistoryMap_joint encode he T).comp
      (measurable_fst.prodMk measurable_snd.fst)).prodMk measurable_snd.snd)
def firstObservationKernel {X Ω W B : Type} [MeasurableSpace X] [MeasurableSpace Ω]
    [MeasurableSpace W] [MeasurableSpace B] (A : QueryAlg X Ω)
    (ν : ObsKernel X) (hνm : ν.IsMeasurable) (encode : W × B → Ω) (he : Measurable encode)
    (T : ℕ) : Kernel ((W × (Fin T → ℝ)) × B) ℝ :=
  (observationKernel A ν hνm T).comap (fun p => firstHistoryMap encode p.1 p.2)
    (measurable_firstHistoryMap_joint encode he T)
def secondObservationKernel {X Ω W B : Type} [MeasurableSpace X] [MeasurableSpace Ω]
    [MeasurableSpace W] [MeasurableSpace B] (A : QueryAlg X Ω)
    (ν : ObsKernel X) (hνm : ν.IsMeasurable) (encode : W × B → Ω) (he : Measurable encode)
    (T : ℕ) : Kernel ((W × (Fin T → ℝ)) × (B × ℝ)) ℝ :=
  (observationKernel A ν hνm (T + 1)).comap (fun p => secondHistoryMap encode p.1 p.2)
    (measurable_secondHistoryMap_joint encode he T)
def coordinateFirstPairKernel {X Ω W B : Type} [MeasurableSpace X] [MeasurableSpace Ω]
    [MeasurableSpace W] [MeasurableSpace B] (A : QueryAlg X Ω) (Q : Measure B)
    (ν : ObsKernel X) (hνm : ν.IsMeasurable) (encode : W × B → Ω) (he : Measurable encode)
    (T : ℕ) : Kernel (W × (Fin T → ℝ)) (B × ℝ) :=
  Kernel.const _ Q ⊗ₖ firstObservationKernel A ν hνm encode he T
def coordinatePairKernel {X Ω W B : Type} [MeasurableSpace X] [MeasurableSpace Ω]
    [MeasurableSpace W] [MeasurableSpace B] (A : QueryAlg X Ω) (Q : Measure B)
    (ν : ObsKernel X) (hνm : ν.IsMeasurable) (encode : W × B → Ω) (he : Measurable encode)
    (T : ℕ) : Kernel (W × (Fin T → ℝ)) ((B × ℝ) × ℝ) :=
  coordinateFirstPairKernel A Q ν hνm encode he T ⊗ₖ secondObservationKernel A ν hνm encode he T
end LG2021.Concentration
end
end
/- LG2021ConcentrationObservationPath -/
section
noncomputable section
namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory BilateralProfitMHR Algorithm
open scoped ENNReal Classical
end LG2021.Concentration
end
end
/- LG2021ConcentrationPredictableMeans -/
section
noncomputable section
namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory BilateralProfitMHR Algorithm
/-- The predictable scalar center is defined by the actual first-observation and center kernels. -/
def scalarPredictableMean {X Ω W : Type} [MeasurableSpace X] [MeasurableSpace Ω]
    [MeasurableSpace W] {d : ℕ} (A : QueryAlg X Ω)
    (ν : ObsKernel X) (hνm : ν.IsMeasurable) (encode : W × Space d → Ω) (he : Measurable encode)
    (lambda r : ℝ) (z : Space d) {T : ℕ} (w : W × (Fin T → ℝ)) : ℝ :=
  (∫ p : Space d × ℝ, p.2 * scalarCoefficient lambda r z p.1
    ∂coordinateFirstPairKernel A (gaussian d) ν hνm encode he T w) -
  ∫ y : ℝ, y ∂secondObservationKernel A ν hνm encode he T (w, (0, 0))
/-- The directional center is the actual predictable expectation of the first-observation estimate. -/
def gradientPredictableMean {X Ω W : Type} [MeasurableSpace X] [MeasurableSpace Ω]
    [MeasurableSpace W] {d : ℕ} (A : QueryAlg X Ω)
    (ν : ObsKernel X) (hνm : ν.IsMeasurable) (encode : W × Space d → Ω) (he : Measurable encode)
    (lambda r : ℝ) (z η : Space d) {T : ℕ} (w : W × (Fin T → ℝ)) : ℝ :=
  ∫ p : Space d × ℝ, p.2 * directionalGradientCoefficient lambda r z η p.1
    ∂coordinateFirstPairKernel A (gaussian d) ν hνm encode he T w
end LG2021.Concentration
namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory BilateralProfitMHR Algorithm
end LG2021.Concentration
end
end
/- LG2021ConcentrationPathAccumulation -/
section
noncomputable section
namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory BilateralProfitMHR
open scoped ENNReal
end LG2021.Concentration
end
end
/- LG2021ConcentrationPredictable -/
section
noncomputable section
namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory BilateralProfitMHR Algorithm
/-- Retain all candidate blocks and precisely the Gaussian coordinates already consumed. -/
def prefixSeed {d u n : ℕ} (p : ℕ) (s : Seed d u n) : Seed d u n :=
  (s.1, fun j => if j.val < p then s.2 j else 0)
/-- Drop the two most recent observations from a paired history. -/
def beforePair {p : ℕ} (ys : Fin (2 * p + 2) → ℝ) : Fin (2 * p) → ℝ :=
  fun j => ys ⟨j.val, by omega⟩
/-- A concrete cumulative statistic driven by the actual observed pairs and consumed Gaussian coordinates. -/
def pairSum {d u n : ℕ}
    (increment : (p : ℕ) → Seed d u n → (Fin (2 * p) → ℝ) → (Space d × ℝ) × ℝ → ℝ) :
    (p : ℕ) → Seed d u n → (Fin (2 * p) → ℝ) → ℝ
  | 0, _, _ => 0
  | p + 1, s, ys =>
      let history : Fin (2 * p + 2) → ℝ := fun j => ys ⟨j.val, by omega⟩
      pairSum increment p s (beforePair history) +
        increment p (prefixSeed p s) (beforePair history)
          ((seedGaussian s p, history ⟨2 * p, by omega⟩), history ⟨2 * p + 1, by omega⟩)
end LG2021.Concentration
end
end
/- LG2021ConcentrationKernelPrefix -/
section
noncomputable section
namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory BilateralProfitMHR Algorithm
def removeGaussianSeed {d u n : ℕ} (i : Fin (n + 1))
    (s : Seed d u n) : GaussianRemainder d u n :=
  (s.1, Fin.removeNth i s.2)
def canonicalGaussianRemainder {d u n : ℕ} (i : Fin (n + 1))
    (w : GaussianRemainder d u n) : GaussianRemainder d u n :=
  removeGaussianSeed i (prefixSeed i.val (insertGaussianSeed i (w, 0)))
end LG2021.Concentration
end
end
/- LG2021ConcentrationPathFinite -/
section
noncomputable section
namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory BilateralProfitMHR Algorithm
open scoped ENNReal
end LG2021.Concentration
end
end
/- LG2021ConcentrationPredictableEstimators -/
section
noncomputable section
set_option maxHeartbeats 800000
namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory BilateralProfitMHR Algorithm
open scoped ENNReal
/-- Scalar estimation error, centered by the actual observation kernels and stopped predictably. -/
def scalarIncrement {d u : ℕ} (cfg : OracleConfig)
    (K : Set (Space d)) (hK : MeasurableSet K) (R : ℝ) (anchor : Space d)
    (ν : ObsKernel (Space d)) (hνm : ν.IsMeasurable)
    (enabled : ℕ → Bool)
    (active : (p : ℕ) → Seed d u cfg.horizon × (Fin (2 * p) → ℝ) → Bool)
    (z : (p : ℕ) → Seed d u cfg.horizon × (Fin (2 * p) → ℝ) → Space d)
    (p : ℕ) (s : Seed d u cfg.horizon) (ys : Fin (2 * p) → ℝ) (q : (Space d × ℝ) × ℝ) : ℝ :=
  if hp : p < cfg.horizon + 1 then
    if enabled p && active p (s, ys) then
      q.1.2 * scalarCoefficient cfg.lambda cfg.radius (z p (s, ys)) q.1.1 - q.2 -
        scalarPredictableMean (policy (u := u) cfg K hK R anchor) ν hνm
          (insertGaussianSeed ⟨p, hp⟩) (measurable_insertGaussianSeed cfg ⟨p, hp⟩)
          cfg.lambda cfg.radius (z p (s, ys)) (removeGaussianSeed ⟨p, hp⟩ s, ys)
    else 0
  else 0
end LG2021.Concentration
namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory BilateralProfitMHR Algorithm
open scoped ENNReal
end LG2021.Concentration
end
end
/- LG2021ConcentrationPredictableGradient -/
section
noncomputable section
set_option maxHeartbeats 800000
namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory BilateralProfitMHR Algorithm
open scoped ENNReal
/-- Directional estimation error with predictable stopping and a parameter-domain guard. -/
def gradientIncrement {d u : ℕ} (cfg : OracleConfig)
    (K : Set (Space d)) (hK : MeasurableSet K) (R : ℝ) (anchor : Space d)
    (ν : ObsKernel (Space d)) (hνm : ν.IsMeasurable)
    (enabled : ℕ → Bool)
    (active : (p : ℕ) → Seed d u cfg.horizon × (Fin (2 * p) → ℝ) → Bool)
    (z η : (p : ℕ) → Seed d u cfg.horizon × (Fin (2 * p) → ℝ) → Space d)
    (p : ℕ) (s : Seed d u cfg.horizon) (ys : Fin (2 * p) → ℝ) (q : (Space d × ℝ) × ℝ) : ℝ :=
  if hp : p < cfg.horizon + 1 then
    if enabled p && active p (s, ys) then
      if cfg.lambda * ‖z p (s, ys)‖ ≤ 1 ∧ ‖η p (s, ys)‖ ≤ 1 then
        q.1.2 * directionalGradientCoefficient cfg.lambda cfg.radius (z p (s, ys)) (η p (s, ys)) q.1.1 -
          gradientPredictableMean (policy (u := u) cfg K hK R anchor) ν hνm
            (insertGaussianSeed ⟨p, hp⟩) (measurable_insertGaussianSeed cfg ⟨p, hp⟩)
            cfg.lambda cfg.radius (z p (s, ys)) (η p (s, ys)) (removeGaussianSeed ⟨p, hp⟩ s, ys)
      else 0
    else 0
  else 0
end LG2021.Concentration
end
end
/- LG2021ConcentrationBernstein -/
section
set_option autoImplicit false
namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory
end LG2021.Concentration
end
/- LG2021OracleConfidenceArithmetic -/
section
noncomputable section
namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory
def oracleMomentConstant : ℝ := 10^6
def oracleConcentrationConstant : ℝ := 1/(10^12)
def scalarConfidenceThreshold (lambda H m : ℝ) : ℝ :=
  (oracleMomentConstant/lambda+1)*Real.sqrt (H/(oracleConcentrationConstant*m))
def gradientConfidenceThreshold (H m : ℝ) : ℝ :=
  oracleMomentConstant*Real.sqrt (H/(oracleConcentrationConstant*m))
end LG2021.Concentration
end
end
/- LG2021ConcentrationHistoryPrefix -/
section
noncomputable section
namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory BilateralProfitMHR
open scoped ENNReal
/-- Retain the seed and the first observations of a finite path. -/
def historyPrefix {Ω : Type} {T N : ℕ} (hTN : T ≤ N)
    (w : Ω × (Fin N → ℝ)) : Ω × (Fin T → ℝ) :=
  (w.1, fun j => w.2 (Fin.castLE hTN j))
end LG2021.Concentration
end
end
/- LG2021ConcentrationEstimatorConfidence -/
section
noncomputable section
namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory BilateralProfitMHR Algorithm
open scoped ENNReal
/-- Number of deterministic times included in a stopped-estimator comparison. -/
def enabledCount (enabled : ℕ → Bool) (N : ℕ) : ℕ :=
  ((Finset.range N).filter fun p => enabled p).card
end LG2021.Concentration
namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory BilateralProfitMHR Algorithm
open scoped ENNReal
end LG2021.Concentration
end
end
/- LG2021ConcentrationTerminalConfidence -/
section
noncomputable section
namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory BilateralProfitMHR Algorithm
open scoped ENNReal
end LG2021.Concentration
end
end
/- LG2021AlgorithmInvariant -/
section
noncomputable section
namespace LG2021.Algorithm
open Set MeasureTheory BilateralProfitMHR
open scoped Classical
end LG2021.Algorithm
end
end
/- LG2021OracleSampleComplexity -/
section
noncomputable section
namespace LG2021.Algorithm
open MeasureTheory
end LG2021.Algorithm
end
end
/- LG2021AlgorithmTrace -/
section
noncomputable section
namespace LG2021.Algorithm
open scoped Classical
def traceState {d u : ℕ} (cfg : OracleConfig) (K : Set (Space d)) (R : ℝ)
    (seed : Seed d u cfg.horizon) (ys : ℕ → ℝ × ℝ) (p : ℕ) : State d u p :=
  runState cfg K R seed p (fun i => ys i)
def traceWinner {d u : ℕ} (cfg : OracleConfig) (K : Set (Space d)) (R : ℝ)
    (seed : Seed d u cfg.horizon) (ys : ℕ → ℝ × ℝ) (p : ℕ) : Option (Fin u) :=
  let st := traceState cfg K R seed ys p
  winner cfg (st.2.2.2.1 + 1)
    (updatedScalars cfg st (seedGaussian seed p) (ys p).1 (ys p).2)
def traceStage {d u : ℕ} (cfg : OracleConfig) (K : Set (Space d)) (R : ℝ)
    (seed : Seed d u cfg.horizon) (ys : ℕ → ℝ × ℝ) : ℕ → ℕ
  | 0 => 0
  | p + 1 => traceStage cfg K R seed ys p +
      if traceWinner cfg K R seed ys p = none then 0 else 1
def traceCore {d u : ℕ} (cfg : OracleConfig) (K : Set (Space d)) (R : ℝ)
    (seed : Seed d u cfg.horizon) (ys : ℕ → ℝ × ℝ) (p : ℕ) :
    Frame d × (Fin u → Space d) :=
  ((traceState cfg K R seed ys p).2.1, (traceState cfg K R seed ys p).2.2.1)
end LG2021.Algorithm
end
end
/- LG2021TraceSums -/
section
noncomputable section
namespace LG2021.Algorithm
open Concentration
def traceScalarUpdate {d u : ℕ} (cfg : OracleConfig) (K : Set (Space d)) (R : ℝ)
    (seed : Seed d u cfg.horizon) (ys : ℕ → ℝ × ℝ) (p : ℕ) (s : Fin u) : ℝ :=
  (ys p).1 * scalarCoefficient cfg.lambda cfg.radius
    ((traceState cfg K R seed ys p).2.2.1 s) (seedGaussian seed p) - (ys p).2
def traceGradientUpdate {d u : ℕ} (cfg : OracleConfig) (K : Set (Space d)) (R : ℝ)
    (seed : Seed d u cfg.horizon) (ys : ℕ → ℝ × ℝ) (p : ℕ) (s : Fin u) : Space d :=
  (ys p).1 • gradientCoefficient cfg.lambda cfg.radius
    ((traceState cfg K R seed ys p).2.2.1 s) (seedGaussian seed p)
end LG2021.Algorithm
end
end
/- LG2021TerminalTrace -/
section
noncomputable section
namespace LG2021.Algorithm
def terminalPairs {n : ℕ} (ys : Fin n → ℝ) (p : ℕ) : ℝ × ℝ :=
  if hp : 2 * p + 1 < n then
    (ys ⟨2 * p, by omega⟩, ys ⟨2 * p + 1, hp⟩) else (0, 0)
def observationPrefix {n : ℕ} (ys : Fin n → ℝ) (τ : ℕ) (hτ : τ ≤ n) : Fin τ → ℝ :=
  fun i => ys (i.castLE hτ)
end LG2021.Algorithm
end
end
/- LG2021RegretAggregation -/
section
namespace LG2021
end LG2021
end
/- LG2021StageAggregation -/
section
noncomputable section
namespace LG2021.Algorithm
open scoped Classical
def stageFiber (tag : ℕ → ℕ) (N s : ℕ) : Finset ℕ :=
  (Finset.range N).filter (fun p => tag p = s)
def stages (tag : ℕ → ℕ) (N : ℕ) : Finset ℕ := (Finset.range N).image tag
def stageValue (tag : ℕ → ℕ) (N : ℕ) (g : ℕ → ℝ) (s : ℕ) : ℝ :=
  if hs : (stageFiber tag N s).Nonempty then g ((stageFiber tag N s).max' hs) else 0
end LG2021.Algorithm
end
end
/- LG2021StageSampleCost -/
section
noncomputable section
namespace LG2021.Algorithm
open scoped Classical
def sampleBudget (cfg : OracleConfig) (u : ℕ) : ℝ :=
  64 * max ((cfg.momentConstant / cfg.lambda + 1) ^ 2)
    ((cfg.momentConstant * cfg.radius) ^ 2) * confidenceLog cfg u / cfg.concentrationConstant
def effectiveGap (n : ℕ) (k Δ : ℝ) : ℝ :=
  if Δ ≤ 2 * (k + 1) / (n : ℝ) then 0 else min 1 Δ
end LG2021.Algorithm
end
end
/- LG2021StageRegret -/
section
noncomputable section
namespace LG2021.Algorithm
open MeasureTheory
def frameGap {d : ℕ} (L : Space d → ℝ) (xstar : Space d) (F : Frame d) : ℝ :=
  gaussianMean (fun x => L (frameApply F x)) - L xstar
def traceComparatorGap {d u : ℕ} (cfg : OracleConfig) (K : Set (Space d)) (R : ℝ)
    (seed : Seed d u cfg.horizon) (ys : ℕ → ℝ × ℝ) (L : Space d → ℝ)
    (xstar : Space d) (p : ℕ) : ℝ :=
  frameGap L xstar (traceState cfg K R seed ys p).2.1
end LG2021.Algorithm
end
end
/- LG2021TraceMeasurable -/
section
noncomputable section
namespace LG2021.Algorithm
open MeasureTheory
open scoped Classical
def sameStageBefore {d u N : ℕ} (cfg : OracleConfig) (K : Set (Space d)) (R : ℝ)
    (a p : ℕ) (seed : Seed d u cfg.horizon) (ys : Fin N → ℝ) : Bool :=
  if traceStage cfg K R seed (terminalPairs ys) p = traceStage cfg K R seed (terminalPairs ys) a
    then true else false
end LG2021.Algorithm
end
end
/- LG2021ConcentrationStageEstimators -/
section
noncomputable section
namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory BilateralProfitMHR Algorithm
/-- The same-stage stopping flag is read before the next pair is observed. -/
def stageActive {d u : ℕ} (cfg : OracleConfig) (K : Set (Space d)) (R : ℝ) (a p : ℕ)
    (w : Seed d u cfg.horizon × (Fin (2 * p) → ℝ)) : Bool :=
  sameStageBefore cfg K R a p w.1 w.2
/-- Candidate fixed at the proposed start of an oracle stage. -/
def stageCandidate {d u : ℕ} (cfg : OracleConfig) (K : Set (Space d)) (R : ℝ)
    (a : ℕ) (s : Fin u) (p : ℕ) (w : Seed d u cfg.horizon × (Fin (2 * p) → ℝ)) : Space d :=
  (traceState cfg K R w.1 (terminalPairs w.2) a).2.2.1 s
/-- Source-simplex direction fixed at stage start, normalized by twice the outer radius. -/
def stageDirection {d u : ℕ} (cfg : OracleConfig) (K : Set (Space d)) (R : ℝ)
    (a : ℕ) (s : Fin u) (v : Space d) (p : ℕ)
    (w : Seed d u cfg.horizon × (Fin (2 * p) → ℝ)) : Space d :=
  (2 * cfg.radius)⁻¹ • (frameUnapply (traceState cfg K R w.1 (terminalPairs w.2) a).2.1 v -
    stageCandidate cfg K R a s p w)
/-- The actual scalar error process associated with a deterministic proposed stage start. -/
def stageScalarError {d u : ℕ} (cfg : OracleConfig)
    (K : Set (Space d)) (hK : MeasurableSet K) (R : ℝ) (anchor : Space d)
    (ν : ObsKernel (Space d)) (hνm : ν.IsMeasurable) (a : ℕ) (s : Fin u)
    (b : ℕ) (w : Seed d u cfg.horizon × (Fin (2 * b) → ℝ)) : ℝ :=
  pairSum (scalarIncrement cfg K hK R anchor ν hνm (fun p => decide (a ≤ p))
    (stageActive cfg K R a) (stageCandidate cfg K R a s)) b w.1 w.2
/-- The corresponding normalized directional error process. -/
def stageGradientError {d u : ℕ} (cfg : OracleConfig)
    (K : Set (Space d)) (hK : MeasurableSet K) (R : ℝ) (anchor : Space d)
    (ν : ObsKernel (Space d)) (hνm : ν.IsMeasurable) (a : ℕ) (s : Fin u) (v : Space d)
    (b : ℕ) (w : Seed d u cfg.horizon × (Fin (2 * b) → ℝ)) : ℝ :=
  pairSum (gradientIncrement cfg K hK R anchor ν hνm (fun p => decide (a ≤ p))
    (stageActive cfg K R a) (stageCandidate cfg K R a s) (stageDirection cfg K R a s v)) b w.1 w.2
end LG2021.Concentration
end
end
/- LG2021ConcentrationSumExpansion -/
section
noncomputable section
namespace LG2021.Concentration
open Algorithm
/-- The available scalar observation prefix, totalized by zero outside the recorded history. -/
def historyAt {N : ℕ} (ys : Fin N → ℝ) (p : ℕ) : Fin (2 * p) → ℝ :=
  if h : 2 * p ≤ N then observationPrefix ys (2 * p) h else fun _ => 0
end LG2021.Concentration
end
end
/- LG2021ConcentrationStageExpansion -/
section
noncomputable section
namespace LG2021.Concentration
open Algorithm
end LG2021.Concentration
namespace LG2021.Concentration
open Algorithm BilateralProfitMHR
/-- Actual scalar predictable center along a terminal path, for a fixed stage-start candidate. -/
def stageScalarCenter {d u N : ℕ} (cfg : OracleConfig)
    (K : Set (Space d)) (hK : MeasurableSet K) (R : ℝ) (anchor : Space d)
    (ν : ObsKernel (Space d)) (hνm : ν.IsMeasurable) (a : ℕ) (k : Fin u)
    (s : Seed d u cfg.horizon) (ys : Fin N → ℝ) (j : ℕ) : ℝ :=
  if hj : j < cfg.horizon + 1 then
    scalarPredictableMean (policy (u := u) cfg K hK R anchor) ν hνm
      (insertGaussianSeed ⟨j, hj⟩) (measurable_insertGaussianSeed cfg ⟨j, hj⟩)
      cfg.lambda cfg.radius ((traceState cfg K R s (terminalPairs ys) a).2.2.1 k)
      (removeGaussianSeed ⟨j, hj⟩ (prefixSeed j s), historyAt ys j)
  else 0
end LG2021.Concentration
namespace LG2021.Concentration
open Algorithm BilateralProfitMHR
def fixedStageDirection {d u N : ℕ} (cfg : OracleConfig) (K : Set (Space d)) (R : ℝ)
    (a : ℕ) (k : Fin u) (v : Space d) (s : Seed d u cfg.horizon) (ys : Fin N → ℝ) : Space d :=
  (2 * cfg.radius)⁻¹ • (frameUnapply (traceState cfg K R s (terminalPairs ys) a).2.1 v -
    (traceState cfg K R s (terminalPairs ys) a).2.2.1 k)
/-- Actual directional predictable center along a terminal path. -/
def stageGradientCenter {d u N : ℕ} (cfg : OracleConfig)
    (K : Set (Space d)) (hK : MeasurableSet K) (R : ℝ) (anchor : Space d)
    (ν : ObsKernel (Space d)) (hνm : ν.IsMeasurable) (a : ℕ) (k : Fin u) (v : Space d)
    (s : Seed d u cfg.horizon) (ys : Fin N → ℝ) (j : ℕ) : ℝ :=
  if hj : j < cfg.horizon + 1 then
    gradientPredictableMean (policy (u := u) cfg K hK R anchor) ν hνm
      (insertGaussianSeed ⟨j, hj⟩) (measurable_insertGaussianSeed cfg ⟨j, hj⟩)
      cfg.lambda cfg.radius ((traceState cfg K R s (terminalPairs ys) a).2.2.1 k)
      (fixedStageDirection cfg K R a k v s ys)
      (removeGaussianSeed ⟨j, hj⟩ (prefixSeed j s), historyAt ys j)
  else 0
end LG2021.Concentration
end
end
/- LG2021AlgorithmEllipsoidHelpers -/
section
noncomputable section
namespace LG2021.Algorithm
open Matrix MeasureTheory ModernConvex.EllipsoidMethod
end LG2021.Algorithm
end
end
/- LG2021AlgorithmShallow -/
section
noncomputable section
namespace LG2021.Algorithm
open Matrix MeasureTheory ModernConvex.EllipsoidMethod
def shallowSlice {d : ℕ} (c : Fin d → ℝ) (B : Matrix (Fin d) (Fin d) ℝ)
    (p : Fin d → ℝ) : Set (Fin d → ℝ) :=
  {x | ∃ u, u ⬝ᵥ u ≤ 1 ∧ p ⬝ᵥ u ≤ 1 / (2 * (d : ℝ)) ∧ x = c + B *ᵥ u}
end LG2021.Algorithm
end
end
/- LG2021AlgorithmVolume -/
section
/-!
Minimum-ellipsoid and protected-volume adapters. The source simplex supplies
the protected positive volume. The geometric contraction is the explicit
shallow-cut theorem.
-/
noncomputable section
namespace LG2021.Algorithm
open Matrix MeasureTheory Set ModernConvex.Ellipsoids
open LG2021.JohnHelpers
open scoped ENNReal
end LG2021.Algorithm
end
end
/- LG2021AlgorithmSimplex -/
section
noncomputable section
namespace LG2021.Algorithm
open Matrix MeasureTheory Set
open scoped BigOperators Classical
def sliceRadius : ℝ := Real.sqrt (3 / 4)
end LG2021.Algorithm
end
end
/- LG2021GaussianGeometryConvex -/
section
noncomputable section
namespace LG2021
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
end LG2021
end
end
/- LG2021AlgorithmPreservation -/
section
/-! The stopping test and its actual confidence estimates preserve every
near-minimizing point. The strict margin also justifies inward rational rounding. -/
noncomputable section
namespace LG2021.Algorithm
end LG2021.Algorithm
end
end
/- LG2021AlgorithmStageVolume -/
section
noncomputable section
namespace LG2021.Algorithm
open Set MeasureTheory Matrix ModernConvex.Ellipsoids
open scoped Classical
def traceCut {d u : ℕ} (cfg : OracleConfig) (K : Set (Space d)) (R : ℝ)
    (seed : Seed d u cfg.horizon) (ys : ℕ → ℝ × ℝ) (p : ℕ) (s : Fin u) : Cut d :=
  let st := traceState cfg K R seed ys p
  cutFromEstimate st.2.1 (st.2.2.1 s)
    (gradientEstimate (st.2.2.2.1 + 1) (updatedGradients cfg st (seedGaussian seed p) (ys p).1) s)
def traceCertified {d u : ℕ} (cfg : OracleConfig) (K : Set (Space d)) (R : ℝ)
    (seed : Seed d u cfg.horizon) (ys : ℕ → ℝ × ℝ) (p : ℕ) (s : Fin u) : ℝ :=
  let st := traceState cfg K R seed ys p
  lowerBound cfg (st.2.2.2.1 + 1)
    (updatedScalars cfg st (seedGaussian seed p) (ys p).1 (ys p).2) s
def traceDet {d u : ℕ} (cfg : OracleConfig) (K : Set (Space d)) (R : ℝ)
    (seed : Seed d u cfg.horizon) (ys : ℕ → ℝ × ℝ) (p : ℕ) : ℝ :=
  |(chosenOuterFrame (nativeCodedBody K (traceState cfg K R seed ys p).1)).1.det|
end LG2021.Algorithm
end
end
/- LG2021CandidateSampling -/
section
noncomputable section
namespace LG2021.Algorithm
open MeasureTheory
def candidateCount (n : ℕ) : ℕ := Nat.ceil (48 * Real.log (3 * (n : ℝ) ^ 2))
end LG2021.Algorithm
end
end
/- LG2021RateAlgebra -/
section
noncomputable section
namespace LG2021.Algorithm
open Concentration
end LG2021.Algorithm
end
end
/- LG2021AlgorithmStageRate -/
section
noncomputable section
namespace LG2021.Algorithm
open Set MeasureTheory Concentration
def sourceSimplexVolume (d : ℕ) (D L : ℝ) : ℝ :=
  (Real.exp (-L) / D)^d * sliceRadius^(d - 1) / (2 * (d.factorial : ℝ))
def simplexLogPenalty (d : ℕ) : ℝ :=
  |Real.log (2 * (d.factorial : ℝ))| + (d : ℝ) * |Real.log 2| +
    ((d - 1 : ℕ) : ℝ) * |Real.log sliceRadius|
end LG2021.Algorithm
end
end
/- LG2021AlgorithmGoodHistory -/
section
noncomputable section
namespace LG2021.Algorithm
open Set MeasureTheory
def traceSampleCount {d u : ℕ} (cfg : OracleConfig) (K : Set (Space d)) (R : ℝ)
    (seed : Seed d u cfg.horizon) (ys : ℕ → ℝ × ℝ) (p : ℕ) : ℕ :=
  (traceState cfg K R seed ys p).2.2.2.1 + 1
def traceScalar {d u : ℕ} (cfg : OracleConfig) (K : Set (Space d)) (R : ℝ)
    (seed : Seed d u cfg.horizon) (ys : ℕ → ℝ × ℝ) (p : ℕ) (s : Fin u) : ℝ :=
  scalarEstimate (traceSampleCount cfg K R seed ys p)
    (updatedScalars cfg (traceState cfg K R seed ys p) (seedGaussian seed p) (ys p).1 (ys p).2) s
def traceGradient {d u : ℕ} (cfg : OracleConfig) (K : Set (Space d)) (R : ℝ)
    (seed : Seed d u cfg.horizon) (ys : ℕ → ℝ × ℝ) (p : ℕ) (s : Fin u) : Space d :=
  gradientEstimate (traceSampleCount cfg K R seed ys p)
    (updatedGradients cfg (traceState cfg K R seed ys p) (seedGaussian seed p) (ys p).1) s
def traceLocalLoss {d u : ℕ} (cfg : OracleConfig) (K : Set (Space d)) (R : ℝ)
    (seed : Seed d u cfg.horizon) (ys : ℕ → ℝ × ℝ) (f : Space d → ℝ) (p : ℕ) : Space d → ℝ :=
  fun x => f (frameApply (traceState cfg K R seed ys p).2.1 x)
def traceGap {d u : ℕ} (cfg : OracleConfig) (K : Set (Space d)) (R : ℝ)
    (seed : Seed d u cfg.horizon) (ys : ℕ → ℝ × ℝ) (f : Space d → ℝ) (p : ℕ) (s : Fin u) : ℝ :=
  surrogate cfg.lambda (traceLocalLoss cfg K R seed ys f p) ((traceState cfg K R seed ys p).2.2.1 s) -
    traceLocalLoss cfg K R seed ys f p 0
def traceGradientDeviation {d u : ℕ} (cfg : OracleConfig) (K : Set (Space d)) (R : ℝ)
    (seed : Seed d u cfg.horizon) (ys : ℕ → ℝ × ℝ) (f : Space d → ℝ)
    (p : ℕ) (s : Fin u) (w : Space d) : ℝ :=
  let st := traceState cfg K R seed ys p
  inner ℝ (traceGradient cfg K R seed ys p s -
    gradient (surrogate cfg.lambda (traceLocalLoss cfg K R seed ys f p)) (st.2.2.1 s))
      (frameUnapply st.2.1 w - st.2.2.1 s)
end LG2021.Algorithm
end
end
/- LG2021ConcentrationStageBuffers -/
section
noncomputable section
namespace LG2021.Concentration
open Algorithm BilateralProfitMHR
end LG2021.Concentration
namespace LG2021.Concentration
open Algorithm BilateralProfitMHR
end LG2021.Concentration
namespace LG2021.Concentration
open Algorithm BilateralProfitMHR
end LG2021.Concentration
end
end
/- LG2021GuardedRegret -/
section
noncomputable section
namespace LG2021
open MeasureTheory ProbabilityTheory Set
open scoped Classical
/-- The feasible Gaussian proposal, expressed in the coordinates of the current body. -/
def radialGuard {d : ℕ} (r : ℝ) (x : Space d) : Space d :=
  if ‖x‖ ≤ r then x else 0
namespace Algorithm
end Algorithm
end LG2021
end
end
/- LG2021PairRegret -/
section
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory BilateralProfitMHR Algorithm Set
open scoped Classical
/-- The two actual query losses in one sequential pair. The second query may
depend on the first observation. -/
def coordinatePairLoss {X Ω W B : Type} [MeasurableSpace X] [MeasurableSpace Ω]
    (A : QueryAlg X Ω) (encode : W × B → Ω) {T : ℕ}
    (w : W × (Fin T → ℝ)) (L : X → ℝ) (p : (B × ℝ) × ℝ) : ℝ :=
  L (A.query T (encode (w.1, p.1.1)) w.2) +
    L (A.query (T + 1) (encode (w.1, p.1.1)) (Fin.snoc w.2 p.1.2))
end LG2021.Concentration
end
end
/- LG2021AlgorithmParameters -/
section
noncomputable section
namespace LG2021.Algorithm
open Concentration
def oracleConfig (d : ℕ) (D : ℝ) (n : ℕ) : OracleConfig where
  horizon := n
  radius := paperRadius d (parameterLog d D n)
  lambda := paperLambda d (parameterLog d D n)
  momentConstant := oracleMomentConstant
  concentrationConstant := oracleConcentrationConstant
end LG2021.Algorithm
end
end
/- LG2021ConcentrationActualBias -/
section
noncomputable section
set_option maxHeartbeats 1000000
namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory BilateralProfitMHR Algorithm Set
open scoped Classical
end LG2021.Concentration
end
end
/- LG2021ConcentrationStageBias -/
section
noncomputable section
set_option maxHeartbeats 1000000
namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory BilateralProfitMHR Algorithm Set
open scoped Classical
end LG2021.Concentration
end
end
/- LG2021ConcentrationStageEvents -/
section
noncomputable section
namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory BilateralProfitMHR Algorithm
/-- Failure of a scalar stopped-stage comparison at any pair of deterministic endpoints. -/
def scalarStageFailure {d u : ℕ} (cfg : OracleConfig)
    (K : Set (Space d)) (hK : MeasurableSet K) (R : ℝ) (anchor : Space d)
    (ν : ObsKernel (Space d)) (hνm : ν.IsMeasurable) (N : ℕ) (H : ℝ) :
    Set (Seed d u cfg.horizon × (Fin (2 * N) → ℝ)) :=
  {w | ∃ a b : Fin (N + 1), ∃ s : Fin u, a.val < b.val ∧
    scalarConfidenceThreshold cfg.lambda H ((b.val-a.val : ℕ) : ℝ) ≤
      |stageScalarError cfg K hK R anchor ν hνm a.val s b.val
        (historyPrefix (by have hb := b.isLt; omega : 2 * b.val ≤ 2 * N) w) /
          ((b.val-a.val : ℕ) : ℝ)|}
/-- Failure of a normalized simplex-direction comparison in the Bernstein quadratic regime. -/
def gradientStageFailure {d u : ℕ} (cfg : OracleConfig)
    (K : Set (Space d)) (hK : MeasurableSet K) (R : ℝ) (anchor : Space d)
    (ν : ObsKernel (Space d)) (hνm : ν.IsMeasurable) (N : ℕ) (H : ℝ) (v : Fin (d+1) → Space d) :
    Set (Seed d u cfg.horizon × (Fin (2 * N) → ℝ)) :=
  {w | ∃ a b : Fin (N + 1), ∃ s : Fin u, ∃ k : Fin (d+1), a.val < b.val ∧
    H / oracleConcentrationConstant ≤ ((b.val-a.val : ℕ) : ℝ) ∧
    gradientConfidenceThreshold H ((b.val-a.val : ℕ) : ℝ) ≤
      |stageGradientError cfg K hK R anchor ν hνm a.val s (v k) b.val
        (historyPrefix (by have hb := b.isLt; omega : 2 * b.val ≤ 2 * N) w) /
          ((b.val-a.val : ℕ) : ℝ)|}
end LG2021.Concentration
namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory BilateralProfitMHR Algorithm
end LG2021.Concentration
end
end
/- LG2021StageStarts -/
section
noncomputable section
namespace LG2021.Algorithm
open scoped Classical
end LG2021.Algorithm
end
end
/- LG2021ConcentrationActualConfidence -/
section
noncomputable section
set_option maxHeartbeats 1000000
namespace LG2021.Concentration
open Algorithm BilateralProfitMHR MeasureTheory ProbabilityTheory
end LG2021.Concentration
namespace LG2021.Concentration
open Algorithm BilateralProfitMHR MeasureTheory ProbabilityTheory
end LG2021.Concentration
end
end
/- LG2021ConfidencePrefix -/
section
noncomputable section
namespace LG2021.Algorithm
end LG2021.Algorithm
end
end
/- LG2021WinnerSamples -/
section
noncomputable section
namespace LG2021.Algorithm
end LG2021.Algorithm
end
end
/- LG2021ConcentrationGoodHistory -/
section
noncomputable section
set_option maxHeartbeats 1000000
namespace LG2021.Concentration
open Algorithm BilateralProfitMHR MeasureTheory ProbabilityTheory
end LG2021.Concentration
namespace LG2021.Concentration
open Algorithm BilateralProfitMHR MeasureTheory ProbabilityTheory
end LG2021.Concentration
namespace LG2021.Concentration
open Algorithm BilateralProfitMHR MeasureTheory ProbabilityTheory
end LG2021.Concentration
end
end
/- LG2021ConcentrationConfidenceEvent -/
section
noncomputable section
namespace LG2021.Concentration
open Algorithm BilateralProfitMHR MeasureTheory ProbabilityTheory
/-- The simultaneous scalar and retained-direction estimator event on the actual terminal path space. -/
def estimatorGood {d u : ℕ} (cfg : OracleConfig)
    (K : Set (Space d)) (hK : MeasurableSet K) (R : ℝ) (anchor : Space d)
    (ν : ObsKernel (Space d)) (hνm : ν.IsMeasurable) (N : ℕ) (v : Fin (d+1) → Space d) :
    Set (Seed d u cfg.horizon × (Fin (2*N) → ℝ)) :=
  (scalarStageFailure cfg K hK R anchor ν hνm N (confidenceLog cfg u))ᶜ ∩
    (gradientStageFailure cfg K hK R anchor ν hνm N (confidenceLog cfg u) v)ᶜ
end LG2021.Concentration
end
end
/- LG2021ConcentrationCandidateCoordinates -/
section
noncomputable section
namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory BilateralProfitMHR Algorithm
open scoped ENNReal
abbrev CandidateRemainder (d u n : ℕ) :=
  (Fin n → Fin u → Space d) × (Fin (n + 1) → Space d)
def candidateBlockMeasure (d u : ℕ) (cfg : OracleConfig) : Measure (Fin u → Space d) :=
  Measure.pi (fun _ : Fin u => sphereMeasure d (cfg.radius / (2 * (d : ℝ))))
instance candidateBlockMeasure_probability (d u : ℕ) (cfg : OracleConfig) :
    IsProbabilityMeasure (candidateBlockMeasure d u cfg) := by
  unfold candidateBlockMeasure
  infer_instance
def candidateRemainderMeasure (d u : ℕ) (cfg : OracleConfig) :
    Measure (CandidateRemainder d u cfg.horizon) :=
  (Measure.pi (fun _ : Fin cfg.horizon => candidateBlockMeasure d u cfg)).prod
    (Measure.pi (fun _ : Fin (cfg.horizon + 1) => gaussian d))
instance candidateRemainderMeasure_probability (d u : ℕ) (cfg : OracleConfig) :
    IsProbabilityMeasure (candidateRemainderMeasure d u cfg) := by
  unfold candidateRemainderMeasure
  infer_instance
def insertCandidateSeed {d u n : ℕ} (i : Fin (n + 1))
    (w : CandidateRemainder d u n × (Fin u → Space d)) : Seed d u n :=
  (Fin.insertNth i w.2 w.1.1, w.1.2)
end LG2021.Concentration
end
end
/- LG2021CurrentConfidence -/
section
noncomputable section
namespace LG2021.Algorithm
set_option maxHeartbeats 1000000
end LG2021.Algorithm
end
end
/- LG2021FinalRateAlgebra -/
section
noncomputable section
namespace LG2021.Algorithm
def separationFactor (d : ℕ) : ℝ := 4096 * (d : ℝ) * Real.sqrt (d : ℝ)
end LG2021.Algorithm
end
end
/- LG2021CandidateHitGeometry -/
section
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace LG2021.Algorithm
open Set MeasureTheory Concentration
open scoped Classical
def frameCandidateGap {d : ℕ} (lambda : ℝ) (L : Space d → ℝ) (F : Frame d) (z : Space d) : ℝ :=
  surrogate lambda (fun x => L (frameApply F x)) z - L (frameApply F 0)
end LG2021.Algorithm
end
end
/- LG2021CandidateHitEvent -/
section
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace LG2021.Algorithm
open Set MeasureTheory Concentration BilateralProfitMHR
open scoped ENNReal Classical
def candidateStartValid {d u T : ℕ} (cfg : OracleConfig) (K : Set (Space d)) (R : ℝ)
    (xstar : Space d) (p : ℕ) (w : Seed d u cfg.horizon × (Fin T → ℝ)) : Prop :=
  let st := traceState cfg K R w.1 (terminalPairs w.2) p
  st.2.2.2.1 = 0 ∧ (interior (codedBody K st.1)).Nonempty ∧ xstar ∈ codedBody K st.1
def candidateHit {d u T : ℕ} (cfg : OracleConfig) (K : Set (Space d)) (R : ℝ)
    (L : Space d → ℝ) (xstar : Space d) (p : ℕ)
    (w : Seed d u cfg.horizon × (Fin T → ℝ)) : Prop :=
  ∃ s : Fin u,
    (traceComparatorGap cfg K R w.1 (terminalPairs w.2) L xstar p - 1/(cfg.horizon : ℝ)) /
      separationFactor d ≤ traceGap cfg K R w.1 (terminalPairs w.2) L p s
def candidateStartFailure {d u T : ℕ} (cfg : OracleConfig) (K : Set (Space d)) (R : ℝ)
    (L : Space d → ℝ) (xstar : Space d) (p : ℕ) :
    Set (Seed d u cfg.horizon × (Fin T → ℝ)) :=
  {w | candidateStartValid cfg K R xstar p w ∧ ¬candidateHit cfg K R L xstar p w}
end LG2021.Algorithm
end
end
/- LG2021CandidateNormSupport -/
section
noncomputable section
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
namespace LG2021.Algorithm
open Set MeasureTheory Concentration BilateralProfitMHR
open scoped ENNReal
def candidateSeedGood {d u : ℕ} (cfg : OracleConfig) (seed : Seed d u cfg.horizon) : Prop :=
  ∀ p : Fin (cfg.horizon+1), ∀ s : Fin u, ‖seed.1 p s‖ ≤ cfg.radius/(2*(d : ℝ))
end LG2021.Algorithm
end
end
/- LG2021CandidateHitTerminal -/
section
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace LG2021.Algorithm
open Set MeasureTheory Concentration BilateralProfitMHR
open scoped ENNReal Classical
def candidateTerminalGood {d u N : ℕ} (cfg : OracleConfig) (K : Set (Space d)) (R : ℝ)
    (L : Space d → ℝ) (xstar : Space d) : Set (Seed d u cfg.horizon × (Fin (2*N) → ℝ)) :=
  {w | ∀ p ≤ N, candidateStartValid cfg K R xstar p w → candidateHit cfg K R L xstar p w}
def candidateTerminalEvent {d u N : ℕ} (cfg : OracleConfig) (K : Set (Space d)) (R : ℝ)
    (L : Space d → ℝ) (xstar : Space d) : Set (Seed d u cfg.horizon × (Fin (2*N) → ℝ)) :=
  candidateTerminalGood cfg K R L xstar ∩ {w | candidateSeedGood cfg w.1}
end LG2021.Algorithm
end
end
/- LG2021CandidateHitLift -/
section
noncomputable section
namespace LG2021.Algorithm
open Set MeasureTheory Concentration
end LG2021.Algorithm
end
end
/- LG2021PairLossMartingale -/
section
noncomputable section
set_option maxHeartbeats 1000000
namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory BilateralProfitMHR Algorithm Set
open scoped ENNReal Classical
/-- The exact pre-Gaussian conditional mean of the two actual query losses. -/
def pairLossMean {X Ω W B : Type} [MeasurableSpace X] [MeasurableSpace Ω]
    [MeasurableSpace W] [MeasurableSpace B] (A : QueryAlg X Ω) (Q : Measure B)
    (ν : ObsKernel X) (hνm : ν.IsMeasurable) (encode : W × B → Ω) (he : Measurable encode)
    (L : X → ℝ) {T : ℕ} (w : W × (Fin T → ℝ)) : ℝ :=
  ∫ p, coordinatePairLoss A encode w L p ∂coordinatePairKernel A Q ν hνm encode he T w
/-- Center the actual bounded pair loss at its exact predictable mean. -/
def pairLossIncrement {d u : ℕ} (cfg : OracleConfig) (K : Set (Space d))
    (hK : MeasurableSet K) (R : ℝ) (anchor : Space d)
    (ν : ObsKernel (Space d)) (hνm : ν.IsMeasurable) (L : Space d → ℝ)
    (p : ℕ) (s : Seed d u cfg.horizon) (ys : Fin (2 * p) → ℝ)
    (z : (Space d × ℝ) × ℝ) : ℝ :=
  if hp : p < cfg.horizon + 1 then
    let i : Fin (cfg.horizon + 1) := ⟨p, hp⟩
    let w := (removeGaussianSeed i s, ys)
    let A := policy (u := u) cfg K hK R anchor
    coordinatePairLoss A (insertGaussianSeed i) w L z -
      pairLossMean A (gaussian d) ν hνm (insertGaussianSeed i)
        (measurable_insertGaussianSeed cfg i) L w
  else 0
end LG2021.Concentration
end
end
/- LG2021PairLossTerminal -/
section
noncomputable section
set_option maxHeartbeats 1000000
namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory BilateralProfitMHR Algorithm Set
open scoped ENNReal Classical
private theorem pairSum_eq_sum {d u n : ℕ}
    (increment : (p : ℕ) → Seed d u n → (Fin (2 * p) → ℝ) → (Space d × ℝ) × ℝ → ℝ)
    (N : ℕ) (s : Seed d u n) (ys : Fin (2 * N) → ℝ) :
    pairSum increment N s ys = ∑ p : Fin N,
      increment p.val (prefixSeed p.val s)
        (fun j => ys ⟨j.val, by have := p.isLt; have := j.isLt; omega⟩)
        ((seedGaussian s p.val, ys ⟨2 * p.val, by have := p.isLt; omega⟩),
          ys ⟨2 * p.val + 1, by have := p.isLt; omega⟩) := by
  induction N with
  | zero => simp [pairSum]
  | succ N ih =>
      simp only [pairSum, ih, Fin.sum_univ_castSucc]
      apply congrArg₂ (fun a b : ℝ => a + b)
      · apply Finset.sum_congr rfl
        intro p hp
        rfl
      · rfl
def realPathLoss {X Ω : Type} [MeasurableSpace X] [MeasurableSpace Ω]
    (A : QueryAlg X Ω) (L : X → ℝ) {τ : ℕ} (w : Ω × (Fin τ → ℝ)) : ℝ :=
  ∑ i : Fin τ, L (A.pastQueries w.1 w.2 i)
def pairLossPredictableMean {d u : ℕ} (cfg : OracleConfig) (K : Set (Space d))
    (hK : MeasurableSet K) (R : ℝ) (anchor : Space d)
    (ν : ObsKernel (Space d)) (hνm : ν.IsMeasurable) (L : Space d → ℝ)
    (p : ℕ) (s : Seed d u cfg.horizon) (ys : Fin (2 * p) → ℝ) : ℝ :=
  if hp : p < cfg.horizon + 1 then
    let i : Fin (cfg.horizon + 1) := ⟨p, hp⟩
    pairLossMean (policy (u := u) cfg K hK R anchor) (gaussian d) ν hνm
      (insertGaussianSeed i) (measurable_insertGaussianSeed cfg i) L (removeGaussianSeed i s, ys)
  else 0
/-- Sum of the exact conditional pair means evaluated before their Gaussian coordinates are revealed. -/
def predictablePairLossTotal {d u : ℕ} (cfg : OracleConfig) (K : Set (Space d))
    (hK : MeasurableSet K) (R : ℝ) (anchor : Space d)
    (ν : ObsKernel (Space d)) (hνm : ν.IsMeasurable) (L : Space d → ℝ)
    (N : ℕ) (w : Seed d u cfg.horizon × (Fin (2 * N) → ℝ)) : ℝ :=
  ∑ p : Fin N, pairLossPredictableMean cfg K hK R anchor ν hνm L p.val (prefixSeed p.val w.1)
    (fun j => w.2 ⟨j.val, by have := p.isLt; have := j.isLt; omega⟩)
end LG2021.Concentration
end
end
/- LG2021PairLossTrace -/
section
noncomputable section
set_option maxHeartbeats 1000000
namespace LG2021.Concentration
open MeasureTheory ProbabilityTheory BilateralProfitMHR Algorithm Set
open scoped ENNReal Classical
end LG2021.Concentration
end
end
/- LG2021ConcentrationTerminalGood -/
section
noncomputable section
set_option maxHeartbeats 1500000
namespace LG2021.Concentration
open Algorithm BilateralProfitMHR MeasureTheory ProbabilityTheory
/-- Concrete deterministic facts delivered simultaneously by the terminal probability event. -/
structure TerminalGoodFacts {d : ℕ} (cfg : OracleConfig)
    (K : Set (Space d)) (hK : MeasurableSet K) (R : ℝ) (anchor : Space d)
    (F : Space d → ℝ) (xstar : Space d) (v : Fin (d+1) → Space d)
    (w : Seed d (candidateCount cfg.horizon) cfg.horizon × (Fin cfg.horizon → ℝ)) : Prop where
  candidate_norm : ∀ p k, ‖seedCandidates w.1 p k‖ ≤ cfg.radius / (2 * (d : ℝ))
  scalar : ∀ p < cfg.horizon/2,
    (interior (codedBody K (traceState cfg K R w.1 (terminalPairs w.2) p).1)).Nonempty → ∀ k,
    |traceScalar cfg K R w.1 (terminalPairs w.2) p k - traceGap cfg K R w.1 (terminalPairs w.2) F p k| ≤
      confidenceRadius cfg (candidateCount cfg.horizon) (traceSampleCount cfg K R w.1 (terminalPairs w.2) p)
  gradient : ∀ p < cfg.horizon/2,
    (interior (codedBody K (traceState cfg K R w.1 (terminalPairs w.2) p).1)).Nonempty →
    (∀ i, v i ∈ codedBody K (traceState cfg K R w.1 (terminalPairs w.2) p).1) →
    ∀ k, traceWinner cfg K R w.1 (terminalPairs w.2) p = some k → ∀ i,
    traceGradientDeviation cfg K R w.1 (terminalPairs w.2) F p k (v i) ≤
      2 * cfg.radius * (cfg.momentConstant * Real.sqrt (confidenceLog cfg (candidateCount cfg.horizon) /
        (cfg.concentrationConstant * (traceSampleCount cfg K R w.1 (terminalPairs w.2) p : ℝ))) +
          1 / (8 * cfg.radius * (cfg.horizon : ℝ)))
  candidate_hit :
    (∀ p ≤ cfg.horizon/2, (interior (codedBody K (traceState cfg K R w.1 (terminalPairs w.2) p).1)).Nonempty) →
    (∀ p ≤ cfg.horizon/2, xstar ∈ codedBody K (traceState cfg K R w.1 (terminalPairs w.2) p).1) →
    ∀ p ≤ cfg.horizon/2, ∃ k,
      (traceComparatorGap cfg K R w.1 (terminalPairs w.2) F xstar p - 1/(cfg.horizon : ℝ))/separationFactor d ≤
        traceGap cfg K R w.1 (terminalPairs w.2) F p k
  path_regret :
    (∀ p < cfg.horizon/2, (interior (codedBody K (traceState cfg K R w.1 (terminalPairs w.2) p).1)).Nonempty) →
    realPathLoss (policy (u := candidateCount cfg.horizon) cfg K hK R anchor) F w -
      (cfg.horizon : ℝ)*F xstar ≤
      2*(∑ p ∈ Finset.range (cfg.horizon/2), min 1 (traceComparatorGap cfg K R w.1 (terminalPairs w.2) F xstar p)) +
        Real.sqrt ((cfg.horizon : ℝ)*Real.log cfg.horizon) + 1
end LG2021.Concentration
namespace LG2021.Concentration
open Algorithm BilateralProfitMHR MeasureTheory ProbabilityTheory
end LG2021.Concentration
end
end
/- LG2021ComparatorNonneg -/
section
noncomputable section
namespace LG2021.Algorithm
end LG2021.Algorithm
end
end
/- LG2021PathwiseRegret -/
section
noncomputable section
namespace LG2021.Algorithm
open Concentration
end LG2021.Algorithm
end
end
/- LG2021DeterministicClosure -/
section
noncomputable section
set_option maxHeartbeats 1000000
namespace LG2021.Algorithm
open MeasureTheory Concentration Set
end LG2021.Algorithm
end
end
/- LG2021ExpectedRegret -/
section
noncomputable section
namespace LG2021
open MeasureTheory BilateralProfitMHR
open scoped ENNReal
end LG2021
end
end
/- LG2021CanonicalExpectedRegret -/
section
noncomputable section
namespace LG2021.Algorithm
open MeasureTheory BilateralProfitMHR BilateralProfitMHR.CorollaryTransport Concentration
open scoped ENNReal
end LG2021.Algorithm
end
end
/- Canonical fixed-dimensional bandit theorem -/
section
noncomputable section
set_option maxHeartbeats 2000000
namespace LG2021
open MeasureTheory BilateralProfitMHR BilateralProfitMHR.CorollaryTransport
open Algorithm Concentration Set Metric
end LG2021
end
end
/- LG2021LipschitzExtension -/
section
/-!
The global extension needed only in the analysis of the bandit policy.
The infimal-convolution construction follows the existing real Lipschitz
extension proof in Mathlib; compact convexity additionally preserves convexity.
The infimal-convolution formulation supplies the global extension used in the formal proof.
-/
noncomputable section
namespace LG2021
open Set
open scoped NNReal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
def convexLipschitzExtension (K : Set E) (C : ℝ≥0) (f : E → ℝ) (x : E) : ℝ :=
  sInf ((fun y => f y + (C : ℝ) * ‖x - y‖) '' K)
end LG2021
end
end
/- LG2021Erosion -/
section
/-!
The known-body erosion used in Appendix F of Lattimore and György (2021).
The interior Lipschitz proof adapts Mathlib's convex secant argument, using
the loss range [0,1] to obtain the exact constant. The loss and its extension
are analysis objects; the eroded body uses only the known body and scale.
-/
noncomputable section
namespace LG2021
open Set Metric
open scoped NNReal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
end LG2021
end
end
/- CorollaryTransport -/
section
namespace BilateralProfitMHR.CorollaryTransport
open MeasureTheory
open scoped ENNReal
section Geometry
variable {X Y Ω : Type} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Ω]
def mapQuery (f : Y → X) (hf : Measurable f) (A : QueryAlg Y Ω) : QueryAlg X Ω where
  query τ ω y := f (A.query τ ω y)
  query_measurable τ := hf.comp (A.query_measurable τ)
def pullKernel (f : Y → X) (ν : ObsKernel X) : ObsKernel Y :=
  fun τ xs ys x => ν τ (fun i => f (xs i)) ys (f x)
end Geometry
section Observations
variable {X Ω : Type} [MeasurableSpace X] [MeasurableSpace Ω]
end Observations
end BilateralProfitMHR.CorollaryTransport
end
/- CorollaryNormalization -/
section
namespace BilateralProfitMHR.CorollaryTransport
open MeasureTheory
open scoped ENNReal
end BilateralProfitMHR.CorollaryTransport
end
/- LG2021ErosionTransport -/
section
noncomputable section
namespace LG2021
open MeasureTheory BilateralProfitMHR BilateralProfitMHR.CorollaryTransport Set Metric
open scoped ENNReal
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]
end LG2021
end
end
/- LG2021Reduction -/
section
namespace LG2021
open MeasureTheory BilateralProfitMHR BilateralProfitMHR.CorollaryTransport
open scoped ENNReal
end LG2021
end
/- LG2021CanonicalTransport -/
section
/-! Quantifier-preserving reduction from the canonical Lipschitz problem to
continuous convex losses, arbitrary affine dimension, and the stated noise norm.
The reduction preserves the choice of policy before the unknown loss and noise. -/
noncomputable section
namespace LG2021
open MeasureTheory BilateralProfitMHR BilateralProfitMHR.CorollaryTransport Set Metric
open scoped ENNReal
end LG2021
end
end
/- LG2021NormalizedTransport -/
section
noncomputable section
namespace LG2021
open MeasureTheory BilateralProfitMHR BilateralProfitMHR.CorollaryTransport Set Metric
end LG2021
end
end
/- LG2021SharpClosure -/
section
noncomputable section
set_option maxHeartbeats 2000000
namespace LG2021.Algorithm
open MeasureTheory Concentration Set
/-- A path bound retaining explicit dimension and confidence factors. -/
def sharpPathBound (d : ℕ) (D : ℝ) (n : ℕ) : ℝ :=
  2 * Real.sqrt (4 * separationFactor d ^ 2 *
    sampleBudget (oracleConfig d D n) (candidateCount n) + 1) *
      Real.sqrt ((n : ℝ) * (129 * (d : ℝ)^2 * parameterLog d D n)) +
        Real.sqrt ((n : ℝ) * Real.log n) + 4 * (separationFactor d + 1) + 1
end LG2021.Algorithm
end
end
/- LG2021SharpRateBase -/
section
noncomputable section
namespace LG2021
open Concentration
end LG2021
end
end
/- LG2021SharpRateAlgebra -/
section
noncomputable section
namespace LG2021.Algorithm
open Concentration
end LG2021.Algorithm
end
end
section
namespace LG2021.Algorithm
end LG2021.Algorithm
end
/- LG2021SharpStageRate -/
section
noncomputable section
namespace LG2021.Algorithm
open Set MeasureTheory Concentration
end LG2021.Algorithm
end
end
/- LG2021SharpTransport -/
section
/-!
Transport of the explicit universal dimension bound through Lipschitz extension
and the known-body erosion. The comparator is an infimum, so the convex loss
need not be continuous at the boundary of its domain.
-/
noncomputable section
namespace LG2021
open MeasureTheory BilateralProfitMHR BilateralProfitMHR.CorollaryTransport Set Metric
open scoped ENNReal
/-- The canonical policy guarantee with its explicit dimension and diameter
dependence. The policy and its probability space precede the loss and noise. -/
def SharpCanonicalBandit (C : ℝ) : Prop :=
  ∀ d : ℕ, 0 < d → ∀ n : ℕ, 2 ≤ n → ∀ D : ℝ, 2 ≤ D →
    ∀ K : Set (EuclideanSpace ℝ (Fin d)), IsCompact K → Convex ℝ K →
      closedBall 0 1 ⊆ K → (∀ x ∈ K, ∀ y ∈ K, dist x y ≤ D) →
      ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P ∧
        ∃ A : QueryAlg (EuclideanSpace ℝ (Fin d)) Ω, A.IsOn K ∧
          ∀ L : EuclideanSpace ℝ (Fin d) → ℝ,
            ConvexOn ℝ univ L → LipschitzWith 1 L → (∀ x, 0 ≤ L x) →
            (∀ x ∈ K, L x ∈ Icc 0 1) →
            ∀ ν : ObsKernel (EuclideanSpace ℝ (Fin d)), ν.IsMeasurable →
              UnitNoiseCond K L ν →
                expectedCumLoss A P ν
                  (fun x => ENNReal.ofReal (L x - sInf (L '' K))) n ≤
                    ENNReal.ofReal (C * sharpRate d D n)
section Erosion
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]
end Erosion
end LG2021
end
end
/- LG2021SharpRateFixed -/
section
noncomputable section
namespace LG2021
end LG2021
end
end
/- LG2021SharpSourceTransport -/
section
/-!
The explicit source rate for arbitrary locations of the contained unit ball.
The loss comparator is its infimum on the compact action set; whenever the
minimum is attained this equals the source's minimum comparator.
-/
noncomputable section
namespace LG2021
open MeasureTheory BilateralProfitMHR BilateralProfitMHR.CorollaryTransport Set Metric
open scoped ENNReal
end LG2021
end
end
/- LG2021SharpMain -/
section
noncomputable section
set_option maxHeartbeats 2000000
namespace LG2021
open MeasureTheory BilateralProfitMHR BilateralProfitMHR.CorollaryTransport
open Algorithm Concentration Set Metric
end LG2021
end
end
open LG2021 MeasureTheory BilateralProfitMHR BilateralProfitMHR.CorollaryTransport Set Metric


