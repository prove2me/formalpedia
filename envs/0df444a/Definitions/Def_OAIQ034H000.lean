-- Prove2me | Definitions.Def_OAIQ034H000
-- name    : OAIQ034H000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T05:33:05.085649+00:00
-- url     : https://prove2.me/theorems/010db45d-273f-4d81-8363-82d9953fc8f0
-- title:
--   Definitions bundle OAIQ034H000 of the split of OpenAI, A hyperbolic group with no geometric CAT(0) action (result family 257)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.HyperbolicObstruction.main`, carved from OpenAI's openai/math development (OpenAI, *A hyperbolic group with no geometric CAT(0) action (result family 257)*, OpenAI Math Release, September 25, 2026, result family 257, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 555 declarations of OpenAI's Lean: 227 definitions, 18 inductive types or structures, 10 instances and 300 theorems. The definitions and types are `OAI.HyperbolicObstruction.BasedHigherContraction.nullhomotopy`, `OAI.HyperbolicObstruction.BasedSquareContraction.contraction`, `OAI.HyperbolicObstruction.BasedSquareContraction.faceObstruction`, `OAI.HyperbolicObstruction.BasedSquareContraction.facePath`, `OAI.HyperbolicObstruction.BasedSquareContraction.loopSquare`, `OAI.HyperbolicObstruction.BasedTriangleContraction.contraction`, `OAI.HyperbolicObstruction.BasedTriangleContraction.square`, `OAI.HyperbolicObstruction.BasedTriangleContraction.theta`, `OAI.HyperbolicObstruction.BernoulliCandidates.OverlapEvent`, `OAI.HyperbolicObstruction.BernoulliCandidates.OverlapType`, `OAI.HyperbolicObstruction.BernoulliCandidates.Present`, `OAI.HyperbolicObstruction.BernoulliCandidates.count`, `OAI.HyperbolicObstruction.BernoulliCandidates.shared`, `OAI.HyperbolicObstruction.CATActionWitness`, `OAI.HyperbolicObstruction.CATZero.mid`, `OAI.HyperbolicObstruction.CATZero.radialPairing`, `OAI.HyperbolicObstruction.CATZero.segment`, `OAI.HyperbolicObstruction.CATZero.tangentDist`, `OAI.HyperbolicObstruction.CATZero.tangentPairing`, `OAI.HyperbolicObstruction.ClosedCoverGluing.glue`, `OAI.HyperbolicObstruction.ClosedCoverGluing.gluePrism`, `OAI.HyperbolicObstruction.CochainLinear`, `OAI.HyperbolicObstruction.Coincidence.RankBad`, `OAI.HyperbolicObstruction.Coincidence.contactCharge`, `OAI.HyperbolicObstruction.Coincidence.maxRepresentative`, `OAI.HyperbolicObstruction.Coincidence.rankOn`, `OAI.HyperbolicObstruction.Coincidence.rankRate`, `OAI.HyperbolicObstruction.Coincidence.signedAssignment`, `OAI.HyperbolicObstruction.Coincidence.unsignedRank`, `OAI.HyperbolicObstruction.Coincidence.unsignedValues`, `OAI.HyperbolicObstruction.ConditionalStar`, `OAI.HyperbolicObstruction.ConditionalStar.branch`, `OAI.HyperbolicObstruction.ConeData`, `OAI.HyperbolicObstruction.ConeData.Opposite`, `OAI.HyperbolicObstruction.ConeData.Parallel`, `OAI.HyperbolicObstruction.ConeData.add`, `OAI.HyperbolicObstruction.ConeData.inductiveMean`, `OAI.HyperbolicObstruction.ConeData.normSq`, `OAI.HyperbolicObstruction.ConeData.pairing`, `OAI.HyperbolicObstruction.ConeData.translate` and 205 more.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry/HyperbolicGroups, in whole or in part: `HyperbolicGroups_ActualContact`, `HyperbolicGroups_BasedSquareContraction`, `HyperbolicGroups_BasedTriangleContraction`, `HyperbolicGroups_BoundaryList`, `HyperbolicGroups_CATZero`, `HyperbolicGroups_Candidate`, `HyperbolicGroups_Chernoff`, `HyperbolicGroups_ClosedCoverGluing`, `HyperbolicGroups_Coincidence`, `HyperbolicGroups_Concentration`, `HyperbolicGroups_ConditionalStar`, `HyperbolicGroups_ConeApexProducer`, `HyperbolicGroups_ConeCellTarget`, `HyperbolicGroups_ConeData`, `HyperbolicGroups_ConeFanCorner`, `HyperbolicGroups_ConeFrozenTarget`, `HyperbolicGroups_ConeGraph`, `HyperbolicGroups_ConeSkeleton`, `HyperbolicGroups_ConeWalkTarget`, `HyperbolicGroups_CoreFan`, `HyperbolicGroups_CycleDecomposition`, `HyperbolicGroups_FaceWalk`, `HyperbolicGroups_FanApex`, `HyperbolicGroups_FiniteLaw`, `HyperbolicGroups_FrozenWalk`, `HyperbolicGroups_FullWalkNormal`, `HyperbolicGroups_GenericMoment`, `HyperbolicGroups_GenericTable`, `HyperbolicGroups_GeometricAction`, `HyperbolicGroups_Graph`, `HyperbolicGroups_GraphWordFilling`, `HyperbolicGroups_HSpaceFundamental`, `HyperbolicGroups_HSpacePathObstruction`, `HyperbolicGroups_IncidenceTemplate`, `HyperbolicGroups_IndexedFace`, `HyperbolicGroups_IndexedFillingValue`, `HyperbolicGroups_MacroCertificate`, `HyperbolicGroups_MacroCycle`, `HyperbolicGroups_MacroWalk`, `HyperbolicGroups_MappedPicture`, `HyperbolicGroups_MetricHexagon`, `HyperbolicGroups_Moment`, `HyperbolicGroups_NormalCell`, `HyperbolicGroups_Normalization`, `HyperbolicGroups_ParameterizedSquareFilling`, `HyperbolicGroups_PathHomotopyTopology`, `HyperbolicGroups_PermEuler`, `HyperbolicGroups_PermSwitch`, `HyperbolicGroups_PictureContact`, `HyperbolicGroups_PictureEuler`, `HyperbolicGroups_PictureMap`, `HyperbolicGroups_PolygonTarget`, `HyperbolicGroups_Presentation`, `HyperbolicGroups_PresentationDisk`, `HyperbolicGroups_Random`, `HyperbolicGroups_Selection`, `HyperbolicGroups_SquarePathFilling`, `HyperbolicGroups_TableSelection`, `HyperbolicGroups_TangentCone`, `HyperbolicGroups_TangentRay`, `HyperbolicGroups_Template`, `HyperbolicGroups_TriangleSquare`, `HyperbolicGroups_WalkCell`, `HyperbolicGroups_WalkClasses`, `HyperbolicGroups_WalkConeLink`, `HyperbolicGroups_WalkFanCorner`, `HyperbolicGroups_WalkFanIncoming`, `HyperbolicGroups_WalkFragment`, `HyperbolicGroups_WalkRadial`, `HyperbolicGroups_WalkRawPosition`, `HyperbolicGroups_WeightedCoincidence`, `HyperbolicGroups_WordDisk`, `HyperbolicGroups_WordPicture`.
--
--   **Imports.** It imports the published bundle `Def_HyperbolicObstruction`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ034H003`, `OAIQ034H004`, `OAIQ034H005` and `OAIQ034H006`.
-- source:
--   OpenAI, A hyperbolic group with no geometric CAT(0) action (result family 257), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 257; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-hyperbolic-group-with-no-geometric-CAT0-action-September-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry/HyperbolicGroups at commit adc7f12

import Mathlib
import Definitions.Def_HyperbolicObstruction

section
-- module Solutions.OAIQ034_HG.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    dite p a b = b h := dif_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_CATZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped Topology ContinuousMap

noncomputable section
namespace HyperbolicObstruction
namespace CATZero

variable {X : Type*} [MetricSpace X]

/-- The comparison segment chosen from the CAT(0) comparison condition. -/
def segment (h : CATZero X) (x y : X) : ℝ → X := (h x y).choose

theorem segment_spec (h : CATZero X) (x y : X) :
    IsSegment (segment h x y) x y := (h x y).choose_spec.1

theorem segment_cn (h : CATZero X) (x y z : X) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    dist z (segment h x y t) ^ 2 ≤
      (1 - t) * dist z x ^ 2 + t * dist z y ^ 2 - t * (1 - t) * dist x y ^ 2 :=
  (h x y).choose_spec.2 z t ht

theorem segment_left (h : CATZero X) (x y : X) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    dist x (segment h x y t) = t * dist x y := by
  have hs := (segment_spec h x y).2.2 0 (by norm_num) t ht
  rw [(segment_spec h x y).1] at hs
  simpa only [zero_sub, abs_neg, abs_of_nonneg ht.1] using hs

theorem segment_right (h : CATZero X) (x y : X) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    dist (segment h x y t) y = (1 - t) * dist x y := by
  have hs := (segment_spec h x y).2.2 t ht 1 (by norm_num)
  rw [(segment_spec h x y).2.1] at hs
  rw [abs_of_nonpos (sub_nonpos.mpr ht.2)] at hs
  simpa only [neg_sub] using hs

/-- CAT(0) comparison applies to any point with the prescribed division
    distances, rather than just to the initially chosen segment. -/
theorem eq_segment_of_dist (h : CATZero X) {x y p : X} {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hx : dist x p = t * dist x y)
    (hy : dist p y = (1 - t) * dist x y) :
    p = segment h x y t := by
  have hc := segment_cn h x y p ht
  rw [dist_comm p x, hx, hy] at hc
  have hz : dist p (segment h x y t) ^ 2 ≤ 0 := by nlinarith [hc]
  have hn : 0 ≤ dist p (segment h x y t) := dist_nonneg
  exact dist_eq_zero.mp (by nlinarith)

/-- Metric midpoint, available without completeness or properness. -/
def mid (h : CATZero X) (x y : X) : X := segment h x y (1 / 2)

theorem dist_left_mid (h : CATZero X) (x y : X) :
    dist x (mid h x y) = dist x y / 2 := by
  simpa [mid, div_eq_mul_inv, mul_comm] using segment_left h x y (t := 1 / 2) (by norm_num)

theorem dist_mid_right (h : CATZero X) (x y : X) :
    dist (mid h x y) y = dist x y / 2 := by
  have hs := segment_right h x y (t := 1 / 2) (by norm_num)
  norm_num at hs
  simpa [mid, div_eq_mul_inv, mul_comm] using hs

theorem mid_cn (h : CATZero X) (x y z : X) :
    dist z (mid h x y) ^ 2 ≤
      (dist z x ^ 2 + dist z y ^ 2) / 2 - dist x y ^ 2 / 4 := by
  have hc := segment_cn h x y z (t := 1 / 2) (by norm_num)
  dsimp [mid]
  linarith [hc]

/-- Source Lemma `energy:quadrilateral`, with its midpoint error retained. -/
theorem quadrilateral (h : CATZero X) (a b c d : X) :
    dist a c ^ 2 + dist b d ^ 2 + 4 * dist (mid h a c) (mid h b d) ^ 2 ≤
      dist a b ^ 2 + dist b c ^ 2 + dist c d ^ 2 + dist d a ^ 2 := by
  have hb := mid_cn h a c b
  have hd := mid_cn h a c d
  have hm := mid_cn h b d (mid h a c)
  rw [dist_comm b (mid h a c), dist_comm b a] at hb
  rw [dist_comm d (mid h a c), dist_comm d c] at hd
  linarith

end CATZero
end HyperbolicObstruction

noncomputable section
namespace HyperbolicObstruction

/-- The metric description of nonnegative radial dilations in a Euclidean
cone, with the angular cosine eliminated by polarization. No linear or
associative addition is included. -/
structure ConeData (X : Type*) [MetricSpace X] where
  vertex : X
  scale : ℝ → X → X
  scale_zero : ∀ x, scale 0 x = vertex
  scale_one : ∀ x, scale 1 x = x
  radial_metric : ∀ r s : ℝ, 0 ≤ r → 0 ≤ s → ∀ x y : X,
    dist (scale r x) (scale s y) ^ 2 =
      (r ^ 2 - r * s) * dist vertex x ^ 2 +
      (s ^ 2 - r * s) * dist vertex y ^ 2 + r * s * dist x y ^ 2

namespace ConeData
variable {X : Type*} [MetricSpace X] (T : ConeData X)

def normSq (x : X) : ℝ := dist T.vertex x ^ 2

def pairing (x y : X) : ℝ := (T.normSq x + T.normSq y - dist x y ^ 2) / 2

theorem pairing_comm (x y : X) : T.pairing x y = T.pairing y x := by
  simp only [pairing, dist_comm x y]
  ring

@[simp] theorem pairing_self (x : X) : T.pairing x x = T.normSq x := by
  simp [pairing]

@[simp] theorem normSq_vertex : T.normSq T.vertex = 0 := by simp [normSq]

@[simp] theorem pairing_vertex (x : X) : T.pairing T.vertex x = 0 := by
  simp [pairing, normSq]

theorem dist_sq (x y : X) :
    dist x y ^ 2 = T.normSq x + T.normSq y - 2 * T.pairing x y := by
  dsimp [pairing]
  ring

theorem normSq_scale {r : ℝ} (hr : 0 ≤ r) (x : X) :
    T.normSq (T.scale r x) = r ^ 2 * T.normSq x := by
  have hc := T.radial_metric r 0 hr (by norm_num) x x
  simpa [T.scale_zero, normSq, dist_comm] using hc

theorem pairing_scale {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) (x y : X) :
    T.pairing (T.scale r x) (T.scale s y) = r * s * T.pairing x y := by
  unfold pairing
  rw [T.normSq_scale hr, T.normSq_scale hs, T.radial_metric r s hr hs]
  dsimp [normSq]
  ring

theorem pairing_scale_left {r : ℝ} (hr : 0 ≤ r) (x y : X) :
    T.pairing (T.scale r x) y = r * T.pairing x y := by
  simpa [T.scale_one] using T.pairing_scale hr (show (0 : ℝ) ≤ 1 by norm_num) x y

theorem pairing_scale_right {r : ℝ} (hr : 0 ≤ r) (x y : X) :
    T.pairing x (T.scale r y) = r * T.pairing x y := by
  rw [T.pairing_comm, T.pairing_scale_left hr, T.pairing_comm y x]

/-- In a CAT(0) Euclidean cone, comparison towards the vertex is an equality.
The reverse bound is obtained by comparing towards twice the division point;
no flat-sector theorem is assumed. -/
theorem normSq_segment (h : CATZero X) (x y : X) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    T.normSq (CATZero.segment h x y t) =
      (1 - t) * T.normSq x + t * T.normSq y - t * (1 - t) * dist x y ^ 2 := by
  let p := CATZero.segment h x y t
  have hp : p = CATZero.segment h x y t := rfl
  have hleft := CATZero.segment_left h x y ht
  have hright := CATZero.segment_right h x y ht
  have lower := CATZero.segment_cn h x y T.vertex ht
  have upper := CATZero.segment_cn h x y (T.scale 2 p) ht
  have hpp := T.radial_metric 2 1 (by norm_num) (by norm_num) p p
  have hpx := T.radial_metric 2 1 (by norm_num) (by norm_num) p x
  have hpy := T.radial_metric 2 1 (by norm_num) (by norm_num) p y
  simp only [T.scale_one, dist_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, mul_zero, add_zero] at hpp
  simp only [T.scale_one] at hpx hpy
  rw [dist_comm p x, hp, hleft] at hpx
  rw [hp, hright] at hpy
  change T.normSq p ≤ _ at lower
  change dist (T.scale 2 p) p ^ 2 ≤ _ at upper
  rw [hpp, hpx, hpy] at upper
  dsimp only [normSq, p] at *
  nlinarith [lower, upper]


@[simp] theorem normSq_eq_zero (x : X) : T.normSq x = 0 ↔ x = T.vertex := by
  simp [normSq, dist_eq_zero, eq_comm]

@[simp] theorem scale_vertex {r : ℝ} (hr : 0 ≤ r) :
    T.scale r T.vertex = T.vertex := by
  apply (T.normSq_eq_zero _).mp
  rw [T.normSq_scale hr, T.normSq_vertex, mul_zero]

/-- Scalar-product concavity, derived directly from CN and radial equality. -/
theorem pairing_segment (h : CATZero X) (w x y : X) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (1 - t) * T.pairing w x + t * T.pairing w y ≤
      T.pairing w (CATZero.segment h x y t) := by
  have hc := CATZero.segment_cn h x y w ht
  unfold pairing
  rw [T.normSq_segment h x y ht]
  nlinarith [hc]

/-- The manuscript's two-vector cone addition (not an associative operation). -/
def add (h : CATZero X) (x y : X) : X := T.scale 2 (CATZero.mid h x y)

theorem normSq_mid (h : CATZero X) (x y : X) :
    T.normSq (CATZero.mid h x y) =
      (T.normSq x + T.normSq y) / 2 - dist x y ^ 2 / 4 := by
  have hm := T.normSq_segment h x y (t := 1 / 2) (by norm_num)
  change T.normSq (CATZero.mid h x y) = _ at hm
  linarith

theorem normSq_add (h : CATZero X) (x y : X) :
    T.normSq (T.add h x y) = T.normSq x + T.normSq y + 2 * T.pairing x y := by
  unfold add
  rw [T.normSq_scale (by norm_num), T.normSq_mid h, T.dist_sq x y]
  ring

/-- Source Equation `geom:sum-concavity`. -/
theorem pairing_add (h : CATZero X) (w x y : X) :
    T.pairing w x + T.pairing w y ≤ T.pairing w (T.add h x y) := by
  have hc := T.pairing_segment h w x y (t := 1 / 2) (by norm_num)
  change (1 - (1 / 2 : ℝ)) * T.pairing w x + (1 / 2 : ℝ) * T.pairing w y ≤
    T.pairing w (CATZero.mid h x y) at hc
  unfold add
  rw [T.pairing_scale_right (by norm_num)]
  linarith

/-- Equal-length opposite points of a cone. The zero pair is permitted. -/
def Opposite (c d : X) : Prop :=
  T.normSq c = T.normSq d ∧ T.pairing c d = -T.normSq c

theorem add_opposite (h : CATZero X) {c d : X} (hop : T.Opposite c d) :
    T.add h c d = T.vertex := by
  apply (T.normSq_eq_zero _).mp
  rw [T.normSq_add h, hop.2, ← hop.1]
  ring

theorem opposite_pairing (h : CATZero X) {c d : X} (hop : T.Opposite c d) (x : X) :
    T.pairing c x + T.pairing d x ≤ 0 := by
  have ha := T.pairing_add h x c d
  rw [T.add_opposite h hop, T.pairing_comm x T.vertex, T.pairing_vertex,
    T.pairing_comm x c, T.pairing_comm x d] at ha
  exact ha

/-- The zero set of the sum of the two Busemann coordinates of an axis.
All splitting identities used below are proved from CN, not assumed. -/
def Parallel (c d x : X) : Prop := T.pairing c x + T.pairing d x = 0

def translate (h : CATZero X) (c : X) (t : ℝ) (x : X) : X :=
  T.add h x (T.scale t c)

end ConeData
end HyperbolicObstruction

end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_TangentRay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped Topology ContinuousMap
noncomputable section
noncomputable section
noncomputable section

namespace HyperbolicObstruction
namespace CATZero
variable {X : Type*} [MetricSpace X]

theorem segment_dist (h : CATZero X) (x y : X) {s t : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    dist (segment h x y s) (segment h x y t) = |s - t| * dist x y :=
  (segment_spec h x y).2.2 s hs t ht

theorem segment_mul (h : CATZero X) (x y : X) {s t : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    segment h x (segment h x y t) s = segment h x y (s * t) := by
  have hst : s * t ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨mul_nonneg hs.1 ht.1, by nlinarith [ht.2, mul_nonneg (sub_nonneg.mpr hs.2) ht.1]⟩
  symm
  apply eq_segment_of_dist h hs
  · rw [segment_left h x y hst, segment_left h x y ht]
    ring
  · rw [segment_dist h x y hst ht, segment_left h x y ht,
      abs_of_nonpos (by nlinarith [mul_nonneg (sub_nonneg.mpr hs.2) ht.1])]
    ring

/-- Radial contraction, used in the construction of the tangent pseudometric. -/
theorem radial_contraction (h : CATZero X) (o x y : X) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    dist (segment h o x t) (segment h o y t) ≤ t * dist x y := by
  have ha := segment_cn h o y (segment h o x t) ht
  have hb := segment_cn h o x y ht
  rw [dist_comm (segment h o x t) o, segment_left h o x ht,
    dist_comm (segment h o x t) y] at ha
  rw [dist_comm y o, dist_comm y x] at hb
  have hab : dist (segment h o x t) (segment h o y t) ^ 2 ≤ t ^ 2 * dist x y ^ 2 := by
    nlinarith [mul_nonneg ht.1
      (show 0 ≤ (1 - t) * dist o y ^ 2 + t * dist x y ^ 2 -
        t * (1 - t) * dist o x ^ 2 - dist y (segment h o x t) ^ 2 by linarith)]
  nlinarith [dist_nonneg (x := segment h o x t) (y := segment h o y t),
    mul_nonneg ht.1 (dist_nonneg (x := x) (y := y))]

/-- A comparison scalar product at two positive positions on radial segments.
Its supremum as the positions decrease is the tangent scalar product. -/
def radialPairing (h : CATZero X) (o x y : X) (a b : ℝ) : ℝ :=
  (a ^ 2 * dist o x ^ 2 + b ^ 2 * dist o y ^ 2 -
    dist (segment h o x a) (segment h o y b) ^ 2) / (2 * a * b)

theorem radialPairing_comm (h : CATZero X) (o x y : X) (a b : ℝ) :
    radialPairing h o x y a b = radialPairing h o y x b a := by
  unfold radialPairing
  rw [dist_comm (segment h o x a) (segment h o y b)]
  ring

theorem radialPairing_upper (h : CATZero X) (o x y : X) {a b : ℝ}
    (ha : a ∈ Set.Ioc (0 : ℝ) 1) (hb : b ∈ Set.Ioc (0 : ℝ) 1) :
    radialPairing h o x y a b ≤ dist o x * dist o y := by
  have hdx := dist_triangle o (segment h o y b) (segment h o x a)
  have hdy := dist_triangle o (segment h o x a) (segment h o y b)
  rw [segment_left h o x ⟨ha.1.le, ha.2⟩, segment_left h o y ⟨hb.1.le, hb.2⟩,
    dist_comm (segment h o y b) (segment h o x a)] at hdx
  rw [segment_left h o x ⟨ha.1.le, ha.2⟩, segment_left h o y ⟨hb.1.le, hb.2⟩] at hdy
  unfold radialPairing
  apply (div_le_iff₀ (mul_pos (mul_pos (by norm_num) ha.1) hb.1)).mpr
  have hs : (a * dist o x - b * dist o y) ^ 2 ≤
      dist (segment h o x a) (segment h o y b) ^ 2 := by
    have hp := mul_nonneg
      (show 0 ≤ dist (segment h o x a) (segment h o y b) -
        (a * dist o x - b * dist o y) by linarith)
      (show 0 ≤ dist (segment h o x a) (segment h o y b) +
        (a * dist o x - b * dist o y) by linarith)
    nlinarith
  nlinarith [hs]

/-- Comparison products increase when either point moves towards the base. -/
theorem radialPairing_antitone_left (h : CATZero X) (o x y : X)
    {a a' b : ℝ} (ha : 0 < a) (haa : a ≤ a') (ha' : a' ≤ 1)
    (hb : b ∈ Set.Ioc (0 : ℝ) 1) :
    radialPairing h o x y a' b ≤ radialPairing h o x y a b := by
  have hap : 0 < a' := lt_of_lt_of_le ha haa
  have ht : a / a' ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨(div_pos ha hap).le, (div_le_one hap).mpr haa⟩
  have hc := segment_cn h o (segment h o x a') (segment h o y b) ht
  rw [segment_mul h o x ht ⟨hap.le, ha'⟩, div_mul_cancel₀ a hap.ne',
    dist_comm (segment h o y b) o, segment_left h o y ⟨hb.1.le, hb.2⟩,
    segment_left h o x ⟨hap.le, ha'⟩,
    dist_comm (segment h o y b) (segment h o x a),
    dist_comm (segment h o y b) (segment h o x a')] at hc
  unfold radialPairing
  apply (div_le_div_iff₀ (mul_pos (mul_pos (by norm_num) hap) hb.1)
    (mul_pos (mul_pos (by norm_num) ha) hb.1)).mpr
  have hc' := mul_le_mul_of_nonneg_left hc hap.le
  field_simp at hc'
  nlinarith [mul_nonneg hb.1.le (sub_nonneg.mpr hc')]

theorem radialPairing_antitone_right (h : CATZero X) (o x y : X)
    {a b b' : ℝ} (ha : a ∈ Set.Ioc (0 : ℝ) 1)
    (hb : 0 < b) (hbb : b ≤ b') (hb' : b' ≤ 1) :
    radialPairing h o x y a b' ≤ radialPairing h o x y a b := by
  rw [radialPairing_comm h o x y a b', radialPairing_comm h o x y a b]
  exact radialPairing_antitone_left h o y x hb hbb hb' ha

/-- Definition by bounded supremum, so no completeness of the ambient CAT(0)
space is required to form comparison products in its tangent cone. -/
def tangentPairing (h : CATZero X) (o x y : X) : ℝ :=
  sSup {v | ∃ a ∈ Set.Ioc (0 : ℝ) 1, ∃ b ∈ Set.Ioc (0 : ℝ) 1,
    v = radialPairing h o x y a b}

theorem tangentPairing_set_nonempty (h : CATZero X) (o x y : X) :
    Set.Nonempty {v | ∃ a ∈ Set.Ioc (0 : ℝ) 1, ∃ b ∈ Set.Ioc (0 : ℝ) 1,
      v = radialPairing h o x y a b} :=
  ⟨_, 1, by norm_num, 1, by norm_num, rfl⟩

theorem tangentPairing_set_bddAbove (h : CATZero X) (o x y : X) :
    BddAbove {v | ∃ a ∈ Set.Ioc (0 : ℝ) 1, ∃ b ∈ Set.Ioc (0 : ℝ) 1,
      v = radialPairing h o x y a b} := by
  refine ⟨dist o x * dist o y, ?_⟩
  rintro v ⟨a, ha, b, hb, rfl⟩
  exact radialPairing_upper h o x y ha hb

theorem radialPairing_le_tangentPairing (h : CATZero X) (o x y : X) {a b : ℝ}
    (ha : a ∈ Set.Ioc (0 : ℝ) 1) (hb : b ∈ Set.Ioc (0 : ℝ) 1) :
    radialPairing h o x y a b ≤ tangentPairing h o x y :=
  le_csSup (tangentPairing_set_bddAbove h o x y) ⟨a, ha, b, hb, rfl⟩

theorem tangentPairing_upper (h : CATZero X) (o x y : X) :
    tangentPairing h o x y ≤ dist o x * dist o y := by
  apply csSup_le (tangentPairing_set_nonempty h o x y)
  rintro v ⟨a, ha, b, hb, rfl⟩
  exact radialPairing_upper h o x y ha hb

theorem tangentPairing_comm (h : CATZero X) (o x y : X) :
    tangentPairing h o x y = tangentPairing h o y x := by
  unfold tangentPairing
  congr 1
  ext v
  constructor <;> rintro ⟨a, ha, b, hb, rfl⟩
  · exact ⟨b, hb, a, ha, radialPairing_comm h o x y a b⟩
  · exact ⟨b, hb, a, ha, radialPairing_comm h o y x a b⟩

theorem tangentPairing_self (h : CATZero X) (o x : X) :
    tangentPairing h o x x = dist o x ^ 2 := by
  apply le_antisymm
  · simpa only [pow_two] using tangentPairing_upper h o x x
  · have hl := radialPairing_le_tangentPairing h o x x (a := 1) (b := 1)
      (by norm_num) (by norm_num)
    simpa [radialPairing] using hl

open Filter Topology

theorem radialPairing_tendsto (h : CATZero X) (o x y : X)
    {ι : Type*} {F : Filter ι} {a b : ι → ℝ}
    (ha : Tendsto a F (𝓝 0)) (hb : Tendsto b F (𝓝 0))
    (hap : ∀ᶠ i in F, 0 < a i) (hbp : ∀ᶠ i in F, 0 < b i) :
    Tendsto (fun i => radialPairing h o x y (a i) (b i)) F
      (𝓝 (tangentPairing h o x y)) := by
  apply tendsto_order.mpr
  constructor
  · intro v hv
    obtain ⟨w, ⟨a', ha', b', hb', rfl⟩, hvw⟩ :=
      exists_lt_of_lt_csSup (tangentPairing_set_nonempty h o x y) hv
    filter_upwards [hap, hbp, ha.eventually (gt_mem_nhds ha'.1),
      hb.eventually (gt_mem_nhds hb'.1)] with i hai hbi hai' hbi'
    exact hvw.trans_le ((radialPairing_antitone_left h o x y hai hai'.le ha'.2 hb').trans
      (radialPairing_antitone_right h o x y ⟨hai, hai'.le.trans ha'.2⟩
        hbi hbi'.le hb'.2))
  · intro v hv
    filter_upwards [hap, hbp, ha.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
      hb.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with i hai hbi hai' hbi'
    exact (radialPairing_le_tangentPairing h o x y ⟨hai, hai'.le⟩ ⟨hbi, hbi'.le⟩).trans_lt hv

/-- Distance between formal nonnegative multiples of two radial directions. -/
def tangentDist (h : CATZero X) (o x y : X) (r s : ℝ) : ℝ :=
  Real.sqrt (r ^ 2 * dist o x ^ 2 + s ^ 2 * dist o y ^ 2 -
    2 * r * s * tangentPairing h o x y)

theorem tangentDist_sq_nonneg (h : CATZero X) (o x y : X) {r s : ℝ}
    (hr : 0 ≤ r) (hs : 0 ≤ s) :
    0 ≤ r ^ 2 * dist o x ^ 2 + s ^ 2 * dist o y ^ 2 -
      2 * r * s * tangentPairing h o x y := by
  have hh := tangentPairing_upper h o x y
  nlinarith [mul_nonneg (mul_nonneg hr hs) (sub_nonneg.mpr hh),
    sq_nonneg (r * dist o x - s * dist o y)]

theorem tangentDist_sq (h : CATZero X) (o x y : X) {r s : ℝ}
    (hr : 0 ≤ r) (hs : 0 ≤ s) :
    tangentDist h o x y r s ^ 2 = r ^ 2 * dist o x ^ 2 + s ^ 2 * dist o y ^ 2 -
      2 * r * s * tangentPairing h o x y :=
  Real.sq_sqrt (tangentDist_sq_nonneg h o x y hr hs)

theorem tangentDist_comm (h : CATZero X) (o x y : X) (r s : ℝ) :
    tangentDist h o x y r s = tangentDist h o y x s r := by
  unfold tangentDist
  rw [tangentPairing_comm h o x y]
  congr 1
  ring

@[simp] theorem tangentDist_zero_left (h : CATZero X) (o x y : X) {s : ℝ}
    (hs : 0 ≤ s) : tangentDist h o x y 0 s = s * dist o y := by
  unfold tangentDist
  have he : (0 : ℝ) ^ 2 * dist o x ^ 2 + s ^ 2 * dist o y ^ 2 -
      2 * 0 * s * tangentPairing h o x y = (s * dist o y) ^ 2 := by ring
  rw [he, Real.sqrt_sq (mul_nonneg hs dist_nonneg)]

@[simp] theorem tangentDist_zero_right (h : CATZero X) (o x y : X) {r : ℝ}
    (hr : 0 ≤ r) : tangentDist h o x y r 0 = r * dist o x := by
  rw [tangentDist_comm, tangentDist_zero_left h o y x hr]

theorem tangentDist_tendsto_pos (h : CATZero X) (o x y : X) {r s : ℝ}
    (hr : 0 < r) (hs : 0 < s) :
    Tendsto (fun t : ℝ => dist (segment h o x (t * r)) (segment h o y (t * s)) / t)
      (𝓝[>] 0) (𝓝 (tangentDist h o x y r s)) := by
  have ht : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have htp : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t := eventually_mem_nhdsWithin
  have htr : Tendsto (fun t : ℝ => t * r) (𝓝[>] 0) (𝓝 0) := by
    simpa using ht.mul_const r
  have hts : Tendsto (fun t : ℝ => t * s) (𝓝[>] 0) (𝓝 0) := by
    simpa using ht.mul_const s
  have hp := radialPairing_tendsto h o x y htr hts
    (htp.mono fun _ hx => mul_pos hx hr) (htp.mono fun _ hx => mul_pos hx hs)
  have hl : Tendsto (fun t : ℝ => Real.sqrt
      (r ^ 2 * dist o x ^ 2 + s ^ 2 * dist o y ^ 2 -
        2 * r * s * radialPairing h o x y (t * r) (t * s))) (𝓝[>] 0)
      (𝓝 (tangentDist h o x y r s)) :=
    (tendsto_const_nhds.sub (tendsto_const_nhds.mul hp)).sqrt
  apply hl.congr'
  filter_upwards [htp] with t htp'
  unfold radialPairing
  have he : r ^ 2 * dist o x ^ 2 + s ^ 2 * dist o y ^ 2 -
      2 * r * s * (( (t * r) ^ 2 * dist o x ^ 2 + (t * s) ^ 2 * dist o y ^ 2 -
        dist (segment h o x (t * r)) (segment h o y (t * s)) ^ 2) /
          (2 * (t * r) * (t * s))) =
      (dist (segment h o x (t * r)) (segment h o y (t * s)) / t) ^ 2 := by
    field_simp
    ring
  rw [he, Real.sqrt_sq (div_nonneg dist_nonneg htp'.le)]

theorem tangentDist_tendsto_zero_left (h : CATZero X) (o x y : X) {s : ℝ}
    (hs : 0 ≤ s) :
    Tendsto (fun t : ℝ => dist (segment h o x (t * 0)) (segment h o y (t * s)) / t)
      (𝓝[>] 0) (𝓝 (tangentDist h o x y 0 s)) := by
  rw [tangentDist_zero_left h o x y hs]
  have ht : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have htp : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t := eventually_mem_nhdsWithin
  have hts : Tendsto (fun t : ℝ => t * s) (𝓝[>] 0) (𝓝 0) := by
    simpa using ht.mul_const s
  apply tendsto_const_nhds.congr'
  filter_upwards [htp, hts.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1))]
    with t htp' hts'
  rw [mul_zero, (segment_spec h o x).1,
    segment_left h o y ⟨mul_nonneg htp'.le hs, hts'⟩]
  field_simp

theorem tangentDist_tendsto (h : CATZero X) (o x y : X) {r s : ℝ}
    (hr : 0 ≤ r) (hs : 0 ≤ s) :
    Tendsto (fun t : ℝ => dist (segment h o x (t * r)) (segment h o y (t * s)) / t)
      (𝓝[>] 0) (𝓝 (tangentDist h o x y r s)) := by
  rcases eq_or_lt_of_le hr with he | hr
  · subst r
    exact tangentDist_tendsto_zero_left h o x y hs
  rcases eq_or_lt_of_le hs with he | hs
  · subst s
    simpa only [dist_comm, tangentDist_comm h o x y r 0] using
      tangentDist_tendsto_zero_left h o y x hr.le
  exact tangentDist_tendsto_pos h o x y hr hs

theorem tangentDist_triangle (h : CATZero X) (o x y z : X) {r s t : ℝ}
    (hr : 0 ≤ r) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    tangentDist h o x z r t ≤ tangentDist h o x y r s + tangentDist h o y z s t := by
  apply le_of_tendsto_of_tendsto (tangentDist_tendsto h o x z hr ht)
    ((tangentDist_tendsto h o x y hr hs).add (tangentDist_tendsto h o y z hs ht))
  filter_upwards [show ∀ᶠ a : ℝ in 𝓝[>] 0, 0 < a from eventually_mem_nhdsWithin]
    with a ha
  simpa only [add_div] using div_le_div_of_nonneg_right
    (dist_triangle (segment h o x (a * r)) (segment h o y (a * s))
      (segment h o z (a * t))) ha.le

theorem tangentDist_same (h : CATZero X) (o x : X) (r s : ℝ) :
    tangentDist h o x x r s = |r - s| * dist o x := by
  unfold tangentDist
  rw [tangentPairing_self]
  have he : r ^ 2 * dist o x ^ 2 + s ^ 2 * dist o x ^ 2 -
      2 * r * s * dist o x ^ 2 = ((r - s) * dist o x) ^ 2 := by ring
  rw [he, Real.sqrt_sq_eq_abs, abs_mul, abs_of_nonneg dist_nonneg]

theorem tangentDist_quadrilateral (h : CATZero X) (o a b c d : X)
    {r s t u : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) (ht : 0 ≤ t) (hu : 0 ≤ u) :
    tangentDist h o a c r t ^ 2 + tangentDist h o b d s u ^ 2 ≤
      tangentDist h o a b r s ^ 2 + tangentDist h o b c s t ^ 2 +
        tangentDist h o c d t u ^ 2 + tangentDist h o d a u r ^ 2 := by
  apply le_of_tendsto_of_tendsto
    (((tangentDist_tendsto h o a c hr ht).pow 2).add
      ((tangentDist_tendsto h o b d hs hu).pow 2))
    (((((tangentDist_tendsto h o a b hr hs).pow 2).add
      ((tangentDist_tendsto h o b c hs ht).pow 2)).add
      ((tangentDist_tendsto h o c d ht hu).pow 2)).add
      ((tangentDist_tendsto h o d a hu hr).pow 2))
  filter_upwards [show ∀ᶠ k : ℝ in 𝓝[>] 0, 0 < k from eventually_mem_nhdsWithin]
    with k hk
  have hq := quadrilateral h (segment h o a (k * r)) (segment h o b (k * s))
    (segment h o c (k * t)) (segment h o d (k * u))
  have hq' : dist (segment h o a (k * r)) (segment h o c (k * t)) ^ 2 +
      dist (segment h o b (k * s)) (segment h o d (k * u)) ^ 2 ≤
      dist (segment h o a (k * r)) (segment h o b (k * s)) ^ 2 +
      dist (segment h o b (k * s)) (segment h o c (k * t)) ^ 2 +
      dist (segment h o c (k * t)) (segment h o d (k * u)) ^ 2 +
      dist (segment h o d (k * u)) (segment h o a (k * r)) ^ 2 := by
    nlinarith [sq_nonneg (dist
      (mid h (segment h o a (k * r)) (segment h o c (k * t)))
      (mid h (segment h o b (k * s)) (segment h o d (k * u))))]
  simpa only [div_pow, add_div] using div_le_div_of_nonneg_right hq' (sq_nonneg k)

theorem tangentDist_radial_left (h : CATZero X) (o x y : X) {a r s : ℝ}
    (ha : a ∈ Set.Icc (0 : ℝ) 1) (hr : 0 ≤ r) (hs : 0 ≤ s) :
    tangentDist h o (segment h o x a) y r s = tangentDist h o x y (r * a) s := by
  have ht : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have htp : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t := eventually_mem_nhdsWithin
  have htr : Tendsto (fun t : ℝ => t * r) (𝓝[>] 0) (𝓝 0) := by
    simpa using ht.mul_const r
  have he : (fun t : ℝ =>
      dist (segment h o (segment h o x a) (t * r)) (segment h o y (t * s)) / t)
      =ᶠ[𝓝[>] 0] (fun t : ℝ =>
      dist (segment h o x (t * (r * a))) (segment h o y (t * s)) / t) := by
    filter_upwards [htp, htr.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1))]
      with t ht' htr'
    rw [segment_mul h o x ⟨mul_nonneg ht'.le hr, htr'⟩ ha, mul_assoc]
  exact tendsto_nhds_unique ((tangentDist_tendsto h o (segment h o x a) y hr hs).congr' he)
    (tangentDist_tendsto h o x y (mul_nonneg hr ha.1) hs)

/-- Metric form of the log comparison, for any common radial factor. -/
theorem tangentDist_le (h : CATZero X) (o x y : X) {r : ℝ} (hr : 0 ≤ r) :
    tangentDist h o x y r r ≤ r * dist x y := by
  have ht : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have htp : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t := eventually_mem_nhdsWithin
  have htr : Tendsto (fun t : ℝ => t * r) (𝓝[>] 0) (𝓝 0) := by
    simpa using ht.mul_const r
  apply le_of_tendsto_of_tendsto (tangentDist_tendsto h o x y hr hr) tendsto_const_nhds
  filter_upwards [htp, htr.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1))]
    with t ht' htr'
  apply (div_le_iff₀ ht').mpr
  calc
    dist (segment h o x (t * r)) (segment h o y (t * r)) ≤ (t * r) * dist x y :=
      radial_contraction h o x y ⟨mul_nonneg ht'.le hr, htr'⟩
    _ = (r * dist x y) * t := by ring

end CATZero
end HyperbolicObstruction

noncomputable section
namespace HyperbolicObstruction
open Filter Topology UniformSpace
open scoped NNReal
variable {X : Type*} [MetricSpace X]

/-- Represented directions with an arbitrary nonnegative radial length factor.
Zero-distance representatives are identified by the Hausdorff completion. -/
structure TangentRay (h : CATZero X) (o : X) where
  weight : ℝ≥0
  point : X

namespace TangentRay
variable (h : CATZero X) (o : X)

instance instPseudoMetricSpace : PseudoMetricSpace (TangentRay h o) where
  dist p q := CATZero.tangentDist h o p.point q.point p.weight q.weight
  dist_self p := by rw [CATZero.tangentDist_same]; simp
  dist_comm p q := CATZero.tangentDist_comm h o p.point q.point p.weight q.weight
  dist_triangle p q r := CATZero.tangentDist_triangle h o p.point q.point r.point
    p.weight.coe_nonneg q.weight.coe_nonneg r.weight.coe_nonneg

def scale (r : ℝ≥0) (p : TangentRay h o) : TangentRay h o := ⟨r * p.weight, p.point⟩

theorem dist_def (p q : TangentRay h o) :
    dist p q = CATZero.tangentDist h o p.point q.point p.weight q.weight := rfl

theorem quadrilateral (a b c d : TangentRay h o) :
    dist a c ^ 2 + dist b d ^ 2 ≤
      dist a b ^ 2 + dist b c ^ 2 + dist c d ^ 2 + dist d a ^ 2 :=
  CATZero.tangentDist_quadrilateral h o a.point b.point c.point d.point
    a.weight.coe_nonneg b.weight.coe_nonneg c.weight.coe_nonneg d.weight.coe_nonneg

end TangentRay

/-- The completed cone of represented directions, built from radial CAT(0)
comparison limits rather than postulated to exist. -/
abbrev TangentCone (h : CATZero X) (o : X) := Completion (TangentRay h o)


end HyperbolicObstruction
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_TangentCone
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped Topology ContinuousMap
noncomputable section
noncomputable section
noncomputable section
noncomputable section
namespace HyperbolicObstruction
open Filter Topology UniformSpace
open scoped NNReal
variable {X : Type*} [MetricSpace X]

namespace TangentCone
variable (h : CATZero X) (o : X)

def scaleN (r : ℝ≥0) : TangentCone h o → TangentCone h o :=
  Completion.map (TangentRay.scale h o r)

@[fun_prop] theorem continuous_scaleN (r : ℝ≥0) : Continuous (scaleN h o r) := Completion.continuous_map

end TangentCone
end HyperbolicObstruction

noncomputable section
namespace HyperbolicObstruction
open Filter Topology UniformSpace
open scoped NNReal

/-- Quadrilateral comparison and approximate midpoints give a convergent
midpoint sequence in a complete metric space. -/
theorem midpoint_limit {Y : Type*} [MetricSpace Y] [CompleteSpace Y]
    (quad : ∀ a b c d : Y, dist a c ^ 2 + dist b d ^ 2 ≤
      dist a b ^ 2 + dist b c ^ 2 + dist c d ^ 2 + dist d a ^ 2)
    (x y : Y) (u : ℕ → Y) (b : ℕ → ℝ)
    (hb : Tendsto b atTop (𝓝 (dist x y)))
    (hu : ∀ᶠ n in atTop, dist x (u n) ≤ b n / 2 ∧ dist y (u n) ≤ b n / 2) :
    ∃ m, Tendsto u atTop (𝓝 m) ∧ dist x m = dist x y / 2 ∧
      dist y m = dist x y / 2 := by
  have hc : CauchySeq u := by
    apply Metric.cauchySeq_iff.mpr
    intro ε hε
    have hev : ∀ᶠ n in atTop, b n ^ 2 < dist x y ^ 2 + ε ^ 2 :=
      (hb.pow 2).eventually (gt_mem_nhds (by nlinarith [sq_pos_of_pos hε]))
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hu.and hev)
    refine ⟨N, ?_⟩
    intro i hi j hj
    obtain ⟨⟨hix, hiy⟩, hbi⟩ := hN i hi
    obtain ⟨⟨hjx, hjy⟩, hbj⟩ := hN j hj
    have hq := quad x (u i) y (u j)
    rw [dist_comm (u i) y, dist_comm (u j) x] at hq
    have hix' := sq_le_sq₀ (dist_nonneg (x := x) (y := u i))
      (le_trans dist_nonneg hix) |>.mpr hix
    have hiy' := sq_le_sq₀ (dist_nonneg (x := y) (y := u i))
      (le_trans dist_nonneg hiy) |>.mpr hiy
    have hjx' := sq_le_sq₀ (dist_nonneg (x := x) (y := u j))
      (le_trans dist_nonneg hjx) |>.mpr hjx
    have hjy' := sq_le_sq₀ (dist_nonneg (x := y) (y := u j))
      (le_trans dist_nonneg hjy) |>.mpr hjy
    nlinarith [dist_nonneg (x := u i) (y := u j)]
  obtain ⟨m, hm⟩ := cauchySeq_tendsto_of_complete hc
  have hx : dist x m ≤ dist x y / 2 :=
    le_of_tendsto_of_tendsto (tendsto_const_nhds.dist hm) (hb.div_const 2)
      (hu.mono fun _ hh => hh.1)
  have hy : dist y m ≤ dist x y / 2 :=
    le_of_tendsto_of_tendsto (tendsto_const_nhds.dist hm) (hb.div_const 2)
      (hu.mono fun _ hh => hh.2)
  have ht := dist_triangle x m y
  rw [dist_comm m y] at ht
  exact ⟨m, hm, by linarith, by linarith⟩

namespace TangentCone
variable {X : Type*} [MetricSpace X] (h : CATZero X) (o : X)

def atScale (k : ℝ) (p : TangentRay h o) : X :=
  CATZero.segment h o p.point (k * (p.weight : ℝ))

def rescale (k : ℝ) (x : X) : TangentCone h o :=
  (⟨Real.toNNReal k⁻¹, x⟩ : TangentRay h o)

theorem rescale_atScale {k : ℝ} (hk : 0 < k) (p : TangentRay h o)
    (hp : k * (p.weight : ℝ) ≤ 1) : rescale h o k (atScale h o k p) = p := by
  apply dist_eq_zero.mp
  rw [rescale, Completion.dist_eq, TangentRay.dist_def]
  dsimp only [atScale]
  rw [Real.coe_toNNReal _ (le_of_lt (inv_pos.mpr hk)),
    CATZero.tangentDist_radial_left h o p.point p.point
      ⟨mul_nonneg hk.le p.weight.coe_nonneg, hp⟩ (inv_nonneg.mpr hk.le)
      p.weight.coe_nonneg]
  rw [← mul_assoc, inv_mul_cancel₀ hk.ne', one_mul, CATZero.tangentDist_same]
  simp

theorem dist_rescale_le {k : ℝ} (hk : 0 < k) (x y : X) :
    dist (rescale h o k x) (rescale h o k y) ≤ dist x y / k := by
  rw [rescale, rescale, Completion.dist_eq, TangentRay.dist_def]
  dsimp only
  rw [Real.coe_toNNReal _ (inv_nonneg.mpr hk.le)]
  simpa only [div_eq_mul_inv, mul_comm] using
    CATZero.tangentDist_le h o x y (inv_nonneg.mpr hk.le)

def shrink (n : ℕ) : ℝ := 1 / (n + 1 : ℝ)

theorem shrink_pos (n : ℕ) : 0 < shrink n := by
  unfold shrink
  positivity

theorem shrink_tendsto : Tendsto shrink atTop (𝓝[>] 0) := by
  apply tendsto_nhdsWithin_iff.mpr
  exact ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
    Filter.Eventually.of_forall shrink_pos⟩

theorem shrink_weight (p : TangentRay h o) :
    ∀ᶠ n in atTop, shrink n * (p.weight : ℝ) ≤ 1 := by
  have ht : Tendsto (fun n => shrink n * (p.weight : ℝ)) atTop (𝓝 0) := by
    simpa only [zero_mul] using (tendsto_nhds_of_tendsto_nhdsWithin shrink_tendsto).mul_const
      (p.weight : ℝ)
  exact ht.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1))

def approxMid (p q : TangentRay h o) (n : ℕ) : TangentCone h o :=
  rescale h o (shrink n) (CATZero.mid h (atScale h o (shrink n) p)
    (atScale h o (shrink n) q))

def approxDist (p q : TangentRay h o) (n : ℕ) : ℝ :=
  dist (atScale h o (shrink n) p) (atScale h o (shrink n) q) / shrink n

theorem approxDist_tendsto (p q : TangentRay h o) :
    Tendsto (approxDist h o p q) atTop (𝓝 (dist p q)) :=
  (CATZero.tangentDist_tendsto h o p.point q.point
    p.weight.coe_nonneg q.weight.coe_nonneg).comp shrink_tendsto

theorem approxMid_bound (p q : TangentRay h o) :
    ∀ᶠ n in atTop, dist (p : TangentCone h o) (approxMid h o p q n) ≤
        approxDist h o p q n / 2 ∧
      dist (q : TangentCone h o) (approxMid h o p q n) ≤ approxDist h o p q n / 2 := by
  filter_upwards [shrink_weight h o p, shrink_weight h o q] with n hp hq
  constructor
  · rw [← rescale_atScale h o (shrink_pos n) p hp]
    have hh := dist_rescale_le h o (shrink_pos n) (atScale h o (shrink n) p)
      (CATZero.mid h (atScale h o (shrink n) p) (atScale h o (shrink n) q))
    rw [CATZero.dist_left_mid] at hh
    exact hh.trans_eq (by unfold approxDist; ring)
  · rw [← rescale_atScale h o (shrink_pos n) q hq]
    have hh := dist_rescale_le h o (shrink_pos n) (atScale h o (shrink n) q)
      (CATZero.mid h (atScale h o (shrink n) p) (atScale h o (shrink n) q))
    rw [dist_comm (atScale h o (shrink n) q), CATZero.dist_mid_right] at hh
    exact hh.trans_eq (by unfold approxDist; ring)

theorem quadrilateral (a b c d : TangentCone h o) :
    dist a c ^ 2 + dist b d ^ 2 ≤
      dist a b ^ 2 + dist b c ^ 2 + dist c d ^ 2 + dist d a ^ 2 := by
  induction a using Completion.induction_on with
  | hp => apply isClosed_le <;> fun_prop
  | ih a =>
    induction b, c, d using Completion.induction_on₃ with
    | hp => apply isClosed_le <;> fun_prop
    | ih b c d =>
      simpa only [Completion.dist_eq] using TangentRay.quadrilateral h o a b c d

theorem represented_midpoint_limit (p q : TangentRay h o) :
    ∃ m : TangentCone h o, Tendsto (approxMid h o p q) atTop (𝓝 m) ∧
      dist (p : TangentCone h o) m = dist p q / 2 ∧
      dist (q : TangentCone h o) m = dist p q / 2 := by
  simpa only [Completion.dist_eq] using midpoint_limit (quadrilateral h o)
    (p : TangentCone h o) (q : TangentCone h o) (approxMid h o p q) (approxDist h o p q)
    (by simpa only [Completion.dist_eq] using approxDist_tendsto h o p q)
    (approxMid_bound h o p q)


theorem approxMid_cn (p q z : TangentRay h o) :
    ∀ᶠ n in atTop, dist (z : TangentCone h o) (approxMid h o p q n) ^ 2 ≤
      (approxDist h o z p n ^ 2 + approxDist h o z q n ^ 2) / 2 -
        approxDist h o p q n ^ 2 / 4 := by
  filter_upwards [shrink_weight h o z] with n hz
  rw [← rescale_atScale h o (shrink_pos n) z hz]
  apply (sq_le_sq₀ dist_nonneg (div_nonneg dist_nonneg (shrink_pos n).le) |>.mpr
    (dist_rescale_le h o (shrink_pos n) (atScale h o (shrink n) z)
      (CATZero.mid h (atScale h o (shrink n) p) (atScale h o (shrink n) q)))).trans
  have hc := div_le_div_of_nonneg_right
    (CATZero.mid_cn h (atScale h o (shrink n) p) (atScale h o (shrink n) q)
      (atScale h o (shrink n) z)) (sq_nonneg (shrink n))
  convert hc using 1
  · simp only [div_pow]
  · simp only [approxDist, div_pow]
    ring

theorem exists_represented_mid (p q : TangentRay h o) :
    ∃ m : TangentCone h o,
      dist (p : TangentCone h o) m = dist p q / 2 ∧
      dist (q : TangentCone h o) m = dist p q / 2 ∧
      ∀ z : TangentCone h o, dist z m ^ 2 ≤
        (dist z p ^ 2 + dist z q ^ 2) / 2 - dist p q ^ 2 / 4 := by
  obtain ⟨m, hm, hmp, hmq⟩ := represented_midpoint_limit h o p q
  refine ⟨m, hmp, hmq, ?_⟩
  intro z
  induction z using Completion.induction_on with
  | hp => apply isClosed_le <;> fun_prop
  | ih z =>
    have ht := (((approxDist_tendsto h o z p).pow 2).add
      ((approxDist_tendsto h o z q).pow 2)).div_const 2
    have ht' := ((approxDist_tendsto h o p q).pow 2).div_const 4
    have hl := le_of_tendsto_of_tendsto ((tendsto_const_nhds.dist hm).pow 2)
      (ht.sub ht') (approxMid_cn h o p q z)
    simpa only [Completion.dist_eq] using hl

def representedMid (p q : TangentRay h o) : TangentCone h o :=
  (exists_represented_mid h o p q).choose

def coneMid : TangentCone h o → TangentCone h o → TangentCone h o :=
  Completion.extension₂ (representedMid h o)

@[fun_prop] theorem continuous_coneMid :
    Continuous (fun p : TangentCone h o × TangentCone h o => coneMid h o p.1 p.2) :=
  (Completion.uniformContinuous_extension₂ (representedMid h o)).uniformContinuous.continuous

end TangentCone
end HyperbolicObstruction

end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_ConeData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped Topology ContinuousMap
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section

noncomputable section
namespace HyperbolicObstruction

namespace CATZero
variable {X : Type*} [MetricSpace X]

/-- Restricting a chosen CAT(0) segment gives the chosen segment, including
reversed subsegments. -/
theorem segment_between (h : CATZero X) (x y : X) {s u t : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) 1) (hu : u ∈ Set.Icc (0 : ℝ) 1)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    segment h (segment h x y s) (segment h x y u) t =
      segment h x y ((1 - t) * s + t * u) := by
  have hm : (1 - t) * s + t * u ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact add_nonneg (mul_nonneg (sub_nonneg.mpr ht.2) hs.1) (mul_nonneg ht.1 hu.1)
    · nlinarith [mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr hs.2),
        mul_nonneg ht.1 (sub_nonneg.mpr hu.2)]
  symm
  apply eq_segment_of_dist h ht
  · rw [(segment_spec h x y).2.2 s hs _ hm, (segment_spec h x y).2.2 s hs u hu]
    rw [show s - ((1 - t) * s + t * u) = t * (s - u) by ring, abs_mul,
      abs_of_nonneg ht.1]
    ring
  · rw [(segment_spec h x y).2.2 _ hm u hu, (segment_spec h x y).2.2 s hs u hu]
    rw [show (1 - t) * s + t * u - u = (1 - t) * (s - u) by ring, abs_mul,
      abs_of_nonneg (sub_nonneg.mpr ht.2)]
    ring

/-- A nonexpanding map that preserves one endpoint distance preserves the
whole parametrized segment between those endpoints. -/
theorem map_segment_of_dist {Y : Type*} [MetricSpace Y] (hX : CATZero X) (hY : CATZero Y)
    (f : X → Y) (hf : ∀ a b, dist (f a) (f b) ≤ dist a b)
    (x y : X) (hxy : dist (f x) (f y) = dist x y) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    f (segment hX x y t) = segment hY (f x) (f y) t := by
  have hx := hf x (segment hX x y t)
  have hy := hf (segment hX x y t) y
  rw [segment_left hX x y ht, ← hxy] at hx
  rw [segment_right hX x y ht, ← hxy] at hy
  have htri := dist_triangle (f x) (f (segment hX x y t)) (f y)
  exact eq_segment_of_dist hY ht (by linarith) (by linarith)

end CATZero
end HyperbolicObstruction

noncomputable section

noncomputable section
namespace HyperbolicObstruction
namespace CATZero
variable {X : Type*} [MetricSpace X]

theorem segment_reverse (h : CATZero X) (x y : X) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) : segment h y x (1 - t) = segment h x y t := by
  have hs := segment_between h x y (s := 1) (u := 0) (t := 1 - t)
    (by norm_num) (by norm_num) ⟨by linarith [ht.2], by linarith [ht.1]⟩
  simpa only [(segment_spec h x y).1, (segment_spec h x y).2.1,
    sub_sub_cancel, mul_one, mul_zero, add_zero] using hs

theorem mid_swap (h : CATZero X) (x y : X) : mid h y x = mid h x y := by
  have he := segment_reverse h x y (t := 1 / 2) (by norm_num)
  norm_num at he
  exact he

end CATZero

end HyperbolicObstruction

end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_GeometricAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped Topology ContinuousMap
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section

namespace HyperbolicObstruction
namespace CATZero
variable {X : Type*} [MetricSpace X]

theorem dist_mid_mid_le (h : CATZero X) (a b c d : X) :
    dist (mid h a b) (mid h c d) ≤ (dist a c + dist b d) / 2 := by
  have h₁ := radial_contraction h a b d (t := 1 / 2) (by norm_num)
  have h₂ := radial_contraction h d a c (t := 1 / 2) (by norm_num)
  change dist (mid h a b) (mid h a d) ≤ _ at h₁
  change dist (mid h d a) (mid h d c) ≤ _ at h₂
  rw [mid_swap h a d, mid_swap h c d] at h₂
  have ht := dist_triangle (mid h a b) (mid h a d) (mid h c d)
  linarith

end CATZero

end HyperbolicObstruction

noncomputable section

noncomputable section

noncomputable section
namespace HyperbolicObstruction
open scoped BigOperators

namespace ConeData
variable {X : Type*} [MetricSpace X] (T : ConeData X)

/-- The ordered inductive mean, with the harmless value vertex for an empty
list. For a list of length j+1, append its last point with weight 1/(j+1). -/
def inductiveMean (T : ConeData X) (h : CATZero X) : (n : ℕ) → (Fin n → X) → X
  | 0, _ => T.vertex
  | n + 1, v => CATZero.segment h
      (inductiveMean T h n (fun i => v i.castSucc)) (v (Fin.last n)) (1 / (n + 1 : ℝ))

end ConeData
end HyperbolicObstruction

noncomputable section
namespace HyperbolicObstruction
open scoped BigOperators

/-- A finite probability law, retaining real weights for the conditional
couplings. Uniform laws are exactly the table match distributions. -/
structure FiniteLaw (α : Type*) [Fintype α] where
  mass : α → ℝ
  nonneg : ∀ a, 0 ≤ mass a
  sum_one : (∑ a, mass a) = 1

namespace FiniteLaw
variable {α β : Type*} [Fintype α] [Fintype β]

def expect (μ : FiniteLaw α) (f : α → ℝ) : ℝ := ∑ a, μ.mass a * f a

theorem expect_const (μ : FiniteLaw α) (c : ℝ) : μ.expect (fun _ => c) = c := by
  rw [expect, ← Finset.sum_mul, μ.sum_one, one_mul]

theorem expect_add (μ : FiniteLaw α) (f g : α → ℝ) :
    μ.expect (fun a => f a + g a) = μ.expect f + μ.expect g := by
  simp [expect, mul_add, Finset.sum_add_distrib]

theorem expect_sub (μ : FiniteLaw α) (f g : α → ℝ) :
    μ.expect (fun a => f a - g a) = μ.expect f - μ.expect g := by
  simp [expect, mul_sub, Finset.sum_sub_distrib]

theorem expect_mul (μ : FiniteLaw α) (c : ℝ) (f : α → ℝ) :
    μ.expect (fun a => c * f a) = c * μ.expect f := by
  simp [expect, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem expect_mono (μ : FiniteLaw α) {f g : α → ℝ} (hle : ∀ a, f a ≤ g a) :
    μ.expect f ≤ μ.expect g :=
  Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hle a) (μ.nonneg a)

end FiniteLaw
end HyperbolicObstruction

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_FiniteLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped Topology ContinuousMap
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section

noncomputable section

noncomputable section
namespace HyperbolicObstruction
namespace CATZero
variable {X : Type*} [MetricSpace X]

/-- The exact equality case of the quadrilateral inequality, also used for
hexagons whose diagonals have squared length at least three. -/
theorem quadrilateral_saturation (h : CATZero X) (a b c d : X) (r s : ℝ)
    (hac : r ≤ dist a c ^ 2) (hbd : s ≤ dist b d ^ 2)
    (hsides : dist a b ^ 2 + dist b c ^ 2 + dist c d ^ 2 + dist d a ^ 2 = r + s) :
    dist a c ^ 2 = r ∧ dist b d ^ 2 = s ∧ mid h a c = mid h b d := by
  have hq := quadrilateral h a b c d
  rw [hsides] at hq
  have hn := sq_nonneg (dist (mid h a c) (mid h b d))
  refine ⟨by linarith, by linarith, ?_⟩
  apply dist_eq_zero.mp
  nlinarith [dist_nonneg (x := mid h a c) (y := mid h b d)]

end CATZero

end HyperbolicObstruction

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_MetricHexagon
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped Topology ContinuousMap
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section


noncomputable section
namespace HyperbolicObstruction
namespace IncidenceTemplate
open scoped BigOperators

/-- Points A,B,C,D followed by the three remaining nonzero vectors. -/
def vector : Fin 7 → Fin 3 → ZMod 2 :=
  ![![1,0,0], ![0,1,0], ![0,0,1], ![1,1,1], ![1,1,0], ![1,0,1], ![0,1,1]]

/-- Lines are the kernels of the seven nonzero linear functionals. -/
def Incident (i l : Fin 7) : Prop := ∑ j, vector i j * vector l j = 0

instance instDecidableIncident (i l : Fin 7) : Decidable (Incident i l) := inferInstanceAs (Decidable (_ = _))

/-- X representatives occupy 0,...,6 and the four Y representatives 7,...,10. -/
def pointOfRepresentative (r : Fin 11) : Fin 7 :=
  if h : r.val < 7 then ⟨r.val, h⟩ else ⟨r.val - 7, by omega⟩

end IncidenceTemplate
namespace CoreGeometry
open IncidenceTemplate
abbrev Vertex := Fin 11 ⊕ Fin 7

end CoreGeometry
end HyperbolicObstruction


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_Template
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction
namespace IncidenceTemplate
open scoped BigOperators
/-- All incidences except Y_D--CD. Both sides have fixed named positions. -/
abbrev Edge := {p : Fin 11 × Fin 7 // Incident (pointOfRepresentative p.1) p.2 ∧ p ≠ (10,4)}

def isLoose (e : Edge) : Prop := e.val = (3,4)

instance instDecidableIsLoose (e : Edge) : Decidable (isLoose e) := inferInstanceAs (Decidable (_ = _))

def fan (i : Fin 7) : Finset Edge :=
  Finset.univ.filter (fun e => pointOfRepresentative e.val.1 = i ∧ ¬isLoose e)

def code (e : Edge) : ℕ := 7 * e.val.1.val + e.val.2.val

/-- One canonical orientation of each unoriented nonbacktracking two-edge path. -/
abbrev TwoPath := {p : Edge × Edge // code p.1 < code p.2 ∧
  (p.1.val.1 = p.2.val.1 ∨ p.1.val.2 = p.2.val.2)}

abbrev Field := Edge ⊕ (TwoPath × Fin 2)

instance instFieldDecidableEq : DecidableEq Field := instDecidableEqSum


/-- The four coordinates of a square row: two core fields and two private ones. -/
def squareSupport (τ : TwoPath) : Finset Field :=
  {Sum.inl τ.val.1, Sum.inl τ.val.2, Sum.inr (τ, 0), Sum.inr (τ, 1)}

end IncidenceTemplate
end HyperbolicObstruction
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_CoreFan
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction
namespace CoreGeometry
open IncidenceTemplate

/-- The actual vertices of the seven fan templates. The punctured D fan has
only its two non-CD ports. All representatives of its point are retained. -/
def IsFanVertex (i : Fin 7) : Vertex → Prop
  | .inl r => pointOfRepresentative r = i
  | .inr l => Incident i l ∧ (i,l) ≠ (3,4)

instance instDecidableIsFanVertex (i : Fin 7) (v : Vertex) : Decidable (IsFanVertex i v) := by
  cases v <;> unfold IsFanVertex <;> infer_instance

abbrev FanVertex (i : Fin 7) := {v : Vertex // IsFanVertex i v}

lemma card_fanVertex : ∀ i : Fin 7, Fintype.card (FanVertex i) = ![5,5,5,4,4,4,4] i := by
  decide

lemma card_fanVertex_le (i : Fin 7) : Fintype.card (FanVertex i) ≤ 5 := by
  rw [card_fanVertex]; fin_cases i <;> decide

lemma edge_fan_vertices (e : Edge) (i : Fin 7) (h : e ∈ fan i) :
    IsFanVertex i (.inl e.val.1) ∧ IsFanVertex i (.inr e.val.2) := by
  have certificate : ∀ (e : Edge) (i : Fin 7), e ∈ fan i →
      IsFanVertex i (.inl e.val.1) ∧ IsFanVertex i (.inr e.val.2) := by decide
  exact certificate e i h

def linePart : Vertex → Bool
  | .inl _ => false
  | .inr _ => true

end CoreGeometry
end HyperbolicObstruction
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_PermSwitch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
variable {D : Type*} [DecidableEq D]

section Finite
variable [Fintype D]

/-- Number of darts minus number of vertex cycles, including singleton cycles.
The integer form avoids artificial truncated-subtraction side conditions. -/
def defect (p : Perm D) : ℤ := p.support.card - p.cycleType.card

def cycles (p : Perm D) : ℤ := Fintype.card D - defect p

end Finite
end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_PermEuler
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {D : Type*} [DecidableEq D] [Fintype D]

omit [DecidableEq D] in
lemma sameCycle_le_of_apply {p : Perm D} {s : Setoid D}
    (h : ∀ x, s x (p x)) : SameCycle.setoid p ≤ s := by
  intro a b hab
  obtain ⟨n,rfl⟩ := hab.exists_nat_pow_eq
  clear hab
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ',mul_apply]
    exact s.trans' ih (h _)

end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_PictureMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
variable {D : Type*}

/-- Oriented polygonal side-pairings (darts are individually indexed sides).
`face` turns around each polygon; `edge` pairs sides with opposite orientation.
Vertices are the cycles of `face * edge`, so no abstract vertex incidences or
Euler changes are supplied as hypotheses. -/
structure PictureMap (D : Type*) where
  face : Perm D
  edge : Perm D
  edge_sq : edge * edge = 1
  edge_ne : ∀ d, edge d ≠ d

namespace PictureMap
variable (M : PictureMap D)

def vertex : Perm D := M.face * M.edge

lemma edge_edge (x : D) : M.edge (M.edge x) = x := by
  have h := congrArg (fun p : Perm D => p x) M.edge_sq
  exact h

variable [DecidableEq D]

/-- Crosswise re-pairing of the two specified outgoing sides. All original
face cycles (hence all original corners and their maps) are unchanged. -/
def switch (a b : D) : PictureMap D where
  face := M.face
  edge := swap a b * M.edge * swap a b
  edge_sq := by
    calc
      _ = swap a b * M.edge * (swap a b * swap a b) * M.edge * swap a b := by group
      _ = swap a b * (M.edge * M.edge) * swap a b := by rw [swap_mul_self,mul_one,mul_assoc (swap a b) M.edge M.edge]
      _ = 1 := by rw [M.edge_sq]; simp
  edge_ne := by
    intro d he
    have hh := congrArg (swap a b) he
    have hz : M.edge (swap a b d) = swap a b d := by
      simpa only [mul_apply,swap_apply_self] using hh
    exact M.edge_ne _ hz

@[simp] lemma switch_face (a b : D) : (M.switch a b).face = M.face := rfl

section Finite
variable [Fintype D]

def euler : ℤ := cycles M.vertex + cycles M.face - (Fintype.card D : ℤ) / 2

end Finite
end PictureMap
end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_PictureEuler
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
variable {D : Type*} [DecidableEq D] [Fintype D]

namespace PictureMap
variable (M : PictureMap D)

/-- Connected components of the actual polygon identifications on darts. -/
def components : Setoid D := SameCycle.setoid M.vertex ⊔ SameCycle.setoid M.edge

/-- Combinatorial genus zero, expressed directly on the actual side-pairing.
This definition neither asserts nor replaces a topological realization. -/
def GenusZero : Prop := M.euler = 2 * (Nat.card (Quotient M.components) : ℤ)

end PictureMap
end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_MappedPicture
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {D : Type*} [DecidableEq D] [Fintype D]

namespace PictureMap

omit [DecidableEq D] [Fintype D] in
@[ext] lemma ext {M N : PictureMap D} (hf : M.face = N.face) (he : M.edge = N.edge) : M = N := by
  cases M
  cases N
  cases hf
  cases he
  rfl

variable {L V : Type*}

/-- Literal oriented-edge and vertex labels into any target one-skeleton.
The vertex label of a dart is the initial vertex of its oriented edge label.
No filling or normal-form conclusion is included in this compatibility. -/
def Respects (M : PictureMap D) (label : D → L) (start : L → V) (rev : L → L) : Prop :=
  (∀ d, start (label (M.vertex d)) = start (label d)) ∧
    ∀ d, label (M.edge d) = rev (label d)

end PictureMap
end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_ConditionalStar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped Topology ContinuousMap
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
open scoped BigOperators ENNReal
noncomputable section
noncomputable section
open Filter Topology
noncomputable section
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
open Filter Topology

namespace HyperbolicObstruction

/-- A conditional star: branches agree exactly on the named fields.
The finite law placed on it below need not be uniform. -/
def ConditionalStar {F L Ω : Type*} [DecidableEq F] (label : Ω → F → L)
    (I : Finset F) (k : ℕ) :=
  {b : Fin (k + 1) → Ω // ∀ j i, i ∈ I → label (b j) i = label (b 0) i}

namespace ConditionalStar
variable {F L Ω : Type*} [DecidableEq F] {label : Ω → F → L} {I : Finset F} {k : ℕ}
instance instFintypeOfDecidableEq [Fintype Ω] [DecidableEq L] : Fintype (ConditionalStar label I k) :=
  inferInstanceAs (Fintype {branches : Fin (k + 1) → Ω //
    ∀ branch field, field ∈ I → label (branches branch) field = label (branches 0) field})

def branch (j : Fin (k + 1)) (b : ConditionalStar label I k) : Ω := b.val j

end ConditionalStar

end HyperbolicObstruction


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_Graph
attribute [-instance] _root_.OAI.HyperbolicObstruction.CoreGeometry.instDecidableIsFanVertex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction
namespace MasterGraph
open IncidenceTemplate
abbrev Vertex := CoreGeometry.Vertex ⊕ TwoPath

def left (τ : TwoPath) : CoreGeometry.Vertex :=
  if τ.val.1.val.1 = τ.val.2.val.1 then .inr τ.val.1.val.2 else .inl τ.val.1.val.1
def middle (τ : TwoPath) : CoreGeometry.Vertex :=
  if τ.val.1.val.1 = τ.val.2.val.1 then .inl τ.val.1.val.1 else .inr τ.val.1.val.2
def right (τ : TwoPath) : CoreGeometry.Vertex :=
  if τ.val.1.val.1 = τ.val.2.val.1 then .inr τ.val.2.val.2 else .inl τ.val.2.val.1

def source : Field → Vertex
  | .inl e => .inl (.inl e.val.1)
  | .inr (τ, j) => if j = 0 then .inl (right τ) else .inr τ

def target : Field → Vertex
  | .inl e => .inl (.inr e.val.2)
  | .inr (τ, j) => if j = 0 then .inr τ else .inl (left τ)

/-- An oriented traversal of one of the fixed master fields. -/
structure Step (a b : Vertex) where
  field : Field
  forward : Bool
  endpoints : if forward then source field = a ∧ target field = b
    else target field = a ∧ source field = b

/-- The actual two core sides of a decoration. -/
def first (τ : TwoPath) : Step (.inl (left τ)) (.inl (middle τ)) :=
  ⟨.inl τ.val.1, if τ.val.1.val.1 = τ.val.2.val.1 then false else true, by
    by_cases h : τ.val.1.val.1 = τ.val.2.val.1 <;>
      simp [h, source, target, left, middle]⟩

def second (τ : TwoPath) : Step (.inl (middle τ)) (.inl (right τ)) :=
  ⟨.inl τ.val.2, if τ.val.1.val.1 = τ.val.2.val.1 then true else false, by
    by_cases h : τ.val.1.val.1 = τ.val.2.val.1
    · simp [h, source, target, middle, right]
    · have he := τ.property.2.resolve_left h
      simp [h, he, source, target, middle, right]⟩

end MasterGraph
end HyperbolicObstruction
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_Random
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction
open scoped BigOperators
namespace FiniteLaw
variable {α : Type*} [Fintype α]
/-- Product of the independent Bernoulli trials in the source table model. -/
def bernoulliProduct {I : Type*} [Fintype I] [DecidableEq I] (p : I → ℝ)
    (hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1) : FiniteLaw (I → Bool) where
  mass w := ∏ i, if w i then p i else 1 - p i
  nonneg w := Finset.prod_nonneg (fun i _ => by
    split_ifs
    · exact (hp i).1
    · exact sub_nonneg.mpr (hp i).2)
  sum_one := by
    rw [← Fintype.prod_sum (fun i (b : Bool) => if b then p i else 1 - p i)]
    simp

lemma bernoulliProduct_expect_product {I : Type*} [Fintype I] [DecidableEq I] (p : I → ℝ)
    (hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1) (f : I → Bool → ℝ) :
    (bernoulliProduct p hp).expect (fun w => ∏ i, f i (w i)) =
      ∏ i, ((1 - p i) * f i false + p i * f i true) := by
  unfold expect bernoulliProduct
  simp only
  simp_rw [← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i (b : Bool) => (if b then p i else 1 - p i) * f i b)]
  simp [add_comm]

/-- Probability of simultaneous inclusion for any specified, distinct trials. -/
lemma bernoulliProduct_all {I : Type*} [Fintype I] [DecidableEq I]
    (p : I → ℝ) (hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1) (s : Finset I) :
    (bernoulliProduct p hp).expect (fun w => if ∀ i ∈ s, w i = true then 1 else 0) =
      ∏ i ∈ s, p i := by
  classical
  have hprod (w : I → Bool) :
      (if ∀ i ∈ s, w i = true then (1 : ℝ) else 0) =
        ∏ i, if i ∈ s → w i = true then (1 : ℝ) else 0 := by
    rw [Fintype.prod_boole]
  rw [show (fun w : I → Bool => if ∀ i ∈ s, w i = true then (1 : ℝ) else 0) =
      (fun w => ∏ i, if i ∈ s → w i = true then (1 : ℝ) else 0) from funext hprod]
  rw [bernoulliProduct_expect_product p hp (fun i b => if i ∈ s → b = true then 1 else 0)]
  calc
    _ = ∏ i, if i ∈ s then p i else 1 := by
      apply Finset.prod_congr rfl
      intro i _
      by_cases h : i ∈ s <;> simp [h]
    _ = ∏ i ∈ s, p i := by simp

/-- Probability, in real rather than ENNReal coordinates, of a finite event. -/
def prob (μ : FiniteLaw α) (E : α → Prop) [DecidablePred E] : ℝ :=
  μ.expect (fun a => if E a then 1 else 0)

/-- The finite union bound; no independence is assumed here. -/
lemma prob_exists_le {J : Type*} [Fintype J] (μ : FiniteLaw α)
    (E : J → α → Prop) [∀ j, DecidablePred (E j)] :
    μ.prob (fun a => ∃ j, E j a) ≤ ∑ j, μ.prob (E j) := by
  classical
  unfold prob expect
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro a _
  rw [← Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ (μ.nonneg a)
  by_cases h : ∃ j, E j a
  · obtain ⟨j, hj⟩ := h
    simp only [show ∃ j, E j a from ⟨j, hj⟩, ↓reduceIte]
    exact (Finset.single_le_sum (f := fun j => if E j a then (1 : ℝ) else 0)
      (fun j _ => by split_ifs <;> norm_num) (Finset.mem_univ j)).trans' (by simp [hj])
  · simp only [h, ↓reduceIte]
    exact Finset.sum_nonneg fun j _ => by split_ifs <;> norm_num

end FiniteLaw

namespace TableModel
variable {F R A : Type*} [Fintype F] [Fintype R] [Fintype A]
  [DecidableEq F] [DecidableEq R] [DecidableEq A]

/-- Each table has a distinct type, but all its coordinate fields use the same
alphabet. Coinciding numerical values at different fields are permitted. -/
abbrev Entry (support : R → Finset F) := Σ r, (support r → A)

def row (support : R → Finset F) (σ : F → A) (r : R) : Entry (A := A) support :=
  ⟨r, fun j => σ j⟩

end TableModel
end HyperbolicObstruction

noncomputable section

noncomputable section
namespace HyperbolicObstruction
open scoped BigOperators
namespace TableModel
variable {F R A : Type*} [Fintype F] [Fintype R] [Fintype A]
  [DecidableEq F] [DecidableEq R] [DecidableEq A]

/-- Coincidence counting uses equality only within each coordinate field;
the letters in other fields range independently over the very same alphabet. -/
lemma sum_coincidence (σ : F → A) (W : Finset F) :
    (∑ τ : F → A, if ∀ i ∈ W, τ i = σ i then (1 : ℝ) else 0) =
      (Fintype.card A : ℝ) ^ (Fintype.card F - W.card) := by
  classical
  have he (τ : F → A) :
      (if ∀ i ∈ W, τ i = σ i then (1 : ℝ) else 0) =
      ∏ i, if i ∈ W → τ i = σ i then (1 : ℝ) else 0 := by
    rw [Fintype.prod_boole]
  simp_rw [he]
  rw [← Fintype.prod_sum (fun i (a : A) => if i ∈ W → a = σ i then (1 : ℝ) else 0)]
  calc
    _ = ∏ i : F, if i ∈ W then (1 : ℝ) else Fintype.card A := by
      apply Finset.prod_congr rfl
      intro i _
      by_cases hi : i ∈ W <;> simp [hi]
    _ = _ := by
      rw [Finset.prod_ite]
      simp [Finset.filter_not, Finset.card_sdiff_of_subset (Finset.subset_univ W)]

end TableModel
end HyperbolicObstruction
end
end
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_Moment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
open scoped BigOperators
namespace HyperbolicObstruction
namespace FiniteLaw
variable {α : Type*} [Fintype α]

def variance (μ : FiniteLaw α) (f : α → ℝ) : ℝ :=
  μ.expect (fun a => (f a - μ.expect f) ^ 2)

lemma variance_eq (μ : FiniteLaw α) (f : α → ℝ) :
    μ.variance f = μ.expect (fun a => f a ^ 2) - μ.expect f ^ 2 := by
  unfold variance
  simp_rw [sub_sq, show ∀ a, 2 * f a * μ.expect f = (2 * μ.expect f) * f a by intro a; ring]
  rw [μ.expect_add, μ.expect_sub, μ.expect_mul, μ.expect_const]
  ring

end FiniteLaw

end HyperbolicObstruction
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_Normalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
open scoped BigOperators
namespace HyperbolicObstruction
namespace FiniteLaw
variable {α β : Type*} [Fintype α] [Fintype β]

@[ext] lemma ext {μ ν : FiniteLaw α} (h : μ.mass = ν.mass) : μ = ν := by
  cases μ
  cases ν
  cases h
  rfl

end FiniteLaw
end HyperbolicObstruction
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_Chernoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
open scoped BigOperators
namespace HyperbolicObstruction
namespace FiniteLaw
variable {α : Type*} [Fintype α]

lemma prob_mono (μ : FiniteLaw α) {E F : α → Prop} [DecidablePred E] [DecidablePred F]
    (h : ∀ a, E a → F a) : μ.prob E ≤ μ.prob F := by
  apply μ.expect_mono
  intro a
  by_cases he : E a
  · simp [he,h a he]
  · simp [he]
    split_ifs <;> norm_num

end FiniteLaw
end HyperbolicObstruction
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_IncidenceTemplate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
namespace HyperbolicObstruction

namespace IncidenceTemplate

abbrev Row := Fin 7 ⊕ (Unit ⊕ TwoPath)

/-- The 98 distinct array types of the exact master pattern. -/
def rowSupport : Row → Finset Field
  | Sum.inl i => (fan i).map Function.Embedding.inl
  | Sum.inr (Sum.inl _) => Finset.univ.map Function.Embedding.inl
  | Sum.inr (Sum.inr τ) => squareSupport τ

end IncidenceTemplate
end HyperbolicObstruction
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_Concentration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
open scoped BigOperators
namespace HyperbolicObstruction
namespace TableModel
variable {F R A : Type*} [Fintype F] [Fintype R] [Fintype A]
  [DecidableEq F] [DecidableEq R] [DecidableEq A]

lemma powerProbability_pos {N : ℝ} (hN : 1 ≤ N) (c : ℝ) : 0 < N ^ (-c) :=
  Real.rpow_pos_of_pos (by linarith) _

end TableModel
end HyperbolicObstruction
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_GenericTable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
open scoped BigOperators
namespace HyperbolicObstruction
namespace BernoulliCandidates
variable {V S I A : Type*} [Fintype V] [Fintype S] [Fintype I] [Fintype A]
  [DecidableEq V] [DecidableEq S] [DecidableEq I] [DecidableEq A]

/-- Row positions of a candidate may belong to the same array. Actual trials,
not row positions, are the independent Bernoulli variables. -/
def Present (row : (V → A) → S → I) (w : I → Bool) (σ : V → A) : Prop :=
  ∀ s, w (row σ s) = true

instance instDecidablePresent (row : (V → A) → S → I) (w : I → Bool) (σ : V → A) :
    Decidable (Present row w σ) := inferInstanceAs (Decidable (∀ position, w (row σ position) = true))

def count (row : (V → A) → S → I) (C : Finset (V → A)) (w : I → Bool) : ℕ :=
  (C.filter (Present row w)).card

def shared (row : (V → A) → S → I) (σ τ : V → A) : Finset S :=
  Finset.univ.filter (fun s => ∃ r, row τ s = row σ r)

omit [Fintype V] [Fintype I] [Fintype A] [DecidableEq V] [DecidableEq S] [DecidableEq A] in
lemma shared_image (row : (V → A) → S → I) (σ τ : V → A) :
    (Finset.univ.image (row σ)) ∩ (Finset.univ.image (row τ)) =
      (shared row σ τ).image (row τ) := by
  classical
  ext i
  simp only [Finset.mem_inter, Finset.mem_image, Finset.mem_univ, true_and,
    shared, Finset.mem_filter]
  constructor
  · rintro ⟨⟨r,hr⟩,⟨s,hs⟩⟩
    exact ⟨s, ⟨r, hs.trans hr.symm⟩, hs⟩
  · rintro ⟨s, ⟨r,he⟩,hs⟩
    exact ⟨⟨r, he.symm.trans hs⟩,⟨s,hs⟩⟩

omit [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq S] [DecidableEq A] in
lemma prob_present (row : (V → A) → S → I) (p : I → ℝ)
    (hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1) (σ : V → A)
    (hi : Function.Injective (row σ)) :
    (FiniteLaw.bernoulliProduct p hp).prob (fun w => Present row w σ) =
      ∏ s, p (row σ s) := by
  classical
  have he (w : I → Bool) : Present row w σ ↔
      ∀ i ∈ Finset.univ.image (row σ), w i = true := by
    simp [Present]
  simp only [FiniteLaw.prob, he]
  rw [FiniteLaw.bernoulliProduct_all,
    Finset.prod_image (fun _ _ _ _ h => hi h)]

omit [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq S] [DecidableEq A] in
lemma prob_pair (row : (V → A) → S → I) (p : I → ℝ)
    (hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1) (σ τ : V → A)
    (hσ : Function.Injective (row σ)) (hτ : Function.Injective (row τ))
    (hpos : ∀ s, 0 < p (row τ s)) :
    (FiniteLaw.bernoulliProduct p hp).prob (fun w => Present row w σ ∧ Present row w τ) =
      (∏ s, p (row σ s)) * (∏ s, p (row τ s)) *
        (∏ s ∈ shared row σ τ, p (row τ s))⁻¹ := by
  classical
  have he (w : I → Bool) : Present row w σ ∧ Present row w τ ↔
      ∀ i ∈ Finset.univ.image (row σ) ∪ Finset.univ.image (row τ), w i = true := by
    simp only [Present, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hσ, hτ⟩ i (⟨r, hr⟩ | ⟨r, hr⟩)
      · simpa only [← hr] using hσ r
      · simpa only [← hr] using hτ r
    · intro hh
      exact ⟨fun r => hh _ (Or.inl ⟨r, rfl⟩), fun r => hh _ (Or.inr ⟨r, rfl⟩)⟩
  have hov : (∏ i ∈ (Finset.univ.image (row σ)) ∩ (Finset.univ.image (row τ)), p i) =
      ∏ s ∈ shared row σ τ, p (row τ s) := by
    rw [shared_image, Finset.prod_image (fun _ _ _ _ h => hτ h)]
  have hne : (∏ s ∈ shared row σ τ, p (row τ s)) ≠ 0 :=
    ne_of_gt (Finset.prod_pos (fun s _ => hpos s))
  apply (eq_mul_inv_iff_mul_eq₀ hne).mpr
  simp only [FiniteLaw.prob, he]
  rw [FiniteLaw.bernoulliProduct_all, ← hov, Finset.prod_union_inter,
    Finset.prod_image (fun _ _ _ _ h => hσ h),
    Finset.prod_image (fun _ _ _ _ h => hτ h)]

omit [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq S] [DecidableEq A] in
lemma expect_count (row : (V → A) → S → I) (p : I → ℝ)
    (hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1) (C : Finset (V → A))
    (hi : ∀ σ ∈ C, Function.Injective (row σ)) (q : S → ℝ)
    (hq : ∀ σ ∈ C, ∀ s, p (row σ s) = q s) :
    (FiniteLaw.bernoulliProduct p hp).expect (fun w => (count row C w : ℝ)) =
      C.card * ∏ s, q s := by
  classical
  have he (w : I → Bool) : (count row C w : ℝ) =
      ∑ σ ∈ C, if Present row w σ then 1 else 0 := by simp [count]
  simp_rw [he]
  unfold FiniteLaw.expect
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    _ = ∑ σ ∈ C, ∏ s, q s := by
      apply Finset.sum_congr rfl
      intro σ hσ
      change (FiniteLaw.bernoulliProduct p hp).prob _ = _
      rw [prob_present row p hp σ (hi σ hσ)]
      simp_rw [hq σ hσ]
    _ = _ := by simp

omit [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq S] [DecidableEq A] in
lemma variance_count (row : (V → A) → S → I) (p : I → ℝ)
    (hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1) (C : Finset (V → A))
    (hi : ∀ σ ∈ C, Function.Injective (row σ)) (q : S → ℝ) (hpos : ∀ s, 0 < q s)
    (hq : ∀ σ ∈ C, ∀ s, p (row σ s) = q s) :
    (FiniteLaw.bernoulliProduct p hp).variance (fun w => (count row C w : ℝ)) =
      (∏ s, q s) ^ 2 * ∑ σ ∈ C, ∑ τ ∈ C, ((∏ s ∈ shared row σ τ, q s)⁻¹ - 1) := by
  classical
  have hc (w : I → Bool) : (count row C w : ℝ) ^ 2 =
      ∑ σ ∈ C, ∑ τ ∈ C, if Present row w σ ∧ Present row w τ then 1 else 0 := by
    have hc : (count row C w : ℝ) = ∑ σ ∈ C, if Present row w σ then 1 else 0 := by simp [count]
    rw [hc, pow_two, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro σ _
    apply Finset.sum_congr rfl
    intro τ _
    by_cases hσ : Present row w σ <;> by_cases hτ : Present row w τ <;> simp [hσ,hτ]
  have hs : (FiniteLaw.bernoulliProduct p hp).expect (fun w => (count row C w : ℝ) ^ 2) =
      (∏ s, q s) ^ 2 * ∑ σ ∈ C, ∑ τ ∈ C, (∏ s ∈ shared row σ τ, q s)⁻¹ := by
    simp_rw [hc]
    unfold FiniteLaw.expect
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro σ hσ
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro τ hτ
    change (FiniteLaw.bernoulliProduct p hp).prob _ = _
    rw [prob_pair row p hp σ τ (hi σ hσ) (hi τ hτ)
      (fun s => by rw [hq τ hτ]; exact hpos s)]
    simp_rw [hq σ hσ, hq τ hτ]
    ring
  rw [FiniteLaw.variance_eq, hs, expect_count row p hp C hi q hq]
  simp_rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  ring

/-- A fixed, finite overcount of all nonempty matching types. Types with
incompatible coordinate constraints simply have zero realizations. -/
abbrev OverlapType (S : Type*) [Fintype S] := {J : Finset S // J.Nonempty} × (S → S)

def OverlapEvent (row : (V → A) → S → I) (σ τ : V → A) (o : OverlapType S) : Prop :=
  ∀ s ∈ o.1.val, row τ s = row σ (o.2 s)

instance instDecidableOverlapEvent (row : (V → A) → S → I) (σ τ : V → A) (o : OverlapType S) :
    Decidable (OverlapEvent row σ τ o) := inferInstanceAs (Decidable (∀ s ∈ o.1.val, _))

omit [Fintype V] [Fintype I] [Fintype A] [DecidableEq V] [DecidableEq A] in
lemma inverse_overlap_le (row : (V → A) → S → I) (σ τ : V → A)
    (q : S → ℝ) (hq : ∀ s, 0 < q s) :
    (∏ s ∈ shared row σ τ, q s)⁻¹ - 1 ≤
      ∑ o : OverlapType S, if OverlapEvent row σ τ o then (∏ s ∈ o.1.val, q s)⁻¹ else 0 := by
  classical
  have hn (o : OverlapType S) :
      0 ≤ if OverlapEvent row σ τ o then (∏ s ∈ o.1.val, q s)⁻¹ else 0 := by
    split_ifs
    · exact inv_nonneg.mpr (Finset.prod_nonneg fun s _ => (hq s).le)
    · norm_num
  by_cases he : (shared row σ τ).Nonempty
  · let f (s : S) : S := if hs : ∃ r, row τ s = row σ r then Classical.choose hs else s
    let o : OverlapType S := (⟨shared row σ τ, he⟩, f)
    have ho : OverlapEvent row σ τ o := by
      intro s hs
      have hh : ∃ r, row τ s = row σ r := (Finset.mem_filter.mp hs).2
      exact by simpa [o,f,hh] using Classical.choose_spec hh
    have hsingle := Finset.single_le_sum (fun o _ => hn o) (Finset.mem_univ o)
    simp only [ho, ↓reduceIte] at hsingle
    exact (sub_le_self _ zero_le_one).trans hsingle
  · rw [Finset.not_nonempty_iff_eq_empty.mp he]
    simp only [Finset.prod_empty, inv_one, sub_self]
    exact Finset.sum_nonneg fun o _ => hn o

omit [Fintype I] in
/-- Once one admissible second assignment is fixed, every other realization of
an overlap type agrees with it on the union of the selected row supports. This
is a counting fact, not an independence claim about different coordinate fields. -/
lemma overlap_assignment_count (row : (V → A) → S → I) (support : S → Finset V)
    (read : ∀ σ τ s, row σ s = row τ s → ∀ v ∈ support s, σ v = τ v)
    (C : Finset (V → A)) (σ : V → A) (o : OverlapType S) :
    (∑ τ ∈ C, if OverlapEvent row σ τ o then (1 : ℝ) else 0) ≤
      (Fintype.card A : ℝ) ^ (Fintype.card V - (o.1.val.biUnion support).card) := by
  classical
  by_cases he : ∃ τ ∈ C, OverlapEvent row σ τ o
  · obtain ⟨τ₀,hτ₀,he₀⟩ := he
    rw [← TableModel.sum_coincidence τ₀ (o.1.val.biUnion support)]
    calc
      _ ≤ ∑ τ ∈ C, if ∀ v ∈ o.1.val.biUnion support, τ v = τ₀ v then (1 : ℝ) else 0 := by
        apply Finset.sum_le_sum
        intro τ _
        by_cases hh : OverlapEvent row σ τ o
        · have hread : ∀ v ∈ o.1.val.biUnion support, τ v = τ₀ v := by
            intro v hv
            obtain ⟨s,hs,hv⟩ := Finset.mem_biUnion.mp hv
            exact read τ τ₀ s ((hh s hs).trans (he₀ s hs).symm) v hv
          rw [ite_eq_left hh, ite_eq_left hread]
        · simp only [hh, ↓reduceIte]
          split_ifs <;> norm_num
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ C)
        (fun _ _ _ => by split_ifs <;> norm_num)
  · have hz : ∀ τ ∈ C, ¬OverlapEvent row σ τ o := by simpa using he
    simp only [Finset.sum_eq_zero (fun τ hτ => ite_eq_right (hz τ hτ))]
    positivity

end BernoulliCandidates
end HyperbolicObstruction
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_GenericMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
open scoped BigOperators
namespace HyperbolicObstruction
namespace BernoulliCandidates
variable {V S I A : Type*} [Fintype V] [Fintype S] [Fintype I] [Fintype A]
  [DecidableEq V] [DecidableEq S] [DecidableEq I] [DecidableEq A]

omit [Fintype S] [DecidableEq S] in
lemma overlap_power_bound {N ε : ℝ} (hN : 1 ≤ N) (support : S → Finset V)
    (c : S → ℝ) (J : Finset S)
    (gap : ε ≤ ((J.biUnion support).card : ℝ) - ∑ s ∈ J, c s) :
    N ^ (Fintype.card V - (J.biUnion support).card) * (∏ s ∈ J, N ^ (-c s))⁻¹ ≤
      N ^ Fintype.card V * N ^ (-ε) := by
  have hN0 : 0 < N := by linarith
  have he : (∏ s ∈ J, N ^ (-c s))⁻¹ = N ^ (∑ s ∈ J, c s) := by
    rw [← Real.rpow_sum_of_pos hN0, Finset.sum_neg_distrib, Real.rpow_neg hN0.le, inv_inv]
  have hc := Finset.card_le_univ (J.biUnion support)
  rw [he, ← Real.rpow_natCast N (Fintype.card V - (J.biUnion support).card),
    ← Real.rpow_natCast N (Fintype.card V), ← Real.rpow_add hN0, ← Real.rpow_add hN0]
  apply Real.rpow_le_rpow_of_exponent_le hN
  rw [Nat.cast_sub hc]
  linarith

omit [Fintype I] in
lemma sum_inverse_overlap_power [Nonempty A] (row : (V → A) → S → I)
    (support : S → Finset V)
    (read : ∀ σ τ s, row σ s = row τ s → ∀ v ∈ support s, σ v = τ v)
    (C : Finset (V → A)) (σ : V → A) (c : S → ℝ) {ε : ℝ}
    (gap : ∀ J : Finset S, J.Nonempty →
      ε ≤ ((J.biUnion support).card : ℝ) - ∑ s ∈ J, c s) :
    (∑ τ ∈ C, ((∏ s ∈ shared row σ τ, (Fintype.card A : ℝ) ^ (-c s))⁻¹ - 1)) ≤
      Fintype.card (OverlapType S) * (Fintype.card A : ℝ) ^ Fintype.card V *
        (Fintype.card A : ℝ) ^ (-ε) := by
  classical
  have hn : (1 : ℝ) ≤ Fintype.card A := by
    exact_mod_cast (show 1 ≤ Fintype.card A from Fintype.card_pos)
  calc
    _ ≤ ∑ τ ∈ C, ∑ o : OverlapType S, if OverlapEvent row σ τ o then
        (∏ s ∈ o.1.val, (Fintype.card A : ℝ) ^ (-c s))⁻¹ else 0 := by
      apply Finset.sum_le_sum
      intro τ _
      exact inverse_overlap_le row σ τ _ (fun s => TableModel.powerProbability_pos hn (c s))
    _ = ∑ o : OverlapType S, (∑ τ ∈ C, if OverlapEvent row σ τ o then (1 : ℝ) else 0) *
        (∏ s ∈ o.1.val, (Fintype.card A : ℝ) ^ (-c s))⁻¹ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro o _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro τ _
      split_ifs <;> simp
    _ ≤ ∑ o : OverlapType S,
        (Fintype.card A : ℝ) ^ (Fintype.card V - (o.1.val.biUnion support).card) *
        (∏ s ∈ o.1.val, (Fintype.card A : ℝ) ^ (-c s))⁻¹ := by
      apply Finset.sum_le_sum
      intro o _
      exact mul_le_mul_of_nonneg_right (overlap_assignment_count row support read C σ o) (by positivity)
    _ ≤ ∑ _o : OverlapType S, (Fintype.card A : ℝ) ^ Fintype.card V *
        (Fintype.card A : ℝ) ^ (-ε) := by
      apply Finset.sum_le_sum
      intro o _
      exact overlap_power_bound hn support c o.1.val (gap _ o.1.property)
    _ = _ := by simp; ring

/-- The complete overlap-counting rule for row positions in possibly repeated
arrays, before substituting a candidate-cardinality lower bound. -/
theorem variance_power [Nonempty A] (row : (V → A) → S → I)
    (support : S → Finset V)
    (read : ∀ σ τ s, row σ s = row τ s → ∀ v ∈ support s, σ v = τ v)
    (p : I → ℝ) (hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1) (C : Finset (V → A))
    (hi : ∀ σ ∈ C, Function.Injective (row σ)) (c : S → ℝ)
    (hq : ∀ σ ∈ C, ∀ s, p (row σ s) = (Fintype.card A : ℝ) ^ (-c s))
    {ε : ℝ} (gap : ∀ J : Finset S, J.Nonempty →
      ε ≤ ((J.biUnion support).card : ℝ) - ∑ s ∈ J, c s) :
    (FiniteLaw.bernoulliProduct p hp).variance (fun w => (count row C w : ℝ)) ≤
      (∏ s, (Fintype.card A : ℝ) ^ (-c s)) ^ 2 * C.card *
      (Fintype.card (OverlapType S) * (Fintype.card A : ℝ) ^ Fintype.card V *
        (Fintype.card A : ℝ) ^ (-ε)) := by
  have hn : (1 : ℝ) ≤ Fintype.card A := by
    exact_mod_cast (show 1 ≤ Fintype.card A from Fintype.card_pos)
  rw [variance_count row p hp C hi _ (fun s => TableModel.powerProbability_pos hn (c s)) hq]
  calc
    _ ≤ (∏ s, (Fintype.card A : ℝ) ^ (-c s)) ^ 2 *
        ∑ _σ ∈ C, (Fintype.card (OverlapType S) * (Fintype.card A : ℝ) ^ Fintype.card V *
          (Fintype.card A : ℝ) ^ (-ε)) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      exact Finset.sum_le_sum fun σ _ => sum_inverse_overlap_power row support read C σ c gap
    _ = _ := by simp; ring

/-- Explicit relative variance; the lower cardinality is proved below from
fieldwise injectivity, not assumed as a sampling conclusion. -/
theorem relative_variance_power [Nonempty A] (row : (V → A) → S → I)
    (support : S → Finset V)
    (read : ∀ σ τ s, row σ s = row τ s → ∀ v ∈ support s, σ v = τ v)
    (p : I → ℝ) (hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1) (C : Finset (V → A))
    (hi : ∀ σ ∈ C, Function.Injective (row σ)) (c : S → ℝ)
    (hq : ∀ σ ∈ C, ∀ s, p (row σ s) = (Fintype.card A : ℝ) ^ (-c s))
    (hC : ((Fintype.card A : ℝ) / 2) ^ Fintype.card V ≤ C.card)
    {ε : ℝ} (gap : ∀ J : Finset S, J.Nonempty →
      ε ≤ ((J.biUnion support).card : ℝ) - ∑ s ∈ J, c s) :
    (FiniteLaw.bernoulliProduct p hp).variance (fun w => (count row C w : ℝ)) ≤
      Fintype.card (OverlapType S) * 2 ^ Fintype.card V * (Fintype.card A : ℝ) ^ (-ε) *
      ((FiniteLaw.bernoulliProduct p hp).expect (fun w => (count row C w : ℝ))) ^ 2 := by
  have hpow : (Fintype.card A : ℝ) ^ Fintype.card V ≤ (2 : ℝ) ^ Fintype.card V * C.card := by
    calc
      _ = (2 : ℝ) ^ Fintype.card V * ((Fintype.card A : ℝ) / 2) ^ Fintype.card V := by
        rw [← mul_pow]; congr 1; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hC (by positivity)
  rw [expect_count row p hp C hi _ hq]
  refine (variance_power row support read p hp C hi c hq gap).trans ?_
  calc
    _ ≤ (∏ s, (Fintype.card A : ℝ) ^ (-c s)) ^ 2 * C.card *
        (Fintype.card (OverlapType S) * ((2 : ℝ) ^ Fintype.card V * C.card) *
          (Fintype.card A : ℝ) ^ (-ε)) := by
      gcongr
    _ = _ := by ring

end BernoulliCandidates
end HyperbolicObstruction
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_Candidate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
open scoped BigOperators
namespace HyperbolicObstruction
namespace BernoulliCandidates
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq A]

/-- A convenient subset of the actual fieldwise-injective candidates consists
of globally injective free values avoiding every pinned letter. This is only a
lower bound; the actual candidate set does not prohibit cross-field coincidences. -/
lemma card_lower_of_embeddings (C : Finset (V → A)) (B : Finset A)
    (hC : ∀ f : V ↪ {a : A // a ∉ B}, (fun v => (f v).val) ∈ C) :
    ((Fintype.card A - B.card).descFactorial (Fintype.card V)) ≤ C.card := by
  classical
  have hi : Function.Injective (fun f : V ↪ {a : A // a ∉ B} =>
      (⟨fun v => (f v).val, hC f⟩ : C)) := by
    intro f g h
    apply DFunLike.ext
    intro v
    exact Subtype.ext (congrFun (congrArg Subtype.val h) v)
  have hh := Fintype.card_le_of_injective _ hi
  rw [Fintype.card_embedding_eq] at hh
  have hb : Fintype.card {a : A // a ∉ B} = Fintype.card A - B.card := by
    simp
  simpa only [hb, Fintype.card_coe] using hh

lemma real_descFactorial_lower (N b v : ℕ) (h : 2 * (b + v) ≤ N) :
    ((N : ℝ) / 2) ^ v ≤ ((N - b).descFactorial v : ℝ) := by
  have hb : b ≤ N := by omega
  have hnv : v ≤ N - b + 1 := by omega
  have hs : (N : ℝ) / 2 ≤ (N - b + 1 - v : ℕ) := by
    rw [Nat.cast_sub hnv, Nat.cast_add, Nat.cast_sub hb]
    push_cast
    have h' : (2 : ℝ) * (b + v) ≤ N := by exact_mod_cast h
    linarith
  exact (pow_le_pow_left₀ (by positivity) hs v).trans
    (by exact_mod_cast (N - b).pow_sub_le_descFactorial v)

lemma card_lower_half (C : Finset (V → A)) (B : Finset A)
    (hC : ∀ f : V ↪ {a : A // a ∉ B}, (fun v => (f v).val) ∈ C)
    (h : 2 * (B.card + Fintype.card V) ≤ Fintype.card A) :
    ((Fintype.card A : ℝ) / 2) ^ Fintype.card V ≤ C.card := by
  exact (real_descFactorial_lower _ _ _ h).trans
    (by exact_mod_cast card_lower_of_embeddings C B hC)

end BernoulliCandidates
end HyperbolicObstruction
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_TableSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
open scoped BigOperators
open Filter Topology
namespace HyperbolicObstruction
namespace IncidenceTemplate
variable {J A : Type*} [Fintype J] [Fintype A] [DecidableEq A] [Nonempty A]

/-- The alphabet of rank n+1, including each generator and its formal inverse.
This is an arbitrarily large cofinal set of the literal source alphabets. -/
abbrev SymmetricAlphabet (n : ℕ) := Fin (n+1) × Bool

lemma card_symmetricAlphabet (n : ℕ) : Fintype.card (SymmetricAlphabet n) = 2*(n+1) := by
  simp [Fintype.card_prod,Nat.mul_comm]

end IncidenceTemplate
end HyperbolicObstruction
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_Presentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction

namespace LetterPresentation
open IncidenceTemplate MasterGraph
variable (n : ℕ)
abbrev Alphabet := SymmetricAlphabet n

def inverseLetter : Alphabet n ≃ Alphabet n where
  toFun a := (a.1,!a.2)
  invFun a := (a.1,!a.2)
  left_inv := by rintro ⟨a,b⟩; cases b <;> rfl
  right_inv := by rintro ⟨a,b⟩; cases b <;> rfl

end LetterPresentation
end HyperbolicObstruction
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_ConeSkeleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
attribute [local instance] Classical.propDecidable
namespace HyperbolicObstruction
namespace ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation

variable (n : ℕ)
abbrev FanRow := Σ i : Fin 7, rowSupport (.inl i) → Alphabet n
variable (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)

/-- Fan occurrences are the actual included rows, counted once even if several
top occurrences use them. Positions are NOT identified by generator labels. -/
abbrev Fan := {b : FanRow n // w ⟨.inl b.1,b.2⟩ = true}

abbrev Vertex := Unit ⊕ Fan n w
abbrev Edge := Fin (n+1) ⊕ (Σ b : Fan n w, FanVertex b.val.1)
abbrev Dart := Edge n w × Bool

def start : Dart n w → Vertex n w
  | (.inl _,_) => .inl ()
  | (.inr b,true) => .inr b.1
  | (.inr _,false) => .inl ()

def rev (l : Dart n w) : Dart n w := (l.1,!l.2)
def isApex : Vertex n w → Bool
  | .inl _ => false
  | .inr _ => true

abbrev Outgoing (f : Fan n w) := {l : Dart n w // start n w l = .inr f}

def radialLabel (f : Fan n w) (v : FanVertex f.val.1) : Outgoing n w f :=
  ⟨(.inr ⟨f,v⟩,true),rfl⟩

lemma radialLabel_bijective (f : Fan n w) : Function.Bijective (radialLabel n w f) := by
  constructor
  · intro a b h
    have hs : (⟨f,a⟩ : Σ b : Fan n w, FanVertex b.val.1) = ⟨f,b⟩ :=
      Sum.inr.inj (congrArg (fun d => d.val.1) h)
    exact eq_of_heq (Sigma.mk.inj_iff.mp hs).2
  · rintro ⟨⟨e,b⟩,h⟩
    rcases e with e | ⟨f',v⟩
    · simp [start] at h
    · cases b with
      | false => simp [start] at h
      | true =>
        have he : f' = f := Sum.inr.inj h
        subst f'
        exact ⟨v,rfl⟩

instance instFintypeOutgoing (f : Fan n w) : Fintype (Outgoing n w f) :=
  Fintype.ofEquiv (FanVertex f.val.1) (Equiv.ofBijective _ (radialLabel_bijective n w f))

lemma card_outgoing (f : Fan n w) : Fintype.card (Outgoing n w f) ≤ 5 := by
  classical
  rw [← Fintype.card_congr (Equiv.ofBijective _ (radialLabel_bijective n w f))]
  exact card_fanVertex_le f.val.1

end ConeSkeleton
end HyperbolicObstruction
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_MacroCertificate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
open scoped BigOperators
namespace HyperbolicObstruction.MacroGraph
open IncidenceTemplate

/-- The literal 15-vertex macro graph: point and line vertices, and the single
subdivision vertex of the exceptional incidence D--CD. -/
abbrev Vertex := (Fin 7 ⊕ Fin 7) ⊕ Unit

def exceptional : Vertex := .inr ()

def Adjacent : Vertex → Vertex → Prop
  | .inl (.inl i), .inl (.inr l) => Incident i l ∧ (i,l) ≠ (3,4)
  | .inl (.inr l), .inl (.inl i) => Incident i l ∧ (i,l) ≠ (3,4)
  | .inl (.inl i), .inr _ => i = 3
  | .inr _, .inl (.inl i) => i = 3
  | .inl (.inr l), .inr _ => l = 4
  | .inr _, .inl (.inr l) => l = 4
  | _, _ => False

lemma adjacent_symm {a b : Vertex} (h : Adjacent a b) : Adjacent b a := by
  rcases a with ((i|l)|⟨⟩) <;> rcases b with ((j|m)|⟨⟩) <;> exact h

lemma adjacent_ne {a b : Vertex} (h : Adjacent a b) : a ≠ b := by
  rintro rfl
  rcases a with ((i|l)|⟨⟩) <;> exact h


end HyperbolicObstruction.MacroGraph
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_ConeGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation
attribute [local instance] Classical.propDecidable
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)

abbrev CoreRow := IncidenceTemplate.Edge → Alphabet n

def extendCore (a : CoreRow n) : Field → Alphabet n
  | .inl e => a e
  | .inr _ => (0,true)

/-- Only the 32 actual top fields index a top occurrence. Decorations are NOT
extra coordinates indexing redundant copies of a top cone. -/
abbrev Top := {a : CoreRow n //
  w (TableModel.row rowSupport (extendCore n a) (.inr (.inl ()))) = true ∧
  ∀ i : Fin 7, w (TableModel.row rowSupport (extendCore n a) (.inl i)) = true}

def slot (a : Top n w) (i : Fin 7) : Fan n w :=
  ⟨⟨i,fun f => extendCore n a.val f.val⟩,a.property.2 i⟩

def letterDart (a : Alphabet n) : Dart n w := (.inl a.1,a.2)

lemma rev_rev (l : Dart n w) : rev n w (rev n w l) = l := by
  rcases l with ⟨e,b⟩; cases b <;> rfl

lemma rev_letter (a : Alphabet n) : rev n w (letterDart n w a) =
    letterDart n w (inverseLetter n a) := rfl

lemma start_letter (a : Alphabet n) : start n w (letterDart n w a) = .inl () := by
  rcases a with ⟨e,b⟩; cases b <;> rfl

def macroVertex (a : Top n w) : MacroGraph.Vertex → Vertex n w
  | .inl (.inl i) => .inr (slot n w a i)
  | _ => .inl ()

def loose : IncidenceTemplate.Edge := ⟨(3,4),by decide⟩

/-- The literal map of the subdivided incidence graph from source02:72--79.
The exceptional two-edge path is radial X_D followed by the loose letter. -/
def macroStep (a : Top n w) {u v : MacroGraph.Vertex} (h : MacroGraph.Adjacent u v) : Dart n w := by
  rcases u with ((i|l)|⟨⟩) <;> rcases v with ((j|m)|⟨⟩)
  · exact h.elim
  · exact (.inr ⟨slot n w a i,⟨.inr m,h⟩⟩,true)
  · have hi : i = 3 := h
    subst i
    exact (.inr ⟨slot n w a 3,⟨.inl 3,by change IsFanVertex 3 (.inl 3); decide⟩⟩,true)
  · exact (.inr ⟨slot n w a j,⟨.inr l,h⟩⟩,false)
  · exact h.elim
  · exact rev n w (letterDart n w (a.val loose))
  · have hj : j = 3 := h
    subst j
    exact (.inr ⟨slot n w a 3,⟨.inl 3,by change IsFanVertex 3 (.inl 3); decide⟩⟩,false)
  · exact letterDart n w (a.val loose)
  · exact h.elim

lemma macroStep_start (a : Top n w) {u v : MacroGraph.Vertex} (h : MacroGraph.Adjacent u v) :
    start n w (macroStep n w a h) = macroVertex n w a u := by
  rcases u with ((i|l)|⟨⟩) <;> rcases v with ((j|m)|⟨⟩)
  · exact h.elim
  · rfl
  · have hi : i = 3 := h; subst i; rfl
  · rfl
  · exact h.elim
  · exact start_letter n w (inverseLetter n (a.val loose))
  · have hj : j = 3 := h; subst j; rfl
  · exact start_letter n w _
  · exact h.elim

lemma macroStep_reverse (a : Top n w) {u v : MacroGraph.Vertex} (h : MacroGraph.Adjacent u v) :
    macroStep n w a (MacroGraph.adjacent_symm h) = rev n w (macroStep n w a h) := by
  rcases u with ((i|l)|⟨⟩) <;> rcases v with ((j|m)|⟨⟩)
  · exact h.elim
  · rfl
  · have hi : i = 3 := h; subst i; rfl
  · rfl
  · exact h.elim
  · exact (rev_rev n w _).symm
  · have hj : j = 3 := h; subst j; rfl
  · rfl
  · exact h.elim

lemma macroStep_end (a : Top n w) {u v : MacroGraph.Vertex} (h : MacroGraph.Adjacent u v) :
    start n w (rev n w (macroStep n w a h)) = macroVertex n w a v := by
  rw [← macroStep_reverse]
  exact macroStep_start n w a _

/-- Each fan triangle retains its original edge field and BOTH distinct
radial ports, independently of repetitions in the assigned generator row. -/
abbrev FanTriangle := Σ b : Fan n w, {e : IncidenceTemplate.Edge // e ∈ fan b.val.1}

def fanLetter (f : FanTriangle n w) : Alphabet n :=
  f.1.val.2 ⟨.inl f.2.val,by simp [rowSupport]⟩

def fanLeft (f : FanTriangle n w) : FanVertex f.1.val.1 :=
  ⟨.inl f.2.val.val.1,(edge_fan_vertices _ _ f.2.property).1⟩
def fanRight (f : FanTriangle n w) : FanVertex f.1.val.1 :=
  ⟨.inr f.2.val.val.2,(edge_fan_vertices _ _ f.2.property).2⟩

def fanSide (f : FanTriangle n w) : Fin 3 → Dart n w :=
  ![(.inr ⟨f.1,fanLeft n w f⟩,true),letterDart n w (fanLetter n w f),
    (.inr ⟨f.1,fanRight n w f⟩,false)]

lemma fanSide_closed (f : FanTriangle n w) (i : Fin 3) :
    start n w (fanSide n w f (finRotate 3 i)) = start n w (rev n w (fanSide n w f i)) := by
  fin_cases i
  · exact start_letter n w _
  · exact (start_letter n w (inverseLetter n (fanLetter n w f))).symm
  · rfl

end HyperbolicObstruction.ConeSkeleton
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_CycleDecomposition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.ConeWalks
open SimpleGraph
variable {V A : Type*} {G : SimpleGraph V} [AddCommGroup A]

/-- A simple loop with its actual base vertex and edge traversals. -/
abbrev Circuit (G : SimpleGraph V) := Σ a : V, {p : G.Walk a a // p.IsCycle}

end HyperbolicObstruction.ConeWalks
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_MacroCycle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
open scoped BigOperators
namespace HyperbolicObstruction.MacroGraph
open IncidenceTemplate

/-- A cyclic simple macro polygon with at least three sides, expressed by its
actual vertices and successor. The normal-form splitting must produce this
data; all template bounds below are derived. -/
structure Polygon where
  n : ℕ
  vertex : Fin n → Vertex
  next : Equiv.Perm (Fin n)
  injective : Function.Injective vertex
  adjacent : ∀ i, Adjacent (vertex i) (vertex (next i))
  no_backtrack : ∀ i, next (next i) ≠ i

end HyperbolicObstruction.MacroGraph
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_MacroWalk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.MacroGraph

def graph : SimpleGraph Vertex where
  Adj := Adjacent
  symm := ⟨fun _ _ => adjacent_symm⟩
  loopless := ⟨fun _ adjacent => adjacent_ne adjacent rfl⟩

/-- The actual vertex-simple macro polygon obtained from a library cycle. -/
def ofCycle {u : Vertex} (p : graph.Walk u u) (hp : p.IsCycle) : Polygon where
  n := p.length
  vertex i := p.getVert i.val
  next := finRotate p.length
  injective := by
    intro i j h
    apply Fin.ext
    exact hp.getVert_injOn' (by simpa using Nat.le_sub_one_of_lt i.isLt)
      (by simpa using Nat.le_sub_one_of_lt j.isLt) h
  adjacent := by
    intro i
    have : NeZero p.length := ⟨by have := hp.three_le_length; omega⟩
    have hone : ((1 : Fin p.length) : ℕ) = 1 := by
      change 1 % p.length = 1
      exact Nat.mod_eq_of_lt (by have := hp.three_le_length; omega)
    have h := p.adj_getVert_succ i.isLt
    change Adjacent (p.getVert i.val) (p.getVert (i.val + 1)) at h
    change Adjacent (p.getVert i.val) (p.getVert (finRotate p.length i).val)
    rw [finRotate_apply,Fin.val_add]
    by_cases hi : i.val + 1 < p.length
    · simpa only [hone,
        Nat.mod_eq_of_lt hi] using h
    · have he : i.val + 1 = p.length := by omega
      simpa only [hone,
        he,Nat.mod_self,SimpleGraph.Walk.getVert_length,SimpleGraph.Walk.getVert_zero] using h
  no_backtrack := by
    intro i he
    have : NeZero p.length := ⟨by have := hp.three_le_length; omega⟩
    simp only [finRotate_apply] at he
    have hval := congrArg Fin.val he
    have h3 := hp.three_le_length
    have hone : ((1 : Fin p.length) : ℕ) = 1 := by
      change 1 % p.length = 1
      exact Nat.mod_eq_of_lt (by omega)
    simp only [Fin.val_add,hone] at hval
    by_cases h1 : i.val + 1 < p.length
    · rw [Nat.mod_eq_of_lt h1] at hval
      by_cases h2 : i.val + 2 < p.length
      · rw [show i.val + 1 + 1 = i.val + 2 by omega, Nat.mod_eq_of_lt h2] at hval
        omega
      · rw [show i.val + 1 + 1 = p.length by omega, Nat.mod_self] at hval
        omega
    · rw [show i.val + 1 = p.length by omega, Nat.mod_self] at hval
      simp only [Nat.zero_add, Nat.mod_eq_of_lt (show 1 < p.length by omega)] at hval
      omega

end HyperbolicObstruction.MacroGraph
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_IndexedFace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable

variable {D S : Type*}

/-- An indexed cellular face map. Commutation records EACH indexed side (not
just its edge label); injectivity on a face rules out wrapping a cell twice. -/
structure IndexedFaceMap (f : Perm D) (t : Perm S) (j : D → S) : Prop where
  commute : ∀ x, j (f x) = t (j x)
  injective : ∀ {x y}, f.SameCycle x y → j x = j y → x = y

lemma semiconj_perm_pow {f : Perm D} {t : Perm S} {j : D → S}
    (h : ∀ x, j (f x) = t (j x)) (k : ℕ) (x : D) :
    j ((f ^ k) x) = (t ^ k) (j x) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pow_succ',mul_apply,h,ih,pow_succ',mul_apply]

lemma semiconj_perm_inv {f : Perm D} {t : Perm S} {j : D → S}
    (h : ∀ x, j (f x) = t (j x)) (x : D) :
    j (f⁻¹ x) = t⁻¹ (j x) := by
  apply t.injective
  simpa only [Perm.inv_def,apply_symm_apply] using (h (f⁻¹ x)).symm

lemma semiconj_perm_zpow {f : Perm D} {t : Perm S} {j : D → S}
    (h : ∀ x, j (f x) = t (j x)) (k : ℤ) (x : D) :
    j ((f ^ k) x) = (t ^ k) (j x) := by
  cases k with
  | ofNat k => simpa using semiconj_perm_pow h k x
  | negSucc k =>
    simpa only [zpow_negSucc,inv_pow] using
      semiconj_perm_pow (semiconj_perm_inv h) (k+1) x

lemma semiconj_perm_sameCycle {f : Perm D} {t : Perm S} {j : D → S}
    (h : ∀ x, j (f x) = t (j x)) {a b : D} (hab : f.SameCycle a b) :
    t.SameCycle (j a) (j b) := by
  obtain ⟨k,rfl⟩ := hab
  exact ⟨k,(semiconj_perm_zpow h k a).symm⟩

end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_NormalCell
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
universe u v w z k

/-- Oriented, individually indexed polygon boundaries in a target cell
complex. In a lifted target, `S` includes the lift of the cell. Opposite
orientations have disjoint side cycles; the same indexed side is retained
when reversing. These data contain no diagram or normal-form assertion. -/
structure CellTarget (S : Type v) (L : Type w) (V : Type z) (A : Type k)
    [AddCommMonoid A] where
  next : Perm S
  opposite : Perm S
  opposite_sq : opposite * opposite = 1
  reverse_next : ∀ s, opposite (next s) = next⁻¹ (opposite s)
  opposite_cycle : ∀ s, ¬ next.SameCycle s (opposite s)
  edge : S → L
  start : L → V
  rev : L → L
  rev_rev : ∀ l, rev (rev l) = l
  edge_opposite : ∀ s, edge (opposite s) = rev (edge s)
  next_start : ∀ s, start (edge (next s)) = start (rev (edge s))
  apex : V → Bool
  radial : ∀ s, apex (start (edge s)) = true → apex (start (rev (edge s))) = false
  weight : S → A
  weight_next : ∀ s, weight (next s) = weight s
  weight_opposite : ∀ s, weight s + weight (opposite s) = 0

variable {S : Type v} {L : Type w} {V : Type z} {A : Type k} [AddCommMonoid A]

/-- A finite genus-zero side pairing with actual indexed cellular face maps.
This describes a raw picture, without any reducedness or link bounds. -/
structure CellPicture (T : CellTarget S L V A) where
  Dart : Type u
  [finite : Fintype Dart]
  [decEq : DecidableEq Dart]
  pairing : PictureMap Dart
  index : Dart → S
  mapped : IndexedFaceMap pairing.face T.next index
  respects : pairing.Respects (T.edge ∘ index) T.start T.rev
  genusZero : pairing.GenusZero

attribute [instance] CellPicture.finite CellPicture.decEq

end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_PolygonTarget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable

namespace PolygonTarget
variable {C L V A : Type*} [AddCommGroup A]

/-- An actual finite closed edge boundary for each cell, with indexed sides.
The cell type may be infinite (as in the universal cover); every cell boundary
is finite. Orientation reversal is constructed, not postulated. -/
structure Boundary (C : Type*) (L : Type*) (V : Type*) where
  size : C → ℕ
  positive : ∀ c, 0 < size c
  label : (c : C) → Fin (size c) → L
  start : L → V
  rev : L → L
  inv : ∀ l, rev (rev l) = l
  closed : ∀ c i, start (label c (finRotate (size c) i)) = start (rev (label c i))

namespace Boundary
variable (B : Boundary C L V)
abbrev Side := Σ c : C, Bool × Fin (B.size c)

def next : Perm B.Side where
  toFun s := ⟨s.1,s.2.1,if s.2.1 then finRotate (B.size s.1) s.2.2 else (finRotate (B.size s.1))⁻¹ s.2.2⟩
  invFun s := ⟨s.1,s.2.1,if s.2.1 then (finRotate (B.size s.1))⁻¹ s.2.2 else finRotate (B.size s.1) s.2.2⟩
  left_inv := by rintro ⟨c,b,i⟩; cases b <;> simp only [Bool.false_eq_true,ite_false,ite_true,Perm.inv_def,apply_symm_apply,symm_apply_apply]
  right_inv := by rintro ⟨c,b,i⟩; cases b <;> simp only [Bool.false_eq_true,ite_false,ite_true,Perm.inv_def,apply_symm_apply,symm_apply_apply]

def opposite : Perm B.Side where
  toFun s := ⟨s.1,!s.2.1,s.2.2⟩
  invFun s := ⟨s.1,!s.2.1,s.2.2⟩
  left_inv := by rintro ⟨c,b,i⟩; cases b <;> rfl
  right_inv := by rintro ⟨c,b,i⟩; cases b <;> rfl

def sideLabel (s : B.Side) : L := if s.2.1 then B.label s.1 s.2.2 else B.rev (B.label s.1 s.2.2)

def weight (w : C → A) (s : B.Side) : A := if s.2.1 then w s.1 else -(w s.1)

lemma reverse_next (s : B.Side) : B.opposite (B.next s) = B.next⁻¹ (B.opposite s) := by
  rcases s with ⟨c,b,i⟩; cases b <;> rfl

lemma edge_opposite (s : B.Side) : B.sideLabel (B.opposite s) = B.rev (B.sideLabel s) := by
  rcases s with ⟨c,b,i⟩; cases b <;> simp [sideLabel,opposite,B.inv]

end Boundary
end PolygonTarget

end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_WordDisk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


/-! Algebraic van Kampen existence, with actual words and area-counted local
moves (not a finiteness or isoperimetric assumption). Free cancellation has
zero cost; each orientation of a listed relator disk has cost one. -/
noncomputable section
namespace HyperbolicObstruction.WordPictures

variable {A : Type*}
abbrev Word (A : Type*) := List (A × Bool)

end HyperbolicObstruction.WordPictures
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_PresentationDisk
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeOutgoing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction
namespace LetterPresentation
open IncidenceTemplate MasterGraph
variable (n : ℕ)

def stepLetter {a b : MasterGraph.Vertex} (l : Field → Alphabet n) (s : MasterGraph.Step a b) :
    Alphabet n := if s.forward then l s.field else inverseLetter n (l s.field)

end LetterPresentation
end HyperbolicObstruction
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_ConeCellTarget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation
attribute [local instance] Classical.propDecidable
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)

abbrev TopPolygon := Top n w × ConeWalks.Circuit MacroGraph.graph
abbrev Square := Σ τ : TwoPath,
  {r : rowSupport (.inr (.inr τ)) → Alphabet n // w ⟨.inr (.inr τ),r⟩ = true}
abbrev Six := {r : Fin 6 → Alphabet n // d r = true}

/-- Only actual positions index rows; this extension is a device for reading
an oriented word and cannot introduce duplicate row occurrences. -/
def extendRow (r : Row) (l : rowSupport r → Alphabet n) : Field → Alphabet n :=
  fun f => if h : f ∈ rowSupport r then l ⟨f,h⟩ else (0,true)

def squareSide (s : Square n w) : Fin 4 → Dart n w :=
  let l := extendRow n (.inr (.inr s.1)) s.2.val
  ![letterDart n w (stepLetter n l (MasterGraph.first s.1)),
    letterDart n w (stepLetter n l (MasterGraph.second s.1)),
    letterDart n w (l (.inr (s.1,0))),letterDart n w (l (.inr (s.1,1)))]

lemma squareSide_start (s : Square n w) (i : Fin 4) :
    start n w (squareSide n w s i) = .inl () := by
  fin_cases i <;> exact start_letter n w _

lemma squareSide_end (s : Square n w) (i : Fin 4) :
    start n w (rev n w (squareSide n w s i)) = .inl () := by
  fin_cases i <;> exact start_letter n w (inverseLetter n _)

def topSide (a : TopPolygon n w) (i : Fin a.2.2.val.length) : Dart n w :=
  macroStep n w a.1 ((MacroGraph.ofCycle a.2.2.val a.2.2.property).adjacent i)

lemma topSide_closed (a : TopPolygon n w) (i : Fin a.2.2.val.length) :
    start n w (topSide n w a (finRotate _ i)) = start n w (rev n w (topSide n w a i)) := by
  rw [topSide,macroStep_start,topSide,macroStep_end]
  rfl

/-- The three actual kinds of faces AFTER radial top triangles have been
assembled and the closed macro walks split into simple cycles. Such assembly
and its genus preservation are separate obligations, not fields here. -/
abbrev Cell := FanTriangle n w ⊕ (TopPolygon n w ⊕ (Square n w ⊕ Six n d))

def size : Cell n w d → ℕ
  | .inl _ => 3
  | .inr (.inl a) => a.2.2.val.length
  | .inr (.inr (.inl _)) => 4
  | .inr (.inr (.inr _)) => 6

def side : (c : Cell n w d) → Fin (size n w d c) → Dart n w
  | .inl f => fanSide n w f
  | .inr (.inl a) => topSide n w a
  | .inr (.inr (.inl s)) => squareSide n w s
  | .inr (.inr (.inr s)) => fun i => letterDart n w (s.val i)

lemma size_positive (c : Cell n w d) : 0 < size n w d c := by
  rcases c with f | (a | (s | s))
  · change 0 < 3; decide
  · exact lt_of_lt_of_le (by decide : 0 < 3) a.2.2.property.three_le_length
  · change 0 < 4; decide
  · change 0 < 6; decide

lemma side_closed (c : Cell n w d) (i : Fin (size n w d c)) :
    start n w (side n w d c (finRotate _ i)) = start n w (rev n w (side n w d c i)) := by
  rcases c with f | (a | (s | s))
  · exact fanSide_closed n w f i
  · exact topSide_closed n w a i
  · exact (squareSide_start n w s _).trans (squareSide_end n w s i).symm
  · exact (start_letter n w _).trans (start_letter n w (inverseLetter n _)).symm

def boundary : PictureSwitch.PolygonTarget.Boundary (Cell n w d) (Dart n w) (Vertex n w) where
  size := size n w d
  positive := size_positive n w d
  label := side n w d
  start := start n w
  rev := rev n w
  inv := rev_rev n w
  closed := side_closed n w d

end HyperbolicObstruction.ConeSkeleton
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_Coincidence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
open scoped BigOperators
open Filter Topology
namespace HyperbolicObstruction
namespace Coincidence

variable {V S I : Type*} [Fintype V] [Fintype S] [Fintype I]
  [DecidableEq V] [DecidableEq S] [DecidableEq I]

/-- Signs remain separate at every position, even inside one unsigned class. -/
def signedAssignment {k n : ℕ} (c : V → Fin k) (ε : V → Bool) (a : Fin k → Fin (n+1)) :
    V → IncidenceTemplate.SymmetricAlphabet n := fun v => (a (c v), ε v)

def unsignedValues {n : ℕ} (σ : V → IncidenceTemplate.SymmetricAlphabet n) : Finset (Fin (n+1)) :=
  Finset.univ.image (fun v => (σ v).1)

def unsignedRank {n : ℕ} (σ : V → IncidenceTemplate.SymmetricAlphabet n) : ℕ :=
  Fintype.card V - (unsignedValues σ).card

omit [DecidableEq V] in
lemma unsignedValues_card_le {n : ℕ} (σ : V → IncidenceTemplate.SymmetricAlphabet n) :
    (unsignedValues σ).card ≤ Fintype.card V := Finset.card_image_le

omit [DecidableEq V] in
lemma signed_factorization {n : ℕ} (σ : V → IncidenceTemplate.SymmetricAlphabet n) :
    ∃ (c : V → Fin (unsignedValues σ).card) (ε : V → Bool)
      (a : Fin (unsignedValues σ).card → Fin (n+1)), signedAssignment c ε a = σ := by
  let e : unsignedValues σ ≃ Fin (unsignedValues σ).card :=
    (Fintype.equivFin _).trans (finCongr (Fintype.card_coe _))
  refine ⟨fun v => e ⟨(σ v).1,Finset.mem_image.mpr ⟨v,Finset.mem_univ _,rfl⟩⟩,
    fun v => (σ v).2, fun i => (e.symm i).val, ?_⟩
  funext v
  simp only [signedAssignment,Equiv.symm_apply_apply,Prod.eta]

omit [Fintype V] [DecidableEq V] [DecidableEq S] in
/-- A specified unsigned coincidence pattern is rare exactly when its number
of classes is smaller than the total independent trial cost. Distinctness is
explicit, so repeated occurrences are not incorrectly charged twice. -/
theorem signed_pattern_bound {k n : ℕ} (c : V → Fin k) (ε : V → Bool)
    (row : (V → IncidenceTemplate.SymmetricAlphabet n) → S → I)
    (p : I → ℝ) (hp : ∀ i, p i ∈ Set.Icc (0:ℝ) 1)
    (q : S → ℝ) (hq : ∀ σ s, p (row σ s) = q s) :
    (FiniteLaw.bernoulliProduct p hp).prob (fun w => ∃ a : Fin k → Fin (n+1),
      Function.Injective (row (signedAssignment c ε a)) ∧
      BernoulliCandidates.Present row w (signedAssignment c ε a)) ≤
      (n+1:ℝ)^k * ∏ s, q s := by
  classical
  let μ := FiniteLaw.bernoulliProduct p hp
  apply (μ.prob_exists_le (fun a w => Function.Injective (row (signedAssignment c ε a)) ∧
    BernoulliCandidates.Present row w (signedAssignment c ε a))).trans
  have hq0 : 0 ≤ ∏ s, q s := by
    exact Finset.prod_nonneg fun s _ =>
      (hq (signedAssignment c ε (fun _ => 0)) s ▸ (hp _).1)
  calc
    _ ≤ ∑ a : Fin k → Fin (n+1), ∏ s, q s := by
      apply Finset.sum_le_sum
      intro a _
      by_cases hi : Function.Injective (row (signedAssignment c ε a))
      · simp only [hi,true_and]
        change (FiniteLaw.bernoulliProduct p hp).prob _ ≤ _
        rw [BernoulliCandidates.prob_present row p hp _ hi]
        simp only [hq,le_refl]
      · simp only [hi,false_and,FiniteLaw.prob,ite_false,FiniteLaw.expect_const]
        exact hq0
    _ = _ := by simp [Nat.cast_pow,Nat.cast_add]


omit [DecidableEq S] in
lemma patterns_bound {k n : ℕ}
    (row : (V → IncidenceTemplate.SymmetricAlphabet n) → S → I)
    (p : I → ℝ) (hp : ∀ i, p i ∈ Set.Icc (0:ℝ) 1)
    (q : S → ℝ) (hq : ∀ σ s, p (row σ s) = q s) :
    (FiniteLaw.bernoulliProduct p hp).prob (fun w => ∃ (c : V → Fin k) (ε : V → Bool)
      (a : Fin k → Fin (n+1)), Function.Injective (row (signedAssignment c ε a)) ∧
      BernoulliCandidates.Present row w (signedAssignment c ε a)) ≤
      (k:ℝ)^Fintype.card V * 2^Fintype.card V * ((n+1:ℝ)^k * ∏ s, q s) := by
  classical
  let μ := FiniteLaw.bernoulliProduct p hp
  apply (μ.prob_exists_le _).trans
  calc
    _ ≤ ∑ c : V → Fin k, ∑ ε : V → Bool, ((n+1:ℝ)^k * ∏ s, q s) := by
      apply Finset.sum_le_sum
      intro c _
      exact (μ.prob_exists_le _).trans (Finset.sum_le_sum fun ε _ =>
        signed_pattern_bound c ε row p hp q hq)
    _ = _ := by simp [Nat.cast_pow,mul_assoc]

def rankRate (J : ℕ) (cost N : ℝ) : ℝ :=
  ∑ k : Fin (J+1), if (k:ℝ)+cost < 0 then
    (k:ℝ)^J * 2^J * N^((k:ℝ)+cost) else 0

lemma rankRate_tendsto (J : ℕ) (cost : ℝ) :
    Tendsto (rankRate J cost) atTop (𝓝 0) := by
  unfold rankRate
  have hh (k : Fin (J+1)) : Tendsto (fun N : ℝ => if (k:ℝ)+cost < 0 then
      (k:ℝ)^J * 2^J * N^((k:ℝ)+cost) else 0) atTop (𝓝 0) := by
    split_ifs with h
    · have ht := (tendsto_rpow_neg_atTop (neg_pos.mpr h)).const_mul ((k:ℝ)^J * 2^J)
      simpa only [neg_neg,mul_zero] using ht
    · exact tendsto_const_nhds
  simpa only [rankRate,Finset.sum_const_zero] using tendsto_finsetSum Finset.univ (fun k _ => hh k)

/-- Concrete bad event: an included collection of distinct trials has more
unsigned coincidences than its information budget permits. -/
def RankBad {n : ℕ} (row : (V → IncidenceTemplate.SymmetricAlphabet n) → S → I)
    (cost : ℝ) (w : I → Bool) : Prop :=
  ∃ σ, Function.Injective (row σ) ∧ BernoulliCandidates.Present row w σ ∧
    (Fintype.card V:ℝ)+cost < unsignedRank σ

instance instDecidablePredForallBoolRankBad {n : ℕ} (row : (V → IncidenceTemplate.SymmetricAlphabet n) → S → I)
    (cost : ℝ) : DecidablePred (RankBad row cost) := fun _ => Classical.propDecidable _

omit [Fintype S] [Fintype I] [DecidableEq V] [DecidableEq S] [DecidableEq I] in
lemma rank_bad_classes {n : ℕ}
    (row : (V → IncidenceTemplate.SymmetricAlphabet n) → S → I) (cost : ℝ) (w : I → Bool)
    (h : RankBad row cost w) :
    ∃ k : Fin (Fintype.card V+1), (k:ℝ)+cost < 0 ∧
      ∃ (c : V → Fin k) (ε : V → Bool) (a : Fin k → Fin (n+1)),
        Function.Injective (row (signedAssignment c ε a)) ∧
        BernoulliCandidates.Present row w (signedAssignment c ε a) := by
  obtain ⟨σ,hi,hp,hr⟩ := h
  have hk := unsignedValues_card_le σ
  have hr' : ((unsignedValues σ).card:ℝ)+cost < 0 := by
    rw [unsignedRank,Nat.cast_sub hk] at hr
    linarith
  obtain ⟨c,ε,a,ha⟩ := signed_factorization σ
  exact ⟨⟨_,Nat.lt_succ_of_le hk⟩,hr',c,ε,a,by simpa only [ha] using hi,by simpa only [ha] using hp⟩

omit [DecidableEq S] in
/-- The finite first-moment coincidence estimate, including every sign choice
and every unsigned partition. -/
theorem rank_bad_bound {n : ℕ}
    (row : (V → IncidenceTemplate.SymmetricAlphabet n) → S → I)
    (p : I → ℝ) (hp : ∀ i, p i ∈ Set.Icc (0:ℝ) 1)
    (cost : S → ℝ) (hq : ∀ σ s,
      p (row σ s) = (Fintype.card (IncidenceTemplate.SymmetricAlphabet n):ℝ)^(cost s)) :
    (FiniteLaw.bernoulliProduct p hp).prob (RankBad row (∑ s, cost s)) ≤
      rankRate (Fintype.card V) (∑ s, cost s)
        (Fintype.card (IncidenceTemplate.SymmetricAlphabet n)) := by
  classical
  let μ := FiniteLaw.bernoulliProduct p hp
  let N : ℝ := Fintype.card (IncidenceTemplate.SymmetricAlphabet n)
  have hN : 0 < N := by dsimp [N]; exact_mod_cast Fintype.card_pos
  have hbase : (n+1:ℝ) ≤ N := by
    dsimp [N]
    rw [IncidenceTemplate.card_symmetricAlphabet]
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  let E (k : Fin (Fintype.card V+1)) (w : I → Bool) : Prop :=
    (k:ℝ)+(∑ s, cost s) < 0 ∧
      ∃ (c : V → Fin k) (ε : V → Bool) (a : Fin k → Fin (n+1)),
        Function.Injective (row (signedAssignment c ε a)) ∧
        BernoulliCandidates.Present row w (signedAssignment c ε a)
  have hmono : μ.prob (RankBad row (∑ s, cost s)) ≤
      μ.prob (fun w => ∃ k, E k w) :=
    μ.prob_mono (fun w h => rank_bad_classes row (∑ s, cost s) w h)
  have hunion : μ.prob (fun w => ∃ k, E k w) ≤ ∑ k, μ.prob (E k) := by
    convert μ.prob_exists_le E using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
  apply hmono.trans (hunion.trans _)
  unfold rankRate
  apply Finset.sum_le_sum
  intro k _
  dsimp only [E]
  by_cases hk : (k:ℝ)+(∑ s, cost s) < 0
  · simp only [hk,true_and,ite_true]
    apply (patterns_bound row p hp (fun s => N^(cost s)) hq).trans
    have hpow : (n+1:ℝ)^k.val ≤ N^k.val := pow_le_pow_left₀ (by positivity) hbase _
    have he : N^k.val * (∏ s, N^(cost s)) = N^((k:ℝ)+(∑ s, cost s)) := by
      rw [← Real.rpow_sum_of_pos hN,← Real.rpow_natCast,← Real.rpow_add hN]
    rw [← he]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hpow (Finset.prod_nonneg fun s _ => Real.rpow_nonneg hN.le _))
      (by positivity)
  · simp only [hk,false_and,ite_false,FiniteLaw.prob,FiniteLaw.expect_const,le_refl]

end Coincidence
end HyperbolicObstruction
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_FaceWalk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {D C V : Type*} [DecidableEq D] [Fintype D]
namespace PictureMap

/-- A literal closed target walk on each source face: the next side starts
where this side ends. This imposes no injectivity or normal form. -/
def FaceClosed (M : PictureMap D) (source target : D → V) : Prop :=
  ∀ x, source (M.face x) = target x

/-- The indexed target occurrence stays constant around each source face.
Distinct occurrence indices remain distinct even if their labels agree. -/
def FaceKind (M : PictureMap D) (kind : D → C) : Prop := ∀ x, kind (M.face x) = kind x

end PictureMap
end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_WalkCell
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
universe u v w z k t r

/-- Indexed oriented steps in polygonal cells, with selected cells permitted
to have arbitrary closed template walks. In the cone target these are precisely
top-cone walks; all fan triangles and decoration disks are frozen. Template
vertices retain their occurrence index, while `vertex` is their actual image
in the target one-skeleton. These are incidence definitions, not diagram or
normal-form hypotheses. -/
structure WalkCellTarget (S : Type v) (C : Type w) (W : Type z) (L : Type k)
    (V : Type t) (A : Type r) [AddCommMonoid A] where
  kind : S → C
  free : C → Bool
  front : S → W
  back : S → W
  vertex : W → V
  label : S → L
  start : L → V
  rev : L → L
  rev_rev : ∀ l, rev (rev l) = l
  front_label : ∀ s, start (label s) = vertex (front s)
  back_label : ∀ s, start (rev (label s)) = vertex (back s)
  opposite : S → S
  opposite_kind : ∀ s, kind (opposite s) = kind s
  opposite_front : ∀ s, front (opposite s) = back s
  opposite_back : ∀ s, back (opposite s) = front s
  opposite_label : ∀ s, label (opposite s) = rev (label s)
  loopless : ∀ s, free (kind s) = true → front s ≠ back s
  simple : ∀ s t, free (kind s) = true → kind s = kind t →
    front s = front t → back s = back t → s = t
  weight : S → A
  opposite_weight : ∀ s, free (kind s) = true → weight s + weight (opposite s) = 0

variable {S : Type v} {C : Type w} {W : Type z} {L : Type k} {V : Type t}
  {A : Type r} [AddCommMonoid A]

structure WalkPicture (T : WalkCellTarget S C W L V A) where
  Dart : Type u
  [finite : Fintype Dart]
  [decEq : DecidableEq Dart]
  pairing : PictureMap Dart
  index : Dart → S
  closed : pairing.FaceClosed (T.front ∘ index) (T.back ∘ index)
  kind : pairing.FaceKind (T.kind ∘ index)
  paired : ∀ x, T.label (index (pairing.edge x)) = T.rev (T.label (index x))
  genusZero : pairing.GenusZero
attribute [instance] WalkPicture.finite WalkPicture.decEq

namespace WalkPicture
variable {T : WalkCellTarget S C W L V A} (P : WalkPicture.{u} T)

lemma respects : P.pairing.Respects (T.label ∘ P.index) T.start T.rev := by
  constructor
  · intro x
    change T.start (T.label (P.index (P.pairing.face (P.pairing.edge x)))) = _
    have hc := P.closed (P.pairing.edge x)
    dsimp only [Function.comp_apply] at hc
    rw [T.front_label,hc,← T.back_label,P.paired,T.rev_rev]
    rfl
  · exact P.paired

end WalkPicture
end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_ConeWalkTarget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation
open PictureSwitch
attribute [local instance] Classical.propDecidable
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)

/-- Actual non-top cells; these faces must not be split during macro surgery. -/
abbrev FrozenCell := FanTriangle n w ⊕ (Square n w ⊕ Six n d)

def frozenCell : FrozenCell n w d → Cell n w d
  | .inl f => .inl f
  | .inr e => .inr (.inr e)

def frozenBoundary : PolygonTarget.Boundary (FrozenCell n w d) (Dart n w) (Vertex n w) where
  size c := size n w d (frozenCell n w d c)
  positive cell := size_positive n w d (frozenCell n w d cell)
  label c := side n w d (frozenCell n w d c)
  start := start n w
  rev := rev n w
  inv := rev_rev n w
  closed cell := side_closed n w d (frozenCell n w d cell)

abbrev WalkStep := (Top n w × MacroGraph.graph.Dart) ⊕ (frozenBoundary n w d).Side
abbrev WalkKind := Top n w ⊕ FrozenCell n w d
abbrev WalkVertex := (Top n w × MacroGraph.Vertex) ⊕ Vertex n w

def walkKind : WalkStep n w d → WalkKind n w d
  | .inl s => .inl s.1
  | .inr s => .inr s.1

def walkFree : WalkKind n w d → Bool
  | .inl _ => true
  | .inr _ => false

def walkFront : WalkStep n w d → WalkVertex n w
  | .inl s => .inl (s.1,s.2.fst)
  | .inr s => .inr (start n w ((frozenBoundary n w d).sideLabel s))

def walkBack : WalkStep n w d → WalkVertex n w
  | .inl s => .inl (s.1,s.2.snd)
  | .inr s => .inr (start n w (rev n w ((frozenBoundary n w d).sideLabel s)))

def walkVertex : WalkVertex n w → Vertex n w
  | .inl s => macroVertex n w s.1 s.2
  | .inr v => v

def walkLabel : WalkStep n w d → Dart n w
  | .inl s => macroStep n w s.1 s.2.adj
  | .inr s => (frozenBoundary n w d).sideLabel s

def walkOpposite : WalkStep n w d → WalkStep n w d
  | .inl s => .inl (s.1,s.2.symm)
  | .inr s => .inr ((frozenBoundary n w d).opposite s)

lemma walkOpposite_kind (s : WalkStep n w d) :
    walkKind n w d (walkOpposite n w d s) = walkKind n w d s := by
  cases s <;> rfl

lemma walkOpposite_label (s : WalkStep n w d) :
    walkLabel n w d (walkOpposite n w d s) = rev n w (walkLabel n w d s) := by
  rcases s with s | s
  · exact macroStep_reverse n w s.1 s.2.adj
  · exact (frozenBoundary n w d).edge_opposite s

lemma walkOpposite_front (s : WalkStep n w d) :
    walkFront n w d (walkOpposite n w d s) = walkBack n w d s := by
  rcases s with s | s
  · rfl
  · change Sum.inr (start n w ((frozenBoundary n w d).sideLabel
        ((frozenBoundary n w d).opposite s))) = _
    rw [(frozenBoundary n w d).edge_opposite]; rfl

lemma walkOpposite_back (s : WalkStep n w d) :
    walkBack n w d (walkOpposite n w d s) = walkFront n w d s := by
  rcases s with s | s
  · rfl
  · change Sum.inr (start n w (rev n w ((frozenBoundary n w d).sideLabel
        ((frozenBoundary n w d).opposite s)))) = _
    rw [(frozenBoundary n w d).edge_opposite]
    change Sum.inr (start n w (rev n w (rev n w _))) = _
    rw [rev_rev]; rfl

lemma walk_loopless (s : WalkStep n w d) (hs : walkFree n w d (walkKind n w d s) = true) :
    walkFront n w d s ≠ walkBack n w d s := by
  rcases s with s | s
  · intro he
    exact s.2.fst_ne_snd (congrArg Prod.snd (Sum.inl.inj he))
  · cases hs

lemma walk_simple (s t : WalkStep n w d) (hs : walkFree n w d (walkKind n w d s) = true)
    (hk : walkKind n w d s = walkKind n w d t)
    (hf : walkFront n w d s = walkFront n w d t)
    (hb : walkBack n w d s = walkBack n w d t) : s = t := by
  rcases s with s | s
  · rcases t with t | t
    · have hf' : s.2.fst = t.2.fst :=
        congrArg (fun q : Top n w × MacroGraph.Vertex => q.2) (Sum.inl.inj hf)
      have hb' : s.2.snd = t.2.snd :=
        congrArg (fun q : Top n w × MacroGraph.Vertex => q.2) (Sum.inl.inj hb)
      exact congrArg Sum.inl (Prod.ext (Sum.inl.inj hk)
        (SimpleGraph.Dart.ext s.2 t.2 (Prod.ext hf' hb')))
    · cases hk
  · cases hs

variable {A : Type*} [AddCommGroup A]

/-- A frozen oriented face contributes its cellular coefficient once, at its
zero-th POSITION, not once per side. Top steps contribute their individually
indexed oriented elementary cone triangles. -/
def walkWeight (c : Top n w → MacroGraph.graph.Dart → A) (f : FrozenCell n w d → A) :
    WalkStep n w d → A
  | .inl s => c s.1 s.2
  | .inr s => if s.2.2.val = 0 then (frozenBoundary n w d).weight f s else 0

lemma walkWeight_opposite (c : Top n w → MacroGraph.graph.Dart → A)
    (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A) (s : WalkStep n w d) :
    walkWeight n w d c f s + walkWeight n w d c f (walkOpposite n w d s) = 0 := by
  rcases s with s | ⟨s,b,i⟩
  · change c s.1 s.2 + c s.1 s.2.symm = 0
    rw [hc,add_neg_cancel]
  · by_cases hi : i.val = 0 <;> cases b <;> simp [walkWeight,walkOpposite,PolygonTarget.Boundary.opposite,
      PolygonTarget.Boundary.weight,hi]

/-- Literal target for the actual top occurrences and their subdivided macro
edges. No simple-cycle or normal-picture assertion is included in this data.
In particular two DISTINCT top polygons using a common indexed cone side are
recognized as cancellable. -/
def walkTarget (c : Top n w → MacroGraph.graph.Dart → A)
    (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A) :
    WalkCellTarget (WalkStep n w d) (WalkKind n w d) (WalkVertex n w)
      (Dart n w) (Vertex n w) A where
  kind := walkKind n w d
  free := walkFree n w d
  front := walkFront n w d
  back := walkBack n w d
  vertex := walkVertex n w
  label := walkLabel n w d
  start := start n w
  rev := rev n w
  rev_rev := rev_rev n w
  front_label := by
    rintro (s | s)
    · exact macroStep_start n w s.1 s.2.adj
    · rfl
  back_label := by
    rintro (s | s)
    · exact macroStep_end n w s.1 s.2.adj
    · rfl
  opposite := walkOpposite n w d
  opposite_kind := walkOpposite_kind n w d
  opposite_front := walkOpposite_front n w d
  opposite_back := walkOpposite_back n w d
  opposite_label := walkOpposite_label n w d
  loopless := walk_loopless n w d
  simple := walk_simple n w d
  weight := walkWeight n w d c f
  opposite_weight := fun s _ => walkWeight_opposite n w d c hc f s

end HyperbolicObstruction.ConeSkeleton
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_FrozenWalk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
universe u v w z k t r
variable {S : Type v} {C : Type w} {W : Type z} {L : Type k} {V : Type t}
  {A : Type r} [AddCommMonoid A]

/-- Additional literal boundary indexing for the cells which are not free
macro walks. No normalization property is packaged into this data. -/
structure FrozenTarget (T : WalkCellTarget S C W L V A) where
  next : Perm S
  reverse : Perm S
  reverse_eq : ∀ s, reverse s = T.opposite s
  reverse_sq : reverse * reverse = 1
  reverse_next : ∀ s, reverse (next s) = next⁻¹ (reverse s)
  opposite_cycle : ∀ s, ¬ next.SameCycle s (reverse s)
  opposite_weight : ∀ s, T.weight s + T.weight (reverse s) = 0

namespace WalkPicture
variable {T : WalkCellTarget S C W L V A} (P : WalkPicture.{u} T)

abbrev FrozenDart := {x : P.Dart // T.free (T.kind (P.index x)) = false}

def frozenFace : Perm P.FrozenDart := P.pairing.face.subtypePerm (by
  intro x
  change T.free ((T.kind ∘ P.index) (P.pairing.face x)) = false ↔ _
  rw [P.kind]; rfl)

/-- Frozen source faces use one complete indexed side cycle, without wrapping.
This property is imposed on raw cellular face maps, not on their reducedness. -/
def FrozenMapped (B : FrozenTarget T) : Prop :=
  IndexedFaceMap P.frozenFace B.next (P.index ∘ Subtype.val)

end WalkPicture
end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_WalkRadial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
universe u v w z k t r
variable {S : Type v} {C : Type w} {W : Type z} {L : Type k} {V : Type t}
  {A : Type r} [AddCommMonoid A]
namespace WalkPicture
variable {T : WalkCellTarget S C W L V A} (P : WalkPicture.{u} T)

def RadialInjective (apex : V → Bool) : Prop := ∀ a b,
  apex (T.start (T.label (P.index a))) = true → P.pairing.vertex.SameCycle a b →
    T.label (P.index a) = T.label (P.index b) → a = b

end WalkPicture
end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_FullWalkNormal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
universe u v w z k t r
variable {S : Type v} {C : Type w} {W : Type z} {L : Type k} {V : Type t}
  {A : Type r} [AddCommMonoid A]
namespace WalkPicture
variable {T : WalkCellTarget S C W L V A} (P : WalkPicture.{u} T)

/-- No adjacent sides are oppositely indexed pieces of the same target cell,
including both the free top occurrences and all genuine frozen cells. -/
def FullyReduced : Prop := ∀ a, P.index (P.pairing.edge a) ≠ T.opposite (P.index a)

end WalkPicture
end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_WalkRawPosition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch
attribute [local instance] Classical.propDecidable
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)

def isLetter (l : Dart n w) : Bool := match l.1 with | .inl _ => true | .inr _ => false

universe u

end HyperbolicObstruction.ConeSkeleton
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_FanApex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
open scoped BigOperators
namespace HyperbolicObstruction.FanLink

inductive Mark (F : Type*)
  | absent | triangle | top (f : F)
  deriving DecidableEq

end HyperbolicObstruction.FanLink
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_WalkClasses
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
universe u v w z k t r
variable {S : Type v} {C : Type w} {W : Type z} {L : Type k} {V : Type t}
  {A : Type r} [AddCommMonoid A]
namespace WalkPicture
variable {T : WalkCellTarget S C W L V A} (P : WalkPicture.{u} T)

abbrev Face := Quotient (SameCycle.setoid P.pairing.face)
abbrev Vertex := Quotient (SameCycle.setoid P.pairing.vertex)

def faceClass (x : P.Dart) : P.Face := Quotient.mk _ x
def vertexClass (x : P.Dart) : P.Vertex := Quotient.mk _ x

lemma vertexClass_eq {x y : P.Dart} : P.vertexClass x = P.vertexClass y ↔ P.pairing.vertex.SameCycle x y :=
  Quotient.eq

lemma vertexClass_out (x : P.Vertex) : P.vertexClass x.out = x := Quotient.out_eq _

lemma kind_cycle {x y : P.Dart} (h : P.pairing.face.SameCycle x y) :
    T.kind (P.index x) = T.kind (P.index y) := by
  exact sameCycle_one.mp (semiconj_perm_sameCycle (t := (1 : Perm C)) P.kind h)

def faceKind : P.Face → C := Quotient.lift (T.kind ∘ P.index) (fun _ _ h => P.kind_cycle h)

abbrev Link (z : P.Vertex) := {x : P.Dart // P.vertexClass x = z}

def linkNext (z : P.Vertex) : Perm (P.Link z) := P.pairing.vertex⁻¹.subtypePerm (by
  intro x
  have he : P.vertexClass (P.pairing.vertex⁻¹ x) = P.vertexClass x :=
    (P.vertexClass_eq).mpr (sameCycle_inv.mp ((SameCycle.rfl (x := x)).apply_left))
  rw [he])

lemma link_card (z : P.Vertex) :
    Fintype.card (P.Link z) = Fintype.card {x : P.Dart // P.pairing.vertex.SameCycle z.out x} := by
  apply Fintype.card_congr
  apply Equiv.subtypeEquivRight
  intro x
  rw [← P.vertexClass_eq,P.vertexClass_out]
  exact eq_comm

end WalkPicture
end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_ConeFanCorner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation
open PictureSwitch PictureSwitch.PolygonTarget
attribute [local instance] Classical.propDecidable
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)

def leftDart (f : FanTriangle n w) : Dart n w := (.inr ⟨f.1,fanLeft n w f⟩,true)
def rightDart (f : FanTriangle n w) : Dart n w := (.inr ⟨f.1,fanRight n w f⟩,true)

def dartPart (l : Dart n w) : Bool :=
  match l.1 with
  | .inl _ => false
  | .inr v => linePart v.2.val

lemma endpoints_injective {f g : FanTriangle n w}
    (hl : leftDart n w f = leftDart n w g) (hr : rightDart n w f = rightDart n w g) : f = g := by
  rcases f with ⟨b,e⟩; rcases g with ⟨c,k⟩
  have hb : b = c := Sum.inr.inj (congrArg (start n w) hl)
  subst c
  have hleft : fanLeft n w ⟨b,e⟩ = fanLeft n w ⟨b,k⟩ :=
    (radialLabel_bijective n w b).1 (Subtype.ext hl)
  have hright : fanRight n w ⟨b,e⟩ = fanRight n w ⟨b,k⟩ :=
    (radialLabel_bijective n w b).1 (Subtype.ext hr)
  have he : e = k := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · exact Sum.inl.inj (congrArg Subtype.val hleft)
    · exact Sum.inr.inj (congrArg Subtype.val hright)
  cases he
  rfl

def corner (f : FanTriangle n w) (o : Bool) : (boundary n w d).Side :=
  ⟨.inl f,o,if o then (0 : Fin 3) else (2 : Fin 3)⟩

def cornerOut (f : FanTriangle n w) (o : Bool) : Dart n w :=
  if o then leftDart n w f else rightDart n w f

def cornerIn (f : FanTriangle n w) (o : Bool) : Dart n w :=
  if o then rightDart n w f else leftDart n w f

/-- These are precisely the two orientations of the apex corner of an
actual indexed fan triangle. No quotient by generator labels is made. -/
lemma apex_side_corner (f : FanTriangle n w) (o : Bool) (i : Fin 3)
    (ha : isApex n w (start n w ((boundary n w d).sideLabel ⟨.inl f,o,i⟩)) = true) :
    (⟨.inl f,o,i⟩ : (boundary n w d).Side) = corner n w d f o := by
  cases o <;> fin_cases i
  · cases ha
  · simp [Boundary.sideLabel,boundary,side,fanSide,rev_letter,start_letter,isApex] at ha
  · rfl
  · rfl
  · simp [Boundary.sideLabel,boundary,side,fanSide,start_letter,isApex] at ha
  · cases ha

lemma corner_bipartite (f : FanTriangle n w) (o : Bool) :
    dartPart n w (cornerOut n w f o) ≠ dartPart n w (cornerIn n w f o) := by
  cases o
  · change true ≠ false
    decide
  · change false ≠ true
    decide

/-- A reversed pair of apex corner ports determines the SAME fan triangle
with opposite orientation. This is the actual simple bipartite fan graph
fact that rules out a triangle-only two-step link in a reduced picture. -/
lemma reverse_corner_unique {f g : FanTriangle n w} {o p : Bool}
    (hout : cornerOut n w f o = cornerIn n w g p)
    (hin : cornerIn n w f o = cornerOut n w g p) : g = f ∧ p = !o := by
  cases o <;> cases p
  · have he := congrArg (dartPart n w) hout
    cases he
  · exact ⟨(endpoints_injective n w hin hout).symm,rfl⟩
  · exact ⟨(endpoints_injective n w hout hin).symm,rfl⟩
  · have he := congrArg (dartPart n w) hout
    cases he

end HyperbolicObstruction.ConeSkeleton
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_ConeFrozenTarget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation
open PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)

def freeReverse : Perm (Top n w × MacroGraph.graph.Dart) where
  toFun s := (s.1,s.2.symm)
  invFun s := (s.1,s.2.symm)
  left_inv := by intro s; rcases s with ⟨a,e⟩; rfl
  right_inv := by intro s; rcases s with ⟨a,e⟩; rfl

variable {A : Type*} [AddCommGroup A]

def walkFrozenTarget (c : Top n w → MacroGraph.graph.Dart → A)
    (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A) :
    FrozenTarget (walkTarget n w d c hc f) where
  next := Equiv.sumCongr 1 (frozenBoundary n w d).next
  reverse := Equiv.sumCongr (freeReverse n w) (frozenBoundary n w d).opposite
  reverse_eq := by rintro (s | s) <;> rfl
  reverse_sq := by
    apply Equiv.ext
    rintro (⟨a,e⟩ | ⟨a,b,i⟩)
    · rfl
    · cases b <;> rfl
  reverse_next := by
    rintro (s | s)
    · rfl
    · exact congrArg Sum.inr ((frozenBoundary n w d).reverse_next s)
  opposite_cycle := by
    let F : WalkStep n w d → Option (Top n w × MacroGraph.graph.Dart) :=
      fun s => match s with | .inl a => some a | .inr _ => none
    let G : WalkStep n w d → Option Bool :=
      fun s => match s with | .inl _ => none | .inr a => some a.2.1
    have hF : ∀ s, F ((Equiv.sumCongr (1 : Perm (Top n w × MacroGraph.graph.Dart)) (frozenBoundary n w d).next) s) = F s := by
      rintro (s | s) <;> rfl
    have hG : ∀ s, G ((Equiv.sumCongr (1 : Perm (Top n w × MacroGraph.graph.Dart)) (frozenBoundary n w d).next) s) = G s := by
      rintro (s | s) <;> rfl
    rintro (⟨a,e⟩ | ⟨a,b,i⟩) h
    · have hh := sameCycle_one.mp (semiconj_perm_sameCycle (t := (1 : Perm (Option (Top n w × MacroGraph.graph.Dart)))) hF h)
      have he : e = e.symm := congrArg Prod.snd (Option.some.inj hh)
      exact e.fst_ne_snd (congrArg (fun e : MacroGraph.graph.Dart => e.fst) he)
    · have hh := sameCycle_one.mp (semiconj_perm_sameCycle (t := (1 : Perm (Option Bool))) hG h)
      cases b <;> cases hh
  opposite_weight := by
    rintro (s | s)
    · exact walkWeight_opposite n w d c hc f (.inl s)
    · exact walkWeight_opposite n w d c hc f (.inr s)

end HyperbolicObstruction.ConeSkeleton
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_WalkFanCorner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation
open PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
universe u
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable {A : Type*} [AddCommGroup A]
variable (c : Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A)
variable (P : WalkPicture.{u} (walkTarget n w d c hc f))

lemma walk_start_link_constant {x y : P.Dart} (h : P.pairing.vertex.SameCycle x y) :
    start n w (walkLabel n w d (P.index x)) = start n w (walkLabel n w d (P.index y)) := by
  exact (sameCycle_le_of_apply
    (s := Setoid.ker (fun x => start n w (walkLabel n w d (P.index x))))
    (fun x => (P.respects.1 x).symm)) h

lemma walk_index_edge_previous (hm : P.FrozenMapped (walkFrozenTarget n w d c hc f))
    (x : P.Dart) (hy : walkFree n w d (walkKind n w d (P.index (P.pairing.vertex x))) = false) :
    P.index (P.pairing.edge x) =
      (walkFrozenTarget n w d c hc f).next⁻¹ (P.index (P.pairing.vertex x)) := by
  have he : walkFree n w d (walkKind n w d (P.index (P.pairing.edge x))) = false := by
    have hk := P.kind (P.pairing.edge x)
    change walkKind n w d (P.index (P.pairing.vertex x)) =
      walkKind n w d (P.index (P.pairing.edge x)) at hk
    rw [← hk]; exact hy
  apply (walkFrozenTarget n w d c hc f).next.injective
  simp only [Perm.inv_def,apply_symm_apply]
  exact (hm.commute ⟨P.pairing.edge x,he⟩).symm

variable {c hc f}
def frozenCorner (g : FanTriangle n w) (o : Bool) : WalkStep n w d :=
  .inr ⟨.inl g,o,if o then (0 : Fin 3) else (2 : Fin 3)⟩

lemma frozenCorner_label (g : FanTriangle n w) (o : Bool) :
    walkLabel n w d (frozenCorner n w d g o) = cornerOut n w g o := by
  cases o <;> rfl

lemma frozenCorner_previous (g : FanTriangle n w) (o : Bool) :
    rev n w (walkLabel n w d ((walkFrozenTarget n w d c hc f).next⁻¹
      (frozenCorner n w d g o))) = cornerIn n w g o := by
  cases o <;> rfl

lemma frozenCorner_reverse (g : FanTriangle n w) (o : Bool) :
    (walkFrozenTarget n w d c hc f).next⁻¹ (frozenCorner n w d g (!o)) =
      walkOpposite n w d (frozenCorner n w d g o) := by
  cases o <;> rfl

variable (c hc f)
lemma walk_corner_ports (hm : P.FrozenMapped (walkFrozenTarget n w d c hc f))
    {x : P.Dart} {g h : FanTriangle n w} {o p : Bool}
    (hx : P.index x = frozenCorner n w d g o)
    (hy : P.index (P.pairing.vertex x) = frozenCorner n w d h p) :
    cornerOut n w g o = cornerIn n w h p := by
  have he : walkLabel n w d (P.index (P.pairing.edge x)) =
      rev n w (walkLabel n w d (P.index x)) := P.respects.2 x
  rw [walk_index_edge_previous n w d c hc f P hm x (by rw [hy]; rfl),hy,hx,
    frozenCorner_label] at he
  have hh := congrArg (rev n w) he
  rw [frozenCorner_previous,rev_rev] at hh
  exact hh.symm

lemma walk_fan_corner {x : P.Dart} {g : FanTriangle n w} {o : Bool} {i : Fin 3}
    (hx : P.index x = .inr ⟨.inl g,o,i⟩)
    (ha : isApex n w (start n w (walkLabel n w d (P.index x))) = true) :
    P.index x = frozenCorner n w d g o := by
  rw [hx]
  have hh := apex_side_corner n w d g o i (by rw [hx] at ha; exact ha)
  cases o <;> fin_cases i <;> first | rfl | cases hh

end HyperbolicObstruction.ConeSkeleton
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_WalkConeLink
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation
open PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
universe u
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable {A : Type*} [AddCommGroup A]
variable (c : Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A)
variable (P : WalkPicture.{u} (walkTarget n w d c hc f))

lemma walk_apex_cases (x : P.Dart)
    (ha : isApex n w (start n w (walkLabel n w d (P.index x))) = true) :
    (∃ a e, P.index x = .inl (a,e)) ∨ ∃ g o, P.index x = frozenCorner n w d g o := by
  cases hx : P.index x with
  | inl s => exact Or.inl ⟨s.1,s.2,rfl⟩
  | inr s =>
    rcases s with ⟨g,o,i⟩
    rcases g with g | (s | z)
    · exact Or.inr ⟨g,o,by
        have h := walk_fan_corner n w d c hc f P hx ha
        rw [hx] at h
        exact h⟩
    · exfalso
      change Fin 4 at i
      rw [hx] at ha
      cases o with
      | false =>
        change isApex n w (start n w (rev n w (squareSide n w s i))) = true at ha
        rw [squareSide_end] at ha
        cases ha
      | true =>
        change isApex n w (start n w (squareSide n w s i)) = true at ha
        rw [squareSide_start] at ha
        cases ha
    · exfalso
      change Fin 6 at i
      rw [hx] at ha
      cases o with
      | false =>
        change isApex n w (start n w (rev n w (letterDart n w (z.val i)))) = true at ha
        rw [rev_letter,start_letter] at ha
        cases ha
      | true =>
        change isApex n w (start n w (letterDart n w (z.val i))) = true at ha
        rw [start_letter] at ha
        cases ha

lemma walk_link_card (hrad : P.RadialInjective (isApex n w)) (a : P.Dart) (b : Fan n w)
    (ha : start n w (walkLabel n w d (P.index a)) = .inr b) :
    Fintype.card {x : P.Dart // P.pairing.vertex.SameCycle a x} ≤ 5 := by
  let j : {x : P.Dart // P.pairing.vertex.SameCycle a x} → Outgoing n w b := fun x =>
    ⟨walkLabel n w d (P.index x.val),
      (walk_start_link_constant n w d c hc f P x.property).symm.trans ha⟩
  have hj : Function.Injective j := by
    intro x y hxy
    apply Subtype.ext
    apply hrad x.val y.val
    · change isApex n w (start n w (walkLabel n w d (P.index x.val))) = true
      rw [← walk_start_link_constant n w d c hc f P x.property,ha]; rfl
    · exact x.property.symm.trans y.property
    · exact congrArg Subtype.val hxy
  exact (Fintype.card_le_of_injective j hj).trans (card_outgoing n w b)

end HyperbolicObstruction.ConeSkeleton
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_WalkFanIncoming
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation
open PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
universe u
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable {A : Type*} [AddCommGroup A]
variable (c : Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A)
variable (P : WalkPicture.{u} (walkTarget n w d c hc f))

lemma walk_vertex_inverse (x : P.Dart) :
    P.pairing.vertex⁻¹ x = P.pairing.edge (P.pairing.face⁻¹ x) := by
  apply P.pairing.vertex.injective
  rw [Perm.inv_def,apply_symm_apply]
  change x = P.pairing.face (P.pairing.edge (P.pairing.edge (P.pairing.face⁻¹ x)))
  rw [P.pairing.edge_edge,Perm.inv_def,apply_symm_apply]

lemma walk_index_previous (hm : P.FrozenMapped (walkFrozenTarget n w d c hc f))
    (x : P.Dart) (hx : walkFree n w d (walkKind n w d (P.index x)) = false) :
    P.index (P.pairing.face⁻¹ x) = (walkFrozenTarget n w d c hc f).next⁻¹ (P.index x) := by
  have he : walkFree n w d (walkKind n w d (P.index (P.pairing.face⁻¹ x))) = false := by
    have hk := P.kind (P.pairing.face⁻¹ x)
    rw [Perm.inv_def,apply_symm_apply] at hk
    change walkKind n w d (P.index x) = walkKind n w d (P.index (P.pairing.face⁻¹ x)) at hk
    rw [← hk]; exact hx
  apply (walkFrozenTarget n w d c hc f).next.injective
  have hh := (hm.commute ⟨P.pairing.face⁻¹ x,he⟩).symm
  change (walkFrozenTarget n w d c hc f).next (P.index (P.pairing.face⁻¹ x)) =
    P.index (P.pairing.face (P.pairing.face⁻¹ x)) at hh
  simpa only [Perm.inv_def,apply_symm_apply] using hh

lemma walk_corner_incoming (hm : P.FrozenMapped (walkFrozenTarget n w d c hc f))
    {x : P.Dart} {g : FanTriangle n w} {o : Bool}
    (hx : P.index x = frozenCorner n w d g o) :
    walkLabel n w d (P.index (P.pairing.vertex⁻¹ x)) = cornerIn n w g o := by
  rw [walk_vertex_inverse]
  have hh := P.paired (P.pairing.face⁻¹ x)
  change walkLabel n w d (P.index (P.pairing.edge (P.pairing.face⁻¹ x))) =
    rev n w (walkLabel n w d (P.index (P.pairing.face⁻¹ x))) at hh
  rw [hh,walk_index_previous n w d c hc f P hm x (by rw [hx]; rfl),hx,
    frozenCorner_previous]

lemma walk_triangle_bipartite (hm : P.FrozenMapped (walkFrozenTarget n w d c hc f))
    {x : P.Dart} {g : FanTriangle n w} {o : Bool}
    (hx : P.index x = frozenCorner n w d g o) :
    dartPart n w (walkLabel n w d (P.index x)) ≠
      dartPart n w (walkLabel n w d (P.index (P.pairing.vertex⁻¹ x))) := by
  rw [walk_corner_incoming n w d c hc f P hm hx,hx,frozenCorner_label]
  exact corner_bipartite n w g o

end HyperbolicObstruction.ConeSkeleton
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_WalkFragment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation
open PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
universe u
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable {A : Type*} [AddCommGroup A]
variable (c : Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A)
variable (P : WalkPicture.{u} (walkTarget n w d c hc f))
variable (select : P.Face → Bool) (b : Fan n w)

lemma macroVertex_fan_slot (a : Top n w) (v : MacroGraph.Vertex)
    (h : macroVertex n w a v = .inr b) : ∃ i, slot n w a i = b := by
  rcases v with ((i|l)|⟨⟩)
  · exact ⟨i,Sum.inr.inj h⟩
  · cases h
  · cases h

/-- ALL selected top polygons incident to this fan occurrence, not only those
whose boundary actually visits it. -/
abbrev SelectedTop := {z : P.Face // select z = true ∧ ∃ a : Top n w,
  P.faceKind z = .inl a ∧ ∃ i, slot n w a i = b}

/-- Actual source vertices over this fan, represented in the chosen fragment. -/
abbrev ApexInstance := {z : P.Vertex //
  start n w (walkLabel n w d (P.index z.out)) = .inr b ∧
    ∃ x, P.vertexClass x = z ∧ select (P.faceClass x) = true}

lemma instance_start (z : ApexInstance n w d c hc f P select b) (x : P.Link z.val) :
    start n w (walkLabel n w d (P.index x.val)) = .inr b := by
  have hh : P.pairing.vertex.SameCycle z.val.out x.val :=
    P.vertexClass_eq.mp ((P.vertexClass_out _).trans x.property.symm)
  exact (walk_start_link_constant n w d c hc f P hh).symm.trans z.property.1

lemma instance_apex (z : ApexInstance n w d c hc f P select b) (x : P.Link z.val) :
    isApex n w (start n w (walkLabel n w d (P.index x.val))) = true := by
  rw [instance_start n w d c hc f P select b z x]; rfl

def selectedTopAt (z : ApexInstance n w d c hc f P select b) (x : P.Link z.val)
    (hs : select (P.faceClass x.val) = true)
    (ht : ∃ a e, P.index x.val = .inl (a,e)) : SelectedTop n w d c hc f P select b := by
  refine ⟨P.faceClass x.val,hs,?_⟩
  obtain ⟨a,e,hx⟩ := ht
  refine ⟨a,?_,?_⟩
  · change walkKind n w d (P.index x.val) = .inl a
    rw [hx]; rfl
  · apply macroVertex_fan_slot n w b a e.fst
    have hh := instance_start n w d c hc f P select b z x
    rw [hx] at hh
    exact (macroStep_start n w a e.adj).symm.trans hh

def fragmentMark (z : ApexInstance n w d c hc f P select b) (x : P.Link z.val) :
    FanLink.Mark (SelectedTop n w d c hc f P select b) :=
  if hs : select (P.faceClass x.val) = true then
    if ht : ∃ a e, P.index x.val = .inl (a,e) then
      .top (selectedTopAt n w d c hc f P select b z x hs ht)
    else .triangle
  else .absent

lemma mark_triangle_corner (z : ApexInstance n w d c hc f P select b) (x : P.Link z.val)
    (h : fragmentMark n w d c hc f P select b z x = .triangle) :
    ∃ g o, P.index x.val = frozenCorner n w d g o := by
  rcases walk_apex_cases n w d c hc f P x.val
    (instance_apex n w d c hc f P select b z x) with ⟨a,e,hx⟩ | hh
  · have ht : ∃ a e, P.index x.val = .inl (a,e) := ⟨a,e,hx⟩
    unfold fragmentMark at h
    split_ifs at h with hs
  · exact hh

lemma fragment_card (hrad : P.RadialInjective (isApex n w))
    (z : ApexInstance n w d c hc f P select b) : Fintype.card (P.Link z.val) ≤ 5 := by
  rw [P.link_card]
  exact walk_link_card n w d c hc f P hrad z.val.out b z.property.1

lemma fragment_bipartite (hm : P.FrozenMapped (walkFrozenTarget n w d c hc f))
    (z : ApexInstance n w d c hc f P select b) (x : P.Link z.val)
    (h : fragmentMark n w d c hc f P select b z x = .triangle) :
    dartPart n w (walkLabel n w d (P.index x.val)) ≠
      dartPart n w (walkLabel n w d (P.index (P.linkNext z.val x).val)) := by
  obtain ⟨g,o,hx⟩ := mark_triangle_corner n w d c hc f P select b z x h
  exact walk_triangle_bipartite n w d c hc f P hm hx

end HyperbolicObstruction.ConeSkeleton
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_ConeApexProducer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation
open PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
universe u
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable {A : Type*} [AddCommGroup A]
variable (c : Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A)
variable (P : WalkPicture.{u} (walkTarget n w d c hc f))
variable (select : P.Face → Bool)

abbrev SelectedOccurrence := {a : Top n w // ∃ F : P.Face, select F = true ∧ P.faceKind F = .inl a}

end HyperbolicObstruction.ConeSkeleton
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_WeightedCoincidence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
open scoped BigOperators
namespace HyperbolicObstruction
namespace Coincidence

variable {V C E : Type*} [Fintype V] [DecidableEq C]

/-- Coincidence rank on an actual subset of field positions. -/
def rankOn (c : V → C) (s : Finset V) : ℕ := s.card - (s.image c).card

/-- A maximum-weight representative of each nonempty unsigned class. -/
def maxRepresentative (c : V → C) (w : V → ℕ) (v : V) : V :=
  Classical.choose (Finset.exists_max_image (Finset.univ.filter (fun x => c x = c v)) w
    (by exact ⟨v,by simp⟩))

lemma maxRepresentative_mem (c : V → C) (w : V → ℕ) (v : V) :
    c (maxRepresentative c w v) = c v := by
  have h := (Classical.choose_spec (Finset.exists_max_image
    (Finset.univ.filter (fun x => c x = c v)) w (by exact ⟨v,by simp⟩))).1
  exact (Finset.mem_filter.mp h).2

lemma le_maxRepresentative (c : V → C) (w : V → ℕ) (v : V) :
    w v ≤ w (maxRepresentative c w v) := by
  exact (Classical.choose_spec (Finset.exists_max_image
    (Finset.univ.filter (fun x => c x = c v)) w (by exact ⟨v,by simp⟩))).2 v (by simp)

lemma maxRepresentative_eq (c : V → C) (w : V → ℕ) {u v : V} (h : c u = c v) :
    maxRepresentative c w u = maxRepresentative c w v := by
  unfold maxRepresentative
  congr 2
  ext x
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  rw [h]

lemma maxRepresentative_idem (c : V → C) (w : V → ℕ) (v : V) :
    maxRepresentative c w (maxRepresentative c w v) = maxRepresentative c w v :=
  maxRepresentative_eq c w (maxRepresentative_mem c w v)

variable [DecidableEq V]

/-- The representative/nonrepresentative partition computes rank at every
level. A maximal position remains selected whenever any class member does. -/
lemma rank_level (c : V → C) (w : V → ℕ) (j : ℕ) :
    rankOn c (Finset.univ.filter (fun v => j < w v)) =
      (Finset.univ.filter (fun v => j < w v ∧ v ≠ maxRepresentative c w v)).card := by
  let s : Finset V := Finset.univ.filter (fun v => j < w v)
  let t := s.filter (fun v => v = maxRepresentative c w v)
  have ht : s.image c = t.image c := by
    ext a
    constructor
    · intro ha
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp ha
      refine Finset.mem_image.mpr ⟨maxRepresentative c w v,?_,maxRepresentative_mem c w v⟩
      simp only [t,Finset.mem_filter,s,Finset.mem_univ,true_and]
      exact ⟨lt_of_lt_of_le (Finset.mem_filter.mp hv).2 (le_maxRepresentative c w v),
        (maxRepresentative_idem c w v).symm⟩
    · intro ha
      obtain ⟨v,hv,hv'⟩ := Finset.mem_image.mp ha
      exact Finset.mem_image.mpr ⟨v,(Finset.mem_filter.mp hv).1,hv'⟩
  have hi : Set.InjOn c t := by
    intro u hu v hv hc
    rw [(Finset.mem_filter.mp hu).2,(Finset.mem_filter.mp hv).2]
    exact maxRepresentative_eq c w hc
  have hh := Finset.card_filter_add_card_filter_not
    (s := s) (p := fun v => v = maxRepresentative c w v)
  change s.card - (s.image c).card = _
  rw [ht,Finset.card_image_of_injOn hi]
  have hfilter : s.filter (fun v => ¬v = maxRepresentative c w v) =
      Finset.univ.filter (fun v => j < w v ∧ v ≠ maxRepresentative c w v) := by
    ext v
    simp [s]
  change t.card + _ = s.card at hh
  rw [hfilter] at hh
  omega

omit [Fintype V] [DecidableEq V] in
lemma layer_cake (s : Finset V) (w : V → ℕ) (K : ℕ) (hK : ∀ v ∈ s, w v ≤ K) :
    ∑ j ∈ Finset.range K, (s.filter (fun v => j < w v)).card = ∑ v ∈ s, w v := by
  simp only [Finset.card_eq_sum_ones,Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v hv
  have hf : (Finset.range K).filter (fun j => j < w v) = Finset.range (w v) := by
    ext j
    simp only [Finset.mem_filter,Finset.mem_range]
    have hh := hK v hv
    omega
  rw [← Finset.sum_filter,hf]
  simp

/-- Exact integer layer-cake identity. -/
theorem sum_rank_levels (c : V → C) (w : V → ℕ) (K : ℕ) (hK : ∀ v, w v ≤ K) :
    ∑ j ∈ Finset.range K, rankOn c (Finset.univ.filter (fun v => j < w v)) =
      ∑ v ∈ Finset.univ.filter (fun v => v ≠ maxRepresentative c w v), w v := by
  simp_rw [rank_level]
  have he (j : ℕ) : Finset.univ.filter (fun v => j < w v ∧ v ≠ maxRepresentative c w v) =
      (Finset.univ.filter (fun v => v ≠ maxRepresentative c w v)).filter (fun v => j < w v) := by
    ext v
    simp [and_comm]
  simp_rw [he]
  exact layer_cake _ w K (fun v _ => hK v)

/-- Each letter contact is charged to an endpoint other than the class maximum.
This uses actual side capacities, not a forest assumption on the contact graph. -/
def contactCharge (c : V → C) (w : V → ℕ) (l r : E → V) (e : E) : V :=
  if l e = maxRepresentative c w (l e) then r e else l e

lemma contactCharge_endpoint (c : V → C) (w : V → ℕ) (l r : E → V) (e : E) :
    contactCharge c w l r e = l e ∨ contactCharge c w l r e = r e := by
  unfold contactCharge
  split_ifs <;> simp

lemma contactCharge_not_max (c : V → C) (w : V → ℕ) (l r : E → V)
    (hneq : ∀ e, l e ≠ r e) (hc : ∀ e, c (l e) = c (r e)) (e : E) :
    contactCharge c w l r e ≠ maxRepresentative c w (contactCharge c w l r e) := by
  unfold contactCharge
  split_ifs with h
  · intro h'
    apply hneq e
    exact h.trans ((maxRepresentative_eq c w (hc e)).trans h'.symm)
  · exact h

variable [Fintype E]

/-- The contact bound, valid for arbitrary cycles, multiple edges and repeats
of cell copies. Normality is precisely the inequality of the two field indices. -/
theorem contacts_le_weighted_rank (c : V → C) (w : V → ℕ) (l r : E → V)
    (hneq : ∀ e, l e ≠ r e) (hc : ∀ e, c (l e) = c (r e))
    (hcap : ∀ v, (Finset.univ.filter (fun e => l e = v ∨ r e = v)).card ≤ w v)
    (K : ℕ) (hK : ∀ v, w v ≤ K) :
    Fintype.card E ≤ ∑ j ∈ Finset.range K,
      rankOn c (Finset.univ.filter (fun v => j < w v)) := by
  rw [sum_rank_levels c w K hK]
  let f := contactCharge c w l r
  let s := Finset.univ.filter (fun v => v ≠ maxRepresentative c w v)
  have hf (e : E) : f e ∈ s := by
    simp only [s,Finset.mem_filter,Finset.mem_univ,true_and]
    exact contactCharge_not_max c w l r hneq hc e
  have hcard : Fintype.card E = ∑ v ∈ s, (Finset.univ.filter (fun e => f e = v)).card := by
    simp only [Finset.card_eq_sum_ones,Finset.sum_filter]
    rw [Finset.sum_comm]
    simp [hf]
  rw [hcard]
  apply Finset.sum_le_sum
  intro v hv
  apply le_trans (Finset.card_le_card ?_) (hcap v)
  intro e he
  have hh := (Finset.mem_filter.mp he).2
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(contactCharge_endpoint c w l r e).imp
    (fun h => h.symm.trans hh) (fun h => h.symm.trans hh)⟩

end Coincidence
end HyperbolicObstruction
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_PictureContact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch.PictureMap
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {X : Type*} [Fintype X] (P : PictureMap X)
variable (selected raw : X → Prop) (hraw : ∀ x, raw (P.edge x) ↔ raw x)

abbrev SelectedSide := {x : X // raw x ∧ selected x}
abbrev BoundarySide := {x : X // raw x ∧ selected x ∧ ¬selected (P.edge x)}
def number (_P : PictureMap X) (x : X) : Fin (Fintype.card X) := Fintype.equivFin X x
abbrev Contact := {x : X // raw x ∧ selected x ∧ selected (P.edge x) ∧
  P.number x < P.number (P.edge x)}

end HyperbolicObstruction.PictureSwitch.PictureMap
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_ActualContact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators
namespace HyperbolicObstruction.ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
universe u
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable {A : Type*} [AddCommGroup A]
variable (c : Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A)
variable (P : WalkPicture.{u} (walkTarget n w d c hc f)) (select : P.Face → Bool)

def selectedDart (x : P.Dart) : Prop := select (P.faceClass x) = true
def rawDart (x : P.Dart) : Prop := isLetter n w (walkLabel n w d (P.index x)) = true

abbrev ActualContact := P.pairing.Contact (selectedDart n w d c hc f P select) (rawDart n w d c hc f P)
abbrev ActualRawSide := PictureMap.SelectedSide (selectedDart n w d c hc f P select) (rawDart n w d c hc f P)
abbrev ActualRawBoundary := P.pairing.BoundarySide (selectedDart n w d c hc f P select) (rawDart n w d c hc f P)

end HyperbolicObstruction.ConeSkeleton
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_HSpaceFundamental
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual fundamental group of an H-space is abelian. The proof uses the
relative unit homotopies, not an assumed pi-2 comparison theorem. -/
noncomputable section

open scoped Topology unitInterval
namespace HyperbolicObstruction.HSpaceFundamental
open Path.Homotopic
variable {X : Type*} [TopologicalSpace X] [HSpace X]
local notation "e" => (HSpace.e : X)
local notation "m" => (HSpace.hmul : C(X × X,X))

def combine (p q : FundamentalGroup X e) : FundamentalGroup X e :=
  ((Path.Homotopic.prod p q).map m).cast HSpace.hmul_e_e.symm HSpace.hmul_e_e.symm

def combinePath (p q : Path e e) : Path e e :=
  ((p.prod q).map (HSpace.hmul : C(X × X,X)).continuous).cast HSpace.hmul_e_e.symm HSpace.hmul_e_e.symm
lemma combine_mk (p q : Path e e) :
    combine (Path.Homotopic.Quotient.mk p) (Path.Homotopic.Quotient.mk q) = Path.Homotopic.Quotient.mk (combinePath p q) := rfl

lemma combine_refl_right (p : Path e e) :
    (combinePath p (Path.refl e)).Homotopic p := by
  refine ⟨{ toFun := fun tx => HSpace.hmulE (tx.1,p tx.2)
            continuous_toFun := by fun_prop
            map_zero_left := ?_
            map_one_left := ?_
            prop' := ?_ }⟩
  · intro t
    exact HSpace.hmulE.map_zero_left (p t)
  · intro t
    exact HSpace.hmulE.map_one_left (p t)
  · intro t s hs
    rcases hs with hs|hs
    · subst s
      exact ((congrArg (fun x => HSpace.hmulE (t, x)) p.source).trans
        ((HSpace.hmulE.prop t e (Set.mem_singleton e)).trans HSpace.hmul_e_e)).trans
        (combinePath p (Path.refl e)).source.symm
    · simp only [Set.mem_singleton_iff] at hs
      subst s
      exact ((congrArg (fun x => HSpace.hmulE (t, x)) p.target).trans
        ((HSpace.hmulE.prop t e (Set.mem_singleton e)).trans HSpace.hmul_e_e)).trans
        (combinePath p (Path.refl e)).target.symm

lemma combine_refl_left (p : Path e e) :
    (combinePath (Path.refl e) p).Homotopic p := by
  refine ⟨{ toFun := fun tx => HSpace.eHmul (tx.1,p tx.2)
            continuous_toFun := by fun_prop
            map_zero_left := ?_
            map_one_left := ?_
            prop' := ?_ }⟩
  · intro t
    exact HSpace.eHmul.map_zero_left (p t)
  · intro t
    exact HSpace.eHmul.map_one_left (p t)
  · intro t s hs
    rcases hs with hs|hs
    · subst s
      exact ((congrArg (fun x => HSpace.eHmul (t, x)) p.source).trans
        ((HSpace.eHmul.prop t e (Set.mem_singleton e)).trans HSpace.hmul_e_e)).trans
        (combinePath (Path.refl e) p).source.symm
    · simp only [Set.mem_singleton_iff] at hs
      subst s
      exact ((congrArg (fun x => HSpace.eHmul (t, x)) p.target).trans
        ((HSpace.eHmul.prop t e (Set.mem_singleton e)).trans HSpace.hmul_e_e)).trans
        (combinePath (Path.refl e) p).target.symm

lemma combine_one_right (p : FundamentalGroup X e) : combine p 1 = p := by
  induction p using Path.Homotopic.Quotient.ind with | mk p =>
  exact Path.Homotopic.Quotient.eq.mpr (combine_refl_right p)
lemma combine_one_left (p : FundamentalGroup X e) : combine 1 p = p := by
  induction p using Path.Homotopic.Quotient.ind with | mk p =>
  exact Path.Homotopic.Quotient.eq.mpr (combine_refl_left p)

lemma combine_interchange (a b c d : FundamentalGroup X e) :
    combine (a * b) (c * d) = combine a c * combine b d := by
  induction a using Path.Homotopic.Quotient.ind with | mk a =>
  induction b using Path.Homotopic.Quotient.ind with | mk b =>
  induction c using Path.Homotopic.Quotient.ind with | mk c =>
  induction d using Path.Homotopic.Quotient.ind with | mk d =>
  apply congrArg Path.Homotopic.Quotient.mk
  ext t
  simp only [Path.cast_coe,Path.map_coe,Function.comp_apply,
    Path.prod_coe,Path.trans_apply]
  split_ifs <;> rfl

lemma combine_eq_mul (p q : FundamentalGroup X e) : combine p q = p * q := by
  have hh := combine_interchange p 1 1 q
  simpa only [mul_one,one_mul,combine_one_left,combine_one_right] using hh

end HyperbolicObstruction.HSpaceFundamental
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_HSpacePathObstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The cellular obstruction and its exact change under edge corrections. -/
noncomputable section

open scoped Topology unitInterval
namespace HyperbolicObstruction.HSpacePathObstruction
open Path.Homotopic
variable {Y : Type*} [TopologicalSpace Y] [HSpace Y]
local notation "e" => (HSpace.e : Y)
local notation "Q" => Path.Homotopic.Quotient.mk
local notation "m" => (HSpace.hmul : C(Y × Y,Y))

def pairToUnit {a b : Y} (p : Path a e) (q : Path b e) : Path (m (a,b)) e :=
  ((p.prod q).map (HSpace.hmul : C(Y × Y,Y)).continuous).cast rfl HSpace.hmul_e_e.symm

lemma pairToUnit_trans {a b : Y} (p : Path a e) (q : Path b e)
    (u v : Path e e) :
    pairToUnit (p.trans u) (q.trans v) =
      (pairToUnit p q).trans (HSpaceFundamental.combinePath u v) := by
  ext t
  simp only [pairToUnit,HSpaceFundamental.combinePath,Path.cast_coe,Path.map_coe,
    Function.comp_apply,Path.prod_coe,Path.trans_apply]
  split_ifs <;> rfl

def loopClass (p : Path e e) : FundamentalGroup Y e := Q p

lemma loopClass_combine (u v : Path e e) :
    loopClass (HSpaceFundamental.combinePath u v) = loopClass u * loopClass v :=
  (HSpaceFundamental.combine_mk u v).symm.trans
    (HSpaceFundamental.combine_eq_mul (loopClass u) (loopClass v))

/-- Difference of two paths ending at the same basepoint. -/
def difference {a : Y} (p q : Path a e) : FundamentalGroup Y e := Q (p.symm.trans q)

lemma difference_eq_one_iff {a : Y} (p q : Path a e) :
    difference p q = 1 ↔ p.Homotopic q := by
  constructor
  · intro h
    have hh := congrArg (fun z => (Q p).trans z) h
    change (Q p).trans ((Q p).symm.trans (Q q)) = (Q p).trans (.refl e) at hh
    rw [←Path.Homotopic.Quotient.trans_assoc,Path.Homotopic.Quotient.trans_symm,
      Path.Homotopic.Quotient.refl_trans,Path.Homotopic.Quotient.trans_refl] at hh
    exact Path.Homotopic.symm (Path.Homotopic.Quotient.eq.mp hh)
  · intro h
    change (Q p).symm.trans (Q q) = _
    rw [←Path.Homotopic.Quotient.eq.mpr h,Path.Homotopic.Quotient.symm_trans]
    rfl

lemma difference_trans {a : Y} (p q : Path a e) (u v : Path e e) :
    difference (p.trans u) (q.trans v) =
      loopClass v * difference p q * (loopClass u)⁻¹ := by
  change Q ((p.trans u).symm.trans (q.trans v)) =
    (Q u).symm.trans ((Q (p.symm.trans q)).trans (Q v))
  rw [Path.trans_symm]
  simp only [Path.Homotopic.Quotient.mk_trans,Path.Homotopic.Quotient.mk_symm,
    Path.Homotopic.Quotient.trans_assoc]

variable {a b c d : Y}
/-- Obstruction for a face joining the products of its opposite pairs. -/
def obstruction (F : Path (m (a,b)) (m (c,d)))
    (pa : Path a e) (pb : Path b e) (pc : Path c e) (pd : Path d e) :
    FundamentalGroup Y e := difference (pairToUnit pa pb) (F.trans (pairToUnit pc pd))

lemma correction (F : Path (m (a,b)) (m (c,d)))
    (pa : Path a e) (pb : Path b e) (pc : Path c e) (pd : Path d e)
    (ua ub uc ud : Path e e) :
    obstruction F (pa.trans ua) (pb.trans ub) (pc.trans uc) (pd.trans ud) =
      (loopClass uc * loopClass ud) * obstruction F pa pb pc pd *
        (loopClass ua * loopClass ub)⁻¹ := by
  unfold obstruction
  rw [pairToUnit_trans,pairToUnit_trans]
  have ha : Q (F.trans ((pairToUnit pc pd).trans (HSpaceFundamental.combinePath uc ud))) =
      Q ((F.trans (pairToUnit pc pd)).trans (HSpaceFundamental.combinePath uc ud)) := by
    simp only [Path.Homotopic.Quotient.mk_trans,Path.Homotopic.Quotient.trans_assoc]
  change (Q _).symm.trans (Q _) = _
  rw [ha]
  change difference ((pairToUnit pa pb).trans (HSpaceFundamental.combinePath ua ub))
      ((F.trans (pairToUnit pc pd)).trans (HSpaceFundamental.combinePath uc ud)) = _
  rw [difference_trans,loopClass_combine,loopClass_combine]

/-- The face extends once the corrected obstruction is killed, with the actual
prescribed boundary paths retained. -/
lemma obstruction_vanishes_iff (F : Path (m (a,b)) (m (c,d)))
    (pa : Path a e) (pb : Path b e) (pc : Path c e) (pd : Path d e) :
    obstruction F pa pb pc pd = 1 ↔
      ((pairToUnit pa pb).trans (Path.refl e)).Homotopic (F.trans (pairToUnit pc pd)) := by
  rw [obstruction,difference_eq_one_iff]
  constructor
  · intro h
    exact (Path.Homotopic.trans_refl _).trans h
  · intro h
    exact (Path.Homotopic.trans_refl _).symm.trans h

end HyperbolicObstruction.HSpacePathObstruction
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_SquarePathFilling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section


/-! A literal square with prescribed boundary paths, constructed from a relative
path homotopy by an explicit compact quotient. -/
noncomputable section
open scoped Topology unitInterval
open Topology
namespace HyperbolicObstruction.SquarePathFilling

def low (s : I) : ℝ := max (2 * (s : ℝ) - 1) 0
def high (s : I) : ℝ := min (2 * (s : ℝ)) 1
lemma bounds (s : I) : 0 ≤ low s ∧ low s ≤ high s ∧ high s ≤ 1 := by
  have h0 := s.property.1
  have h1 := s.property.2
  unfold low high
  constructor
  · exact le_max_right _ _
  constructor
  · apply max_le <;> apply le_min <;> linarith
  · exact min_le_right _ _
lemma sum (s : I) : high s + low s = 2 * (s : ℝ) := by
  unfold high low
  by_cases h : (s : ℝ) ≤ 1/2
  · rw [min_eq_left (by linarith),max_eq_right (by linarith)]; ring
  · rw [min_eq_right (by linarith),max_eq_left (by linarith)]; ring
lemma gap_pos {s : I} (h0 : (0 : ℝ) < s) (h1 : (s : ℝ) < 1) : low s < high s := by
  unfold high low
  apply max_lt <;> apply lt_min <;> linarith
lemma low_continuous : Continuous low := by unfold low; fun_prop
lemma high_continuous : Continuous high := by unfold high; fun_prop

/-- Horizontal parameter selects a broken boundary path; vertical parameter
runs from its common source to its common target. -/
def quotient : C(I × I,I × I) where
  toFun ts :=
    (⟨(1 - (ts.1 : ℝ)) * high ts.2 + (ts.1 : ℝ) * low ts.2, by
      have ht0 := ts.1.property.1
      have ht1 := ts.1.property.2
      have hb := bounds ts.2
      constructor <;> nlinarith⟩,
     ⟨(1 - (ts.1 : ℝ)) * low ts.2 + (ts.1 : ℝ) * high ts.2, by
      have ht0 := ts.1.property.1
      have ht1 := ts.1.property.2
      have hb := bounds ts.2
      constructor <;> nlinarith⟩)
  continuous_toFun := by
    apply Continuous.prodMk <;> apply Continuous.subtype_mk
    · exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
        (high_continuous.comp continuous_snd)).add
        ((continuous_subtype_val.comp continuous_fst).mul (low_continuous.comp continuous_snd))
    · exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
        (low_continuous.comp continuous_snd)).add
        ((continuous_subtype_val.comp continuous_fst).mul (high_continuous.comp continuous_snd))

lemma quotient_sum (t s : I) :
    ((quotient (t,s)).1 : ℝ) + ((quotient (t,s)).2 : ℝ) = 2 * (s : ℝ) := by
  change (1-(t:ℝ))*high s+(t:ℝ)*low s+((1-(t:ℝ))*low s+(t:ℝ)*high s) = _
  nlinarith [sum s]

lemma quotient_fiber {t s t' s' : I} (h : quotient (t,s) = quotient (t',s')) :
    s = s' ∧ (t = t' ∨ s = 0 ∨ s = 1) := by
  have hsum : 2 * (s : ℝ) = 2 * (s' : ℝ) := by
    rw [←quotient_sum t s,←quotient_sum t' s',h]
  have hs : s = s' := Subtype.ext (by linarith)
  refine ⟨hs,?_⟩
  subst s'
  by_cases h0 : s = 0
  · exact Or.inr (Or.inl h0)
  by_cases h1 : s = 1
  · exact Or.inr (Or.inr h1)
  left
  have h0' : (0 : ℝ) < s := lt_of_le_of_ne s.property.1 (by
    intro he; exact h0 (Subtype.ext he.symm))
  have h1' : (s : ℝ) < 1 := lt_of_le_of_ne s.property.2 (by
    intro he; exact h1 (Subtype.ext he))
  have ht := congrArg (fun z : I × I => (z.2 : ℝ)) h
  change (1-(t:ℝ))*low s+(t:ℝ)*high s =
    (1-(t':ℝ))*low s+(t':ℝ)*high s at ht
  have hg := gap_pos h0' h1'
  apply Subtype.ext
  nlinarith

lemma quotient_surjective : Function.Surjective quotient := by
  rintro ⟨x,y⟩
  let s : I := ⟨((x : ℝ)+(y : ℝ))/2,by constructor <;>
    linarith [x.property.1,x.property.2,y.property.1,y.property.2]⟩
  have slo : low s ≤ (y : ℝ) := by
    dsimp [low,s]
    apply max_le <;> linarith [x.property.2,y.property.1]
  have shi : (y : ℝ) ≤ high s := by
    dsimp [high,s]
    apply le_min <;> linarith [x.property.1,y.property.2]
  by_cases hz : high s = low s
  · refine ⟨(0,s),?_⟩
    have hy : (y : ℝ) = low s := by linarith
    have hx : (x : ℝ) = low s := by
      have hh := sum s
      dsimp [s] at hh
      linarith
    apply Prod.ext <;> apply Subtype.ext <;> dsimp [quotient]
    · norm_num; linarith
    · norm_num; exact hy.symm
  · have hp : 0 < high s - low s := by
      have := (bounds s).2.1
      exact sub_pos.mpr (lt_of_le_of_ne this (Ne.symm hz))
    let t : I := ⟨((y : ℝ) - low s)/(high s - low s),by
      constructor
      · exact div_nonneg (sub_nonneg.mpr slo) hp.le
      · exact (div_le_one hp).mpr (by linarith)⟩
    have he : (t : ℝ) * (high s - low s) = (y : ℝ) - low s := by
      dsimp [t]
      exact div_mul_cancel₀ _ hp.ne'
    refine ⟨(t,s),?_⟩
    apply Prod.ext <;> apply Subtype.ext <;> dsimp [quotient]
    · have hh := sum s
      dsimp [s] at hh
      nlinarith
    · nlinarith

lemma quotient_isQuotientMap : IsQuotientMap quotient :=
  quotient.continuous.isClosedMap.isQuotientMap quotient.continuous quotient_surjective

variable {X : Type*} [TopologicalSpace X] {a b c d : X}
  {p : Path a b} {q : Path a c} {r : Path b d} {s : Path c d}

lemma homotopy_fiber (H : (p.trans r).Homotopy (q.trans s))
    {z z' : I × I} (h : quotient z = quotient z') : H z = H z' := by
  rcases z with ⟨t,v⟩
  rcases z' with ⟨t',v'⟩
  obtain ⟨rfl,hh⟩ := quotient_fiber h
  rcases hh with rfl|rfl|rfl <;> simp

/-- The actual square filling, with no extension assumption. -/
def fill (H : (p.trans r).Homotopy (q.trans s)) : C(I × I,X) where
  toFun z := H (quotient_surjective z).choose
  continuous_toFun := by
    apply quotient_isQuotientMap.continuous_iff.mpr
    have he : (fun z => H (quotient_surjective z).choose) ∘ quotient = H := by
      funext z
      exact homotopy_fiber H (quotient_surjective (quotient z)).choose_spec
    rw [he]
    exact H.continuous

lemma fill_quotient (H : (p.trans r).Homotopy (q.trans s)) (z : I × I) :
    fill H (quotient z) = H z :=
  homotopy_fiber H (quotient_surjective (quotient z)).choose_spec

def half (x : I) : I := ⟨(x:ℝ)/2,by constructor <;>
  linarith [x.property.1,x.property.2]⟩
def upper (x : I) : I := ⟨((x:ℝ)+1)/2,by constructor <;>
  linarith [x.property.1,x.property.2]⟩
lemma low_half (x : I) : low (half x) = 0 := by
  dsimp [low,half]; rw [max_eq_right (by linarith [x.property.2])]
lemma high_half (x : I) : high (half x) = (x:ℝ) := by
  dsimp [high,half]; rw [min_eq_left (by linarith [x.property.2])]; ring
lemma low_upper (x : I) : low (upper x) = (x:ℝ) := by
  dsimp [low,upper]; rw [max_eq_left (by linarith [x.property.1])]; ring
lemma high_upper (x : I) : high (upper x) = 1 := by
  dsimp [high,upper]; rw [min_eq_right (by linarith [x.property.1])]

lemma quotient_bottom (x : I) : quotient (0,half x) = (x,0) := by
  apply Prod.ext <;> apply Subtype.ext <;>
    simp [quotient,low_half,high_half]
lemma quotient_left (x : I) : quotient (1,half x) = (0,x) := by
  apply Prod.ext <;> apply Subtype.ext <;>
    simp [quotient,low_half,high_half]
lemma quotient_right (x : I) : quotient (0,upper x) = (1,x) := by
  apply Prod.ext <;> apply Subtype.ext <;>
    simp [quotient,low_upper,high_upper]
lemma quotient_top (x : I) : quotient (1,upper x) = (x,1) := by
  apply Prod.ext <;> apply Subtype.ext <;>
    simp [quotient,low_upper,high_upper]

lemma trans_half (p : Path a b) (r : Path b d) (x : I) :
    p.trans r (half x) = p x := by
  rw [←Path.extend_apply,Path.extend_trans_of_le_half p r (by
    change (x:ℝ)/2 ≤ 1/2; linarith [x.property.2])]
  have he : 2 * (half x : ℝ) = (x:ℝ) := by dsimp [half]; ring
  rw [he,Path.extend_apply]
lemma trans_upper (p : Path a b) (r : Path b d) (x : I) :
    p.trans r (upper x) = r x := by
  rw [←Path.extend_apply,Path.extend_trans_of_half_le p r (by
    change 1/2 ≤ ((x:ℝ)+1)/2; linarith [x.property.1])]
  have he : 2 * (upper x : ℝ) - 1 = (x:ℝ) := by dsimp [upper]; ring
  rw [he,Path.extend_apply]

@[simp] lemma fill_bottom (H : (p.trans r).Homotopy (q.trans s)) (x : I) :
    fill H (x,0) = p x := by
  rw [←quotient_bottom x,fill_quotient]
  simpa using trans_half p r x
@[simp] lemma fill_left (H : (p.trans r).Homotopy (q.trans s)) (x : I) :
    fill H (0,x) = q x := by
  rw [←quotient_left x,fill_quotient]
  simpa using trans_half q s x
@[simp] lemma fill_right (H : (p.trans r).Homotopy (q.trans s)) (x : I) :
    fill H (1,x) = r x := by
  rw [←quotient_right x,fill_quotient]
  simpa using trans_upper p r x
@[simp] lemma fill_top (H : (p.trans r).Homotopy (q.trans s)) (x : I) :
    fill H (x,1) = s x := by
  rw [←quotient_top x,fill_quotient]
  simpa using trans_upper q s x

end HyperbolicObstruction.SquarePathFilling
end
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_ParameterizedSquareFilling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Boundary-prescribed fillings depend continuously on parameters. This gives
literal square-prism extensions, rather than formal cellular coefficients. -/
noncomputable section

open scoped Topology unitInterval
open Topology
namespace HyperbolicObstruction.SquarePathFilling
variable {X : Type*} [TopologicalSpace X] {a b c d : X}
  {p : Path a b} {q : Path a c} {r : Path b d} {s : Path c d}

lemma quotient_zero (t : I) : quotient (t,0) = (0,0) := by
  apply Prod.ext <;> apply Subtype.ext <;> simp [quotient,low,high]
lemma quotient_one (t : I) : quotient (t,1) = (1,1) := by
  apply Prod.ext <;> apply Subtype.ext <;> norm_num [quotient,low,high]

/-- Recover the relative path homotopy from a genuine square having the
specified four boundary sides. -/
def unfill (f : C(I × I,X))
    (hb : ∀ x, f (x,0) = p x) (hl : ∀ x, f (0,x) = q x)
    (hr : ∀ x, f (1,x) = r x) (ht : ∀ x, f (x,1) = s x) :
    (p.trans r).Homotopy (q.trans s) where
  toContinuousMap := f.comp quotient
  map_zero_left x := by
    by_cases hx : (x:ℝ) ≤ 1/2
    · have hlow : low x = 0 := by unfold low; rw [max_eq_right (by linarith)]
      have hhigh : high x = 2*(x:ℝ) := by unfold high; rw [min_eq_left (by linarith)]
      have he : quotient (0,x) = (⟨2*(x:ℝ),by constructor <;> linarith [x.property.1]⟩,0) := by
        apply Prod.ext <;> apply Subtype.ext <;> simp [quotient,hlow,hhigh]
      change f (quotient (0,x)) = _
      rw [he,hb]
      change _ = p.trans r x
      rw [Path.trans_apply,dite_eq_left hx]
    · have hlow : low x = 2*(x:ℝ)-1 := by unfold low; rw [max_eq_left (by linarith)]
      have hhigh : high x = 1 := by unfold high; rw [min_eq_right (by linarith)]
      have he : quotient (0,x) = (1,⟨2*(x:ℝ)-1,by constructor <;> linarith [x.property.2]⟩) := by
        apply Prod.ext <;> apply Subtype.ext <;> simp [quotient,hlow,hhigh]
      change f (quotient (0,x)) = _
      rw [he,hr]
      change _ = p.trans r x
      rw [Path.trans_apply,dite_eq_right hx]
  map_one_left x := by
    by_cases hx : (x:ℝ) ≤ 1/2
    · have hlow : low x = 0 := by unfold low; rw [max_eq_right (by linarith)]
      have hhigh : high x = 2*(x:ℝ) := by unfold high; rw [min_eq_left (by linarith)]
      have he : quotient (1,x) = (0,⟨2*(x:ℝ),by constructor <;> linarith [x.property.1]⟩) := by
        apply Prod.ext <;> apply Subtype.ext <;> simp [quotient,hlow,hhigh]
      change f (quotient (1,x)) = _
      rw [he,hl]
      change _ = q.trans s x
      rw [Path.trans_apply,dite_eq_left hx]
    · have hlow : low x = 2*(x:ℝ)-1 := by unfold low; rw [max_eq_left (by linarith)]
      have hhigh : high x = 1 := by unfold high; rw [min_eq_right (by linarith)]
      have he : quotient (1,x) = (⟨2*(x:ℝ)-1,by constructor <;> linarith [x.property.2]⟩,1) := by
        apply Prod.ext <;> apply Subtype.ext <;> simp [quotient,hlow,hhigh]
      change f (quotient (1,x)) = _
      rw [he,ht]
      change _ = q.trans s x
      rw [Path.trans_apply,dite_eq_right hx]
  prop' t x hx := by
    rcases hx with rfl|hx
    · change f (quotient (t,0)) = _
      rw [quotient_zero,hb]; simp
    · simp only [Set.mem_singleton_iff] at hx
      subst x
      change f (quotient (t,1)) = _
      rw [quotient_one,hr]; simp

@[simp] lemma fill_unfill (f : C(I × I,X))
    (hb : ∀ x, f (x,0) = p x) (hl : ∀ x, f (0,x) = q x)
    (hr : ∀ x, f (1,x) = r x) (ht : ∀ x, f (x,1) = s x) :
    fill (unfill f hb hl hr ht) = f := by
  ext z
  obtain ⟨z,rfl⟩ := quotient_surjective z
  rw [fill_quotient]; rfl

variable {T : Type*} [TopologicalSpace T] [CompactSpace T] [T2Space T]

/-- The product quotient is an actual compact closed quotient, ensuring
continuous families of fillings without a choice-continuity assumption. -/
def paramQuotient : C(T × (I × I),T × (I × I)) :=
  (ContinuousMap.id T).prodMap quotient
omit [CompactSpace T] [T2Space T] in
lemma paramQuotient_surjective : Function.Surjective (paramQuotient (T := T)) := by
  rintro ⟨t,z⟩
  obtain ⟨w,rfl⟩ := quotient_surjective z
  exact ⟨(t,w),rfl⟩
lemma paramQuotient_isQuotientMap : IsQuotientMap (paramQuotient (T := T)) :=
  paramQuotient.continuous.isClosedMap.isQuotientMap paramQuotient.continuous
    paramQuotient_surjective

variable (b : X)
omit [CompactSpace T] [T2Space T] in
lemma loopFamily_fiber (F : C(T × I,Path b b)) (t : T)
    {z z' : I × I} (h : quotient z = quotient z') : F (t,z.1) z.2 = F (t,z'.1) z'.2 := by
  rcases z with ⟨v,s⟩
  rcases z' with ⟨v',s'⟩
  obtain ⟨rfl,hh⟩ := quotient_fiber h
  rcases hh with rfl|rfl|rfl <;> simp

/-- A family of loop-space paths determines a family of actual square maps. -/
def paramFill (F : C(T × I,Path b b)) : C(T × (I × I),X) where
  toFun tz := F (tz.1,(quotient_surjective tz.2).choose.1)
    (quotient_surjective tz.2).choose.2
  continuous_toFun := by
    apply paramQuotient_isQuotientMap.continuous_iff.mpr
    have he : (fun tz : T × (I × I) => F (tz.1,(quotient_surjective tz.2).choose.1)
        (quotient_surjective tz.2).choose.2) ∘ paramQuotient =
        fun tz : T × (I × I) => F (tz.1,tz.2.1) tz.2.2 := by
      funext tz
      exact loopFamily_fiber b F tz.1 (quotient_surjective (quotient tz.2)).choose_spec
    rw [he]
    exact Path.continuous_uncurry_iff.mpr (F.continuous.comp
      (continuous_fst.prodMk (continuous_fst.comp continuous_snd)))
      |>.comp (continuous_id.prodMk (continuous_snd.comp continuous_snd))

lemma paramFill_quotient (F : C(T × I,Path b b)) (t : T) (z : I × I) :
    paramFill b F (t,quotient z) = F (t,z.1) z.2 := by
  exact loopFamily_fiber b F t (quotient_surjective (quotient z)).choose_spec

end HyperbolicObstruction.SquarePathFilling
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_PathHomotopyTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section


/-! The genuine compact-open path space realizes relative homotopies as paths.
This is the two-dimensional path-space interface used for cellular obstructions. -/
noncomputable section
open scoped Topology unitInterval
namespace HyperbolicObstruction.PathHomotopyTopology
variable {X : Type*} [TopologicalSpace X] {a b : X} {p q : Path a b}

def fromHomotopy (H : p.Homotopy q) : Path p q where
  toFun := H.eval
  continuous_toFun := Path.continuous_uncurry_iff.mp H.continuous
  source' := H.eval_zero
  target' := H.eval_one

@[simp] lemma fromHomotopy_apply (H : p.Homotopy q) (t s : I) :
    fromHomotopy H t s = H (t,s) := rfl

end HyperbolicObstruction.PathHomotopyTopology
end
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_BasedSquareContraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A vanishing actual pi-2 obstruction constructs a continuous square
contraction with four independently prescribed edge contractions. -/
noncomputable section

open scoped Topology unitInterval
namespace HyperbolicObstruction.BasedSquareContraction
open HSpacePathObstruction
variable {X : Type*} [TopologicalSpace X] (b : X)
variable {p q r s : Path b b}
variable (f : C(I × I,X))
  (hb : ∀ x, f (x,0) = p x) (hl : ∀ x, f (0,x) = q x)
  (hr : ∀ x, f (1,x) = r x) (ht : ∀ x, f (x,1) = s x)

def facePath : Path (p.trans r) (q.trans s) :=
  PathHomotopyTopology.fromHomotopy (SquarePathFilling.unfill f hb hl hr ht)

variable (hp : Path p (Path.refl b)) (hq : Path q (Path.refl b)) (hr' : Path r (Path.refl b)) (hs : Path s (Path.refl b))

def faceObstruction : FundamentalGroup (Path b b) (Path.refl b) :=
  obstruction (facePath b f hb hl hr ht) hp hr' hq hs

variable (hz : faceObstruction b f hb hl hr ht hp hq hr' hs = 1)

def loopSquare : C(I × I,Path b b) :=
  SquarePathFilling.fill
    ((obstruction_vanishes_iff (facePath b f hb hl hr ht) hp hr' hq hs).mp hz).some

@[simp] lemma loopSquare_bottom (t : I) :
    loopSquare b f hb hl hr ht hp hq hr' hs hz (t,0) = (hp t).trans (hr' t) :=
  SquarePathFilling.fill_bottom _ t
@[simp] lemma loopSquare_top (t : I) :
    loopSquare b f hb hl hr ht hp hq hr' hs hz (t,1) = (hq t).trans (hs t) :=
  SquarePathFilling.fill_top _ t
@[simp] lemma loopSquare_left (t : I) :
    loopSquare b f hb hl hr ht hp hq hr' hs hz (0,t) = facePath b f hb hl hr ht t :=
  SquarePathFilling.fill_left _ t
@[simp] lemma loopSquare_right (t : I) :
    loopSquare b f hb hl hr ht hp hq hr' hs hz (1,t) = Path.refl b :=
  SquarePathFilling.fill_right _ t

/-- Literal face homotopy. Its domain is the actual closed square prism. -/
def contraction : C(I × (I × I),X) :=
  SquarePathFilling.paramFill b (loopSquare b f hb hl hr ht hp hq hr' hs hz)

@[simp] lemma contraction_initial (z : I × I) :
    contraction b f hb hl hr ht hp hq hr' hs hz (0,z) = f z := by
  obtain ⟨z,rfl⟩ := SquarePathFilling.quotient_surjective z
  unfold contraction
  rw [SquarePathFilling.paramFill_quotient,loopSquare_left]
  rfl
@[simp] lemma contraction_final (z : I × I) :
    contraction b f hb hl hr ht hp hq hr' hs hz (1,z) = b := by
  obtain ⟨z,rfl⟩ := SquarePathFilling.quotient_surjective z
  unfold contraction
  rw [SquarePathFilling.paramFill_quotient,loopSquare_right]
  rfl
@[simp] lemma contraction_bottom (t x : I) :
    contraction b f hb hl hr ht hp hq hr' hs hz (t,(x,0)) = hp t x := by
  unfold contraction
  rw [←SquarePathFilling.quotient_bottom x,SquarePathFilling.paramFill_quotient,loopSquare_bottom]
  exact SquarePathFilling.trans_half _ _ x
@[simp] lemma contraction_right (t x : I) :
    contraction b f hb hl hr ht hp hq hr' hs hz (t,(1,x)) = hr' t x := by
  unfold contraction
  rw [←SquarePathFilling.quotient_right x,SquarePathFilling.paramFill_quotient,loopSquare_bottom]
  exact SquarePathFilling.trans_upper _ _ x
@[simp] lemma contraction_left (t x : I) :
    contraction b f hb hl hr ht hp hq hr' hs hz (t,(0,x)) = hq t x := by
  unfold contraction
  rw [←SquarePathFilling.quotient_left x,SquarePathFilling.paramFill_quotient,loopSquare_top]
  exact SquarePathFilling.trans_half _ _ x
@[simp] lemma contraction_top (t x : I) :
    contraction b f hb hl hr ht hp hq hr' hs hz (t,(x,1)) = hs t x := by
  unfold contraction
  rw [←SquarePathFilling.quotient_top x,SquarePathFilling.paramFill_quotient,loopSquare_top]
  exact SquarePathFilling.trans_upper _ _ x

end HyperbolicObstruction.BasedSquareContraction
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_TriangleSquare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section


/-! A literal closed triangle is the compact quotient of a square collapsing
only its upper edge. Continuous face homotopies therefore descend with their
three prescribed edge tracks. -/
noncomputable section
open scoped Topology unitInterval
open Topology
namespace HyperbolicObstruction.TriangleSquare
abbrev Triangle := { coords : Fin 3 → ℝ | (∀ index, 0 ≤ coords index) ∧ ∑ index, coords index = 1 }

lemma sum_coords (z : Triangle) : z.val 0 + z.val 1 + z.val 2 = 1 := by
  simpa [Fin.sum_univ_succ,add_assoc] using z.property.2
lemma coord_le_one (z : Triangle) (i : Fin 3) : z.val i ≤ 1 := by
  have h := sum_coords z
  have h0 := z.property.1 0
  have h1 := z.property.1 1
  have h2 := z.property.1 2
  fin_cases i <;> dsimp <;> linarith

def quotient : C(I × I,Triangle) where
  toFun z := ⟨![(1-(z.2:ℝ))*(1-(z.1:ℝ)),(1-(z.2:ℝ))*(z.1:ℝ),(z.2:ℝ)],by
    constructor
    · intro i; fin_cases i <;> dsimp
      · exact mul_nonneg (sub_nonneg.mpr z.2.property.2) (sub_nonneg.mpr z.1.property.2)
      · exact mul_nonneg (sub_nonneg.mpr z.2.property.2) z.1.property.1
      · exact z.2.property.1
    · simp [Fin.sum_univ_succ]; ring⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    fin_cases i <;> dsimp <;> fun_prop

@[simp] lemma quotient_zero (x : I) : (quotient (x,0)).val = ![1-(x:ℝ),(x:ℝ),0] := by
  ext i; fin_cases i <;> simp [quotient]
@[simp] lemma quotient_left (y : I) : (quotient (0,y)).val = ![1-(y:ℝ),0,(y:ℝ)] := by
  ext i; fin_cases i <;> simp [quotient]
@[simp] lemma quotient_right (y : I) : (quotient (1,y)).val = ![0,1-(y:ℝ),(y:ℝ)] := by
  ext i; fin_cases i <;> simp [quotient]
@[simp] lemma quotient_one (x : I) : quotient (x,1) = quotient (0,1) := by
  apply Subtype.ext; ext i; fin_cases i <;> simp [quotient]

lemma quotient_surjective : Function.Surjective quotient := by
  intro z
  let y : I := ⟨z.val 2,z.property.1 2,coord_le_one z 2⟩
  have hs := sum_coords z
  by_cases hy : z.val 2 = 1
  · have hz0 : z.val 0 = 0 := by linarith [z.property.1 0,z.property.1 1]
    have hz1 : z.val 1 = 0 := by linarith [z.property.1 0,z.property.1 1]
    refine ⟨(0,1),?_⟩
    apply Subtype.ext; ext i; fin_cases i <;> simp [quotient,hz0,hz1,hy]
  · have hp : 0 < 1-z.val 2 := sub_pos.mpr (lt_of_le_of_ne (coord_le_one z 2) hy)
    let x : I := ⟨z.val 1/(1-z.val 2),div_nonneg (z.property.1 1) hp.le,
      (div_le_one hp).mpr (by linarith [z.property.1 0])⟩
    have hx : (1-z.val 2)*(x:ℝ) = z.val 1 := by
      dsimp [x]; field_simp
    refine ⟨(x,y),?_⟩
    apply Subtype.ext
    ext i; fin_cases i <;> dsimp [quotient,y]
    · nlinarith
    · exact hx

lemma quotient_fiber {z z' : I × I} (h : quotient z = quotient z') :
    z.2 = z'.2 ∧ (z.1 = z'.1 ∨ z.2 = 1) := by
  have hy : z.2 = z'.2 := Subtype.ext (congrArg (fun p : Triangle => p.val 2) h)
  refine ⟨hy,?_⟩
  by_cases h1 : z.2 = 1
  · exact Or.inr h1
  left
  have hh := congrArg (fun p : Triangle => p.val 1) h
  change (1-(z.2:ℝ))*(z.1:ℝ) = (1-(z'.2:ℝ))*(z'.1:ℝ) at hh
  rw [←hy] at hh
  apply Subtype.ext
  exact (mul_left_cancel₀ (by intro he; exact h1 (Subtype.ext (by change (z.2:ℝ) = 1; linarith)))) hh

variable {T X : Type*} [TopologicalSpace T] [TopologicalSpace X]
def paramQuotient : C(T × (I × I),T × Triangle) := (ContinuousMap.id T).prodMap quotient
lemma paramQuotient_surjective : Function.Surjective (paramQuotient (T := T)) := by
  rintro ⟨t,z⟩
  obtain ⟨w,rfl⟩ := quotient_surjective z
  exact ⟨(t,w),rfl⟩
lemma paramQuotient_isQuotientMap [CompactSpace T] [T2Space T] :
    IsQuotientMap (paramQuotient (T := T)) :=
  paramQuotient.continuous.isClosedMap.isQuotientMap paramQuotient.continuous paramQuotient_surjective

variable (F : C(T × (I × I),X)) (ht : ∀ t x, F (t,(x,1)) = F (t,(0,1)))
include ht in
lemma fiber_constant (t : T) {z z' : I × I} (h : quotient z = quotient z') : F (t,z) = F (t,z') := by
  obtain ⟨hy,hx|h1⟩ := quotient_fiber h
  · exact congrArg F (Prod.ext rfl (Prod.ext hx hy))
  · have h1' : z'.2 = 1 := hy.symm.trans h1
    calc F (t,z) = F (t,(z.1,1)) := by rw [←h1]
         _ = F (t,(0,1)) := ht _ _
         _ = F (t,(z'.1,1)) := (ht _ _).symm
         _ = F (t,z') := by rw [←h1']

variable [CompactSpace T] [T2Space T]

def descend : C(T × Triangle,X) where
  toFun tz := F (tz.1,(quotient_surjective tz.2).choose)
  continuous_toFun := by
    apply paramQuotient_isQuotientMap.continuous_iff.mpr
    convert F.continuous using 1
    all_goals try with_reducible_and_instances rfl
    funext tz
    exact fiber_constant F ht tz.1 (quotient_surjective (quotient tz.2)).choose_spec

@[simp] lemma descend_quotient (t : T) (z : I × I) : descend F ht (t,quotient z) = F (t,z) :=
  fiber_constant F ht t (quotient_surjective (quotient z)).choose_spec

end HyperbolicObstruction.TriangleSquare
end
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_BasedTriangleContraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual triangular pi2 obstruction has a literal contracting prism
when the three oriented edge corrections have the prescribed coboundary. -/
noncomputable section

open scoped Topology unitInterval
namespace HyperbolicObstruction.BasedTriangleContraction
open TriangleSquare HSpacePathObstruction
variable {X : Type*} [TopologicalSpace X] (b : X)
local notation "e" => Path.refl b
variable (f : C(Triangle,X))
  (hb : ∀ s, f (quotient (s,0)) = b)
  (hl : ∀ s, f (quotient (0,s)) = b)
  (hr : ∀ s, f (quotient (1,s)) = b)

include hr in
lemma top_const (s : I) : f (quotient (s,1)) = b := by
  rw [quotient_one,←quotient_one (1 : I)]
  exact hr 1

def theta : FundamentalGroup (Path b b) e :=
  BasedSquareContraction.faceObstruction b (p:=e) (q:=e) (r:=e) (s:=e) (f.comp quotient) hb hl hr (top_const b f hr)
    (Path.refl e) (Path.refl e) (Path.refl e) (Path.refl e)

variable (u01 u02 u12 : Path (Path.refl b) (Path.refl b))
  (hu : loopClass u02 * theta b f hb hl hr = loopClass u01 * loopClass u12)

lemma corrected_zero (hu : loopClass u02 * theta b f hb hl hr = loopClass u01 * loopClass u12) :
    BasedSquareContraction.faceObstruction b (p:=e) (q:=e) (r:=e) (s:=e) (f.comp quotient) hb hl hr (top_const b f hr)
      ((Path.refl e).trans u01) ((Path.refl e).trans u02)
      ((Path.refl e).trans u12) ((Path.refl e).trans (Path.refl e)) = 1 := by
  unfold BasedSquareContraction.faceObstruction
  rw [correction]
  have he : loopClass (Path.refl e) = 1 := rfl
  rw [he,mul_one]
  change (loopClass u02 * theta b f hb hl hr) * (loopClass u01 * loopClass u12)⁻¹ = 1
  rw [hu,mul_inv_cancel]

def square : C(I × (I × I),X) :=
  BasedSquareContraction.contraction b (p:=e) (q:=e) (r:=e) (s:=e) (f.comp quotient) hb hl hr (top_const b f hr)
    ((Path.refl e).trans u01) ((Path.refl e).trans u02)
    ((Path.refl e).trans u12) ((Path.refl e).trans (Path.refl e))
    (corrected_zero b f hb hl hr u01 u02 u12 hu)

lemma square_top (t s : I) : square b f hb hl hr u01 u02 u12 hu (t,(s,1)) = b := by
  calc
    _ = ((Path.refl e).trans (Path.refl e)) t s :=
      BasedSquareContraction.contraction_top b (p := e) (q := e) (r := e) (s := e)
        (f.comp quotient) hb hl hr (top_const b f hr)
        ((Path.refl e).trans u01) ((Path.refl e).trans u02)
        ((Path.refl e).trans u12) ((Path.refl e).trans (Path.refl e))
        (corrected_zero b f hb hl hr u01 u02 u12 hu) t s
    _ = b := congrArg (fun p : Path e e => p t s) Path.refl_trans_refl

def contraction : C(I × Triangle,X) := TriangleSquare.descend
  (square b f hb hl hr u01 u02 u12 hu)
  (fun t s => (square_top b f hb hl hr u01 u02 u12 hu t s).trans
    (square_top b f hb hl hr u01 u02 u12 hu t 0).symm)

lemma contraction_initial (z : Triangle) : contraction b f hb hl hr u01 u02 u12 hu (0,z) = f z := by
  obtain ⟨z,rfl⟩ := quotient_surjective z
  unfold contraction
  rw [TriangleSquare.descend_quotient]
  exact BasedSquareContraction.contraction_initial _ _ _ _ _ _ _ _ _ _ _ z
lemma contraction_final (z : Triangle) : contraction b f hb hl hr u01 u02 u12 hu (1,z) = b := by
  obtain ⟨z,rfl⟩ := quotient_surjective z
  unfold contraction
  rw [TriangleSquare.descend_quotient]
  exact BasedSquareContraction.contraction_final _ _ _ _ _ _ _ _ _ _ _ z
lemma contraction_bottom (t s : I) :
    contraction b f hb hl hr u01 u02 u12 hu (t,quotient (s,0)) = ((Path.refl e).trans u01) t s := by
  unfold contraction
  rw [TriangleSquare.descend_quotient]
  exact BasedSquareContraction.contraction_bottom _ _ _ _ _ _ _ _ _ _ _ t s
lemma contraction_left (t s : I) :
    contraction b f hb hl hr u01 u02 u12 hu (t,quotient (0,s)) = ((Path.refl e).trans u02) t s := by
  unfold contraction
  rw [TriangleSquare.descend_quotient]
  exact BasedSquareContraction.contraction_left _ _ _ _ _ _ _ _ _ _ _ t s
lemma contraction_right (t s : I) :
    contraction b f hb hl hr u01 u02 u12 hu (t,quotient (1,s)) = ((Path.refl e).trans u12) t s := by
  unfold contraction
  rw [TriangleSquare.descend_quotient]
  exact BasedSquareContraction.contraction_right _ _ _ _ _ _ _ _ _ _ _ t s

end HyperbolicObstruction.BasedTriangleContraction
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_BoundaryList
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {D : Type*} [DecidableEq D]

/-- An enumerated literal face boundary; the empty outside is allowed. -/
structure IsBoundary (f : Perm D) (xs : List D) : Prop where
  nodup : xs.Nodup
  turn : ∀ x ∈ xs, f x = xs.formPerm x

end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_ClosedCoverGluing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section


/-! Literal continuous gluing on locally finite closed covers. This is used for
cell-by-cell homotopies; it does not assume cell extensions exist. -/
noncomputable section
open scoped Topology unitInterval
namespace HyperbolicObstruction.ClosedCoverGluing
variable {J X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  (S : J → Set X) (φ : ∀ j, C(S j,Y))
  (agree : ∀ i j x (hi : x ∈ S i) (hj : x ∈ S j), φ i ⟨x,hi⟩ = φ j ⟨x,hj⟩)
  (cover : ⋃ j, S j = Set.univ) (closed : ∀ j, IsClosed (S j))
  (finite : LocallyFinite S)

/-- Gluing is with the actual source topology, not a replacement quotient. -/
def glue : C(X,Y) where
  toFun := Set.liftCover S (fun j => φ j) agree cover
  continuous_toFun := by
    apply finite.continuous cover closed
    intro j
    rw [continuousOn_iff_continuous_domRestrict]
    have he : (S j).domRestrict (Set.liftCover S (fun j => φ j) agree cover) = φ j := by
      funext x
      exact Set.liftCover_coe x
    rw [he]
    exact (φ j).continuous

@[simp] lemma glue_apply (j : J) (x : S j) :
    glue S φ agree cover closed finite x = φ j x := by
  change Set.liftCover S (fun j => φ j) agree cover x = φ j x
  exact Set.liftCover_coe x

lemma glue_eq (j : J) (x : X) (hx : x ∈ S j) :
    glue S φ agree cover closed finite x = φ j ⟨x,hx⟩ :=
  glue_apply S φ agree cover closed finite j ⟨x,hx⟩

/-- A homotopy prescribed continuously on each closed cell glues once the
literal formulas coincide on intersections. -/
def gluePrism (H : ∀ j, C(I × S j,Y))
    (ha : ∀ i j (t : I) x (hi : x ∈ S i) (hj : x ∈ S j),
      H i (t,⟨x,hi⟩) = H j (t,⟨x,hj⟩)) : C(I × X,Y) := by
  let T : J → Set (I × X) := fun j => Prod.snd ⁻¹' S j
  let ψ : ∀ j, C(T j,Y) := fun j =>
    { toFun tx := H j (tx.val.1,⟨tx.val.2,tx.property⟩)
      continuous_toFun := (H j).continuous.comp
        ((continuous_fst.comp continuous_subtype_val).prodMk
          ((continuous_snd.comp continuous_subtype_val).subtype_mk _)) }
  have ht : ⋃ j, T j = Set.univ := by
    ext tx
    simpa only [Set.mem_iUnion,Set.mem_preimage,T,Set.mem_univ,iff_true] using
      Set.iUnion_eq_univ_iff.mp cover tx.2
  have hf : LocallyFinite T := finite.preimage_continuous continuous_snd
  exact glue T ψ (fun i j tx hi hj => ha i j tx.1 tx.2 hi hj) ht
    (fun j => (closed j).preimage continuous_snd) hf

end HyperbolicObstruction.ClosedCoverGluing
end
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_GraphWordFilling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.GraphWordFilling
open SimpleGraph WordPictures
variable {V A : Type*} {G : SimpleGraph V}

def word (r : G.Dart → A × Bool) {u v : V} (p : G.Walk u v) : Word A := p.darts.map r
@[simp] lemma word_nil (r : G.Dart → A × Bool) (v : V) : word r (.nil : G.Walk v v) = [] := rfl
@[simp] lemma word_cons (r : G.Dart → A × Bool) {u v w : V} (h : G.Adj u v) (p : G.Walk v w) :
    word r (.cons h p) = r ⟨(u,v),h⟩ :: word r p := rfl
@[simp] lemma word_append (r : G.Dart → A × Bool) {u v w : V}
    (p : G.Walk u v) (q : G.Walk v w) : word r (p.append q) = word r p ++ word r q := by
  simp [word]

end HyperbolicObstruction.GraphWordFilling
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_WordPicture
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.WordPictures
open HyperbolicObstruction.PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
universe u
variable {A : Type u}

def invLetter (a : A × Bool) : A × Bool := (a.1,!a.2)
@[simp] lemma invLetter_invLetter (a : A × Bool) : invLetter (invLetter a) = a := by
  rcases a with ⟨a,b⟩; cases b <;> rfl

def SymmetricRelator (R : Set (Word A)) (w : Word A) : Prop :=
  w ∈ R ∨ FreeGroup.invRev w ∈ R

/-- Finite, genuinely genus-zero van Kampen side-pairings, with a literal
outside word and enumerated indexed relator boundaries on every interior
face. There is no disk-existence or isoperimetric field. -/
structure WordPicture (R : Set (Word A)) (w : Word A) where
  Dart : Type
  [finite : Fintype Dart]
  [decEq : DecidableEq Dart]
  pairing : PictureMap Dart
  genusZero : pairing.GenusZero
  label : Dart → A × Bool
  paired : ∀ x, label (pairing.edge x) = invLetter (label x)
  outside : List Dart
  boundary : IsBoundary pairing.face outside
  word : outside.map label = w
  interior : ∀ x, x ∉ outside → ∃ xs : List Dart,
    IsBoundary pairing.face xs ∧ x ∈ xs ∧ SymmetricRelator R (xs.map label)
attribute [instance] WordPicture.finite WordPicture.decEq

end HyperbolicObstruction.WordPictures
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_Selection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
open Filter Topology
namespace HyperbolicObstruction

universe a b c
/-- A genuine action on an arbitrary chosen space in the specified universe. -/
structure CATActionWitness (G : Type a) [Group G] where
  Space : Type b
  metric : MetricSpace Space
  nonempty : Nonempty Space
  proper : ProperSpace Space
  complete : CompleteSpace Space
  cat : CATZero Space
  action : GeometricAction G Space

attribute [instance] CATActionWitness.metric CATActionWitness.nonempty
  CATActionWitness.proper CATActionWitness.complete

end HyperbolicObstruction
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_IndexedFillingValue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HyperbolicObstruction

/-! The integral filling value of a literal nullword. This is a consequence
of constructed disks and sphere vanishing, not a replacement hypothesis. -/

/-! Literal walks in a signed incidence graph, with componentwise root paths.
No connectedness or universal-cover assertion is assumed. -/

/-! A literal disk-chain left inverse for the integral cell boundary. The
rooted-edge construction avoids assuming an arbitrary-cycle sphere producer. -/

/-! Subdivision of permutation cycles, with exact orbit-count preservation. -/

/-! Local elementary triangle incidence induces the exact radial contraction. -/

/-! Lifting actual word homotopies to the voltage cover, with the negative
orientation based at the positive lift's initial endpoint. -/
namespace VoltageWords

section
open HyperbolicObstruction.WordPictures
variable {A G : Type*} [Group G]

@[simp] lemma invRev_singleton (e : A × Bool) : FreeGroup.invRev [e] = [invLetter e] := rfl

def voltage (v : A → G) (e : A × Bool) : G := if e.2 then v e.1 else (v e.1)⁻¹

def total (v : A → G) (w : Word A) : G := (w.map (voltage v)).prod

@[simp] lemma voltage_inv (v : A → G) (e : A × Bool) :
    voltage v (invLetter e) = (voltage v e)⁻¹ := by
  rcases e with ⟨a,b⟩; cases b <;> simp [voltage,invLetter]

@[simp] lemma total_nil (v : A → G) : total v [] = 1 := rfl
@[simp] lemma total_cons (v : A → G) (e : A × Bool) (w : Word A) :
    total v (e::w) = voltage v e * total v w := rfl
@[simp] lemma total_append (v : A → G) (w z : Word A) :
    total v (w++z) = total v w * total v z := by simp [total]

@[simp] lemma total_inv (v : A → G) (w : Word A) :
    total v (FreeGroup.invRev w) = (total v w)⁻¹ := by
  induction w with
  | nil => simp
  | cons e w ih =>
    rw [FreeGroup.invRev_cons,total_append,ih]
    change (total v w)⁻¹ * (voltage v (invLetter e) * 1) = _
    simp only [voltage_inv,mul_one,total_cons,mul_inv_rev]

def liftLetter (v : A → G) (g : G) (e : A × Bool) : (G × A) × Bool :=
  if e.2 then ((g,e.1),true) else ((g * voltage v e,e.1),false)

@[simp] lemma liftLetter_inv (v : A → G) (g : G) (e : A × Bool) :
    liftLetter v (g * voltage v e) (invLetter e) = invLetter (liftLetter v g e) := by
  rcases e with ⟨a,b⟩; cases b <;> simp [liftLetter,voltage,invLetter]

def liftWord (v : A → G) (g : G) : Word A → Word (G × A)
  | [] => []
  | e::w => liftLetter v g e :: liftWord v (g * voltage v e) w

@[simp] lemma liftWord_nil (v : A → G) (g : G) : liftWord v g [] = [] := rfl
@[simp] lemma liftWord_cons (v : A → G) (g : G) (e : A × Bool) (w : Word A) :
    liftWord v g (e::w) = liftLetter v g e :: liftWord v (g * voltage v e) w := rfl

end

open HyperbolicObstruction.WordPictures HyperbolicObstruction.PictureSwitch

end VoltageWords

/-!
The actual elementary triangles imply the compressed cone polygon equations.
Unlike the redundant polygon bouquet, this presentation retains exactly the
elementary indexed top triangles.
-/

/-! Actual genus-zero disks for every closed elementary loop in the original
letter voltage cover. No cycle-representation or asphericity hypothesis. -/

/-! No reselection: the same final arrays already have the precise uniform
lifted-picture estimate. Apply the new disk-chain left inverse to those arrays. -/

/-! The actual elementary incidence data now defines an actual finite
barycentric polyhedron. This file proves compactness and connectivity only;
no CW-universal-cover comparison is smuggled in as a structure field. -/

/-! Restricting any flat voltage on the actual triangulation to the original
indexed graph. Literal cap triangles prove every original boundary relation. -/

/-! Genuine continuous fundamental groups are generated by the finite edges. -/

/-! New subdivision, collar and cone edges do not create fundamental-group
generators. This concerns the actual barycentric realization. -/

/-! The literal polygon presentation maps to the actual pi1, and its tree
normalization has no hidden van Kampen hypothesis. -/

/-! Identification of the actual finite elementary polyhedron's pi1 with the
original letter presentation, using actual path classes and voltage covers. -/

/-! The actual voltage cover is universal whenever its proved monodromy
comparison is bijective. No simple-connectivity premise on the total space
is substituted for the producer. -/

/-! The literal voltage bundle is an actual simply connected covering
of the actual finite polygon realization. We construct its connectivity from
monodromy, rather than naming an abstract universal cover as a hypothesis. -/

/-! Exact higher homotopy identification for the constructed simply connected
voltage covering of the actual frozen finite polyhedron. -/

section

/-! A literal basepoint-fixing contraction kills the actual cube-relative
homotopy groups, with no Hurewicz/Whitehead assumption. -/
open scoped Topology unitInterval
namespace BasedHigherContraction
variable {X : Type*} [TopologicalSpace X] (z : X) (H : C(I × X,X))
  (h0 : ∀ x, H (0,x) = x) (h1 : ∀ x, H (1,x) = z) (hz : ∀ t, H (t,z) = z)
  {N : Type*}

def nullhomotopy (p : GenLoop N X z) :
    p.val.HomotopyRel (GenLoop.const : GenLoop N X z).val (Cube.boundary N) where
  toFun tx := H (tx.1,p tx.2)
  continuous_toFun := H.continuous.comp (continuous_fst.prodMk (p.val.continuous.comp continuous_snd))
  map_zero_left x := h0 (p x)
  map_one_left x := h1 (p x)
  prop' t x hx := by
    change H (t,p x) = p x
    have hp : p x = z := p.property x hx
    rw [hp,hz]

end BasedHigherContraction
end

/-! Rooted path algebra with exact zero-cost spur cancellations. This is a
literal triangular disk calculus, not an appeal to topological equivalence. -/

/-! Quantitative finite-presentation change, with all word substitutions and
comparison disks constructed. Relator disks are used only after establishing
that the corresponding literal words are null. -/

/-! Literal finite relator words for the proved actual fundamental-group
presentation, including exact rooted route words. -/

/-! Realization of ordinary word disks as literal triangular edge disks over
the frozen finite polyhedron. Free-group folds become actual zero-cost spurs. -/

/-! Group-isomorphism transport for geometric actions. -/

/-! Actual homotopy-equivalence invariance of the fundamental group. -/

/-! The literal finite barycentric complex has exactly the original letter group,
not a conditional presentation of it. -/

/-! The same supplied final arrays yield infinite groups unconditionally.
This discharges the last group-action-side hypothesis; the finite-polyhedron
realization and group-to-topology consequences are still separate obligations. -/

/-! Elementary facts about WordLength and WordDistance for the four-point
characterization of hyperbolicity. -/

/-! Cochains are evaluated on the actual area-counted word homotopies.
Free folds contribute exactly zero; each literal relator contributes its
own cochain integral. No planar realization hypothesis is needed. -/
namespace WordPictures
variable {A G : Type*} [Group G]
namespace Cochain
variable (φ : FreeGroup A →* G) (ω : G → G → ℝ)

def value (w : Word A) : G := φ (FreeGroup.mk w)
def letter (a : A × Bool) : G := value φ [a]
def integral : G → Word A → ℝ
  | _, [] => 0
  | g, a::w => ω g (g*letter φ a) + integral (g*letter φ a) w

@[simp] lemma value_nil : value φ [] = 1 := map_one φ
@[simp] lemma value_append (u v : Word A) : value φ (u++v)=value φ u*value φ v :=
  by simp only [value,←FreeGroup.mul_mk,map_mul]
@[simp] lemma value_cons (a : A × Bool) (w : Word A) :
    value φ (a::w)=letter φ a*value φ w := value_append φ [a] w
@[simp] lemma value_reverse (w : Word A) :
    value φ (FreeGroup.invRev w)=(value φ w)⁻¹ := by simp only [value,←FreeGroup.inv_mk,map_inv]
@[simp] lemma letter_flip (a : A) (b : Bool) : letter φ (a,!b)=(letter φ (a,b))⁻¹ := by
  change value φ (FreeGroup.invRev [(a,b)]) = _
  exact value_reverse φ _
@[simp] lemma integral_nil (g : G) : integral φ ω g []=0 := rfl
@[simp] lemma integral_cons (g : G) (a : A × Bool) (w : Word A) :
    integral φ ω g (a::w)=ω g (g*letter φ a)+integral φ ω (g*letter φ a) w := rfl

end Cochain
end WordPictures

/-! Finite unit-speed vertex paths; all indices are bounded explicitly. -/
section
open Finset
structure VertexPath (X : Type*) where
  length : ℕ
  point : ℕ → X
namespace VertexPath
variable {X : Type*}
def start (p : VertexPath X) := p.point 0
def finish (p : VertexPath X) := p.point p.length
def integral (p : VertexPath X) (ω : X → X → ℝ) : ℝ :=
  ∑ i ∈ range p.length, ω (p.point i) (p.point (i+1))
def reverse (p : VertexPath X) : VertexPath X := ⟨p.length,fun i => p.point (p.length-i)⟩
def sub (p : VertexPath X) (i j : ℕ) : VertexPath X := ⟨j-i,fun k => p.point (i+k)⟩
def append (p q : VertexPath X) : VertexPath X :=
  ⟨p.length+q.length,fun i => if i  ≤  p.length then p.point i else q.point (i-p.length)⟩
@[simp] lemma reverse_length (p : VertexPath X) : p.reverse.length=p.length := rfl
@[simp] lemma reverse_at (p : VertexPath X) (i : ℕ) : p.reverse.point i=p.point (p.length-i) := rfl
@[simp] lemma reverse_start (p : VertexPath X) : p.reverse.start=p.finish := by simp [start,finish]
@[simp] lemma reverse_finish (p : VertexPath X) : p.reverse.finish=p.start := by simp [start,finish]
@[simp] lemma sub_length (p : VertexPath X) (i j : ℕ) : (p.sub i j).length=j-i := rfl
@[simp] lemma sub_at (p : VertexPath X) (i j k : ℕ) : (p.sub i j).point k=p.point (i+k) := rfl
@[simp] lemma sub_start (p : VertexPath X) (i j : ℕ) : (p.sub i j).start=p.point i := by simp [start]
@[simp] lemma append_length (p q : VertexPath X) : (p.append q).length=p.length+q.length := rfl
@[simp] lemma append_start (p q : VertexPath X) : (p.append q).start=p.start := by
  simp [start,append]

variable [MetricSpace X]
def Unit (p : VertexPath X) : Prop := ∀ i<p.length, dist (p.point i) (p.point (i+1))  ≤  1

end VertexPath
end

namespace WordPictures.Cochain
variable {A G : Type*} [Group G]
variable (φ : FreeGroup A →* G)
def path (g : G) (w : Word A) : VertexPath G :=
  ⟨w.length,fun i => g*value φ (w.take i)⟩
@[simp] lemma path_length (g : G) (w : Word A) : (path φ g w).length=w.length := rfl
@[simp] lemma path_point_zero (g : G) (w : Word A) : (path φ g w).point 0=g := by simp [path]
@[simp] lemma path_start (g : G) (w : Word A) : (path φ g w).start=g := path_point_zero φ g w
@[simp] lemma path_finish (g : G) (w : Word A) : (path φ g w).finish=g*value φ w := by
  simp [VertexPath.finish,path]

end WordPictures.Cochain

section
open Finset
open scoped NNReal
namespace VertexPath
variable {X : Type*} [MetricSpace X]
def tentWeight (f u : X→ℝ) (x y : X) : ℝ :=
  (f x+f y)/2*(u y-u x)

end VertexPath
end
section

open scoped NNReal
/-- A quantitative consequence of actual linear word filling, tested by
Lipschitz cochains. This property makes no geometric conclusion an assumption. -/
def CochainLinear (X : Type*) [MetricSpace X] (K : ℝ) : Prop :=
  ∀ p : VertexPath X, p.Unit → p.finish=p.start → ∀ f u : X→ℝ,
    LipschitzWith 1 f → LipschitzWith 3 u →
    |p.integral (VertexPath.tentWeight f u)| ≤ K*p.length
end

/-! A quantitative proof that linear word-homotopy filling bounds imply
four-point hyperbolicity. -/

/-! All clauses of the exact main except exclusion of compatible locally
CAT(-1) finite homotopy models. The complete literal hyperbolicity consequence
is now unconditional, on the SAME finite aspherical complex. -/

/-! The real comparison inequality needed to pass the manuscript's exact
cosh-midpoint CAT(-1) definition to the Euclidean CN midpoint inequality. -/

/-! The global cosh-midpoint comparison implies whole-segment CAT(0)
comparison. No completeness or globalization
hypothesis is hidden in this elementary curvature-monotonicity step. -/

/-! The finite difference maximum principle required for local geodesic
continuation. Endpoint estimates are literal, with no convergence assumption. -/

/-! Literal equal-time interpolation of finite geodesic polygons. -/
open Set Metric

end HyperbolicObstruction

end

end OAI
end


