-- Prove2me | Definitions.Def_OAIQ034H010
-- name    : OAIQ034H010
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T05:40:01.507339+00:00
-- url     : https://prove2.me/theorems/18e17ced-0d3c-4bb1-9586-62429efa5f57
-- title:
--   Definitions bundle OAIQ034H010 of the split of OpenAI, A hyperbolic group with no geometric CAT(0) action (result family 257)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.HyperbolicObstruction.main`, carved from OpenAI's openai/math development (OpenAI, *A hyperbolic group with no geometric CAT(0) action (result family 257)*, OpenAI Math Release, September 25, 2026, result family 257, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 199 declarations of OpenAI's Lean: 75 definitions, 5 inductive types or structures, 7 instances and 112 theorems. The definitions and types are `OAI.HyperbolicObstruction.CoreGeometry.InFan`, `OAI.HyperbolicObstruction.CoreGeometry.MetricCore`, `OAI.HyperbolicObstruction.CoreGeometry.ThreeQuota`, `OAI.HyperbolicObstruction.FinitePolygonModel.Data.contractionFace`, `OAI.HyperbolicObstruction.FinitePolygonModel.Data.coverContraction`, `OAI.HyperbolicObstruction.FinitePolyhedron.EdgeChain.Homotopy`, `OAI.HyperbolicObstruction.FinitePolyhedron.EdgePresentation.voltage`, `OAI.HyperbolicObstruction.FinitePolyhedron.Voltage.FacePrism`, `OAI.HyperbolicObstruction.FinitePolyhedron.Voltage.anchoredFacePrism`, `OAI.HyperbolicObstruction.FinitePolyhedron.Voltage.contraction`, `OAI.HyperbolicObstruction.FinitePolyhedron.Voltage.correctedEdge`, `OAI.HyperbolicObstruction.FinitePolyhedron.Voltage.correctedEdgePrisms`, `OAI.HyperbolicObstruction.FinitePolyhedron.Voltage.correctedFacePrism`, `OAI.HyperbolicObstruction.FinitePolyhedron.Voltage.correctedTriangle`, `OAI.HyperbolicObstruction.FinitePolyhedron.Voltage.correctionEdgeData`, `OAI.HyperbolicObstruction.FinitePolyhedron.Voltage.correctionLoop`, `OAI.HyperbolicObstruction.FinitePolyhedron.Voltage.correctionSquare`, `OAI.HyperbolicObstruction.FinitePolyhedron.Voltage.edgeFacePrism`, `OAI.HyperbolicObstruction.FinitePolyhedron.Voltage.faceLiftHomeomorph`, `OAI.HyperbolicObstruction.FinitePolyhedron.Voltage.fromTrianglePrisms`, `OAI.HyperbolicObstruction.FinitePolyhedron.Voltage.glueFaceHomotopies`, `OAI.HyperbolicObstruction.FinitePolyhedron.Voltage.graphEdgeData`, `OAI.HyperbolicObstruction.FinitePolyhedron.Voltage.homotopyOnRange`, `OAI.HyperbolicObstruction.FinitePolyhedron.Voltage.loopRepresentative`, `OAI.HyperbolicObstruction.FinitePolyhedron.Voltage.terminalContraction`, `OAI.HyperbolicObstruction.FinitePolyhedron.Voltage.triangleCoordinates`, `OAI.HyperbolicObstruction.FinitePolyhedron.Voltage.triangleFacePrism`, `OAI.HyperbolicObstruction.FinitePolyhedron.simplexCoordinates`, `OAI.HyperbolicObstruction.IncidenceTemplate.ConditionalTest.Satisfies`, `OAI.HyperbolicObstruction.IncidenceTemplate.ConditionalTest.closure`, `OAI.HyperbolicObstruction.IncidenceTemplate.ConditionalTest.embedding`, `OAI.HyperbolicObstruction.IncidenceTemplate.ConditionalTest.error`, `OAI.HyperbolicObstruction.IncidenceTemplate.ConditionalTest.rate`, `OAI.HyperbolicObstruction.IncidenceTemplate.ConditionalTest.threshold`, `OAI.HyperbolicObstruction.IncidenceTemplate.Occurrences.probability`, `OAI.HyperbolicObstruction.IncidenceTemplate.SamplingStage`, `OAI.HyperbolicObstruction.IncidenceTemplate.SamplingStage.Alphabet`, `OAI.HyperbolicObstruction.IncidenceTemplate.SamplingStage.LetterGroup`, `OAI.HyperbolicObstruction.IncidenceTemplate.SamplingStage.Matches`, `OAI.HyperbolicObstruction.IncidenceTemplate.SamplingStage.Rows` and 40 more.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry/HyperbolicGroups, in whole or in part: `HyperbolicGroups_BoundaryFold`, `HyperbolicGroups_BoundaryLift`, `HyperbolicGroups_ConditionalStar`, `HyperbolicGroups_CouplingError`, `HyperbolicGroups_Deviation`, `HyperbolicGroups_DiagonalSampling`, `HyperbolicGroups_Exceptional`, `HyperbolicGroups_ExtensionConditioning`, `HyperbolicGroups_FiniteSampling`, `HyperbolicGroups_Graph`, `HyperbolicGroups_GraphAction`, `HyperbolicGroups_GraphLimit`, `HyperbolicGroups_IncidenceTemplate`, `HyperbolicGroups_IndexedFillingValue`, `HyperbolicGroups_IndexedPictureBasic`, `HyperbolicGroups_IndexedPictureClosed`, `HyperbolicGroups_IndexedPictureExistence`, `HyperbolicGroups_IndexedPictureFold`, `HyperbolicGroups_IndexedWordPicture`, `HyperbolicGroups_MetricHexagon`, `HyperbolicGroups_NormalCell`, `HyperbolicGroups_Occurrence`, `HyperbolicGroups_OrbitLimit`, `HyperbolicGroups_PictureMirror`, `HyperbolicGroups_PolygonContraction`, `HyperbolicGroups_PolygonCornerPrimitive`, `HyperbolicGroups_PolygonSphere`, `HyperbolicGroups_PolygonSphereFurther`, `HyperbolicGroups_PolygonTriangleCochains`, `HyperbolicGroups_PolygonTriangles`, `HyperbolicGroups_Presentation`, `HyperbolicGroups_RankCollection`, `HyperbolicGroups_RankSelection`, `HyperbolicGroups_SamplingStage`, `HyperbolicGroups_SelectedPresentation`, `HyperbolicGroups_Shape`, `HyperbolicGroups_SimplexCoordinates`, `HyperbolicGroups_SixCounts`, `HyperbolicGroups_SquareBoundaryExtension`, `HyperbolicGroups_StarActual`, `HyperbolicGroups_StarCoupling`, `HyperbolicGroups_StarError`, `HyperbolicGroups_StarMean`, `HyperbolicGroups_StarRate`, `HyperbolicGroups_StarVariance`, `HyperbolicGroups_Template`, `HyperbolicGroups_Test`, `HyperbolicGroups_TriangleCoordinates`, `HyperbolicGroups_TriangleEdgeIntersection`, `HyperbolicGroups_TriangleHomotopyExtension`, `HyperbolicGroups_VoltageCellGluing`, `HyperbolicGroups_VoltageClosedCells`, `HyperbolicGroups_VoltageEdgeAgreement`, `HyperbolicGroups_VoltageEdgeCorrection`, `HyperbolicGroups_VoltageFacePrisms`, `HyperbolicGroups_VoltageGraphHomotopy`, `HyperbolicGroups_VoltagePrismGluing`, `HyperbolicGroups_VoltageTriangleContraction`, `HyperbolicGroups_VoltageTriangleHomotopy`, `HyperbolicGroups_WalkCover`, `HyperbolicGroups_WordPicture`, `HyperbolicGroups_WordPictureBase`.
--
--   **Imports.** It imports the published bundle `Def_HyperbolicObstruction`; the bundles `OAIQ034H003`, `OAIQ034H004`, `OAIQ034H005` and `OAIQ034H006` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ034H011`.
-- source:
--   OpenAI, A hyperbolic group with no geometric CAT(0) action (result family 257), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 257; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-hyperbolic-group-with-no-geometric-CAT0-action-September-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry/HyperbolicGroups at commit adc7f12

import Mathlib
import Definitions.Def_HyperbolicObstruction
import Definitions.Def_OAIQ034H003
import Definitions.Def_OAIQ034H004
import Definitions.Def_OAIQ034H005
import Definitions.Def_OAIQ034H006

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_BoundaryFold
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutSide _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeOutsideContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypePartBoundary _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativePartBoundary
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
variable (M : PictureMap D) {a b : D} (hab : a ≠ b) (hnext : M.face a = b)

variable {L V : Type*} {label : D → L} {start : L → V} {rev : L → L}

lemma boundaryFold_face_orbits (x y : {x // OffPair a b x}) :
    (M.boundaryFold hab hnext).face.SameCycle x y ↔ M.face.SameCycle x.val y.val := by
  have he : (M.boundaryFold hab hnext).face = erasePair M.face hab := by
    apply Equiv.ext
    exact M.boundaryFold_face hab hnext
  rw [he]
  exact erasePair_orbits M.face hab x y

end PictureMap
end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_PolygonSphere
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
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

variable {D B : Type*}

lemma cycles_of_classifier [DecidableEq D] [Fintype D] [Fintype B]
    (f : Perm D) (j : D → B) (h : ∀ x y, f.SameCycle x y ↔ j x = j y)
    (hs : Function.Surjective j) : cycles f = Fintype.card B := by
  rw [cycles_eq_card_classes,card_quotient_of_classifier (SameCycle.setoid f) j h hs,Nat.card_eq_fintype_card]


end HyperbolicObstruction.PictureSwitch
end
end
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_BoundaryLift
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.PictureSwitch.WalkPicture.instFintypeFace _root_.OAI.HyperbolicObstruction.PictureSwitch.WalkPicture.instFintypeVertex _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutSide _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeOutsideContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypePartBoundary _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativePartBoundary
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

namespace WalkPicture
universe u v w z k t r
variable {S : Type v} {C : Type w} {W : Type z} {L : Type k} {V : Type t}
  {A : Type r} [AddCommMonoid A] {T : WalkCellTarget S C W L V A}
  {P Q : WalkPicture.{u} T} {keep : S → Prop}

/-- Protected-boundary normalization retains the EXACT enumerated word, not
merely its conjugacy class or its image in the presented group. -/
theorem Preserves.boundary (hPQ : P.Preserves keep Q)
    (hk : ∀ s, keep s → T.free (T.kind s) = false)
    (xs : List P.Dart) (hx : IsBoundary P.pairing.face xs)
    (hs : ∀ x, keep (P.index x) ↔ x ∈ xs) :
    ∃ ys : List Q.Dart, IsBoundary Q.pairing.face ys ∧
      ys.map hPQ.map = xs ∧
      ys.map (T.label ∘ Q.index) = xs.map (T.label ∘ P.index) ∧
      ∀ y, keep (Q.index y) ↔ y ∈ ys := by
  obtain ⟨ys,hy,he⟩ := hx.pullback_surviving hPQ.map hPQ.injective
    (fun x hx => hPQ.complete x ((hs x).mpr hx)) (by
      intro y hy
      apply hPQ.face
      rw [hPQ.index]
      exact hk _ ((hs _).mpr hy))
  refine ⟨ys,hy,he,?_,?_⟩
  · rw [← he,List.map_map]
    apply List.map_congr_left
    intro y _
    exact congrArg T.label (hPQ.index y)
  · intro y
    rw [hPQ.index,hs,← he]
    exact List.mem_map_of_injective hPQ.injective

end WalkPicture
end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_MetricHexagon
attribute [-instance] _root_.OAI.HyperbolicObstruction.CoreGeometry.instDecidableIsFanVertex _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
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
namespace CoreGeometry
open IncidenceTemplate
instance instDecidableAdjacent (v w : Vertex) : Decidable (Adjacent v w) := by
  cases v <;> cases w <;> unfold Adjacent <;> infer_instance

end CoreGeometry
end HyperbolicObstruction


noncomputable section
namespace HyperbolicObstruction
namespace CoreGeometry
open IncidenceTemplate

/-- Membership of an (unoriented) core edge in the fan over `i`. Adjacency is
imposed separately. The exceptional loose edge belongs to no fan. -/
def InFan (i : Fin 7) : Vertex → Vertex → Prop
  | .inl r, .inr l => pointOfRepresentative r = i ∧ (r,l) ≠ (3,4)
  | .inr l, .inl r => pointOfRepresentative r = i ∧ (r,l) ≠ (3,4)
  | _, _ => False

instance instDecidableInFan (i : Fin 7) (a b : Vertex) : Decidable (InFan i a b) := by
  cases a <;> cases b <;> unfold InFan <;> infer_instance

/-- The three-edge fan quota, expressed without choosing an orientation for
its fields. With distinct successive fields this says at most two per fan. -/
def ThreeQuota (a b c d : Vertex) : Prop :=
  ∀ i, ¬ (InFan i a b ∧ InFan i b c ∧ InFan i c d)

instance instDecidableThreeQuota (a b c d : Vertex) : Decidable (ThreeQuota a b c d) :=
  inferInstanceAs (Decidable (∀ _i, ¬ (_ ∧ _ ∧ _)))

/-- Exactly the core path distances in Proposition `configuration` (i).
The third condition uses distinct fields and the actual fan quota; the
exceptional loose edge is not charged to the D fan. -/
structure MetricCore {X : Type*} [MetricSpace X] (z : Vertex → X) : Prop where
  side : ∀ a b, Adjacent a b → dist (z a) (z b) ^ 2 = 1
  twoStep : ∀ a b c, Adjacent a b → Adjacent b c → a ≠ c →
    dist (z a) (z c) ^ 2 = 2
  threeStep : ∀ a b c d, Adjacent a b → Adjacent b c → Adjacent c d →
    a ≠ c → b ≠ d → ThreeQuota a b c d → 3 ≤ dist (z a) (z d) ^ 2

end CoreGeometry
end HyperbolicObstruction

noncomputable section
namespace HyperbolicObstruction
namespace CoreGeometry

lemma fullLines_x (i : Fin 4) (a : Fin 6) (ha : a ∈ fullLines i) :
    Adjacent (.inl (xRep i)) (.inr (sixLine a)) := by
  fin_cases i <;> fin_cases a <;> first | (solve | simp [fullLines] at ha) | decide
lemma fullLines_y (i : Fin 4) (a : Fin 6) (ha : a ∈ fullLines i) :
    Adjacent (.inl (yRep i)) (.inr (sixLine a)) := by
  fin_cases i <;> fin_cases a <;> first | (solve | simp [fullLines] at ha) | decide

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
end
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_ConditionalStar
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
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

/-- Only combinatorial sampling assertions occur here, independent of the action
that may be chosen after the random tables have been exposed. This is not a
replacement for the random-table producer. -/
structure SamplingSequence (F : Type*) [DecidableEq F] (Admissible : Finset F → Prop)
    (L Ω : ℕ → Type*) [∀ n, Fintype (L n)] [∀ n, Nonempty (L n)]
    [∀ n, DecidableEq (L n)] [∀ n, Fintype (Ω n)] [∀ n, Nonempty (Ω n)]
    (label : ∀ n, Ω n → F → L n) where
  singleton : ∀ e : F, Tendsto (fun n =>
    ((FiniteLaw.uniform : FiniteLaw (Ω n)).map (fun a => label n a e)).totalVariation
      FiniteLaw.uniform) atTop (𝓝 0)
  star : ∀ (I : Finset F) (e : F), e ∉ I → Admissible (insert e I) → ∀ k : ℕ,
    ∃ η : ℕ → ℝ, Tendsto η atTop (𝓝 0) ∧ ∀ᶠ n in atTop,
      ∃ κ : FiniteLaw (ConditionalStar (label n) I k),
        (∀ j, (κ.map (ConditionalStar.branch j)).totalVariation FiniteLaw.uniform ≤ η n) ∧
        (κ.map (fun b j => label n (ConditionalStar.branch j b) e)).totalVariation
          (FiniteLaw.uniform : FiniteLaw (Fin (k + 1) → L n)) ≤ η n

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
-- module Solutions.OAIQ034_HG.HyperbolicGroups_Template
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeOutgoing _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.IncidenceTemplate.instFieldFintype
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

lemma card_fields : Fintype.card Field = 212 := by
  simp [Fintype.card_sum, Fintype.card_prod, card_twoPaths, card_edges]


lemma no_square_of_small_core (W : Finset Field) (hW : W.toLeft.card < 2)
    (τ : TwoPath) : ¬squareSupport τ ⊆ W := by
  intro h
  have hs : {τ.val.1, τ.val.2} ⊆ W.toLeft := by
    intro e he
    rw [Finset.mem_toLeft]
    apply h
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl <;> simp [squareSupport]
  have hc := Finset.card_le_card hs
  rw [Finset.card_pair (twoPath_ne τ)] at hc
  omega

lemma coreExponent_small (W : Finset Edge) (hW : W.card < 2) :
    coreExponent W = W.card := by
  have hn (i : Fin 7) : ¬fan i ⊆ W := by
    intro hs
    have hcard := Finset.card_le_card hs
    have hl := fan_card_lower i
    omega
  have hu : W ≠ Finset.univ := by
    intro he
    subst W
    have hc := card_edges
    simp only [Finset.card_univ] at hW
    omega
  simp [coreExponent, hn, hu]

/-- Source Lemma `sample:lem-budget`, first inequality, for the actual template. -/
theorem criticalExponent_lower (W : Finset Field) :
    ((min 2 W.card : ℕ) : ℤ) ≤ criticalExponent W := by
  have hnonneg : 0 ≤ ∑ τ, freshScore W τ :=
    Finset.sum_nonneg (fun τ _ => freshScore_nonneg W τ)
  by_cases hW : W.toLeft.card < 2
  · have he : criticalExponent W = W.card := by
      simp only [criticalExponent, coreExponent_small _ hW, freshScore,
        no_square_of_small_core W hW, ite_false, sub_zero]
      rw [count_split W, Nat.cast_add, Nat.cast_sum]
    rw [he]
    exact_mod_cast min_le_right 2 W.card
  · have hc := coreExponent_lower W.toLeft
    have hm : min W.toLeft.card 2 = 2 := by omega
    rw [hm] at hc
    have hmin : ((min 2 W.card : ℕ) : ℤ) ≤ 2 := by exact_mod_cast min_le_left 2 W.card
    unfold criticalExponent
    omega

/-- Source Lemma `sample:lem-budget`, the strengthened admissible-set budget. -/
theorem criticalExponent_admissible (S W : Finset Field) (hS : Admissible S)
    (hSW : S ⊆ W) : (S.card : ℤ) ≤ criticalExponent W := by
  rcases hS with ⟨hS0, hcore⟩ | ⟨τ, _, hc⟩
  · have he : S.card = S.toLeft.card := by
      have hh := Finset.card_toLeft_add_card_toRight (u := S)
      rw [hS0, Finset.card_empty, add_zero] at hh
      exact hh.symm
    rw [he]
    have hbase := coreExponent_admissible S.toLeft W.toLeft hcore
      (Finset.toLeft_subset_toLeft hSW)
    have hz : 0 ≤ ∑ τ, freshScore W τ :=
      Finset.sum_nonneg (fun τ _ => freshScore_nonneg W τ)
    unfold criticalExponent
    omega
  · have hcard := Finset.card_le_card hSW
    have hi : S.card ≤ min 2 W.card := le_min hc hcard
    exact (by exact_mod_cast hi : (S.card : ℤ) ≤
      ((min 2 W.card : ℕ) : ℤ)).trans (criticalExponent_lower W)

end IncidenceTemplate
end HyperbolicObstruction
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_IncidenceTemplate
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeOutgoing _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.IncidenceTemplate.instFieldFintype _root_.OAI.HyperbolicObstruction.IncidenceTemplate.instRowFintype
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

lemma rowSupport_card (r : Row) : 3 ≤ (rowSupport r).card := by
  rcases r with i | (_ | τ)
  · simpa [rowSupport] using fan_card_lower i
  · simp [rowSupport, card_edges]
  · have hn := twoPath_ne τ
    simp [rowSupport, squareSupport, hn]

/-- The closure and its whole-integer positive margin with no uninstantiated
budget hypotheses: this is the exact master-pattern closure of Section 4. -/
theorem exists_critical_closure (I : Finset Field) (e : Field) (he : e ∉ I)
    (hadm : Admissible (insert e I)) :
    ∃ U : Finset Field, I ⊆ U ∧ criticalExponent U = I.card ∧ e ∉ U ∧
      ∀ V : Finset Field, V.Nonempty → Disjoint V U →
        1 ≤ criticalExponent (U ∪ V) - criticalExponent U := by
  have hcard := admissible_card _ hadm
  rw [Finset.card_insert_of_notMem he] at hcard
  have hsmall : I.card ≤ 2 := by omega
  have hnone (r : Row) : ¬rowSupport r ⊆ I := by
    intro hs
    have hle := Finset.card_le_card hs
    have hlo := rowSupport_card r
    omega
  have hi : pattern.exponent I = I.card :=
    pattern.exponent_eq_card I hnone
  have hIadm := admissible_subset hadm (Finset.subset_insert e I)
  obtain ⟨U, hu, hc, heu, hgap⟩ := pattern.critical_closure I e he hi
    (fun W hW => by rw [pattern_exponent]; exact criticalExponent_admissible I W hIadm hW)
    (fun W hW => by rw [pattern_exponent]; exact criticalExponent_admissible _ W hadm hW)
  refine ⟨U, hu, ?_, heu, ?_⟩
  · simpa only [pattern_exponent] using hc
  · intro V hV hdis
    simpa only [pattern_exponent] using hgap V hV hdis

end IncidenceTemplate
end HyperbolicObstruction
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_StarActual
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeOutgoing _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.IncidenceTemplate.instFieldFintype _root_.OAI.HyperbolicObstruction.IncidenceTemplate.instRowFintype
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
namespace IncidenceTemplate
variable {B : Type*} [Fintype B] [DecidableEq B] [Nonempty B]

lemma star_leaf_actual_gap {α β δ : ℝ} (ha : 0 ≤ α) (hb : 7 * α ≤ β) (hd : 0 ≤ δ)
    (U : Finset Field) (e : Field) (he : e ∉ U)
    (gap : ∀ W, W.Nonempty → Disjoint U W → 1 ≤ pattern.exponent (U ∪ W) - pattern.exponent U)
    (J : Finset (StarModel.Pos (B := B) rowSupport U)) (hJ : J.Nonempty) :
    1 - (Fintype.card B : ℝ) * (β + 90 * δ) ≤
      (((J.biUnion (StarModel.rowSupport rowSupport U)) \ StarModel.leafPins U e).card : ℝ) -
        ∑ s ∈ J, actualRowCost α β δ (StarModel.array rowSupport U s) := by
  have hcrit := StarModel.leaf_critical_gap pattern U e he
    (fun W => by rw [pattern_exponent]; exact criticalExponent_lower W) rowSupport_card gap J hJ
  have hc : (1 : ℝ) ≤
      (((J.biUnion (StarModel.rowSupport rowSupport U)) \ StarModel.leafPins U e).card : ℝ) -
        ∑ s ∈ J, (rowCost (StarModel.array rowSupport U s) : ℝ) := by
    exact_mod_cast hcrit
  have hs := star_surcharge ha hb hd U J
  simp only [actualRowCost,Finset.sum_add_distrib]
  linarith

end IncidenceTemplate

end HyperbolicObstruction
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_StarVariance
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeOutgoing _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.StarModel.instFintypeMatches _root_.OAI.HyperbolicObstruction.StarModel.instFintypeStars
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
namespace IncidenceTemplate

variable {B A : Type*} [Fintype B] [Fintype A] [DecidableEq B] [DecidableEq A]
  [Nonempty B] [Nonempty A]

/-- Relative variance for the literal fieldwise-injective leaf count. The
alphabet size threshold and constants are independent of pinned letter values. -/
theorem leaf_variance_bound {α β δ : ℝ} (ha : 0 ≤ α) (hb : 7 * α ≤ β) (hd : 0 ≤ δ)
    (hsmall : (Fintype.card B : ℝ) * (β + 90 * δ) ≤ 1 / 2)
    (U : Finset Field) (e : Field) (he : e ∉ U)
    (gap : ∀ W, W.Nonempty → Disjoint U W → 1 ≤ pattern.exponent (U ∪ W) - pattern.exponent U)
    (ξ : StarModel.Var (B := B) U → A)
    (hξ : PinnedAssignments.PinFieldwise (StarModel.field U) (StarModel.leafPins U e) ξ)
    (hN : 4 * Fintype.card (StarModel.Var (B := B) U) ≤ Fintype.card A) :
    let hp := fun r => TableModel.powerProbability_mem
      (show (1 : ℝ) ≤ Fintype.card A by exact_mod_cast Fintype.card_pos (α := A)) (actualRowCost_nonneg ha hb hd r)
    let μ := TableModel.law rowSupport (fun r => (Fintype.card A : ℝ) ^ (-actualRowCost α β δ r)) hp
    let X := fun w => (StarModel.leafCount rowSupport U e ξ w : ℝ)
    μ.variance X ≤ Fintype.card (BernoulliCandidates.OverlapType (StarModel.Pos (B := B) rowSupport U)) *
      2 ^ Fintype.card (PinnedAssignments.Free (StarModel.leafPins (B := B) U e)) *
      (Fintype.card A : ℝ) ^ (-(1 / 2 : ℝ)) * μ.expect X ^ 2 := by
  apply PinnedAssignments.relative_variance (StarModel.field U) (StarModel.leafPins U e) ξ hξ hN
    (StarModel.row rowSupport U) (StarModel.rowSupport rowSupport U) (StarModel.read_row rowSupport U)
    (fun σ hσ => StarModel.row_injective rowSupport U σ ((StarModel.fieldwise_iff U σ).mp hσ))
    _ _ (fun s => actualRowCost α β δ (StarModel.array rowSupport U s)) (fun _ _ => rfl)
  intro J hJ
  have hh := star_leaf_actual_gap ha hb hd U e he gap J hJ
  linarith

end IncidenceTemplate
end HyperbolicObstruction
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_StarCoupling
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeOutgoing _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
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
namespace StarModel
variable {F R A : Type*} [Fintype F] [Fintype R] [Fintype A]
  [DecidableEq F] [DecidableEq A] {k : ℕ}

def coupling (support : R → Finset F) (U I : Finset F) (hI : I ⊆ U)
    (w : TableModel.Entry (A := A) support → Bool)
    [Nonempty (Stars (B := Fin (k+1)) support U w)] :
    FiniteLaw (ConditionalStar (fun a : Matches support w => a.val) I k) :=
  (FiniteLaw.uniform : FiniteLaw (Stars (B := Fin (k+1)) support U w)).map (toConditional support U I hI w)

lemma coupling_branch (support : R → Finset F) (U I : Finset F) (hI : I ⊆ U)
    (w : TableModel.Entry (A := A) support → Bool)
    [Nonempty (Stars (B := Fin (k+1)) support U w)] (j : Fin (k+1)) :
    (coupling support U I hI w).map (ConditionalStar.branch j) =
      (FiniteLaw.uniform : FiniteLaw (Stars (B := Fin (k+1)) support U w)).map (starBranch support U w j) := by
  rw [coupling,FiniteLaw.map_map]
  rfl

lemma coupling_branch_bound (support : R → Finset F) (U I : Finset F) (hI : I ⊆ U)
    (w : TableModel.Entry (A := A) support → Bool)
    [Nonempty (Stars (B := Fin (k+1)) support U w)] [Nonempty (Matches support w)]
    (j : Fin (k+1)) (a : ℝ) :
    ((coupling support U I hI w).map (ConditionalStar.branch j)).totalVariation FiniteLaw.uniform ≤
      (∑ σ : Matches support w, |(extensionCount support U j (branchValues U σ.val) w : ℝ) - a|) /
        Fintype.card (Stars (B := Fin (k+1)) support U w) := by
  rw [coupling_branch]
  simpa only [card_branch_fiber] using FiniteLaw.uniform_map_bound (starBranch support U w j) a

lemma coupling_leaves (support : R → Finset F) (U I : Finset F) (hI : I ⊆ U)
    (e : F) (he : e ∉ U) (w : TableModel.Entry (A := A) support → Bool)
    [Nonempty (Stars (B := Fin (k+1)) support U w)] :
    (coupling support U I hI w).map (fun z j => (ConditionalStar.branch j z).val e) =
      ((FiniteLaw.uniform : FiniteLaw (Stars (B := Fin (k+1)) support U w)).map
        (starLeaves support U e he w)).map (fun b : Fin (k+1) ↪ A => (b : Fin (k+1) → A)) := by
  rw [coupling,FiniteLaw.map_map,FiniteLaw.map_map]
  rfl

lemma leaf_distribution_bound (support : R → Finset F) (U : Finset F)
    (e : F) (he : e ∉ U) (w : TableModel.Entry (A := A) support → Bool)
    [Nonempty (Stars (B := Fin (k+1)) support U w)] [Nonempty (Fin (k+1) ↪ A)]
    (a₀ : A) (b : ℝ) :
    ((FiniteLaw.uniform : FiniteLaw (Stars (B := Fin (k+1)) support U w)).map
      (starLeaves support U e he w)).totalVariation FiniteLaw.uniform ≤
      (∑ a : Fin (k+1) ↪ A, |(leafCount support U e (leafValues U a a₀) w : ℝ) - b|) /
        Fintype.card (Stars (B := Fin (k+1)) support U w) := by
  have hh := FiniteLaw.uniform_map_bound (starLeaves (B := Fin (k+1)) support U e he w) b
  have hc (a : Fin (k+1) ↪ A) :
      Fintype.card {z : Stars (B := Fin (k+1)) support U w // starLeaves support U e he w z = a} =
        leafCount support U e (leafValues U a a₀) w :=
    card_leaf_fiber support U e he w a a₀
  simp_rw [hc] at hh
  exact hh

/-- Both quantitative conclusions of the deterministic normalization lemma.
The last term is solely the distinct-versus-iid error; no conditional
independence from the common tuple has been assumed. -/
lemma coupling_leaves_bound (support : R → Finset F) (U I : Finset F) (hI : I ⊆ U)
    (e : F) (he : e ∉ U) (w : TableModel.Entry (A := A) support → Bool)
    [Nonempty (Stars (B := Fin (k+1)) support U w)] [Nonempty (Fin (k+1) ↪ A)] [Nonempty A]
    (a₀ : A) (b : ℝ) :
    ((coupling support U I hI w).map (fun z j => (ConditionalStar.branch j z).val e)).totalVariation
      (FiniteLaw.uniform : FiniteLaw (Fin (k+1) → A)) ≤
      (∑ a : Fin (k+1) ↪ A, |(leafCount support U e (leafValues U a a₀) w : ℝ) - b|) /
        Fintype.card (Stars (B := Fin (k+1)) support U w) +
      ((FiniteLaw.uniform : FiniteLaw (Fin (k+1) ↪ A)).map
        (fun a : Fin (k+1) ↪ A => (a : Fin (k+1) → A))).totalVariation
        (FiniteLaw.uniform : FiniteLaw (Fin (k+1) → A)) := by
  rw [coupling_leaves support U I hI e he w]
  apply (FiniteLaw.totalVariation_triangle _
    ((FiniteLaw.uniform : FiniteLaw (Fin (k+1) ↪ A)).map (fun a : Fin (k+1) ↪ A => (a : Fin (k+1) → A))) _).trans
  apply add_le_add _ le_rfl
  apply (FiniteLaw.totalVariation_map_le _ _ (fun a : Fin (k+1) ↪ A => (a : Fin (k+1) → A))).trans
  exact leaf_distribution_bound support U e he w a₀ b

end StarModel
end HyperbolicObstruction
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_ExtensionConditioning
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeOutgoing _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.StarModel.instFintypeMatches _root_.OAI.HyperbolicObstruction.StarModel.instFintypeStars
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
namespace StarModel
variable {F R B A : Type*} [Fintype F] [Fintype R] [Fintype B] [Fintype A]
  [DecidableEq F] [DecidableEq R] [DecidableEq B] [DecidableEq A] [Nonempty B]

/-- The entire law of the residual extension count is unchanged by conditioning
on the fixed branch being an actual match. -/
theorem extension_conditioning (support : R → Finset F) (U : Finset F) (j₀ : B)
    (ξ : Var (B := B) U → A) (p : R → ℝ) (hp : ∀ r, p r ∈ Set.Icc (0 : ℝ) 1)
    (g : ℕ → ℝ) :
    (TableModel.law support p hp).expect (fun w =>
      if TableModel.IsMatch support w (fun f => ξ (coord U j₀ f)) then
        g (extensionCount support U j₀ ξ w) else 0) =
      (∏ r, p r) * (TableModel.law support p hp).expect (fun w => g (extensionCount support U j₀ ξ w)) := by
  have hh := FiniteLaw.bernoulliProduct_event_mul (fun i : TableModel.Entry (A := A) support => p i.1)
    (fun i => hp i.1) (Finset.univ.image (TableModel.row support (fun f => ξ (coord U j₀ f))))
    (fun w => g (extensionCount support U j₀ ξ w))
    (fun w z h => congrArg g (extension_depends support U j₀ ξ w z h))
  have he (w : TableModel.Entry (A := A) support → Bool) :
      (∀ i ∈ Finset.univ.image (TableModel.row support (fun f => ξ (coord U j₀ f))), w i = true) ↔
        TableModel.IsMatch support w (fun f => ξ (coord U j₀ f)) := by
    simp [TableModel.IsMatch]
  simp only [he,Finset.prod_image (fun _ _ _ _ h => TableModel.row_injective support _ h)] at hh
  exact hh

end StarModel
end HyperbolicObstruction
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_Deviation
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeOutgoing _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
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
namespace StarModel
variable {F R B A : Type*} [Fintype F] [Fintype R] [Fintype B] [Fintype A]
  [DecidableEq F] [DecidableEq R] [DecidableEq B] [DecidableEq A] [Nonempty B]

/-- Summing the conditional first-moment bounds costs the expected number of
master matches, *not* the number of all assignments without its match factor. -/
theorem expect_branchDeviation (support : R → Finset F) (U : Finset F) (j : B)
    (p : R → ℝ) (hp : ∀ r, p r ∈ Set.Icc (0 : ℝ) 1) (ξ : Var (B := B) U → A)
    {r : ℝ} (hr : 0 ≤ r)
    (hv : ∀ σ : F → A,
      (TableModel.law support p hp).variance (fun w => (extensionCount support U j (branchValues U σ) w : ℝ)) ≤
        r * (TableModel.law support p hp).expect (fun w => (extensionCount support U j (branchValues U σ) w : ℝ)) ^ 2) :
    let μ := TableModel.law (A := A) support p hp
    let a := μ.expect (fun w => (extensionCount support U j ξ w : ℝ))
    μ.expect (branchDeviation support U j a) ≤
      ((Fintype.card (F → A) : ℝ) * ∏ r, p r) * Real.sqrt r * a := by
  dsimp only
  let μ := TableModel.law (A := A) support p hp
  let a := μ.expect (fun w => (extensionCount support U j ξ w : ℝ))
  change μ.expect (branchDeviation support U j a) ≤ _
  have hs (σ : F → A) : μ.expect (fun w => if TableModel.IsMatch support w σ then
      |(extensionCount support U j (branchValues U σ) w : ℝ) - a| else 0) ≤
        (∏ s, p s) * (Real.sqrt r * a) := by
    have hc := extension_conditioning support U j (branchValues (B := B) U σ) p hp (fun n => |(n : ℝ) - a|)
    simp only [branchValues_coord] at hc
    rw [show μ.expect (fun w => if TableModel.IsMatch support w σ then
      |(extensionCount support U j (branchValues U σ) w : ℝ) - a| else 0) =
      (∏ s, p s) * μ.expect (fun w => |(extensionCount support U j (branchValues U σ) w : ℝ) - a|) from hc]
    apply mul_le_mul_of_nonneg_left _ (Finset.prod_nonneg fun s _ => (hp s).1)
    have he : μ.expect (fun w => (extensionCount support U j (branchValues U σ) w : ℝ)) = a :=
      extension_expect_eq support U j _ ξ p hp
    have hh := μ.expect_abs_sub_le_relative (fun w => (extensionCount support U j (branchValues U σ) w : ℝ))
      hr (μ.expect_nonneg fun _ => Nat.cast_nonneg _) (hv σ)
    simpa only [he] using hh
  unfold branchDeviation
  rw [μ.expect_sum]
  calc
    _ ≤ ∑ _σ : F → A, (∏ s, p s) * (Real.sqrt r * a) := Finset.sum_le_sum fun σ _ => hs σ
    _ = _ := by simp [a,μ]; ring

/-- The corresponding unconditional L1 bound for ordered-distinct leaf lists. -/
theorem expect_leafDeviation (support : R → Finset F) (U : Finset F) (e : F)
    (p : R → ℝ) (hp : ∀ r, p r ∈ Set.Icc (0 : ℝ) 1) (ξ : Var (B := B) U → A)
    (hξ : PinnedAssignments.PinFieldwise (field U) (leafPins U e) ξ) (a₀ : A)
    {r : ℝ} (hr : 0 ≤ r)
    (hv : ∀ a : B ↪ A,
      (TableModel.law support p hp).variance (fun w => (leafCount support U e (leafValues U a a₀) w : ℝ)) ≤
        r * (TableModel.law support p hp).expect (fun w => (leafCount support U e (leafValues U a a₀) w : ℝ)) ^ 2) :
    let μ := TableModel.law (A := A) support p hp
    let b := μ.expect (fun w => (leafCount support U e ξ w : ℝ))
    μ.expect (leafDeviation (B := B) support U e a₀ b) ≤
      (Fintype.card (B ↪ A) : ℝ) * Real.sqrt r * b := by
  dsimp only
  let μ := TableModel.law (A := A) support p hp
  let b := μ.expect (fun w => (leafCount support U e ξ w : ℝ))
  change μ.expect (leafDeviation support U e a₀ b) ≤ _
  unfold leafDeviation
  rw [μ.expect_sum]
  calc
    _ ≤ ∑ _a : B ↪ A, Real.sqrt r * b := by
      apply Finset.sum_le_sum
      intro a _
      have he : μ.expect (fun w => (leafCount support U e (leafValues U a a₀) w : ℝ)) = b :=
        leaf_expect_eq support U e _ ξ p hp (leaf_pin_fieldwise U e a a₀) hξ
      have hh := μ.expect_abs_sub_le_relative (fun w => (leafCount support U e (leafValues U a a₀) w : ℝ))
        hr (μ.expect_nonneg fun _ => Nat.cast_nonneg _) (hv a)
      simpa only [he] using hh
    _ = _ := by simp [b,μ]; ring

end StarModel
end HyperbolicObstruction
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_StarMean
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeOutgoing _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
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

namespace StarModel
variable {F R B A : Type*} [Fintype F] [Fintype R] [Fintype B] [Fintype A]
  [DecidableEq F] [DecidableEq R] [DecidableEq B] [DecidableEq A] [Nonempty B]

lemma expect_starCount_branch (support : R → Finset F) (U : Finset F) (j : B)
    (p : R → ℝ) (hp : ∀ r, p r ∈ Set.Icc (0 : ℝ) 1) (ξ : Var (B := B) U → A) :
    let μ := TableModel.law (A := A) support p hp
    μ.expect (fun w => (starCount (B := B) support U w : ℝ)) =
      ((Fintype.card (F → A) : ℝ) * ∏ r, p r) *
        μ.expect (fun w => (extensionCount support U j ξ w : ℝ)) := by
  dsimp only
  let μ := TableModel.law (A := A) support p hp
  simp_rw [starCount_branch support U j]
  rw [μ.expect_sum]
  have he (σ : F → A) : μ.expect (fun w => if TableModel.IsMatch support w σ then
      (extensionCount support U j (branchValues U σ) w : ℝ) else 0) =
      (∏ r, p r) * μ.expect (fun w => (extensionCount support U j ξ w : ℝ)) := by
    have hh := extension_conditioning support U j (branchValues (B := B) U σ) p hp (fun n => (n : ℝ))
    simp only [branchValues_coord] at hh
    exact hh.trans (congrArg ((∏ r, p r) * ·) (extension_expect_eq support U j _ ξ p hp))
  simp_rw [he]
  simp
  ring

lemma expect_starCount_leaf (support : R → Finset F) (U : Finset F) (e : F) (he : e ∉ U)
    (p : R → ℝ) (hp : ∀ r, p r ∈ Set.Icc (0 : ℝ) 1) (ξ : Var (B := B) U → A)
    (hξ : PinnedAssignments.PinFieldwise (field U) (leafPins U e) ξ) (a₀ : A) :
    let μ := TableModel.law (A := A) support p hp
    μ.expect (fun w => (starCount (B := B) support U w : ℝ)) =
      (Fintype.card (B ↪ A) : ℝ) * μ.expect (fun w => (leafCount support U e ξ w : ℝ)) := by
  dsimp only
  let μ := TableModel.law (A := A) support p hp
  simp_rw [starCount_leaf support U e he _ a₀]
  rw [μ.expect_sum]
  have hh (b : B ↪ A) : μ.expect (fun w => (leafCount support U e (leafValues U b a₀) w : ℝ)) =
      μ.expect (fun w => (leafCount support U e ξ w : ℝ)) :=
    leaf_expect_eq support U e _ ξ p hp (leaf_pin_fieldwise U e b a₀) hξ
  simp_rw [hh]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  rfl

lemma starMean_pos [Nonempty A] (support : R → Finset F) (U : Finset F) (j : B)
    (p : R → ℝ) (hp : ∀ r, p r ∈ Set.Icc (0 : ℝ) 1) (hpos : ∀ r, 0 < p r)
    (ξ : Var (B := B) U → A) (hN : 4 * Fintype.card (Var (B := B) U) ≤ Fintype.card A) :
    0 < (TableModel.law (A := A) support p hp).expect (fun w => (starCount (B := B) support U w : ℝ)) := by
  rw [expect_starCount_branch (A := A) support U j p hp ξ]
  apply mul_pos
  · exact mul_pos (by exact_mod_cast Fintype.card_pos (α := F → A)) (Finset.prod_pos fun r _ => hpos r)
  · exact extensionMean_pos support U j p hp hpos ξ hN

end StarModel
end HyperbolicObstruction
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_StarError
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeOutgoing _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
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

namespace StarModel
variable {F R B A : Type*} [Fintype F] [Fintype R] [Fintype B] [Fintype A]
  [DecidableEq F] [DecidableEq R] [DecidableEq B] [DecidableEq A] [Nonempty B]

lemma normalizedError_nonneg (support : R → Finset F) (U : Finset F) (e : F)
    (p : R → ℝ) (hp : ∀ r, p r ∈ Set.Icc (0 : ℝ) 1) (a₀ : A) (b₀ : B ↪ A)
    (w : TableModel.Entry (A := A) support → Bool) :
    0 ≤ normalizedError support U e p hp a₀ b₀ w := by
  unfold normalizedError
  apply div_nonneg
  · exact add_nonneg (Finset.sum_nonneg fun j _ => branchDeviation_nonneg _ _ _ _ _)
      (leafDeviation_nonneg _ _ _ _ _ _)
  · exact FiniteLaw.expect_nonneg _ (fun _ => Nat.cast_nonneg _)

lemma expect_normalizedError_le (support : R → Finset F) (U : Finset F) (e : F) (he : e ∉ U)
    (p : R → ℝ) (hp : ∀ r, p r ∈ Set.Icc (0 : ℝ) 1) (a₀ : A) (b₀ : B ↪ A)
    (rE : B → ℝ) (rL : ℝ) (hrE : ∀ j, 0 ≤ rE j) (hrL : 0 ≤ rL)
    (hM : 0 < (TableModel.law (A := A) support p hp).expect (fun w => (starCount (B := B) support U w : ℝ)))
    (hvE : ∀ j (σ : F → A),
      (TableModel.law (A := A) support p hp).variance (fun w => (extensionCount support U j (branchValues U σ) w : ℝ)) ≤
        rE j * (TableModel.law (A := A) support p hp).expect (fun w => (extensionCount support U j (branchValues U σ) w : ℝ)) ^ 2)
    (hvL : ∀ b : B ↪ A,
      (TableModel.law (A := A) support p hp).variance (fun w => (leafCount support U e (leafValues U b a₀) w : ℝ)) ≤
        rL * (TableModel.law (A := A) support p hp).expect (fun w => (leafCount support U e (leafValues U b a₀) w : ℝ)) ^ 2) :
    (TableModel.law (A := A) support p hp).expect (normalizedError support U e p hp a₀ b₀) ≤
      (∑ j, Real.sqrt (rE j)) + Real.sqrt rL := by
  let μ := TableModel.law (A := A) support p hp
  let M := μ.expect (fun w => (starCount (B := B) support U w : ℝ))
  have hE (j : B) : μ.expect (branchDeviation support U j
      (μ.expect (fun w => (extensionCount support U j (fun _ => a₀) w : ℝ)))) ≤ Real.sqrt (rE j) * M := by
    have hh := expect_branchDeviation support U j p hp (fun _ => a₀) (hrE j) (hvE j)
    have hm := expect_starCount_branch support U j p hp (fun _ => a₀)
    dsimp only at hh hm
    change M = _ at hm
    rw [hm]
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have hL : μ.expect (leafDeviation (B := B) support U e a₀
      (μ.expect (fun w => (leafCount support U e (leafValues U b₀ a₀) w : ℝ)))) ≤ Real.sqrt rL * M := by
    have hh := expect_leafDeviation (B := B) support U e p hp (leafValues U b₀ a₀)
      (leaf_pin_fieldwise U e b₀ a₀) a₀ hrL hvL
    have hm := expect_starCount_leaf support U e he p hp (leafValues U b₀ a₀)
      (leaf_pin_fieldwise U e b₀ a₀) a₀
    dsimp only at hh hm
    change M = _ at hm
    rw [hm]
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    ring
  unfold normalizedError
  rw [μ.expect_div, μ.expect_add, μ.expect_sum]
  apply (div_le_iff₀ hM).mpr
  calc
    _ ≤ (∑ j, Real.sqrt (rE j) * M) + Real.sqrt rL * M :=
      add_le_add (Finset.sum_le_sum fun j _ => hE j) hL
    _ = _ := by rw [← Finset.sum_mul]; ring

lemma starCount_lower (support : R → Finset F) (U : Finset F) (e : F) (he : e ∉ U)
    (p : R → ℝ) (hp : ∀ r, p r ∈ Set.Icc (0 : ℝ) 1) (a₀ : A) (b₀ : B ↪ A)
    (w : TableModel.Entry (A := A) support → Bool) :
    (TableModel.law (A := A) support p hp).expect (fun w => (starCount (B := B) support U w : ℝ)) -
      leafDeviation (B := B) support U e a₀ ((TableModel.law (A := A) support p hp).expect
        (fun w => (leafCount support U e (leafValues U b₀ a₀) w : ℝ))) w ≤
      (starCount (B := B) support U w : ℝ) := by
  rw [expect_starCount_leaf support U e he p hp (leafValues U b₀ a₀)
    (leaf_pin_fieldwise U e b₀ a₀) a₀, starCount_leaf support U e he w a₀]
  have hh := FiniteLaw.abs_sum_sub_const
    (fun b : B ↪ A => (leafCount support U e (leafValues U b a₀) w : ℝ))
    ((TableModel.law (A := A) support p hp).expect (fun w => (leafCount support U e (leafValues U b₀ a₀) w : ℝ)))
  have hlo := (abs_le.mp hh).1
  unfold leafDeviation
  linarith

lemma starCount_pos_of_error (support : R → Finset F) (U : Finset F) (e : F) (he : e ∉ U)
    (p : R → ℝ) (hp : ∀ r, p r ∈ Set.Icc (0 : ℝ) 1) (a₀ : A) (b₀ : B ↪ A)
    (w : TableModel.Entry (A := A) support → Bool) {ε : ℝ} (hε1 : ε < 1)
    (hM : 0 < (TableModel.law (A := A) support p hp).expect (fun w => (starCount (B := B) support U w : ℝ)))
    (hε : normalizedError support U e p hp a₀ b₀ w ≤ ε) :
    0 < starCount (B := B) support U w := by
  have hl := starCount_lower support U e he p hp a₀ b₀ w
  have hd := (deviations_le_of_error support U e p hp a₀ b₀ w hM hε).2
  have hs : 0 < (starCount (B := B) support U w : ℝ) := by nlinarith
  exact_mod_cast hs

end StarModel
end HyperbolicObstruction
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_CouplingError
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeOutgoing _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
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

namespace StarModel
variable {F R A : Type*} [Fintype F] [Fintype R] [Fintype A]
  [DecidableEq F] [DecidableEq R] [DecidableEq A] [Nonempty A] {k : ℕ}

/-- The error statistic constructs the source coupling on the very same table.
There is no independent choice of a table for different branch marginals. -/
lemma coupling_of_error (support : R → Finset F) (U I : Finset F) (hI : I ⊆ U)
    (e : F) (he : e ∉ U) (p : R → ℝ) (hp : ∀ r, p r ∈ Set.Icc (0 : ℝ) 1)
    (a₀ : A) (b₀ : Fin (k+1) ↪ A) (w : TableModel.Entry (A := A) support → Bool)
    [Nonempty (Stars (B := Fin (k+1)) support U w)] [Nonempty (Matches support w)]
    {ε : ℝ} (hε1 : ε < 1)
    (hM : 0 < (TableModel.law (A := A) support p hp).expect
      (fun w => (starCount (B := Fin (k+1)) support U w : ℝ)))
    (hε : normalizedError support U e p hp a₀ b₀ w ≤ ε) :
    (∀ j : Fin (k+1), ((coupling (k := k) support U I hI w).map (ConditionalStar.branch j)).totalVariation
      FiniteLaw.uniform ≤ ε/(1-ε)) ∧
    ((coupling (k := k) support U I hI w).map (fun z j => (ConditionalStar.branch j z).val e)).totalVariation
      (FiniteLaw.uniform : FiniteLaw (Fin (k+1) → A)) ≤ ε/(1-ε) +
        (1 - ((Fintype.card A).descFactorial (k+1) : ℝ) / (Fintype.card A : ℝ)^(k+1)) := by
  let : Nonempty (Fin (k+1) ↪ A) := ⟨b₀⟩
  let μ := TableModel.law (A := A) support p hp
  let M := μ.expect (fun w => (starCount (B := Fin (k+1)) support U w : ℝ))
  let Z : ℝ := starCount (B := Fin (k+1)) support U w
  have hε0 := (normalizedError_nonneg support U e p hp a₀ b₀ w).trans hε
  obtain ⟨hE,hL⟩ := deviations_le_of_error support U e p hp a₀ b₀ w hM hε
  have hZ : (1-ε)*M ≤ Z := by
    have hl := starCount_lower support U e he p hp a₀ b₀ w
    change M - _ ≤ Z at hl
    change _ ≤ ε*M at hL
    linarith
  constructor
  · intro j
    apply (coupling_branch_bound support U I hI w j
      (μ.expect (fun w => (extensionCount support U j (fun _ => a₀) w : ℝ)))).trans
    rw [← branchDeviation_subtype]
    exact ratio_error_bound hM hε0 hε1 hZ (hE j)
  · have hh := coupling_leaves_bound (k := k) support U I hI e he w a₀
      (μ.expect (fun w => (leafCount support U e (leafValues U b₀ a₀) w : ℝ)))
    rw [FiniteLaw.distinct_tv] at hh
    simp only [Fintype.card_fin] at hh
    apply hh.trans
    exact add_le_add (ratio_error_bound hM hε0 hε1 hZ hL) le_rfl

end StarModel
end HyperbolicObstruction
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_SixCounts
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
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
namespace SixTable
variable {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

lemma count_chernoff {δ ε : ℝ} (hδ : 0 ≤ δ) (hε : 0 < ε) (hε2 : ε ≤ 2)
    {r q : Fin 6} (h : r ≠ q) (u v : A) :
    (law (A := A) δ hδ).prob (fun w => ε*(Fintype.card A : ℝ)^(1-δ) ≤
      |count r q u v w - (Fintype.card A : ℝ)^(1-δ)|) ≤
      2*Real.exp (-ε^2*(Fintype.card A : ℝ)^(1-δ)/4) := by
  simpa only [law,centered_eq δ h,pair_mean δ h] using
    FiniteLaw.centeredCount_chernoff (fun _ : Fin 6 → A => probability (A := A) δ)
      (fun _ => probability_mem hδ) (pairTrials r q u v) hε hε2

/-- Simultaneous control of all ordered pairs in the actual single six-letter
array. No independence of different pair counts is used. -/
theorem badPairs_bound {δ ε : ℝ} (hδ : 0 ≤ δ) (hε : 0 < ε) (hε2 : ε ≤ 2) :
    (law (A := A) δ hδ).prob (BadPairs δ ε) ≤
      60*(Fintype.card A : ℝ)^2*Real.exp (-ε^2*(Fintype.card A : ℝ)^(1-δ)/4) := by
  classical
  apply (FiniteLaw.prob_exists_le (J := PairPositions) (law (A := A) δ hδ)
    (fun rq w => ∃ u v : A, ε*(Fintype.card A : ℝ)^(1-δ) ≤
      |count rq.val.1 rq.val.2 u v w - (Fintype.card A : ℝ)^(1-δ)|)).trans
  calc
    _ ≤ ∑ rq : PairPositions, ∑ u : A, ∑ v : A,
        2*Real.exp (-ε^2*(Fintype.card A : ℝ)^(1-δ)/4) := by
      apply Finset.sum_le_sum
      intro rq _
      apply (FiniteLaw.prob_exists_le (J := A) (law (A := A) δ hδ)
        (fun u w => ∃ v : A, ε*(Fintype.card A : ℝ)^(1-δ) ≤
          |count rq.val.1 rq.val.2 u v w - (Fintype.card A : ℝ)^(1-δ)|)).trans
      apply Finset.sum_le_sum
      intro u _
      apply (FiniteLaw.prob_exists_le (J := A) (law (A := A) δ hδ)
        (fun v w => ε*(Fintype.card A : ℝ)^(1-δ) ≤
          |count rq.val.1 rq.val.2 u v w - (Fintype.card A : ℝ)^(1-δ)|)).trans
      exact Finset.sum_le_sum fun v _ => count_chernoff hδ hε hε2 rq.property u v
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,card_pairPositions]; ring

end SixTable
end HyperbolicObstruction
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_StarRate
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeOutgoing _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
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
variable {B A : Type*} [Fintype B] [Fintype A] [DecidableEq B] [DecidableEq A]
  [Nonempty B] [Nonempty A]

/-- All constants in the error estimate are independent of the alphabet,
parameters and the pinned values. Only the fixed finite star template remains. -/
theorem expectedError_le {α β δ : ℝ} (ha : 0 ≤ α) (hb : 7*α ≤ β) (hd : 0 ≤ δ)
    (hsmall : (Fintype.card B : ℝ) * (β+90*δ) ≤ 1/2)
    (U : Finset Field) (e : Field) (he : e ∉ U)
    (gap : ∀ W, W.Nonempty → Disjoint U W → 1 ≤ pattern.exponent (U ∪ W) - pattern.exponent U)
    (a₀ : A) (b₀ : B ↪ A) (hN : 4 * Fintype.card (StarModel.Var (B := B) U) ≤ Fintype.card A) :
    let p := actualProbability α β δ A
    let hp := actualProbability_mem (A := A) ha hb hd
    (TableModel.law rowSupport p hp).expect (StarModel.normalizedError rowSupport U e p hp a₀ b₀) ≤
      errorRate (B := B) U e (Fintype.card A) := by
  apply StarModel.expect_normalizedError_le rowSupport U e he
    (actualProbability α β δ A) (actualProbability_mem (A := A) ha hb hd) a₀ b₀
    (fun j => extensionRate U j (Fintype.card A)) (leafRate (B := B) U e (Fintype.card A))
  · intro j; unfold extensionRate; positivity
  · unfold leafRate; positivity
  · exact StarModel.starMean_pos rowSupport U (Classical.choice inferInstance) _ _
      (actualProbability_pos α β δ) (fun _ => a₀) hN
  · intro j σ
    exact extension_variance_bound ha hb hd hsmall U j gap (StarModel.branchValues U σ) hN
  · intro b
    exact leaf_variance_bound ha hb hd hsmall U e he gap (StarModel.leafValues U b a₀)
      (StarModel.leaf_pin_fieldwise U e b a₀) hN

end IncidenceTemplate
end HyperbolicObstruction
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_Test
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeOutgoing _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
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

namespace ConditionalTest

def closure (t : ConditionalTest) : Finset Field :=
  (exists_critical_closure t.fields t.leaf t.newLeaf t.admissible).choose

lemma closure_spec (t : ConditionalTest) : t.fields ⊆ t.closure ∧
    criticalExponent t.closure = t.fields.card ∧ t.leaf ∉ t.closure ∧
    ∀ W, W.Nonempty → Disjoint W t.closure →
      1 ≤ criticalExponent (t.closure ∪ W) - criticalExponent t.closure :=
  (exists_critical_closure t.fields t.leaf t.newLeaf t.admissible).choose_spec

lemma closure_gap (t : ConditionalTest) (W : Finset Field) (hW : W.Nonempty) (hd : Disjoint t.closure W) :
    1 ≤ pattern.exponent (t.closure ∪ W) - pattern.exponent t.closure := by
  simp only [pattern_exponent]
  exact t.closure_spec.2.2.2 W hW hd.symm

def threshold (t : ConditionalTest) : ℕ :=
  max (4 * Fintype.card (StarModel.Var (B := Fin (t.k+1)) t.closure)) (t.k+1)

def rate (t : ConditionalTest) (N : ℕ) : ℝ :=
  errorRate (B := Fin (t.k+1)) t.closure t.leaf N

lemma rate_tendsto (t : ConditionalTest) : Tendsto t.rate atTop (𝓝 0) :=
  errorRate_tendsto t.closure t.leaf

variable {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

def embedding (t : ConditionalTest) (hN : t.threshold ≤ Fintype.card A) : Fin (t.k+1) ↪ A :=
  Classical.choice (Function.Embedding.nonempty_of_card_le
    (by simpa only [Fintype.card_fin] using (le_max_right _ _).trans hN :
      Fintype.card (Fin (t.k+1)) ≤ Fintype.card A))

def error (t : ConditionalTest) (α β δ : ℝ) (ha : 0 ≤ α) (hb : 7*α ≤ β) (hd : 0 ≤ δ)
    (hN : t.threshold ≤ Fintype.card A) (w : TableModel.Entry (A := A) rowSupport → Bool) : ℝ :=
  StarModel.normalizedError rowSupport t.closure t.leaf (actualProbability α β δ A)
    (actualProbability_mem ha hb hd) (Classical.choice inferInstance) (t.embedding hN) w

lemma error_nonneg (t : ConditionalTest) (α β δ : ℝ) (ha : 0 ≤ α) (hb : 7*α ≤ β) (hd : 0 ≤ δ)
    (hN : t.threshold ≤ Fintype.card A) (w : TableModel.Entry (A := A) rowSupport → Bool) :
    0 ≤ t.error α β δ ha hb hd hN w := StarModel.normalizedError_nonneg _ _ _ _ _ _ _ _

lemma expectedError (t : ConditionalTest) {α β δ : ℝ} (ha : 0 ≤ α) (hb : 7*α ≤ β) (hd : 0 ≤ δ)
    (hsmall : (t.k+1:ℝ)*(β+90*δ) ≤ 1/2) (hN : t.threshold ≤ Fintype.card A) :
    (TableModel.law rowSupport (actualProbability α β δ A) (actualProbability_mem ha hb hd)).expect
      (t.error α β δ ha hb hd hN) ≤ t.rate (Fintype.card A) := by
  apply expectedError_le ha hb hd (by simpa using hsmall)
    t.closure t.leaf t.closure_spec.2.2.1 t.closure_gap
  exact (le_max_left _ _).trans hN

/-- The coupling is on actual master matches. Its branches agree on exactly the
prescribed named fields, with no assumptions about numerical cross-field values. -/
def Satisfies (t : ConditionalTest) (w : TableModel.Entry (A := A) rowSupport → Bool) (η : ℝ) : Prop :=
  ∃ h : Nonempty (StarModel.Matches rowSupport w), letI := h
    ∃ κ : FiniteLaw (ConditionalStar (fun a : StarModel.Matches rowSupport w => a.val) t.fields t.k),
      (∀ j, (κ.map (ConditionalStar.branch j)).totalVariation FiniteLaw.uniform ≤ η) ∧
      (κ.map (fun z j => (ConditionalStar.branch j z).val t.leaf)).totalVariation
        (FiniteLaw.uniform : FiniteLaw (Fin (t.k+1) → A)) ≤ η

lemma satisfies_of_error (t : ConditionalTest) {α β δ ε : ℝ} (ha : 0 ≤ α) (hb : 7*α ≤ β) (hd : 0 ≤ δ)
    (hN : t.threshold ≤ Fintype.card A) (w : TableModel.Entry (A := A) rowSupport → Bool)
    (hε : ε < 1) (hw : t.error α β δ ha hb hd hN w ≤ ε) :
    t.Satisfies w (ε/(1-ε) +
      (1-((Fintype.card A).descFactorial (t.k+1):ℝ)/(Fintype.card A:ℝ)^(t.k+1))) := by
  let a₀ : A := Classical.choice inferInstance
  let b₀ : Fin (t.k+1) ↪ A := t.embedding hN
  let : Nonempty (Fin (t.k+1) ↪ A) := ⟨b₀⟩
  have hM := StarModel.starMean_pos rowSupport t.closure (0 : Fin (t.k+1))
    (actualProbability α β δ A) (actualProbability_mem ha hb hd)
    (actualProbability_pos α β δ) (fun _ => a₀) ((le_max_left _ _).trans hN)
  have hz := StarModel.starCount_pos_of_error rowSupport t.closure t.leaf t.closure_spec.2.2.1
    (actualProbability α β δ A) (actualProbability_mem ha hb hd) a₀ b₀ w hε hM hw
  let : Nonempty (StarModel.Stars (B := Fin (t.k+1)) rowSupport t.closure w) := Fintype.card_pos_iff.mp hz
  let : Nonempty (StarModel.Matches rowSupport w) :=
    ⟨StarModel.starBranch rowSupport t.closure w (0 : Fin (t.k+1)) (Classical.choice inferInstance)⟩
  have hh := StarModel.coupling_of_error rowSupport t.closure t.fields t.closure_spec.1
    t.leaf t.closure_spec.2.2.1 (actualProbability α β δ A) (actualProbability_mem ha hb hd)
    a₀ b₀ w hε hM hw
  refine ⟨inferInstance,StarModel.coupling (k := t.k) rowSupport t.closure t.fields t.closure_spec.1 w,?_,?_⟩
  · intro j
    apply (hh.1 j).trans
    have he := (FiniteLaw.distinct_tv (α := Fin (t.k+1)) (β := A))
    have hp := FiniteLaw.totalVariation_nonneg
      (((FiniteLaw.uniform : FiniteLaw (Fin (t.k+1) ↪ A)).map (fun b => (b : Fin (t.k+1) → A))))
      FiniteLaw.uniform
    rw [he] at hp
    simp only [Fintype.card_fin] at hp
    linarith
  · exact hh.2

end ConditionalTest
end IncidenceTemplate
end HyperbolicObstruction
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_FiniteSampling
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeOutgoing _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
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

namespace ConditionalTest
variable {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
lemma satisfies_mono (t : ConditionalTest) {w : TableModel.Entry (A := A) rowSupport → Bool}
    {η ξ : ℝ} (h : t.Satisfies w η) (hη : η ≤ ξ) : t.Satisfies w ξ := by
  obtain ⟨hne,κ,hb,hl⟩ := h
  exact ⟨hne,κ,fun i => (hb i).trans hη,hl.trans hη⟩
end ConditionalTest

end IncidenceTemplate
end HyperbolicObstruction
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_DiagonalSampling
attribute [-instance] _root_.OAI.HyperbolicObstruction.Coincidence.instDecidablePredForallBoolRankBad _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeOutgoing _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
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

/-- All finitely many requested tests and the actual six-letter array at one
stage. This is selected below, not an assumption about a desired action. -/
structure SamplingStage (m : ℕ) (δ : ℝ) where
  size : ℕ
  large : m ≤ size
  master : TableModel.Entry (A := SymmetricAlphabet size) rowSupport → Bool
  six : (Fin 6 → SymmetricAlphabet size) → Bool
  nonempty : Nonempty (StarModel.Matches rowSupport master)
  six_good : ¬SixTable.BadPairs δ (stageError m) six
  tests : ∀ p : ConditionalData, ∀ k : ℕ, k ≤ m → (p.test k).Satisfies master (stageError m)


end IncidenceTemplate
end HyperbolicObstruction
end
end
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_Graph
attribute [-instance] _root_.OAI.HyperbolicObstruction.CoreGeometry.instDecidableIsFanVertex _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
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

namespace Path
variable {a b c : Vertex}

def append : {a b c : Vertex} → Path a b → Path b c → Path a c
  | _, _, _, .nil _, q => q
  | _, _, _, .cons s p, q => .cons s (append p q)

def symm : {a b : Vertex} → Path a b → Path b a
  | _, _, .nil a => .nil a
  | _, _, .cons s p => p.symm.append (.cons s.symm (.nil _))
end Path

theorem corePath_nonempty (v : CoreGeometry.Vertex) : Nonempty (Path root (.inl v)) := by
  rcases v with r | l
  · fin_cases r
    · exact ⟨(.nil _)⟩
    · exact ⟨(.cons (coreStep (a := (.inl 0)) (b := (.inr 2)) (by decide)) (.cons (coreStep (a := (.inr 2)) (b := (.inl 1)) (by decide)) (.nil _)))⟩
    · exact ⟨(.cons (coreStep (a := (.inl 0)) (b := (.inr 1)) (by decide)) (.cons (coreStep (a := (.inr 1)) (b := (.inl 2)) (by decide)) (.nil _)))⟩
    · exact ⟨(.cons (coreStep (a := (.inl 0)) (b := (.inr 6)) (by decide)) (.cons (coreStep (a := (.inr 6)) (b := (.inl 3)) (by decide)) (.nil _)))⟩
    · exact ⟨(.cons (coreStep (a := (.inl 0)) (b := (.inr 2)) (by decide)) (.cons (coreStep (a := (.inr 2)) (b := (.inl 4)) (by decide)) (.nil _)))⟩
    · exact ⟨(.cons (coreStep (a := (.inl 0)) (b := (.inr 1)) (by decide)) (.cons (coreStep (a := (.inr 1)) (b := (.inl 5)) (by decide)) (.nil _)))⟩
    · exact ⟨(.cons (coreStep (a := (.inl 0)) (b := (.inr 6)) (by decide)) (.cons (coreStep (a := (.inr 6)) (b := (.inl 6)) (by decide)) (.nil _)))⟩
    · exact ⟨(.cons (coreStep (a := (.inl 0)) (b := (.inr 1)) (by decide)) (.cons (coreStep (a := (.inr 1)) (b := (.inl 7)) (by decide)) (.nil _)))⟩
    · exact ⟨(.cons (coreStep (a := (.inl 0)) (b := (.inr 2)) (by decide)) (.cons (coreStep (a := (.inr 2)) (b := (.inl 8)) (by decide)) (.nil _)))⟩
    · exact ⟨(.cons (coreStep (a := (.inl 0)) (b := (.inr 1)) (by decide)) (.cons (coreStep (a := (.inr 1)) (b := (.inl 9)) (by decide)) (.nil _)))⟩
    · exact ⟨(.cons (coreStep (a := (.inl 0)) (b := (.inr 6)) (by decide)) (.cons (coreStep (a := (.inr 6)) (b := (.inl 10)) (by decide)) (.nil _)))⟩
  · fin_cases l
    · exact ⟨(.cons (coreStep (a := (.inl 0)) (b := (.inr 1)) (by decide)) (.cons (coreStep (a := (.inr 1)) (b := (.inl 2)) (by decide)) (.cons (coreStep (a := (.inl 2)) (b := (.inr 0)) (by decide)) (.nil _))))⟩
    · exact ⟨(.cons (coreStep (a := (.inl 0)) (b := (.inr 1)) (by decide)) (.nil _))⟩
    · exact ⟨(.cons (coreStep (a := (.inl 0)) (b := (.inr 2)) (by decide)) (.nil _))⟩
    · exact ⟨(.cons (coreStep (a := (.inl 0)) (b := (.inr 1)) (by decide)) (.cons (coreStep (a := (.inr 1)) (b := (.inl 5)) (by decide)) (.cons (coreStep (a := (.inl 5)) (b := (.inr 3)) (by decide)) (.nil _))))⟩
    · exact ⟨(.cons (coreStep (a := (.inl 0)) (b := (.inr 1)) (by decide)) (.cons (coreStep (a := (.inr 1)) (b := (.inl 2)) (by decide)) (.cons (coreStep (a := (.inl 2)) (b := (.inr 4)) (by decide)) (.nil _))))⟩
    · exact ⟨(.cons (coreStep (a := (.inl 0)) (b := (.inr 1)) (by decide)) (.cons (coreStep (a := (.inr 1)) (b := (.inl 5)) (by decide)) (.cons (coreStep (a := (.inl 5)) (b := (.inr 5)) (by decide)) (.nil _))))⟩
    · exact ⟨(.cons (coreStep (a := (.inl 0)) (b := (.inr 6)) (by decide)) (.nil _))⟩


def corePath (v : CoreGeometry.Vertex) : Path root (.inl v) := Classical.choice (corePath_nonempty v)

def route (v : Vertex) : Path root v :=
  match v with
  | .inl v => corePath v
  | .inr τ => (corePath (right τ)).append (.cons (Step.pos (.inr (τ,0))) (.nil _))

end MasterGraph
end HyperbolicObstruction
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_GraphAction
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeOutgoing _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.IncidenceTemplate.instFieldFintype
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

namespace Step
variable {G L : Type*} [Group G]

lemma value_symm {a b : Vertex} (s : Step a b) (label : Field → L) (letter : L → G) :
    s.symm.value label letter = (s.value label letter)⁻¹ := by
  cases h : s.forward <;> simp [value, symm, h]
end Step

namespace Path
variable {G L : Type*} [Group G] {a b c : Vertex}

lemma eval_append (label : Field → L) (letter : L → G) (p : Path a b) (q : Path b c) :
    (p.append q).eval label letter = p.eval label letter * q.eval label letter := by
  induction p with
  | nil => simp [append, eval]
  | cons s p ih => simp only [append, eval, ih, mul_assoc]

lemma eval_symm (label : Field → L) (letter : L → G) (p : Path a b) :
    p.symm.eval label letter = (p.eval label letter)⁻¹ := by
  induction p with
  | nil => simp [symm, eval]
  | cons s p ih => simp [symm, eval_append, eval, ih, Step.value_symm]

/-- A field-sign map is compatible with each actual edge traversal. -/
def Compatible (σ : Field → Bool) : {a b : Vertex} → Path a b → Prop
  | _, _, .nil _ => True
  | _, _, .cons s p => σ s.field = s.forward ∧ p.Compatible σ

lemma bound {X : Type*} [MetricSpace X] (A : G →* (X ≃ᵢ X)) (o : X)
    (label : Field → L) (letter : L → G) {M : ℝ}
    (hb : ∀ i, dist o (A (letter i) o) ≤ M) (p : Path a b) :
    dist o (A (p.eval label letter) o) ≤ p.length * M := by
  induction p with
  | nil => simp [eval, length]
  | cons s p ih =>
    have hs : dist o (A (s.value label letter) o) ≤ M := by
      cases h : s.forward
      · simpa only [Step.value, h, Bool.false_eq_true, ↓reduceIte,
          IsometricAction.displacement_inv] using hb (label s.field)
      · simpa only [Step.value, h, ↓reduceIte] using hb (label s.field)
    have hh := (IsometricAction.displacement_mul_le A o _ _).trans (add_le_add hs ih)
    simpa [eval, length, add_mul, add_comm M] using hh
end Path

namespace Potential
variable {L G : Type*} [Group G] {label : Field → L} {letter : L → G}
  (g : Potential label letter)

lemma step {a b : Vertex} (s : Step a b) : g.val b = g.val a * s.value label letter := by
  cases h : s.forward
  · obtain ⟨ha,hb⟩ := s.endpoints_neg h
    simp only [Step.value, h, Bool.false_eq_true, ↓reduceIte]
    have hh := g.edge s.field
    simp only [ha,hb] at hh
    rw [hh, mul_assoc, mul_inv_cancel, mul_one]
  · obtain ⟨ha,hb⟩ := s.endpoints_pos h
    simp only [Step.value, h, ↓reduceIte]
    simpa only [ha,hb] using g.edge s.field

lemma path {a b : Vertex} (p : Path a b) : g.val b = g.val a * p.eval label letter := by
  induction p with
  | nil => simp [Path.eval]
  | cons s p ih => rw [ih, g.step s, mul_assoc]; rfl

lemma route (v : Vertex) : g.val v = (MasterGraph.route v).eval label letter := by
  simpa only [g.root_one, one_mul] using g.path (MasterGraph.route v)

end Potential
end MasterGraph
end HyperbolicObstruction
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_OrbitLimit
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
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
namespace OrbitLimit
universe u v
variable {L Ω : ℕ → Type u} [∀ n, Fintype (L n)]
  [∀ n, Fintype (Ω n)] [∀ n, Nonempty (Ω n)]
  {X : ℕ → Type v} [∀ n, MetricSpace (X n)] {M : ℝ}
  (O : ∀ n, EnergyOrbit (L n) (X n) M)

/-- Actual orbit-coordinate arrays with a uniform bound from the minimizing
basepoints, before taking any product or limiting metric. -/
@[ext] structure Array where
  val : ∀ n, Ω n → X n
  bound : ∃ R : ℝ, 0 ≤ R ∧ ∀ n m, dist (O n).base (val n m) ≤ R

def origin (n : ℕ) : Product (Ω := Ω) (X := X) n :=
  MeanProduct.ofFn _ _ (fun _ => (O n).base)
include O in
theorem productCat (n : ℕ) : CATZero (Product (Ω := Ω) (X := X) n) :=
  MeanProduct.catZero (fun _ => (O n).cat)

variable (U : Ultrafilter ℕ)
def boundedSection (x : Array (Ω := Ω) O) : MetricLimit.Bounded U _ (origin (Ω := Ω) O) :=
  ⟨fun n => MeanProduct.ofFn _ _ (x.val n), by
    obtain ⟨R, hR, hx⟩ := x.bound
    exact ⟨R, fun n => MeanProduct.dist_le_of_forall _ _ hR (hx n)⟩⟩

abbrev Space := MetricLimit.Space (U := U) (X := Product (Ω := Ω) (X := X))
  (o := origin (Ω := Ω) O)
def point (x : Array (Ω := Ω) O) : Space (Ω := Ω) O U := MetricLimit.point (boundedSection O U x)
theorem catZero : CATZero (Space (Ω := Ω) O U) := MetricLimit.catZero (productCat (Ω := Ω) O)

variable {O U}

/-- Coordinate segments stay uniformly bounded. -/
def segment (x y : Array (Ω := Ω) O) (t : ℝ) : Array (Ω := Ω) O :=
  if ht : t ∈ Set.Icc (0 : ℝ) 1 then
    ⟨fun n m => CATZero.segment (O n).cat (x.val n m) (y.val n m) t, by
      obtain ⟨R, hR, hx⟩ := x.bound
      obtain ⟨S, hS, hy⟩ := y.bound
      refine ⟨2 * R + S, by positivity, fun n m => ?_⟩
      have hd : dist (x.val n m) (y.val n m) ≤ R + S := by
        calc
          _ ≤ dist (x.val n m) (O n).base + dist (O n).base (y.val n m) := dist_triangle _ _ _
          _ ≤ R + S := by rw [dist_comm (x.val n m)]; exact add_le_add (hx n m) (hy n m)
      calc
        _ ≤ dist (O n).base (x.val n m) + dist (x.val n m)
          (CATZero.segment (O n).cat (x.val n m) (y.val n m) t) := dist_triangle _ _ _
        _ = dist (O n).base (x.val n m) + t * dist (x.val n m) (y.val n m) := by
          rw [CATZero.segment_left (O n).cat _ _ ht]
        _ ≤ R + dist (x.val n m) (y.val n m) := add_le_add (hx n m)
          (mul_le_of_le_one_left dist_nonneg ht.2)
        _ ≤ 2 * R + S := by linarith⟩
  else x

end OrbitLimit
end HyperbolicObstruction

end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_GraphLimit
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeOutgoing _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.IncidenceTemplate.instFieldFintype
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
namespace MasterGraph
open IncidenceTemplate OrbitLimit
universe u v w
variable {L Ω : ℕ → Type u} [∀ n, Fintype (L n)] [∀ n, Nonempty (L n)]
  [∀ n, DecidableEq (L n)] [∀ n, Fintype (Ω n)] [∀ n, Nonempty (Ω n)]
  {label : ∀ n, Ω n → Field → L n}
  {X : ℕ → Type v} [∀ n, MetricSpace (X n)] {M : ℝ}
  (O : ∀ n, EnergyOrbit (L n) (X n) M)
  {G : ℕ → Type w} [∀ n, Group (G n)]
  (A : ∀ n, G n →* (X n ≃ᵢ X n)) (letter : ∀ n, L n → G n)
  (hact : ∀ n i, A n (letter n i) = (O n).isom i)
  (g : ∀ n m, Potential (label n m) (letter n)) (hM : 0 ≤ M)

/-- The actual graph-valued orbit array, uniformly bounded using the fixed
finite route to each vertex. -/
def array (v : Vertex) : OrbitLimit.Array (Ω := Ω) O where
  val n m := A n ((g n m).val v) (O n).base
  bound := by
    refine ⟨(route v).length * M, mul_nonneg (by positivity) hM, fun n m => ?_⟩
    rw [(g n m).route v]
    exact Path.bound (A n) (O n).base _ _
      (fun i => by rw [hact]; exact (O n).bound i) _

variable (S : SamplingSequence Field Admissible L Ω label)
  {U : Ultrafilter ℕ} (hU : (U : Filter ℕ) ≤ atTop)
  (inv : ∀ n, L n ≃ L n) (hinv : ∀ n i, letter n (inv n i) = (letter n i)⁻¹)

abbrev limit (v : Vertex) : OrbitLimit.Space (Ω := Ω) O U :=
  OrbitLimit.point O U (array O A letter hact g hM v)

end MasterGraph
end HyperbolicObstruction
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_Exceptional
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeOutgoing _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.IncidenceTemplate.instFieldFintype
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

namespace MasterGraph
open IncidenceTemplate OrbitLimit

universe u v w
variable {L Ω : ℕ → Type u} [∀ n, Fintype (L n)]
  {label : ∀ n, Ω n → Field → L n}
  {X : ℕ → Type v} [∀ n, MetricSpace (X n)] {M : ℝ}
  (O : ∀ n, EnergyOrbit (L n) (X n) M)
  {G : ℕ → Type w} [∀ n, Group (G n)]
  (A : ∀ n, G n →* (X n ≃ᵢ X n)) (letter : ∀ n, L n → G n)
  (hact : ∀ n i, A n (letter n i) = (O n).isom i)
  (g : ∀ n m, Potential (label n m) (letter n)) (hM : 0 ≤ M)
  (inv : ∀ n, L n ≃ L n) (hinv : ∀ n i, letter n (inv n i) = (letter n i)⁻¹)

def excTest (n : ℕ) (m : Ω n) : X n :=
  CATZero.mid (O n).cat
    ((O n).isom (inv n (label n m (.inl excC))) (O n).base)
    ((O n).isom (inv n (label n m (.inl excY))) (O n).base)

end MasterGraph
end HyperbolicObstruction
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_Presentation
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeOutgoing _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
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

namespace Path
variable {a b c : Vertex}
lemma isCore_append (p : Path a b) (q : Path b c) (hp : p.IsCore) (hq : q.IsCore) :
    (p.append q).IsCore := by
  induction p with
  | nil => exact hq
  | cons s p ih =>
    intro f hf
    rcases List.mem_cons.mp hf with rfl | hf
    · exact hp _ (List.mem_cons_self)
    · exact ih q (fun f hf => hp f (List.mem_cons_of_mem _ hf)) hq f hf
lemma isCore_symm (p : Path a b) (hp : p.IsCore) : p.symm.IsCore := by
  induction p with
  | nil => exact hp
  | cons s p ih =>
    apply isCore_append _ _ (ih (fun f hf => hp f (List.mem_cons_of_mem _ hf)))
    intro f hf
    simp only [fields,List.mem_cons,List.not_mem_nil,or_false] at hf
    exact hf ▸ hp s.field (List.mem_cons_self)

end Path

end MasterGraph

end HyperbolicObstruction
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_NormalCell
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutSide _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeOutsideContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypePartBoundary _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativePartBoundary
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

variable {S : Type v} {L : Type w} {V : Type z} {A : Type k} [AddCommMonoid A]

attribute [instance] CellPicture.finite CellPicture.decEq

namespace CellPicture
variable {T : CellTarget S L V A} (P : CellPicture.{u} T)

def chain : A := faceChain P.pairing.face (T.weight ∘ P.index)
  (fun x => by change T.weight (P.index (P.pairing.face x)) = _; rw [P.mapped.commute,T.weight_next]; rfl)

end CellPicture
end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_PolygonSphereFurther
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutSide _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeOutsideContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypePartBoundary _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativePartBoundary
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
variable {D B : Type*}

namespace PolygonSphere
variable {I : Type*} (q : Perm I)

variable [Fintype I]

lemma connected (hq : ∀ i j, q.SameCycle i j) (x y : Bool × I) :
    (pairing q).components x y := by
  have h₁ : (pairing q).components x (true,y.2) := by
    rcases x with ⟨b,i⟩
    cases b
    · exact (pairing q).components.trans'
        ((pairing q).edge_le_components (SameCycle.rfl (x := (false,i))).apply_right)
        ((pairing q).face_le_components (face_sameCycle_pos q (hq i y.2)))
    · exact (pairing q).face_le_components (face_sameCycle_pos q (hq i y.2))
  have h₂ : (pairing q).components (true,y.2) y := by
    rcases y with ⟨b,j⟩; cases b
    · exact (pairing q).edge_le_components (SameCycle.rfl (x := (true,j))).apply_right
    · exact (pairing q).components.refl' _
  exact (pairing q).components.trans' h₁ h₂

theorem genusZero [DecidableEq I] (hq : ∀ i j, q.SameCycle i j) (i₀ : I) : (pairing q).GenusZero := by
  have hf : cycles (pairing q).face = 2 := by
    change cycles (turn q) = 2
    have h := cycles_of_classifier (turn q) Prod.fst (face_classes q hq) (fun b => ⟨(b,i₀),rfl⟩)
    simpa using h
  have hv : cycles (pairing q).vertex = Fintype.card I :=
    cycles_of_classifier _ (vertexIndex q) (vertex_classes q) (fun i => ⟨(true,i),rfl⟩)
  have hc : Nat.card (Quotient (pairing q).components) = 1 := by
    have h := card_quotient_of_classifier (pairing q).components (fun _ => ())
      (fun x y => ⟨fun _ => rfl,fun _ => connected q hq x y⟩) (fun _ => ⟨(true,i₀),rfl⟩)
    simpa using h
  change (pairing q).euler = 2 * (Nat.card (Quotient (pairing q).components) : ℤ)
  rw [PictureMap.euler,hf,hv,hc,Fintype.card_prod,Fintype.card_bool]
  push_cast
  omega

end PolygonSphere
end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_PictureMirror
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutSide _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeOutsideContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypePartBoundary _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativePartBoundary
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
variable (M : PictureMap D)

omit [DecidableEq D] in
lemma mirror_components : M.mirror.components = M.components := by
  apply le_antisymm
  · apply M.mirror.components_le
    · intro x
      exact M.face_le_components ((SameCycle.rfl (f := M.face⁻¹) (x := x)).apply_right.of_inv)
    · intro x
      exact M.edge_le_components (SameCycle.rfl (f := M.edge) (x := x)).apply_right
  · apply M.components_le
    · intro x
      exact M.mirror.face_le_components ((SameCycle.rfl (f := M.face) (x := x)).apply_right.inv)
    · intro x
      exact M.mirror.edge_le_components (SameCycle.rfl (f := M.edge) (x := x)).apply_right

lemma mirror_genusZero (h : M.GenusZero) : M.mirror.GenusZero := by
  change M.mirror.euler = _
  rw [M.mirror_euler,M.mirror_components]
  exact h

end PictureMap
end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_WordPicture
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutSide _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeOutsideContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypePartBoundary _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativePartBoundary
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

attribute [instance] WordPicture.finite WordPicture.decEq

namespace WordPicture
variable {R : Set (Word A)} {w : Word A} (P : WordPicture R w)

def mirror : WordPicture R (FreeGroup.invRev w) where
  Dart := P.Dart
  pairing := P.pairing.mirror
  genusZero := P.pairing.mirror_genusZero P.genusZero
  label := invLetter ∘ P.label
  paired := fun x => by
    change invLetter (P.label (P.pairing.edge x)) = invLetter (invLetter (P.label x))
    rw [P.paired]
  outside := P.outside.reverse
  boundary := P.boundary.reverse
  word := by
    simp only [List.map_reverse,List.map_map,← P.word,FreeGroup.invRev]
    rfl
  interior := by
    intro x hx
    have hx' : x ∉ P.outside := by simpa using hx
    obtain ⟨xs,hs,hm,hr⟩ := P.interior x hx'
    refine ⟨xs.reverse,hs.reverse,by simpa using hm,?_⟩
    convert symmetricRelator_inv hr using 1
    all_goals try with_reducible_and_instances rfl
    simp only [List.map_reverse,List.map_map,FreeGroup.invRev]
    rfl

end WordPicture
end HyperbolicObstruction.WordPictures
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_WordPictureBase
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutSide _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeOutsideContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypePartBoundary _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativePartBoundary
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
variable {A : Type*} {R : Set (Word A)} {w : Word A}
namespace WordPicture

/-- The two sides of a genuine relator disk and its distinguished exterior.
Every side is separately indexed, even when its letter is repeated. -/
def polygon (hw : w ∈ R) (hne : w ≠ []) : WordPicture R w where
  Dart := Bool × Fin w.length
  pairing := PolygonSphere.pairing (finRotate w.length)
  genusZero := PolygonSphere.genusZero _
    (fun i j => (finRange_boundary _).sameCycle (List.mem_finRange i) (List.mem_finRange j))
    ⟨0,List.length_pos_iff.mpr hne⟩
  label := fun x => if x.1 then w[x.2.val] else invLetter w[x.2.val]
  paired := by
    rintro ⟨b,i⟩
    cases b <;> simp [PolygonSphere.pairing,PolygonSphere.flip,invLetter_invLetter]
  outside := (List.finRange w.length).map (fun i => (true,i))
  boundary := (finRange_boundary _).map (fun i => (true,i))
    (fun i j h => congrArg Prod.snd h) (fun _ => rfl)
  word := by
    simp only [List.map_map,Function.comp_def,ite_true]
    exact List.map_getElem_finRange w
  interior := by
    rintro ⟨b,i⟩ hx
    cases b with
    | true => exact False.elim (hx (List.mem_map.mpr ⟨i,List.mem_finRange i,rfl⟩))
    | false =>
      refine ⟨(List.finRange w.length).reverse.map (fun i => (false,i)),
        (finRange_boundary _).reverse.map (fun i => (false,i))
          (fun i j h => congrArg Prod.snd h) (fun _ => rfl),?_,?_⟩
      · exact List.mem_map.mpr ⟨i,by simp,rfl⟩
      · have he : List.map (fun x : Bool × Fin w.length => if x.1 then w[x.2.val] else invLetter w[x.2.val])
            ((List.finRange w.length).reverse.map (fun i => (false,i))) = FreeGroup.invRev w := by
          simp only [List.map_map,Function.comp_def,Bool.false_eq_true,ite_false,List.map_reverse]
          change ((List.finRange w.length).map (invLetter ∘ fun i => w[i.val])).reverse = _
          rw [← List.map_map,List.map_getElem_finRange]
          rfl
        rw [he]
        exact Or.inr (by simpa using hw)

lemma of_relator (hw : w ∈ R) : Nonempty (WordPicture R w) := by
  by_cases h : w = []
  · subst w; exact ⟨empty R⟩
  · exact ⟨polygon hw h⟩

/-- A freely canceling pair is the boundary of a single thickened edge,
with no interior cell. -/
def freePair (R : Set (Word A)) (a : A × Bool) : WordPicture R [a,invLetter a] where
  Dart := Bool
  pairing := {
    face := swap false true
    edge := swap false true
    edge_sq := swap_mul_self _ _
    edge_ne := by intro b; cases b <;> decide }
  genusZero := by
    let M : PictureMap Bool := {
      face := swap false true
      edge := swap false true
      edge_sq := swap_mul_self _ _
      edge_ne := by intro b; cases b <;> decide }
    change M.GenusZero
    have hc : ∀ x y, M.components x y := by
      intro x y
      cases x <;> cases y
      · exact M.components.refl' _
      · exact M.edge_le_components (SameCycle.rfl (f := M.edge) (x := false)).apply_right
      · exact M.edge_le_components (SameCycle.rfl (f := M.edge) (x := true)).apply_right
      · exact M.components.refl' _
    let : Subsingleton (Quotient M.components) := ⟨by
      intro x y
      induction x,y using Quotient.inductionOn₂ with
      | h x y => exact Quotient.sound (hc x y)⟩
    have hd : Nat.card (Quotient M.components) = 1 := Nat.card_unique
    change M.euler = 2 * (Nat.card (Quotient M.components) : ℤ)
    rw [hd]
    norm_num [M,PictureMap.euler,PictureMap.vertex,cycles,defect]
    rw [isSwap_iff_cycleType.mp (show (swap false true).IsSwap from ⟨false,true,by decide,rfl⟩)]
    norm_num
  label := fun b => if b then invLetter a else a
  paired := by
    intro b
    cases b <;> simp [invLetter_invLetter]
  outside := [false,true]
  boundary := ⟨by simp,fun _ _ => rfl⟩
  word := rfl
  interior := by intro b hb; cases b <;> exact False.elim (hb (by simp))

end WordPicture
end HyperbolicObstruction.WordPictures
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_Occurrence
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeOutgoing _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
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
namespace Occurrences

def probability (α β δ : ℝ) (A : Type*) [Fintype A] : Entry A → ℝ
  | .inl e => actualProbability α β δ A e.1
  | .inr _ => SixTable.probability (A := A) δ

lemma probability_mem {α β δ : ℝ} {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
    (ha : 0 ≤ α) (hb : 7*α ≤ β) (hd : 0 ≤ δ) (e : Entry A) :
    probability α β δ A e ∈ Set.Icc (0:ℝ) 1 := by
  cases e with
  | inl e => exact actualProbability_mem ha hb hd e.1
  | inr _ => exact SixTable.probability_mem hd


end Occurrences
end IncidenceTemplate
end HyperbolicObstruction
end
end
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_Shape
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeOutgoing _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open Filter Topology
namespace HyperbolicObstruction
namespace IncidenceTemplate
namespace Occurrences

namespace Shape
variable {s u q v : ℕ} (T : Shape s u q)

lemma square_card (τ : TwoPath) : (squareSupport τ).card = 4 := by
  simp [squareSupport,twoPath_ne τ]

lemma cardinal_positions : Fintype.card (T.Pos v) = s + (∑ b, (fan (T.1 b)).card) + 4*q + 6*v := by
  rw [← Nat.card_eq_fintype_card]
  simp only [Pos, Nat.card_sum, Nat.card_sigma, Nat.card_prod, Nat.card_fin]
  simp only [Nat.card_eq_fintype_card, Fintype.card_coe, rowSupport, Finset.card_map,
    square_card, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  omega

end Shape
end Occurrences
end IncidenceTemplate
end HyperbolicObstruction
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_RankCollection
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
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
namespace IncidenceTemplate.Occurrences

instance shapeFintype (s u q : ℕ) : Fintype (Shape s u q) := by
  classical
  unfold Shape
  letI (t : Fin u → Fin 7) : Fintype ((Fin s → (i : Fin 7) → {b : Fin u // t b = i}) ×
      (Fin q → TwoPath)) := inferInstance
  infer_instance

end IncidenceTemplate.Occurrences
end HyperbolicObstruction
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_WalkCover
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.PictureSwitch.WalkPicture.instFintypeFace _root_.OAI.HyperbolicObstruction.PictureSwitch.WalkPicture.instFintypeVertex _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutSide _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeOutsideContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypePartBoundary _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativePartBoundary
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
universe u v w z k t r q p
variable {S : Type v} {C : Type w} {W : Type z} {L : Type k} {V : Type t}
  {A : Type r} [AddCommMonoid A]

namespace WalkCellCover
variable {T : WalkCellTarget S C W L V A} {G : Type q} [Group G]
  (H : WalkCellCover T G) {B : Type p} [AddCommMonoid B]

variable (weight : G → S → B)
  (hw : ∀ g s, T.free (T.kind s) = true → weight g s + weight g (T.opposite s) = 0)

variable (P : WalkPicture.{u} (H.target weight hw))

lemma forget_simple (hs : P.Simple) : (H.forget weight hw P).Simple := by
  intro a b ha hab he
  apply hs a b ha hab
  apply Prod.ext
  · change (P.index a).1 * H.offset (T.opposite (P.index a).2) =
      (P.index b).1 * H.offset (T.opposite (P.index b).2)
    rw [H.deck_face weight hw P hab]
    congr 1
    exact H.free_back _ _ ha (PictureMap.kind_cycle (H.forget weight hw P).kind hab) he
  · exact he

end WalkCellCover
end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_RankSelection
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeOutgoing _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open Filter Topology
namespace HyperbolicObstruction
namespace IncidenceTemplate
namespace Occurrences

lemma expect_join {n : ℕ} {α β δ : ℝ} (ha : 0 ≤ α) (hb : 7*α ≤ β) (hd : 0 ≤ δ)
    (f : (Entry (SymmetricAlphabet n) → Bool) → ℝ) :
    (FiniteLaw.bernoulliProduct (probability α β δ (SymmetricAlphabet n))
      (probability_mem ha hb hd)).expect f =
    ((TableModel.law rowSupport (actualProbability α β δ (SymmetricAlphabet n))
      (actualProbability_mem ha hb hd)).prod (SixTable.law (A := SymmetricAlphabet n) δ hd)).expect
        (fun z => f (Sum.elim z.1 z.2)) := by
  convert FiniteLaw.bernoulliProduct_sum_expect
    (fun e : TableModel.Entry (A := SymmetricAlphabet n) rowSupport => actualProbability α β δ (SymmetricAlphabet n) e.1)
    (fun _ : Fin 6 → SymmetricAlphabet n => SixTable.probability (A := SymmetricAlphabet n) δ)
    (fun e => actualProbability_mem ha hb hd e.1) (fun _ => SixTable.probability_mem hd) f using 1
  · congr 2
    funext e
    cases e <;> rfl
  · rfl

end Occurrences
end IncidenceTemplate
end HyperbolicObstruction
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_SamplingStage
attribute [-instance] _root_.OAI.HyperbolicObstruction.Coincidence.instDecidablePredForallBoolRankBad _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeOutgoing _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
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

namespace SamplingStage
variable {δ : ℕ → ℝ} (s : ∀ m, SamplingStage m (δ m))
abbrev Alphabet (m : ℕ) := SymmetricAlphabet (s m).size
abbrev Matches (m : ℕ) := StarModel.Matches rowSupport (s m).master
instance instNonemptyMatches (m : ℕ) : Nonempty ((Matches s) m) := (s m).nonempty

def label (m : ℕ) (a : (Matches s) m) : Field → (Alphabet s) m := a.val

end SamplingStage

end IncidenceTemplate
end HyperbolicObstruction
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_SelectedPresentation
attribute [-instance] _root_.OAI.HyperbolicObstruction.Coincidence.instDecidablePredForallBoolRankBad _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
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
namespace IncidenceTemplate
namespace SamplingStage
variable {δ : ℕ → ℝ} (s : ∀ m, SamplingStage m (δ m))

abbrev LetterGroup (m : ℕ) := LetterPresentation.Group (s m).size (s m).master (s m).six

def inverse (m : ℕ) : (Alphabet s) m ≃ (Alphabet s) m :=
  LetterPresentation.inverseLetter (s m).size

abbrev Rows (m : ℕ) (u : (Alphabet s) m) := SixTable.Rows (s m).six u
instance instNonemptyRows (m : ℕ) (u : (Alphabet s) m) : Nonempty (Rows s m u) :=
  SixTable.rows_nonempty ((stageError_le_third m).trans_lt (by norm_num)) (s m).six_good u

def rowLaw (m : ℕ) (u : (Alphabet s) m) : FiniteLaw (Rows s m u) := FiniteLaw.uniform

def row (m : ℕ) (u : (Alphabet s) m) (x : Rows s m u) : Fin 5 → (Alphabet s) m :=
  SixTable.row (s m).six u x

end SamplingStage
end IncidenceTemplate
end HyperbolicObstruction
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_IndexedWordPicture
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutSide _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeOutsideContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypePartBoundary _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativePartBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Persistent cell identities on word pictures. Unlike a bare relator witness,
this marking remembers which actual cell each interior face uses. -/
noncomputable section

namespace HyperbolicObstruction.WordPictures.WordPicture
open HyperbolicObstruction.PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {C E V : Type*}
  {R : Set (Word E)} {w : Word E}
  (B : PolygonTarget.Boundary C (E × Bool) V) (P : WordPicture R w)

namespace Indexing
variable {B P} (I : Indexing B P)

def mirror (hrev : B.rev = invLetter) : Indexing B P.mirror where
  index x := (I.index x).map B.opposite
  outside x := by
    change P.Dart at x
    change (I.index x).map B.opposite = none ↔ x ∈ P.outside.reverse
    rw [Option.map_eq_none_iff,I.outside,List.mem_reverse]
  commute x := by
    change P.Dart at x
    change (I.index (P.pairing.face⁻¹ x)).map B.opposite = _
    rw [I.commute_inv,Option.map_map,Option.map_map]
    congr 1
    funext s
    exact reverse_prev s
  injective hxy s hx hy := by
    obtain ⟨a,ha,has⟩ := Option.map_eq_some_iff.mp hx
    obtain ⟨b,hb,hbs⟩ := Option.map_eq_some_iff.mp hy
    have he : a = b := B.opposite.injective (has.trans hbs.symm)
    exact I.injective (sameCycle_inv.mp hxy) a ha (he ▸ hb)
  label x s hx := by
    obtain ⟨a,ha,rfl⟩ := Option.map_eq_some_iff.mp hx
    change invLetter (P.label x) = _
    rw [I.label x a ha,B.edge_opposite,hrev]

end Indexing
end HyperbolicObstruction.WordPictures.WordPicture
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_IndexedPictureFold
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutSide _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeOutsideContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypePartBoundary _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativePartBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HyperbolicObstruction.WordPictures.WordPicture
open HyperbolicObstruction.PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {C E V : Type*} {R : Set (Word E)} {w : Word E}
  {B : PolygonTarget.Boundary C (E × Bool) V} {P : WordPicture R w}
namespace Indexing
variable (I : Indexing B P) {l r : List P.Dart} {a b : P.Dart}
  (he : P.outside = l++a::b::r) (hc : P.label a = invLetter (P.label b))

lemma fold_outside (x : (P.foldAt he hc).Dart) :
    x.val ∈ P.outside ↔ x ∈ (P.foldAt he hc).outside := by
  change {x : P.Dart // OffPair a b x} at x
  change x.val ∈ P.outside ↔ x ∈ (l++r).attachWith (OffPair a b) _
  rw [List.mem_attachWith,he]
  simp only [List.mem_append,List.mem_cons,x.property.1,x.property.2,false_or]

def foldAt : Indexing B (P.foldAt he hc) where
  index x := I.index x.val
  outside x := (I.outside x.val).trans (fold_outside he hc x)
  commute x := by
    by_cases hxo : x.val ∈ P.outside
    · have hxo' := (fold_outside he hc x).mp hxo
      have hfo := (P.foldAt he hc).boundary.invariant hxo'
      have hh := (fold_outside he hc _).mpr hfo
      rw [(I.outside _).mpr hh,(I.outside _).mpr hxo]
      rfl
    · have hb : IsBoundary P.pairing.face (l++a::b::r) := he ▸ P.boundary
      have hab : a ≠ b := by
        have hn := (List.nodup_append.mp hb.nodup).2.1
        exact fun h => (List.nodup_cons.mp hn).1 (by simp [h])
      have hh := P.pairing.boundaryFold_other_face hab hb.middle_next x (by
        intro hh
        exact hxo (P.boundary.mem_of_sameCycle (by rw [he]; simp) hh))
      change I.index ((P.pairing.boundaryFold hab hb.middle_next).face x).val = _
      rw [hh]
      exact I.commute x.val
  injective hxy s hx hy := by
    have hb : IsBoundary P.pairing.face (l++a::b::r) := he ▸ P.boundary
    have hab : a ≠ b := by
      have hn := (List.nodup_append.mp hb.nodup).2.1
      exact fun h => (List.nodup_cons.mp hn).1 (by simp [h])
    apply Subtype.ext
    apply I.injective _ s hx hy
    exact (P.pairing.boundaryFold_face_orbits hab hb.middle_next _ _).mp hxy
  label x s hx := I.label x.val s hx

end Indexing
end HyperbolicObstruction.WordPictures.WordPicture
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_IndexedPictureBasic
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutSide _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeOutsideContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypePartBoundary _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativePartBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact cell disks, free spurs and cyclic basepoint changes with persistent
cell-side identities. -/
noncomputable section

namespace HyperbolicObstruction.WordPictures.WordPicture
open HyperbolicObstruction.PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {C E V A : Type*} [AddCommGroup A]
  {R : Set (Word E)} {w : Word E} {B : PolygonTarget.Boundary C (E × Bool) V}

namespace Indexing

def empty (B : PolygonTarget.Boundary C (E × Bool) V) (R : Set (Word E)) :
    Indexing B (WordPicture.empty R) where
  index := PEmpty.elim
  outside := fun x => PEmpty.elim x
  commute := fun x => PEmpty.elim x
  injective := fun {x} => PEmpty.elim x
  label := fun x => PEmpty.elim x

def freePair (B : PolygonTarget.Boundary C (E × Bool) V) (R : Set (Word E)) (a : E × Bool) :
    Indexing B (WordPicture.freePair R a) where
  index _ := none
  outside x := by
    change Bool at x
    change (none : Option B.Side) = none ↔ x ∈ ([false,true] : List Bool)
    refine iff_of_true rfl ?_
    cases x with
    | false => exact List.mem_cons_self
    | true => exact List.mem_cons_of_mem _ List.mem_cons_self
  commute _ := rfl
  injective := by intros; contradiction
  label := by intros; contradiction

def rotate {P : WordPicture R w} (I : Indexing B P) (k : ℕ) : Indexing B (P.rotate k) where
  index := I.index
  outside x := by
    change P.Dart at x
    exact (I.outside x).trans List.mem_rotate.symm
  commute := I.commute
  injective := I.injective
  label := I.label

end Indexing

variable (B) (hrev : B.rev = invLetter) (c : C)
/-- The literal indicated cell, not a reselected word-equivalent relator. -/
def cellDisk : WordPicture (Set.range B.attachingWord) (B.attachingWord c) where
  Dart := Bool × Fin (B.size c)
  pairing := PolygonSphere.pairing (finRotate (B.size c))
  genusZero := PolygonSphere.genusZero _
    (fun i j => (finRange_boundary _).sameCycle (List.mem_finRange i) (List.mem_finRange j))
    ⟨0,B.positive c⟩
  label x := if x.1 then B.label c x.2 else invLetter (B.label c x.2)
  paired := by
    rintro ⟨b,i⟩
    cases b <;> simp [PolygonSphere.pairing,PolygonSphere.flip,invLetter_invLetter]
  outside := (List.finRange (B.size c)).map (fun i => (true,i))
  boundary := (finRange_boundary _).map (fun i => (true,i))
    (fun i j h => congrArg Prod.snd h) (fun _ => rfl)
  word := by
    simp only [List.map_map,Function.comp_def,ite_true]
    exact List.ofFn_eq_map.symm
  interior := by
    rintro ⟨b,i⟩ hx
    cases b with
    | true => exact False.elim (hx (List.mem_map.mpr ⟨i,List.mem_finRange i,rfl⟩))
    | false =>
      refine ⟨(List.finRange (B.size c)).reverse.map (fun i => (false,i)),
        (finRange_boundary _).reverse.map (fun i => (false,i))
          (fun i j h => congrArg Prod.snd h) (fun _ => rfl),?_,?_⟩
      · exact List.mem_map.mpr ⟨i,by simp,rfl⟩
      · right
        refine ⟨c,?_⟩
        simp only [List.map_map,Function.comp_def,Bool.false_eq_true,ite_false,List.map_reverse]
        symm
        change FreeGroup.invRev (((List.finRange (B.size c)).map (invLetter ∘ B.label c)).reverse) = _
        rw [←List.map_map,←List.ofFn_eq_map]
        change FreeGroup.invRev (FreeGroup.invRev (B.attachingWord c)) = _
        exact FreeGroup.invRev_invRev

def cellDiskIndex : Indexing B (cellDisk B c) where
  index x := if x.1 then none else some ⟨c,false,x.2⟩
  outside x := by
    change Bool × Fin (B.size c) at x
    rcases x with ⟨b,i⟩
    have ht : (true,i) ∈ (List.finRange (B.size c)).map (fun j => (true,j)) :=
      List.mem_map.mpr ⟨i,List.mem_finRange i,rfl⟩
    have hf : (false,i) ∉ (List.finRange (B.size c)).map (fun j => (true,j)) := by
      rintro h
      obtain ⟨j,_,he⟩ := List.mem_map.mp h
      have he := congrArg Prod.fst he
      cases he
    cases b with
    | false => exact iff_of_false (Option.some_ne_none _) hf
    | true => exact iff_of_true rfl ht
  commute x := by
    rcases x with ⟨b,i⟩
    cases b <;> rfl
  injective := by
    rintro ⟨b,i⟩ ⟨b',j⟩ hxy s hi hj
    cases b <;> cases b' <;> simp only [Bool.false_eq_true,ite_false,ite_true,Option.some.injEq,
      reduceCtorEq] at hi hj
    subst s
    have hij : i = j := by simpa using hj.symm
    exact congrArg (fun k => (false,k)) hij
  label x s hx := by
    rcases x with ⟨b,i⟩
    cases b with
    | true => contradiction
    | false =>
      simp only [Bool.false_eq_true,ite_false,Option.some.injEq] at hx
      subst s
      change invLetter (B.label c i) = B.rev (B.label c i)
      rw [hrev]

end HyperbolicObstruction.WordPictures.WordPicture
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_IndexedPictureClosed
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutSide _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeOutsideContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypePartBoundary _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativePartBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HyperbolicObstruction.WordPictures.WordPicture
open HyperbolicObstruction.PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {C E V : Type*} {R : Set (Word E)}
  {B : PolygonTarget.Boundary C (E × Bool) V} {P : WordPicture R []}
namespace Indexing
variable (I : Indexing B P)

variable {A : Type*} [AddCommGroup A]
  (hrev : B.rev = invLetter) (weight : C → A)

def closedPicture : CellPicture (B.target weight (fun _ => false) (by intro _ impossible; cases impossible)) where
  Dart := P.Dart
  pairing := P.pairing
  genusZero := P.genusZero
  index := I.closedIndex
  mapped := I.closed_mapped
  respects := (B.target weight (fun _ => false) (by intro _ impossible; cases impossible)).respects_of_edge
    P.pairing I.closedIndex I.closed_mapped (by
      intro x
      change B.sideLabel (I.closedIndex (P.pairing.edge x)) = B.rev (B.sideLabel (I.closedIndex x))
      rw [← I.label _ _ (I.closedIndex_spec _),← I.label _ _ (I.closedIndex_spec _),hrev]
      exact P.paired x)

end Indexing
end HyperbolicObstruction.WordPictures.WordPicture
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_IndexedPictureExistence
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeCutSide _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeOutsideContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypePartBoundary _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativeCutContact _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeRelativePartBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal nullword disks with chosen persistent cell identities. -/
noncomputable section

namespace HyperbolicObstruction.WordPictures.WordPicture
open HyperbolicObstruction.PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {C E V : Type*} {R : Set (Word E)} {w : Word E}

lemma outsideInvariant (P : WordPicture R w) (x : P.Dart) :
    P.pairing.face x ∈ P.outside ↔ x ∈ P.outside :=
  ⟨fun h => P.boundary.mem_of_sameCycle h SameCycle.rfl.apply_left,
    fun h => P.boundary.mem_of_sameCycle h SameCycle.rfl.apply_right⟩

def insideFace (P : WordPicture R w) : Perm P.InsideDart :=
  P.pairing.face.subtypePerm (fun x => not_congr (P.outsideInvariant x))

variable {B : PolygonTarget.Boundary C (E × Bool) V} (P : WordPicture R w)

/-- Convert a coherent map on the genuine interior faces into a persistent
optional index on the entire diagram. -/
def Indexing.ofInterior (j : P.InsideDart → B.Side)
    (hj : IndexedFaceMap P.insideFace B.next j)
    (hl : ∀ x, P.label x.val = B.sideLabel (j x)) : Indexing B P where
  index x := if hx : x ∈ P.outside then none else some (j ⟨x,hx⟩)
  outside x := by by_cases hx : x ∈ P.outside <;> simp [hx]
  commute x := by
    by_cases hx : x ∈ P.outside
    · simp [hx,(P.outsideInvariant x).mpr hx]
    · have hf : P.pairing.face x ∉ P.outside := fun h => hx ((P.outsideInvariant x).mp h)
      simp only [dite_eq_right hx,dite_eq_right hf,Option.map_some]
      exact congrArg some (hj.commute ⟨x,hx⟩)
  injective := by
    intro x y hxy s hx hy
    by_cases hxo : x ∈ P.outside
    · simp [hxo] at hx
    by_cases hyo : y ∈ P.outside
    · simp [hyo] at hy
    simp only [dite_eq_right hxo,dite_eq_right hyo,Option.some.injEq] at hx hy
    exact congrArg Subtype.val (hj.injective (sameCycle_subtypePerm.mpr hxy) (hx.trans hy.symm))
  label x s hx := by
    by_cases hxo : x ∈ P.outside
    · simp [hxo] at hx
    simp only [dite_eq_right hxo,Option.some.injEq] at hx
    exact (hl ⟨x,hxo⟩).trans (congrArg B.sideLabel hx)

end HyperbolicObstruction.WordPictures.WordPicture
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_PolygonCornerPrimitive
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section


/-! Explicit cyclic antiderivatives for the literal threefold-subdivided
polygon corners. This retains the actual constructor `Position`. -/
noncomputable section
namespace HyperbolicObstruction.FinitePolygonModel.Data
open CyclicTriangleBoundary
variable {V E C B : Type*} [AddCommGroup B]
  (P : Data V E C)

lemma cornerPrimitive_difference (f : P.Position → B)
    (hf : ∀ c, ∑ i : Fin (P.size c), ∑ j : Fin 3, f ⟨c,(i,j)⟩ = 0)
    (q : P.Position) : P.cornerPrimitive f q - P.cornerPrimitive f (P.next q) = f q := by
  have h0 : Finset.Iio (0 : Fin 3) = ∅ := by decide
  have h1 : Finset.Iio (1 : Fin 3) = {0} := by decide
  have h2 : Finset.Iio (2 : Fin 3) = {0,1} := by decide
  rcases q with ⟨c,i,j⟩
  fin_cases j
  · simp [cornerPrimitive,next,Fin.sum_univ_succ,h0,h1]
  · simp [cornerPrimitive,next,Fin.sum_univ_succ,h1,h2]
  · have hh := cyclePrimitive_difference (fun i => ∑ j : Fin 3, f ⟨c,(i,j)⟩) (hf c) i
    simp only [cornerPrimitive]
    change (cyclePrimitive _ i - ∑ j ∈ Finset.Iio (2 : Fin 3), f ⟨c,(i,j)⟩) -
      (cyclePrimitive _ (finRotate (P.size c) i) - ∑ j ∈ Finset.Iio (0 : Fin 3), f ⟨c,(finRotate (P.size c) i,j)⟩) = f ⟨c,(i,2)⟩
    rw [h2,h0,Finset.sum_empty,sub_zero,Finset.sum_pair (by decide : (0 : Fin 3) ≠ 1)]
    calc _ = (cyclePrimitive (fun i => ∑ j : Fin 3, f ⟨c,(i,j)⟩) i -
        cyclePrimitive (fun i => ∑ j : Fin 3, f ⟨c,(i,j)⟩) (finRotate (P.size c) i)) -
        (f ⟨c,(i,0)⟩ + f ⟨c,(i,1)⟩) := by abel
      _ = _ := by
        rw [hh]
        simp only [Fin.sum_univ_three]
        abel

end HyperbolicObstruction.FinitePolygonModel.Data
end
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_PolygonTriangleCochains
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cochain extension with literal initial-sheet coordinates for every collar
triangle. Its only algebraic input is the precise polygon boundary equation. -/
noncomputable section

namespace HyperbolicObstruction.FinitePolygonModel.Data
variable {V E C G B : Type*}
  [DecidableEq V] [DecidableEq E] [DecidableEq C] [Group G] [AddCommGroup B]
  (P : Data V E C) (v : E → G) (w : G × E → B)

variable (T : G → P.Position → Fin 3 → B)

variable (hc : ∀ c, (List.ofFn (fun i => signed v (P.side c i))).prod = 1)
variable (hw : ∀ d c, (∑ i : Fin (P.size c),
    signedCochain v w (d*((List.ofFn (fun i => signed v (P.side c i))).take i.val).prod) (P.side c i)) =
    ∑ i : Fin (P.size c), ∑ j : Fin 3,
      P.triangleWeight T (d*P.cornerOffset v ⟨c,(i,j)⟩) ⟨c,(i,j)⟩)

omit [DecidableEq V] [DecidableEq E] [DecidableEq C] in
include hc hw in
lemma correctionApex_difference (g : G) (q : P.Position) :
    P.correctionApex v w T (g*(P.cornerOffset v q)⁻¹) q -
      P.correctionApex v w T ((g*P.segment v q)*(P.cornerOffset v (P.next q))⁻¹) (P.next q) =
      P.triangleWeight T g q - P.segmentCochain v w g q := by
  have he : (g*P.segment v q)*(P.cornerOffset v (P.next q))⁻¹ = g*(P.cornerOffset v q)⁻¹ := by
    rw [P.cornerOffset_next v hc]
    group
  rw [he,correctionApex,correctionApex,P.cornerPrimitive_difference _
    (P.correctionIncrement_sum v w T hw (g*(P.cornerOffset v q)⁻¹))]
  simp [correctionIncrement,mul_assoc]

include hc hw in
/-- Values on the three LITERAL oriented triangle boundaries. The second
collar orientation uses a plus rather than silently sharing the polygon sign. -/
theorem triangleCochain_coboundary (g : G) (q : P.Position) :
    (P.triangleCochain v w T g (P.outer q) (P.base q) +
      P.triangleCochain v w T (g*P.value v (P.outer q) (P.base q)) (P.base q) (P.base (P.next q)) -
      P.triangleCochain v w T g (P.outer q) (P.base (P.next q)) = T g q 0) ∧
    (P.triangleCochain v w T g (P.outer q) (P.outer (P.next q)) +
      P.triangleCochain v w T (g*P.value v (P.outer q) (P.outer (P.next q))) (P.outer (P.next q)) (P.base (P.next q)) -
      P.triangleCochain v w T g (P.outer q) (P.base (P.next q)) = T g q 1) ∧
    (P.triangleCochain v w T g (P.outer q) (P.outer (P.next q)) +
      P.triangleCochain v w T (g*P.value v (P.outer q) (P.outer (P.next q))) (P.outer (P.next q)) (P.apex q.1) -
      P.triangleCochain v w T g (P.outer q) (P.apex q.1) = T g q 2) := by
  simp only [triangleCochain,P.cochain_outer_base,P.cochain_base_next,P.cochain_outer_nextbase,
    P.cochain_outer_next,P.value_outer_base,P.value_outer_next,mul_one,zero_add,add_zero]
  constructor
  · unfold correctionDiagonal; abel
  constructor
  · unfold correctionOuter; abel
  · have hn : (P.next q).1 = q.1 := rfl
    rw [←hn,P.cochain_outer_apex,hn,P.cochain_outer_apex]
    have hh := P.correctionApex_difference v w T hc hw g q
    rw [←sub_eq_add_neg,sub_neg_eq_add]
    calc _ = P.correctionOuter v w T g q +
        (P.correctionApex v w T (g*(P.cornerOffset v q)⁻¹) q -
          P.correctionApex v w T ((g*P.segment v q)*(P.cornerOffset v (P.next q))⁻¹) (P.next q)) := by abel
      _ = T g q 2 := by rw [hh]; unfold correctionOuter correctionDiagonal triangleWeight; abel

end HyperbolicObstruction.FinitePolygonModel.Data
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_SimplexCoordinates
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section


/-! Explicit finite simplex coordinates, with the actual barycentric subspace
topology. No CW coordinate comparison is assumed. -/
noncomputable section
open scoped Topology
namespace HyperbolicObstruction.FinitePolyhedron
variable {V : Type*} [DecidableEq V] {n : ℕ}

variable [Fintype V]

lemma barycentric_read {e : Fin n → V} (he : Function.Injective e)
    (x : simplex (Finset.univ.image e)) :
    barycentric e (fun i => x.val (e i)) = x.val := by
  funext j
  by_cases hj : j ∈ Finset.univ.image e
  · obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hj
    exact barycentric_at he _ i
  · rw [barycentric_off _ hj,x.property.2.2 j hj]

/-- Canonical homeomorphism to a closed simplex with distinct vertices `e`. -/
def simplexCoordinates {e : Fin n → V} (he : Function.Injective e) :
    {weights : Fin n → ℝ // (∀ index, 0 ≤ weights index) ∧ ∑ index, weights index = 1} ≃ₜ
      simplex (Finset.univ.image e) where
  toFun z := ⟨barycentric e z,barycentric_mem e z⟩
  invFun x := ⟨fun i => x.val (e i),fun i => x.property.1 (e i),by
    rw [←barycentric_sum e (fun i => x.val (e i)),barycentric_read he x]
    exact x.property.2.1⟩
  left_inv z := by apply Subtype.ext; funext i; exact barycentric_at he z i
  right_inv x := Subtype.ext (barycentric_read he x)
  continuous_toFun := ((barycentric_continuous e).comp continuous_subtype_val).subtype_mk _
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact continuous_pi fun i => (continuous_apply (e i)).comp continuous_subtype_val

end HyperbolicObstruction.FinitePolyhedron
end
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_VoltageClosedCells
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Closed simplices in the actual voltage cover. The extended chart formula is
continuous even when its anchor coordinate is zero, by the triangle cocycle. -/
noncomputable section

open scoped Topology
open Set
namespace HyperbolicObstruction.FinitePolyhedron.Voltage
variable {V : Type*} [Fintype V] [DecidableEq V]
  {K : AbstractSimplicialComplex V} {G : Type*} [Group G]
  [TopologicalSpace G] [DiscreteTopology G] (v : Voltage K G)

instance closedFace_compact (s : Finset V) : CompactSpace (closedFace (K := K) s) :=
  isCompact_iff_compactSpace.mp (closedFace_isClosed s).isCompact

lemma faceLift_closedEmbedding {s : Finset V} (hs : s ∈ K.faces) {a : V}
    (ha : a ∈ s) (g : G) : Topology.IsClosedEmbedding (v.faceLift hs ha g) :=
  (v.faceLift hs ha g).continuous.isClosedEmbedding (v.faceLift_injective hs ha g)

lemma liftedClosedFace_closed (q : FaceAnchor (K := K) × G) :
    IsClosed (v.liftedClosedFace q) :=
  (v.faceLift_closedEmbedding q.1.property.1 q.1.property.2 q.2).isClosed_range

end HyperbolicObstruction.FinitePolyhedron.Voltage
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_TriangleCoordinates
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual simplex coordinates and exact boundary decomposition. -/
noncomputable section

open scoped Topology unitInterval
namespace HyperbolicObstruction.FinitePolyhedron.Voltage
open TriangleSquare
variable {V : Type*} [Fintype V] [DecidableEq V] {K : AbstractSimplicialComplex V}

def triangleCoordinates {a b c : V} (h : {a,b,c} ∈ K.faces)
    (he : Function.Injective ![a,b,c]) : Triangle ≃ₜ closedFace (K := K) {a,b,c} :=
  (simplexCoordinates he).trans
    ((Homeomorph.setCongr (congrArg simplex (triangle_image a b c))).trans
      (closedSimplexHomeomorph K h))

lemma triangleCoordinates_apply {a b c : V} (h : {a,b,c} ∈ K.faces)
    (he : Function.Injective ![a,b,c]) (z : Triangle) :
    triangleCoordinates h he z = trianglePoint h z := by
  apply Subtype.ext
  apply Subtype.ext
  rfl

lemma trianglePoint_coordinate {a b c : V} (h : {a,b,c} ∈ K.faces)
    (he : Function.Injective ![a,b,c]) (z : Triangle) (i : Fin 3) :
    (trianglePoint h z).val.val (![a,b,c] i) = z.val i :=
  barycentric_at he z i

end HyperbolicObstruction.FinitePolyhedron.Voltage

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_PolygonTriangles
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal ordered collar triangles and exhaustivity of their two-dimensional
faces. No uniqueness of polygon vertices is presumed. -/
noncomputable section

namespace HyperbolicObstruction.FinitePolygonModel.Data
open FinitePolyhedron FinitePolyhedron.Voltage
variable {V E C : Type*}
  [DecidableEq V] [DecidableEq E] [DecidableEq C] (P : Data V E C)

lemma three_face_collar {s : Finset P.Vertex} (hs : s ∈ P.complex.faces) (hc : s.card = 3) :
    ∃ q j, s = P.collarFace q j := by
  rcases hs.2 with hh|⟨f,hf⟩
  · omega
  · cases f with
    | inl e =>
      have hh := Finset.card_le_card hf
      have he : (P.facet (.inl e)).card ≤ 2 := by
        dsimp [facet,graphFace]; split_ifs <;> exact Finset.card_le_two
      omega
    | inr q =>
      refine ⟨q.1,q.2,Finset.eq_of_subset_of_card_le hf ?_⟩
      exact (P.simplex_card_le_three (P.facet_face (.inr q))).trans (by omega)

end HyperbolicObstruction.FinitePolygonModel.Data
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_TriangleEdgeIntersection
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A nondegenerate triangular simplex meets every edge in its boundary. -/
noncomputable section

open scoped Topology unitInterval
namespace HyperbolicObstruction.FinitePolyhedron.Voltage
open TriangleSquare
variable {V : Type*} [Fintype V] [DecidableEq V] {K : AbstractSimplicialComplex V}

lemma triangle_boundary_of_edge {a b c d e : V} (h : {a,b,c} ∈ K.faces)
    (hi : Function.Injective ![a,b,c]) (h' : {d,e} ∈ K.faces)
    (z : Triangle) (r : I) (he : (trianglePoint h z).val = edgePath K h' r) :
    (∃ s, z = quotient (s,0)) ∨ (∃ s, z = quotient (0,s)) ∨ (∃ s, z = quotient (1,s)) := by
  have hab : a ≠ b := by intro hh; have := hi (a₁:=0) (a₂:=1) hh; exact (by decide : (0:Fin 3) ≠ 1) this
  have hac : a ≠ c := by intro hh; have := hi (a₁:=0) (a₂:=2) hh; exact (by decide : (0:Fin 3) ≠ 2) this
  have hbc : b ≠ c := by intro hh; have := hi (a₁:=1) (a₂:=2) hh; exact (by decide : (1:Fin 3) ≠ 2) this
  have hn : ¬ ({a,b,c} : Finset V) ⊆ {d,e} := by
    intro hs
    have hc := Finset.card_le_card hs
    have hc' := Finset.card_le_two (a:=d) (b:=e)
    have h3 : ({a,b,c} : Finset V).card = 3 := by simp [hab,hac,hbc]
    omega
  obtain ⟨j,hj,hjn⟩ := Finset.not_subset.mp hn
  have hz (i : Fin 3) (hij : ![a,b,c] i = j) : z.val i = 0 := by
    rw [←trianglePoint_coordinate h hi z i,hij]
    have hh := congrArg (fun x : Carrier K => x.val j) he
    rw [edgePath_coordinate] at hh
    have hd : j ≠ d := fun h => hjn (by simp [h])
    have he : j ≠ e := fun h => hjn (by simp [h])
    simpa [hd,he] using hh
  simp only [Finset.mem_insert,Finset.mem_singleton] at hj
  rcases hj with rfl|rfl|rfl
  · exact Or.inr (Or.inr ⟨_,eq_right_of_zero z (hz 0 rfl)⟩)
  · exact Or.inr (Or.inl ⟨_,eq_left_of_zero z (hz 1 rfl)⟩)
  · exact Or.inl ⟨_,eq_bottom_of_zero z (hz 2 rfl)⟩

end HyperbolicObstruction.FinitePolyhedron.Voltage
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_VoltageCellGluing
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Genuine homotopy gluing on the locally finite family of closed lifted
simplices, with no alteration of the voltage-cover topology. -/
noncomputable section

open scoped Topology unitInterval
namespace HyperbolicObstruction.FinitePolyhedron.Voltage
variable {V : Type*} [Fintype V] [DecidableEq V]
  {K : AbstractSimplicialComplex V} {G : Type*} [Group G]
  [TopologicalSpace G] [DiscreteTopology G] (v : Voltage K G)
  {X : Type*} [TopologicalSpace X]

def faceLiftHomeomorph (q : FaceAnchor (K := K) × G) :
    closedFace (K := K) q.1.val.1 ≃ₜ v.liftedClosedFace q :=
  (v.faceLift_closedEmbedding q.1.property.1 q.1.property.2 q.2).isEmbedding.toHomeomorph

variable (H : ∀ q : FaceAnchor (K := K) × G, C(I × closedFace (K := K) q.1.val.1,X))
  (ha : ∀ i j t x y,
    v.faceLift i.1.property.1 i.1.property.2 i.2 x = v.faceLift j.1.property.1 j.1.property.2 j.2 y →
      H i (t,x) = H j (t,y))

def homotopyOnRange (q : FaceAnchor (K := K) × G) : C(I × v.liftedClosedFace q,X) :=
  (H q).comp ((ContinuousMap.id I).prodMap
    ⟨(v.faceLiftHomeomorph q).symm,(v.faceLiftHomeomorph q).symm.continuous⟩)

include ha in
lemma homotopyOnRange_agree (i j : FaceAnchor (K := K) × G) (t : I) x
    (hi : x ∈ v.liftedClosedFace i) (hj : x ∈ v.liftedClosedFace j) :
    v.homotopyOnRange H i (t,⟨x,hi⟩) = v.homotopyOnRange H j (t,⟨x,hj⟩) := by
  apply ha
  have h1 := congrArg Subtype.val ((v.faceLiftHomeomorph i).apply_symm_apply ⟨x,hi⟩)
  have h2 := congrArg Subtype.val ((v.faceLiftHomeomorph j).apply_symm_apply ⟨x,hj⟩)
  exact h1.trans h2.symm

/-- The actual global continuous prism. -/
def glueFaceHomotopies : C(I × v.TotalSpace,X) :=
  ClosedCoverGluing.gluePrism v.liftedClosedFace v.liftedClosedFace_cover
    v.liftedClosedFace_closed v.liftedClosedFace_locallyFinite
    (v.homotopyOnRange H) (v.homotopyOnRange_agree H ha)

end HyperbolicObstruction.FinitePolyhedron.Voltage
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_VoltagePrismGluing
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A genuine dimension-two contraction gluing theorem. Its local input is a
continuous prism for each face, compatible with the SAME edge prisms. -/
noncomputable section

open scoped Topology unitInterval
namespace HyperbolicObstruction.FinitePolyhedron.Voltage
variable {V : Type*} [Fintype V] [DecidableEq V] {K : AbstractSimplicialComplex V}
  {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
  (v : Voltage K G)

variable (z : v.TotalSpace)

variable (E : v.EdgePrisms z)
structure FacePrism (s : Finset V) (hs : s ∈ K.faces) where
  anchor : V
  mem_anchor : anchor ∈ s
  H : G → C(I × closedFace (K := K) s,v.TotalSpace)
  initial : ∀ g x, H g (0,x) = v.faceLift hs mem_anchor g x
  final : ∀ g x, H g (1,x) = z
  edge : ∀ {a b} (he : {a,b} ∈ K.faces) g k t r x,
    v.faceLift hs mem_anchor g x = v.edgeLift he k r → H g (t,x) = E.H he k (t,r)

variable (F : ∀ (s : Finset V) (hs : s ∈ K.faces), v.FacePrism z E s hs)

def anchoredFacePrism (q : FaceAnchor (K := K) × G) :
    C(I × closedFace (K := K) q.1.val.1,v.TotalSpace) :=
  (F q.1.val.1 q.1.property.1).H
    (q.2 * v.value q.1.val.2 (F q.1.val.1 q.1.property.1).anchor)

lemma anchoredFacePrism_lift (q : FaceAnchor (K := K) × G)
    (x : closedFace (K := K) q.1.val.1) :
    v.faceLift q.1.property.1 (F q.1.val.1 q.1.property.1).mem_anchor
      (q.2 * v.value q.1.val.2 (F q.1.val.1 q.1.property.1).anchor) x =
      v.faceLift q.1.property.1 q.1.property.2 q.2 x :=
  v.inChart_change_face q.1.property.1 q.1.property.2
    (F q.1.val.1 q.1.property.1).mem_anchor x q.2

variable (hd : ∀ s ∈ K.faces, s.card ≤ 3)
include hd in
lemma anchoredFacePrism_agree (i j : FaceAnchor (K := K) × G) (t : I)
    (x : closedFace (K := K) i.1.val.1) (y : closedFace (K := K) j.1.val.1)
    (he : v.faceLift i.1.property.1 i.1.property.2 i.2 x =
      v.faceLift j.1.property.1 j.1.property.2 j.2 y) :
    v.anchoredFacePrism z E F i (t,x) = v.anchoredFacePrism z E F j (t,y) := by
  have hh := (v.anchoredFacePrism_lift z E F i x).trans
    (he.trans (v.anchoredFacePrism_lift z E F j y).symm)
  by_cases hst : i.1.val.1 = j.1.val.1
  · rcases i with ⟨⟨⟨s,a⟩,hs,ha⟩,g⟩
    rcases j with ⟨⟨⟨s',b⟩,hs',hb⟩,k⟩
    dsimp at hst
    subst s'
    obtain ⟨hg,hxy⟩ := v.faceLift_sheet_injective hs (F s hs).mem_anchor _ _ x y hh
    change (F s hs).H _ (t,x) = (F s hs).H _ (t,y)
    rw [hg,hxy]
  · let e := v.faceLift i.1.property.1 i.1.property.2 i.2 x
    have hy : v.proj e ∈ closedFace j.1.val.1 := by
      change v.proj (v.faceLift i.1.property.1 i.1.property.2 i.2 x) ∈ _
      rw [he]; exact y.property
    obtain ⟨a,b,h,g,r,hr⟩ := v.intersection_edge i.1.property.1 j.1.property.1
      (hd _ i.1.property.1) (hd _ j.1.property.1) hst e x.property hy
    change (F _ _).H _ (t,x) = (F _ _).H _ (t,y)
    rw [(F _ _).edge h _ g t r x ((v.anchoredFacePrism_lift z E F i x).trans hr.symm),
      (F _ _).edge h _ g t r y ((v.anchoredFacePrism_lift z E F j y).trans (he.symm.trans hr.symm))]

def contraction : C(I × v.TotalSpace,v.TotalSpace) :=
  v.glueFaceHomotopies (v.anchoredFacePrism z E F) (v.anchoredFacePrism_agree z E F hd)

end HyperbolicObstruction.FinitePolyhedron.Voltage
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_VoltageFacePrisms
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Constructions of the actual face-prism input: every edge, and every
nondegenerate triangle with a literal three-sided contracting prism. -/
noncomputable section

open scoped Topology unitInterval
namespace HyperbolicObstruction.FinitePolyhedron.Voltage
open TriangleSquare
variable {V : Type*} [Fintype V] [DecidableEq V] {K : AbstractSimplicialComplex V}
  {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
  (v : Voltage K G) (z : v.TotalSpace) (E : v.EdgePrisms z)

variable {a b : V} (h : {a,b} ∈ K.faces)
def edgeFacePrism : v.FacePrism z E {a,b} h where
  anchor := a
  mem_anchor := by simp
  H g := (E.H h g).comp ⟨fun tx => (tx.1,edgeParameter tx.2),
    continuous_fst.prodMk ((edgeParameter_continuous a b).comp continuous_snd)⟩
  initial g x := by
    change E.H h g (0,edgeParameter x) = _
    rw [E.initial]
    change v.faceLift h (a := a) (by simp) g (edgePoint h (edgeParameter x)) = _
    rw [edgePoint_parameter]
  final g x := E.final h g (edgeParameter x)
  edge h' g k t r x he := by
    apply E.agree
    change v.faceLift h (a := a) (by simp) g (edgePoint h (edgeParameter x)) = _
    rw [edgePoint_parameter]
    exact he

variable {c : V} (ht : {a,b,c} ∈ K.faces) (hi : Function.Injective ![a,b,c])
variable (H : G → C(I × Triangle,v.TotalSpace))
  (h0 : ∀ g p, H g (0,p) = v.triangleLift ht g p)
  (h1 : ∀ g p, H g (1,p) = z)
  (hb : ∀ g t r, H g (t,quotient (r,0)) = E.H (edge_of_subset K ht (by simp) (by simp) : {a,b} ∈ K.faces) g (t,r))
  (hl : ∀ g t r, H g (t,quotient (0,r)) = E.H (edge_of_subset K ht (by simp) (by simp) : {a,c} ∈ K.faces) g (t,r))
  (hr : ∀ g t r, H g (t,quotient (1,r)) = E.H (edge_of_subset K ht (by simp) (by simp) : {b,c} ∈ K.faces) (g*v.value a b) (t,r))

lemma triangleCoordinates_symm_point (x : closedFace (K := K) {a,b,c}) :
    trianglePoint ht ((triangleCoordinates ht hi).symm x) = x := by
  rw [←triangleCoordinates_apply ht hi,(triangleCoordinates ht hi).apply_symm_apply]

include hi hb hl hr in
lemma trianglePrism_edge_agree {d e : V} (h' : {d,e} ∈ K.faces) (g k : G) (t r : I)
    (p : Triangle) (he : v.triangleLift ht g p = v.edgeLift h' k r) :
    H g (t,p) = E.H h' k (t,r) := by
  have hp : (trianglePoint ht p).val = edgePath K h' r := congrArg v.proj he
  rcases triangle_boundary_of_edge ht hi h' p r hp with ⟨s,rfl⟩|⟨s,rfl⟩|⟨s,rfl⟩
  · rw [hb]
    apply E.agree
    exact (v.triangleLift_bottom ht g s).symm.trans he
  · rw [hl]
    apply E.agree
    exact (v.triangleLift_left ht g s).symm.trans he
  · rw [hr]
    apply E.agree
    exact (v.triangleLift_right ht g s).symm.trans he

def triangleFacePrism : v.FacePrism z E {a,b,c} ht where
  anchor := a
  mem_anchor := by simp
  H g := (H g).comp ((ContinuousMap.id I).prodMap
    ⟨(triangleCoordinates ht hi).symm,(triangleCoordinates ht hi).symm.continuous⟩)
  initial g x := by
    change H g (0,(triangleCoordinates ht hi).symm x) = _
    rw [h0]
    change v.faceLift ht (a := a) (by simp) g (trianglePoint ht ((triangleCoordinates ht hi).symm x)) = _
    rw [triangleCoordinates_symm_point ht hi]
  final g x := h1 g ((triangleCoordinates ht hi).symm x)
  edge h' g k t r x he := by
    apply v.trianglePrism_edge_agree z E ht hi H hb hl hr
    change v.faceLift ht (a := a) (by simp) g (trianglePoint ht ((triangleCoordinates ht hi).symm x)) = _
    rw [triangleCoordinates_symm_point ht hi]
    exact he

variable (hd : ∀ s ∈ K.faces, s.card ≤ 3)
  (hf : ∀ s (hs : s ∈ K.faces), s.card = 3 → Nonempty (v.FacePrism z E s hs))
include hd hf in
lemma facePrism_exists (s : Finset V) (hs : s ∈ K.faces) : Nonempty (v.FacePrism z E s hs) := by
  by_cases hc : s.card ≤ 2
  · obtain ⟨a,b,rfl⟩ := nonempty_pair_of_card_le_two (K.isRelLowerSet_faces hs).1 hc
    exact ⟨v.edgeFacePrism z E hs⟩
  · exact hf s hs (by have := hd s hs; omega)

def fromTrianglePrisms : C(I × v.TotalSpace,v.TotalSpace) :=
  v.contraction z E (fun s hs => Classical.choice (v.facePrism_exists z E hd hf s hs)) hd

end HyperbolicObstruction.FinitePolyhedron.Voltage
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_VoltageGraphHomotopy
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A coherent contraction of the actual lifted one-skeleton. The negative
orientation uses spatial reversal of the SAME square, not another choice. -/
noncomputable section

open scoped Topology unitInterval
namespace HyperbolicObstruction.FinitePolyhedron.Voltage
variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
  {K : AbstractSimplicialComplex V} {G : Type*} [Group G]
  [TopologicalSpace G] [DiscreteTopology G] (v : Voltage K G)

variable [SimplyConnectedSpace v.TotalSpace] (z : v.TotalSpace)

lemma edgeHomotopy_reverse {a b : V} (h : {a,b} ∈ K.faces) (g : G) (t s : I) :
    v.edgeHomotopy z (show {b,a} ∈ K.faces by simpa [Finset.pair_comm] using h)
      (g*v.value a b) (t,s) = v.edgeHomotopy z h g (t,unitInterval.symm s) := by
  by_cases hab : a = b
  · subst b
    simp only [edgeHomotopy,ite_true,eq_self]
    change v.vertexTrack z a (g*v.value a a) t = v.vertexTrack z a g t
    rw [v.self a,mul_one]
  by_cases hlt : a < b
  · have hnl : ¬ b < a := not_lt_of_gt hlt
    simp only [edgeHomotopy,hab,Ne.symm hab,ite_false,hlt,hnl,ite_true,ContinuousMap.comp_apply]
    rw [v.value_reverse_mul h]
    rfl
  · have hgt : b < a := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hab)
    simp only [edgeHomotopy,hab,Ne.symm hab,ite_false,hlt,hgt,ite_true,ContinuousMap.comp_apply]
    change _ = v.rawEdgeHomotopy z _ _ (t,unitInterval.symm (unitInterval.symm s))
    rw [unitInterval.symm_symm]

end HyperbolicObstruction.FinitePolyhedron.Voltage
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_VoltageEdgeAgreement
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Gluing of edge data is proved from the literal lifted coordinates. No
agreement of independent choices on intersecting edges is assumed. -/
noncomputable section

open scoped Topology unitInterval
namespace HyperbolicObstruction.FinitePolyhedron.Voltage
variable {V : Type*} [Fintype V] [DecidableEq V]
  {K : AbstractSimplicialComplex V} {G : Type*} [Group G]
  [TopologicalSpace G] [DiscreteTopology G] (v : Voltage K G)

variable {X : Type*}

namespace EdgeData
variable {v} (H : v.EdgeData (X := X))
lemma at_vertex {a b c : V} (h : {a,b} ∈ K.faces) (g d : G) (t s : I)
    (he : v.edgeLift h g s = v.vertexLift c d) : H.edge h g t s = H.vertex c d t := by
  by_cases hab : a = b
  · subst b
    rw [v.edgeLift_self] at he
    obtain ⟨rfl,rfl⟩ := (v.vertexLift_eq_iff a c g d).mp he
    exact H.collapsed _ _ _ _
  have hp := congrArg v.proj he
  obtain ⟨rfl,hac⟩|⟨rfl,hbc⟩ := edgePath_eq_vertex_cases K h hab s hp
  · rw [Path.source] at he
    obtain ⟨rfl,rfl⟩ := (v.vertexLift_eq_iff a c g d).mp he
    exact H.left _ _ _
  · rw [Path.target] at he
    obtain ⟨rfl,rfl⟩ := (v.vertexLift_eq_iff b c (g*v.value a b) d).mp he
    exact H.right _ _ _

lemma agree {a b c d : V} (h : {a,b} ∈ K.faces) (h' : {c,d} ∈ K.faces)
    (g k : G) (t s r : I) (he : v.edgeLift h g s = v.edgeLift h' k r) :
    H.edge h g t s = H.edge h' k t r := by
  by_cases hab : a = b
  · subst b
    rw [H.collapsed]
    exact (H.at_vertex h' k g t r (he.symm.trans (v.edgeLift_self a g s))).symm
  by_cases hcd : c = d
  · subst d
    rw [H.collapsed]
    exact H.at_vertex h g k t s (he.trans (v.edgeLift_self c k r))
  by_cases hs0 : s = 0
  · subst s
    rw [H.left]
    exact (H.at_vertex h' k g t r (he.symm.trans (Path.source _))).symm
  by_cases hs1 : s = 1
  · subst s
    rw [H.right]
    exact (H.at_vertex h' k (g*v.value a b) t r (he.symm.trans (Path.target _))).symm
  have hp := congrArg v.proj he
  obtain ⟨hac,hbd,hst⟩|⟨had,hbc,hst⟩ := edgePath_eq_edge_interior K h h' hab hcd s r hs0 hs1 hp
  · subst c; subst d; subst r
    have hg : g = k := v.edgeLift_sheet_injective h s he
    subst k; rfl
  · subst d; subst c; subst s
    rw [←v.edgeLift_reverse h g r] at he
    have hg : g*v.value a b = k := v.edgeLift_sheet_injective h' r he
    subst k
    exact (H.reversed h g t r).symm
end EdgeData

variable [LinearOrder V] [SimplyConnectedSpace v.TotalSpace] (z : v.TotalSpace)
def graphEdgeData : v.EdgeData (X := v.TotalSpace) where
  vertex a g t := v.vertexTrack z a g t
  edge h g t s := v.edgeHomotopy z h g (t,s)
  left := v.edgeHomotopy_left z
  right := v.edgeHomotopy_right z
  collapsed a g t s := by simp only [edgeHomotopy,ite_true,eq_self]; rfl
  reversed := v.edgeHomotopy_reverse z

lemma edgeHomotopy_agree {a b c d : V} (h : {a,b} ∈ K.faces) (h' : {c,d} ∈ K.faces)
    (g k : G) (t s r : I) (he : v.edgeLift h g s = v.edgeLift h' k r) :
    v.edgeHomotopy z h g (t,s) = v.edgeHomotopy z h' k (t,r) :=
  (v.graphEdgeData z).agree h h' g k t s r he

end HyperbolicObstruction.FinitePolyhedron.Voltage
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_VoltageEdgeCorrection
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Choose representatives of a directed pi2-cochain with LITERAL spatial
reversal, so corrected edge prisms agree as maps, not merely as classes. -/
noncomputable section

open scoped Topology unitInterval
namespace HyperbolicObstruction.FinitePolyhedron.Voltage
open HSpacePathObstruction
variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
  {K : AbstractSimplicialComplex V} {G : Type*} [Group G]
  [TopologicalSpace G] [DiscreteTopology G] (v : Voltage K G) (z : v.TotalSpace)
local notation "e" => Path.refl z

def loopRepresentative (c : v.LoopClass z) : Path e e :=
  (Path.Homotopic.Quotient.mk_surjective c).choose
omit [LinearOrder V] in
lemma loopRepresentative_class (c : v.LoopClass z) : loopClass (v.loopRepresentative z c) = c :=
  (Path.Homotopic.Quotient.mk_surjective c).choose_spec

variable (L : G → V → V → v.LoopClass z)
  (hs : ∀ g a, L g a a = 1)
  (hr : ∀ {a b}, {a,b} ∈ K.faces → ∀ g, L (g*v.value a b) b a = (L g a b)⁻¹)

def correctionLoop {a b : V} (_ : {a,b} ∈ K.faces) (g : G) : Path e e :=
  if a = b then Path.refl e else if a < b then v.loopRepresentative z (L g a b)
  else LoopSpaceReversal.reverse z (v.loopRepresentative z (L (g*v.value a b) b a))

include hs hr in
lemma correctionLoop_class {a b : V} (h : {a,b} ∈ K.faces) (g : G) :
    loopClass (v.correctionLoop z L h g) = L g a b := by
  unfold correctionLoop
  split_ifs with hab hlt
  · subst b; exact (hs g a).symm
  · exact v.loopRepresentative_class z _
  · rw [LoopSpaceReversal.reverse_class,v.loopRepresentative_class,hr h g,inv_inv]

lemma correctionLoop_reverse {a b : V} (h : {a,b} ∈ K.faces) (g : G) (t s : I) :
    v.correctionLoop z L (show {b,a} ∈ K.faces by simpa [Finset.pair_comm] using h)
      (g*v.value a b) t s = v.correctionLoop z L h g t (unitInterval.symm s) := by
  by_cases hab : a = b
  · subst b; simp only [correctionLoop,ite_true,eq_self]; rfl
  by_cases hlt : a < b
  · have hnl : ¬ b < a := not_lt_of_gt hlt
    simp only [correctionLoop,hab,Ne.symm hab,ite_false,hlt,hnl,ite_true]
    rw [v.value_reverse_mul h]
    rfl
  · have hgt : b < a := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hab)
    simp only [correctionLoop,hab,Ne.symm hab,ite_false,hlt,hgt,ite_true]
    rw [LoopSpaceReversal.reverse_apply,unitInterval.symm_symm]

def correctionSquare {a b : V} (h : {a,b} ∈ K.faces) (g : G) : C(I × I,v.TotalSpace) :=
  ⟨fun ts => ((Path.refl e).trans (v.correctionLoop z L h g)) ts.1 ts.2,
    Path.continuous_uncurry_iff.mpr (Path.refl e |>.trans (v.correctionLoop z L h g)).continuous⟩

lemma correctionSquare_reverse {a b : V} (h : {a,b} ∈ K.faces) (g : G) (t s : I) :
    v.correctionSquare z L (show {b,a} ∈ K.faces by simpa [Finset.pair_comm] using h)
      (g*v.value a b) (t,s) = v.correctionSquare z L h g (t,unitInterval.symm s) := by
  simp only [correctionSquare,ContinuousMap.coe_mk,Path.trans_apply]
  split_ifs
  · rfl
  · exact v.correctionLoop_reverse z L h g _ s

lemma correctionSquare_initial {a b : V} (h : {a,b} ∈ K.faces) (g : G) (s : I) :
    v.correctionSquare z L h g (0,s) = z := by simp [correctionSquare]
lemma correctionSquare_final {a b : V} (h : {a,b} ∈ K.faces) (g : G) (s : I) :
    v.correctionSquare z L h g (1,s) = z := by simp [correctionSquare]

def correctionEdgeData : v.EdgeData (X := v.TotalSpace) where
  vertex _ _ _ := z
  edge h g t s := v.correctionSquare z L h g (t,s)
  left h g t := by change ((Path.refl e).trans (v.correctionLoop z L h g)) t 0 = z; exact Path.source _
  right h g t := by change ((Path.refl e).trans (v.correctionLoop z L h g)) t 1 = z; exact Path.target _
  collapsed a g t s := by
    change ((Path.refl e).trans (v.correctionLoop z L (edge_self K a) g)) t s = z
    simp only [correctionLoop,ite_true,eq_self,Path.refl_trans_refl]; rfl
  reversed := v.correctionSquare_reverse z L

end HyperbolicObstruction.FinitePolyhedron.Voltage
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_SquareBoundaryExtension
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Four actual edge homotopies extend a square homotopy, with their literal
boundary formulas retained. -/
noncomputable section

open scoped Topology unitInterval
namespace HyperbolicObstruction.SquareBoundaryExtension
attribute [local instance] Classical.propDecidable
variable {X : Type*} [TopologicalSpace X]

namespace Data
variable (D : Data (X := X))

variable (f : C(Fin 2 → I,X))
  (hf : ∀ q (z : Fin 2 → I), z q.1 = endpoint q.2 →
    D.side q (0,z (other q.1)) = f z)

lemma extend_initial (z : Fin 2 → I) : D.extend f hf (0,z) = f z :=
  CubicalHomotopyExtension.extend_bottom _ _ _ z

end Data
end HyperbolicObstruction.SquareBoundaryExtension
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_TriangleHomotopyExtension
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact homotopy extension on a genuine closed triangle, retaining all
three side tracks and collapsing the fourth square side throughout. -/
noncomputable section

open scoped Topology unitInterval
namespace HyperbolicObstruction.TriangleHomotopyExtension
open TriangleSquare SquareBoundaryExtension
variable {X : Type*} [TopologicalSpace X]

variable (f : C(Triangle,X)) (D : Data (X := X))
  (hf : ∀ q (z : Fin 2 → I), z q.1 = endpoint q.2 →
    D.side q (0,z (other q.1)) = f (quotient (pairCube z)))
  (ht : ∀ t s, D.side (1,true) (t,s) = D.side (1,true) (t,0))

lemma square_initial (z : I × I) : square f D hf (0,z) = f (quotient z) := by
  change D.extend _ hf (0,cubePair z) = _
  rw [D.extend_initial]
  rfl

lemma extend_initial (z : Triangle) : extend f D hf ht (0,z) = f z := by
  obtain ⟨z,rfl⟩ := quotient_surjective z
  rw [extend_square,square_initial]

end HyperbolicObstruction.TriangleHomotopyExtension
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_VoltageTriangleHomotopy
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Extend the SAME coherent lifted graph contraction over each actual closed
triangle. Its terminal map is based along all three sides. -/
noncomputable section

open scoped Topology unitInterval
namespace HyperbolicObstruction.FinitePolyhedron.Voltage
open TriangleSquare SquareBoundaryExtension TriangleHomotopyExtension
variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
  {K : AbstractSimplicialComplex V} {G : Type*} [Group G]
  [TopologicalSpace G] [DiscreteTopology G] (v : Voltage K G)
  [SimplyConnectedSpace v.TotalSpace] (z : v.TotalSpace)

variable {a b c : V} (h : {a,b,c} ∈ K.faces) (g : G)

lemma triangleHomotopy_initial (w : Triangle) : v.triangleHomotopy z h g (0,w) = v.triangleLift h g w :=
  TriangleHomotopyExtension.extend_initial _ _ _ _ w

end HyperbolicObstruction.FinitePolyhedron.Voltage
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_VoltageTriangleContraction
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A literal contracting prism on each lifted triangle once its genuine pi2
obstruction is the coboundary of the constructed directed cochain. -/
noncomputable section

open scoped Topology unitInterval
namespace HyperbolicObstruction.FinitePolyhedron.Voltage
open TriangleSquare HSpacePathObstruction
variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
  {K : AbstractSimplicialComplex V} {G : Type*} [Group G]
  [TopologicalSpace G] [DiscreteTopology G] (v : Voltage K G)
  [SimplyConnectedSpace v.TotalSpace] (z : v.TotalSpace)
  (L : G → V → V → v.LoopClass z)
  (hs : ∀ g a, L g a a = 1)
  (hr : ∀ {a b}, {a,b} ∈ K.faces → ∀ g, L (g*v.value a b) b a = (L g a b)⁻¹)

def correctedEdge {a b : V} (h : {a,b} ∈ K.faces) (g : G) : C(I × I,v.TotalSpace) :=
  PrismConcat.concat (v.edgeHomotopy z h g) (v.correctionSquare z L h g)
    (fun s => (v.edgeHomotopy_final z h g s).trans (v.correctionSquare_initial z L h g s).symm)

lemma correctedEdge_agree {a b c d : V} (h : {a,b} ∈ K.faces) (h' : {c,d} ∈ K.faces)
    (g k : G) (t s r : I) (he : v.edgeLift h g s = v.edgeLift h' k r) :
    v.correctedEdge z L h g (t,s) = v.correctedEdge z L h' k (t,r) :=
  PrismConcat.agree _ _ _ _ _ _ s r
    (fun t => v.edgeHomotopy_agree z h h' g k t s r he)
    (fun t => (v.correctionEdgeData z L).agree h h' g k t s r he) t
lemma correctedEdge_initial {a b : V} (h : {a,b} ∈ K.faces) (g : G) (s : I) :
    v.correctedEdge z L h g (0,s) = v.edgeLift h g s := by
  rw [correctedEdge,PrismConcat.initial,v.edgeHomotopy_initial]
lemma correctedEdge_final {a b : V} (h : {a,b} ∈ K.faces) (g : G) (s : I) :
    v.correctedEdge z L h g (1,s) = z := by
  rw [correctedEdge,PrismConcat.final,v.correctionSquare_final]

variable {a b c : V} (h : {a,b,c} ∈ K.faces) (g : G)
variable (hL : L g a c * v.triangleObstruction z h g = L g a b * L (g*v.value a b) b c)

include hs hr hL in
lemma triangleLoops_correct :
    loopClass (v.correctionLoop z L (edge_of_subset K h (by simp) (by simp) : {a,c} ∈ K.faces) g) *
      v.triangleObstruction z h g =
    loopClass (v.correctionLoop z L (edge_of_subset K h (by simp) (by simp) : {a,b} ∈ K.faces) g) *
    loopClass (v.correctionLoop z L (edge_of_subset K h (by simp) (by simp) : {b,c} ∈ K.faces) (g*v.value a b)) := by
  simp only [v.correctionLoop_class z L hs hr]
  exact hL

def terminalContraction : C(I × Triangle,v.TotalSpace) :=
  BasedTriangleContraction.contraction z (v.basedTriangle z h g)
    (v.basedTriangle_bottom z h g) (v.basedTriangle_left z h g) (v.basedTriangle_right z h g)
    (v.correctionLoop z L (edge_of_subset K h (by simp) (by simp) : {a,b} ∈ K.faces) g)
    (v.correctionLoop z L (edge_of_subset K h (by simp) (by simp) : {a,c} ∈ K.faces) g)
    (v.correctionLoop z L (edge_of_subset K h (by simp) (by simp) : {b,c} ∈ K.faces) (g*v.value a b))
    (v.triangleLoops_correct z L hs hr h g hL)
lemma terminalContraction_initial (p : Triangle) :
    v.terminalContraction z L hs hr h g hL (0,p) = v.basedTriangle z h g p :=
  BasedTriangleContraction.contraction_initial _ _ _ _ _ _ _ _ _ p
lemma terminalContraction_final (p : Triangle) : v.terminalContraction z L hs hr h g hL (1,p) = z :=
  BasedTriangleContraction.contraction_final _ _ _ _ _ _ _ _ _ p
lemma terminalContraction_bottom (t s : I) :
    v.terminalContraction z L hs hr h g hL (t,quotient (s,0)) =
      v.correctionSquare z L (edge_of_subset K h (by simp) (by simp) : {a,b} ∈ K.faces) g (t,s) :=
  BasedTriangleContraction.contraction_bottom _ _ _ _ _ _ _ _ _ t s
lemma terminalContraction_left (t s : I) :
    v.terminalContraction z L hs hr h g hL (t,quotient (0,s)) =
      v.correctionSquare z L (edge_of_subset K h (by simp) (by simp) : {a,c} ∈ K.faces) g (t,s) :=
  BasedTriangleContraction.contraction_left _ _ _ _ _ _ _ _ _ t s
lemma terminalContraction_right (t s : I) :
    v.terminalContraction z L hs hr h g hL (t,quotient (1,s)) =
      v.correctionSquare z L (edge_of_subset K h (by simp) (by simp) : {b,c} ∈ K.faces) (g*v.value a b) (t,s) :=
  BasedTriangleContraction.contraction_right _ _ _ _ _ _ _ _ _ t s

def correctedTriangle : C(I × Triangle,v.TotalSpace) :=
  PrismConcat.concat (v.triangleHomotopy z h g) (v.terminalContraction z L hs hr h g hL)
    (fun p => (v.terminalContraction_initial z L hs hr h g hL p).symm)
lemma correctedTriangle_initial (p : Triangle) :
    v.correctedTriangle z L hs hr h g hL (0,p) = v.triangleLift h g p :=
  (PrismConcat.initial (v.triangleHomotopy z h g) (v.terminalContraction z L hs hr h g hL)
    (fun q => (v.terminalContraction_initial z L hs hr h g hL q).symm) p).trans
      (v.triangleHomotopy_initial z h g p)
lemma correctedTriangle_final (p : Triangle) : v.correctedTriangle z L hs hr h g hL (1,p) = z :=
  (PrismConcat.final (v.triangleHomotopy z h g) (v.terminalContraction z L hs hr h g hL)
    (fun q => (v.terminalContraction_initial z L hs hr h g hL q).symm) p).trans
      (v.terminalContraction_final z L hs hr h g hL p)
lemma correctedTriangle_bottom (t s : I) :
    v.correctedTriangle z L hs hr h g hL (t,quotient (s,0)) =
      v.correctedEdge z L (edge_of_subset K h (by simp) (by simp) : {a,b} ∈ K.faces) g (t,s) :=
  PrismConcat.agree _ _ _ _ _ _ _ _ (fun t => v.triangleHomotopy_bottom z h g t s)
    (fun t => v.terminalContraction_bottom z L hs hr h g hL t s) t
lemma correctedTriangle_left (t s : I) :
    v.correctedTriangle z L hs hr h g hL (t,quotient (0,s)) =
      v.correctedEdge z L (edge_of_subset K h (by simp) (by simp) : {a,c} ∈ K.faces) g (t,s) :=
  PrismConcat.agree _ _ _ _ _ _ _ _ (fun t => v.triangleHomotopy_left z h g t s)
    (fun t => v.terminalContraction_left z L hs hr h g hL t s) t
lemma correctedTriangle_right (t s : I) :
    v.correctedTriangle z L hs hr h g hL (t,quotient (1,s)) =
      v.correctedEdge z L (edge_of_subset K h (by simp) (by simp) : {b,c} ∈ K.faces) (g*v.value a b) (t,s) :=
  PrismConcat.agree _ _ _ _ _ _ _ _ (fun t => v.triangleHomotopy_right z h g t s)
    (fun t => v.terminalContraction_right z L hs hr h g hL t s) t

end HyperbolicObstruction.FinitePolyhedron.Voltage
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_PolygonContraction
attribute [-instance] _root_.OAI.HyperbolicObstruction.HigherCovering.boundary_pathConnected _root_.OAI.HyperbolicObstruction.HigherCovering.cube_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A global continuous contraction of the literal polygon voltage cover,
constructed by cochain correction and locally finite closed-cell gluing. -/
noncomputable section

open scoped Topology unitInterval
namespace HyperbolicObstruction.FinitePolyhedron.Voltage
variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
  {K : AbstractSimplicialComplex V} {G : Type*} [Group G]
  [TopologicalSpace G] [DiscreteTopology G] (v : Voltage K G)
  [SimplyConnectedSpace v.TotalSpace] (z : v.TotalSpace)
  (L : G → V → V → v.LoopClass z)

def correctedEdgePrisms : v.EdgePrisms z where
  H := v.correctedEdge z L
  initial := v.correctedEdge_initial z L
  final := v.correctedEdge_final z L
  agree := v.correctedEdge_agree z L

variable (hs : ∀ g a, L g a a = 1)
  (hr : ∀ {a b}, {a,b} ∈ K.faces → ∀ g, L (g*v.value a b) b a = (L g a b)⁻¹)
  {a b c : V} (h : {a,b,c} ∈ K.faces) (hi : Function.Injective ![a,b,c])
  (hL : ∀ g, L g a c * v.triangleObstruction z h g = L g a b * L (g*v.value a b) b c)

def correctedFacePrism : v.FacePrism z (v.correctedEdgePrisms z L) {a,b,c} h :=
  v.triangleFacePrism z (v.correctedEdgePrisms z L) h hi
    (fun g => v.correctedTriangle z L hs hr h g (hL g))
    (fun g => v.correctedTriangle_initial z L hs hr h g (hL g))
    (fun g => v.correctedTriangle_final z L hs hr h g (hL g))
    (fun g => v.correctedTriangle_bottom z L hs hr h g (hL g))
    (fun g => v.correctedTriangle_left z L hs hr h g (hL g))
    (fun g => v.correctedTriangle_right z L hs hr h g (hL g))
end HyperbolicObstruction.FinitePolyhedron.Voltage

namespace HyperbolicObstruction.FinitePolygonModel.Data
open FinitePolyhedron FinitePolyhedron.Voltage
variable {V E C G : Type*} [Fintype V] [Fintype E] [Fintype C]
  [DecidableEq V] [DecidableEq E] [DecidableEq C] [Group G]
  [TopologicalSpace G] [DiscreteTopology G] (P : Data V E C) (ρ : E → G)
  (hc : ∀ c, (List.ofFn (fun i => signed ρ (P.side c i))).prod = 1)
  [LinearOrder P.Vertex] [SimplyConnectedSpace (P.voltage ρ hc).TotalSpace]
  (z : (P.voltage ρ hc).TotalSpace)

variable (w : G × E → Additive ((P.voltage ρ hc).LoopClass z))

attribute [local instance] OAI.HyperbolicObstruction.FinitePolygonModel.Data.instCommGroupLoopClassVertexVoltage
variable (hw : ∀ d c, (∑ i : Fin (P.size c),
    signedCochain ρ w (d*((List.ofFn (fun i => signed ρ (P.side c i))).take i.val).prod) (P.side c i)) =
    ∑ i : Fin (P.size c), ∑ j : Fin 3,
      P.triangleWeight (P.obstructionWeight ρ hc z) (d*P.cornerOffset ρ ⟨c,(i,j)⟩) ⟨c,(i,j)⟩)
include hw in
lemma obstructionCochain_triangle (q : P.Position) (j : Fin 3) (g : G) :
    P.obstructionCochain ρ hc z w g (P.outer q) (P.collarC q j) *
      (P.voltage ρ hc).triangleObstruction z (P.collar_mem q j) g =
    P.obstructionCochain ρ hc z w g (P.outer q) (P.collarB q j) *
      P.obstructionCochain ρ hc z w (g*(P.voltage ρ hc).value (P.outer q) (P.collarB q j))
        (P.collarB q j) (P.collarC q j) := by
  have hh := P.triangleCochain_coboundary ρ w (P.obstructionWeight ρ hc z) hc hw g q
  apply Additive.ofMul.injective
  change P.triangleCochain ρ w (P.obstructionWeight ρ hc z) g (P.outer q) (P.collarC q j) +
      P.obstructionWeight ρ hc z g q j =
    P.triangleCochain ρ w (P.obstructionWeight ρ hc z) g (P.outer q) (P.collarB q j) +
      P.triangleCochain ρ w (P.obstructionWeight ρ hc z)
        (g*P.value ρ (P.outer q) (P.collarB q j)) (P.collarB q j) (P.collarC q j)
  fin_cases j
  · change _ + P.obstructionWeight ρ hc z g q 0 = _
    rw [add_comm _ (P.obstructionWeight ρ hc z g q 0)]
    exact (eq_add_of_sub_eq hh.1).symm
  · change _ + P.obstructionWeight ρ hc z g q 1 = _
    rw [add_comm _ (P.obstructionWeight ρ hc z g q 1)]
    exact (eq_add_of_sub_eq hh.2.1).symm
  · change _ + P.obstructionWeight ρ hc z g q 2 = _
    rw [add_comm _ (P.obstructionWeight ρ hc z g q 2)]
    exact (eq_add_of_sub_eq hh.2.2).symm

def contractionFace (q : P.Position) (j : Fin 3) :
    (P.voltage ρ hc).FacePrism z
      ((P.voltage ρ hc).correctedEdgePrisms z (P.obstructionCochain ρ hc z w))
      {P.outer q,P.collarB q j,P.collarC q j} (P.collar_mem q j) :=
  (P.voltage ρ hc).correctedFacePrism z (P.obstructionCochain ρ hc z w)
    (P.obstructionCochain_self ρ hc z w) (P.obstructionCochain_reverse ρ hc z w)
    (P.collar_mem q j) (P.collar_injective q j) (P.obstructionCochain_triangle ρ hc z w hw q j)

include hw in
lemma threeFacePrism (s : Finset P.Vertex) (hs : s ∈ P.complex.faces) (h3 : s.card = 3) :
    Nonempty ((P.voltage ρ hc).FacePrism z
      ((P.voltage ρ hc).correctedEdgePrisms z (P.obstructionCochain ρ hc z w)) s hs) := by
  obtain ⟨q,j,hq⟩ := P.three_face_collar hs h3
  rw [P.collarFace_eq] at hq
  subst s
  exact ⟨P.contractionFace ρ hc z w hw q j⟩

def coverContraction : C(I × (P.voltage ρ hc).TotalSpace,(P.voltage ρ hc).TotalSpace) :=
  (P.voltage ρ hc).fromTrianglePrisms z
    ((P.voltage ρ hc).correctedEdgePrisms z (P.obstructionCochain ρ hc z w))
    (fun _ hs => P.simplex_card_le_three hs) (P.threeFacePrism ρ hc z w hw)

end HyperbolicObstruction.FinitePolygonModel.Data
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

namespace IndexedFilling
open HyperbolicObstruction.WordPictures HyperbolicObstruction.WordPictures.WordPicture
open HyperbolicObstruction.PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {C E V A : Type*} [AddCommGroup A]
  (B : PolygonTarget.Boundary C (E × Bool) V) (weight : C → A)

def SphereZero : Prop := ∀ (P : WordPicture (Set.range B.attachingWord) [])
  (I : Indexing B P), I.chain weight = 0

def HasChain (w : Word E) (z : A) : Prop :=
  ∃ P : WordPicture (Set.range B.attachingWord) w, ∃ I : Indexing B P,
    I.chain weight = -z

def Null (w : Word E) : Prop :=
  PresentedGroup.mk (FreeGroup.mk '' Set.range B.attachingWord) (FreeGroup.mk w) = 1

variable {B weight}

/-- Chosen only from genuine, exactly marked genus-zero disks. -/
def value (w : Word E) : A :=
  if h : ∃ z, HasChain B weight w z then h.choose else 0

end IndexedFilling

/-! Literal walks in a signed incidence graph, with componentwise root paths.
No connectedness or universal-cover assertion is assumed. -/

/-! A literal disk-chain left inverse for the integral cell boundary. The
rooted-edge construction avoids assuming an arbitrary-cycle sphere producer. -/

namespace IndexedFilling
open HyperbolicObstruction.WordPictures HyperbolicObstruction.WordPictures.WordPicture
open HyperbolicObstruction.PictureSwitch SignedWalks
attribute [local instance] Classical.propDecidable
variable {C E V A : Type*} [AddCommGroup A]
  (B : PolygonTarget.Boundary C (E × Bool) V) (weight : C → A)

variable (hrev : B.rev = invLetter) (hz : SphereZero B weight)
  (hloop : ∀ x w, Walk B.start x x w → Null B w)

variable {B weight}

variable (B weight)
def edgeValue (e : E) : A := value (B := B) (weight := weight) (correction B.start (e,true))
def leftInverse : (E →₀ ℤ) →ₗ[ℤ] A := Finsupp.linearCombination ℤ (edgeValue B weight)

end IndexedFilling

/-! Subdivision of permutation cycles, with exact orbit-count preservation. -/

/-! Local elementary triangle incidence induces the exact radial contraction. -/

/-! Lifting actual word homotopies to the voltage cover, with the negative
orientation based at the positive lift's initial endpoint. -/

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

/-! Literal area-counted edge-disk calculus on the frozen finite-complex
model. All path algebra below uses only the challenge's stutters and spurs. -/
namespace FinitePolyhedron.EdgeChain
open HyperbolicObstruction.FiniteComplex
variable {K : FiniteComplex}

abbrev Homotopy {a b : K.Vertex} (p q : K.Chain a b) (n : ℕ) : Prop := K.DiskHomotopy p.nodes q.nodes n

end FinitePolyhedron.EdgeChain
end

/-! Rooted path algebra with exact zero-cost spur cancellations. This is a
literal triangular disk calculus, not an appeal to topological equivalence. -/

section

/-! A proved edge-and-triangle presentation of the actual fundamental group
of a finite barycentric realization. The rooted routes are actual edge paths;
no van Kampen theorem or fundamental-group comparison is postulated. -/

attribute [local instance] Classical.propDecidable
open Set
namespace FinitePolyhedron.EdgePresentation
variable {V : Type*} [Fintype V] [DecidableEq V] (K : AbstractSimplicialComplex V)

variable (o : V) (R : ∀ a, EdgeChain K o a)

omit [Fintype V] in
lemma gen_self (a : V) : gen K o R (edge_self K a) = 1 :=
  PresentedGroup.one_of_mem (Relation.self a)

omit [Fintype V] in
lemma gen_triangle {a b c : V} (h : {a,b,c} ∈ K.faces)
    (hab : {a,b} ∈ K.faces) (hbc : {b,c} ∈ K.faces) (hac : {a,c} ∈ K.faces) :
    gen K o R hab * gen K o R hbc = gen K o R hac := by
  have hh := PresentedGroup.one_of_mem
    (rels := show Set (FreeGroup (Generator K)) from Relation K o R)
    (Relation.triangle (K := K) (o := o) (R := R) h hab hbc hac)
  rw [map_mul,map_mul,map_inv,mul_inv_eq_one] at hh
  exact hh

/-- The canonical cocycle of the finite edge presentation. -/
def voltage : Voltage K (PresentationGroup K o R) where
  value a b := if h : {a,b} ∈ K.faces then gen K o R h else 1
  self a := by rw [dite_eq_left (edge_self K a)]; exact gen_self K o R a
  triangle a b c h := by
    have hab := edge_of_subset K h (a := a) (b := b) (by simp) (by simp)
    have hbc := edge_of_subset K h (a := b) (b := c) (by simp) (by simp)
    have hac := edge_of_subset K h (a := a) (b := c) (by simp) (by simp)
    rw [dite_eq_left hab,dite_eq_left hbc,dite_eq_left hac]
    exact gen_triangle K o R h hab hbc hac

end FinitePolyhedron.EdgePresentation
end

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

/-! Finite unit-speed vertex paths; all indices are bounded explicitly. -/

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


