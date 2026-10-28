-- Prove2me | Definitions.Def_OAIQ034H003
-- name    : OAIQ034H003
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T05:36:06.42907+00:00
-- url     : https://prove2.me/theorems/661e6588-9a5b-4353-943b-46711e7c208d
-- title:
--   Definitions bundle OAIQ034H003 of the split of OpenAI, A hyperbolic group with no geometric CAT(0) action (result family 257)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.HyperbolicObstruction.main`, carved from OpenAI's openai/math development (OpenAI, *A hyperbolic group with no geometric CAT(0) action (result family 257)*, OpenAI Math Release, September 25, 2026, result family 257, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 421 declarations of OpenAI's Lean: 204 definitions, 8 inductive types or structures, 19 instances and 190 theorems. The definitions and types are `OAI.HyperbolicObstruction.ConeSkeleton.AllBoundaryIndex`, `OAI.HyperbolicObstruction.ConeSkeleton.AllPaymentIndex`, `OAI.HyperbolicObstruction.ConeSkeleton.AllTriangleIndex`, `OAI.HyperbolicObstruction.ConeSkeleton.AllTurnIndex`, `OAI.HyperbolicObstruction.ConeSkeleton.BoundedConeRelator`, `OAI.HyperbolicObstruction.ConeSkeleton.DecorationSideIndex`, `OAI.HyperbolicObstruction.ConeSkeleton.ElementaryBases`, `OAI.HyperbolicObstruction.ConeSkeleton.ElementaryCell`, `OAI.HyperbolicObstruction.ConeSkeleton.ElementaryDart`, `OAI.HyperbolicObstruction.ConeSkeleton.ElementaryEdge`, `OAI.HyperbolicObstruction.ConeSkeleton.ElementaryLiftSide`, `OAI.HyperbolicObstruction.ConeSkeleton.ElementaryPiOne`, `OAI.HyperbolicObstruction.ConeSkeleton.ElementaryPolygonGroup`, `OAI.HyperbolicObstruction.ConeSkeleton.ElementaryVertex`, `OAI.HyperbolicObstruction.ConeSkeleton.FaceApexDart`, `OAI.HyperbolicObstruction.ConeSkeleton.KindFace`, `OAI.HyperbolicObstruction.ConeSkeleton.LetterC₁`, `OAI.HyperbolicObstruction.ConeSkeleton.LetterC₂`, `OAI.HyperbolicObstruction.ConeSkeleton.LiftedCellularChain`, `OAI.HyperbolicObstruction.ConeSkeleton.MacroCell`, `OAI.HyperbolicObstruction.ConeSkeleton.OccurrenceTrial`, `OAI.HyperbolicObstruction.ConeSkeleton.OriginalEdgeChain`, `OAI.HyperbolicObstruction.ConeSkeleton.OutsideCellSide`, `OAI.HyperbolicObstruction.ConeSkeleton.PolygonGroup`, `OAI.HyperbolicObstruction.ConeSkeleton.RadialBoundarySide`, `OAI.HyperbolicObstruction.ConeSkeleton.RawAccountIndex`, `OAI.HyperbolicObstruction.ConeSkeleton.RawPosition`, `OAI.HyperbolicObstruction.ConeSkeleton.RawPositionSide`, `OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.ActualContact`, `OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.ActualRawBoundary`, `OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.ActualRawSide`, `OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.AllBoundaryIndex`, `OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.AllPaymentIndex`, `OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.AllTriangleIndex`, `OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.AllTurnIndex`, `OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.ApexInstance`, `OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.DecorationSideIndex`, `OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.FaceApexDart`, `OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.Interior`, `OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.InteriorFace` and 172 more.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry/HyperbolicGroups, in whole or in part: `HyperbolicGroups_ActualOccurrenceShape`, `HyperbolicGroups_ActualPosition`, `HyperbolicGroups_ActualRawCount`, `HyperbolicGroups_ConeApexProducer`, `HyperbolicGroups_ConeExteriorWalk`, `HyperbolicGroups_ConeLetterCollapse`, `HyperbolicGroups_ConeMappedWalk`, `HyperbolicGroups_ConePresentationGroup`, `HyperbolicGroups_ContactCapacity`, `HyperbolicGroups_CoreWordGraph`, `HyperbolicGroups_CoverBoundary`, `HyperbolicGroups_ElementaryCone`, `HyperbolicGroups_ElementaryCover`, `HyperbolicGroups_ExteriorTarget`, `HyperbolicGroups_FanApex`, `HyperbolicGroups_FanRoute`, `HyperbolicGroups_FiniteFanData`, `HyperbolicGroups_FragmentSlots`, `HyperbolicGroups_FrozenPrevious`, `HyperbolicGroups_FrozenSideExists`, `HyperbolicGroups_FrozenWalk`, `HyperbolicGroups_Graph`, `HyperbolicGroups_GraphAction`, `HyperbolicGroups_GraphWordFilling`, `HyperbolicGroups_IndexedFace`, `HyperbolicGroups_IndexedFanCards`, `HyperbolicGroups_IndexedFanCounts`, `HyperbolicGroups_IndexedFillingValue`, `HyperbolicGroups_IndexedPayment`, `HyperbolicGroups_LetterNormalPicture`, `HyperbolicGroups_LiftedBasis`, `HyperbolicGroups_MacroCertificate`, `HyperbolicGroups_MacroExceptional`, `HyperbolicGroups_MacroGroup`, `HyperbolicGroups_MacroRadialIndex`, `HyperbolicGroups_MetricHexagon`, `HyperbolicGroups_NormalDiskArea`, `HyperbolicGroups_NormalFaceFilling`, `HyperbolicGroups_Occurrence`, `HyperbolicGroups_PictureContact`, `HyperbolicGroups_PictureDual`, `HyperbolicGroups_PictureTriangulation`, `HyperbolicGroups_PolygonBoundaryList`, `HyperbolicGroups_PolygonTarget`, `HyperbolicGroups_Presentation`, `HyperbolicGroups_PresentationDisk`, `HyperbolicGroups_RelativeApexLocal`, `HyperbolicGroups_RelativeApexProducer`, `HyperbolicGroups_RelativeContact`, `HyperbolicGroups_RelativeExceptional`, `HyperbolicGroups_RelativeFaceCounts`, `HyperbolicGroups_RelativeFaceSide`, `HyperbolicGroups_RelativeFanCapacity`, `HyperbolicGroups_RelativeFanLink`, `HyperbolicGroups_RelativeFragment`, `HyperbolicGroups_RelativeFrozenSide`, `HyperbolicGroups_RelativeInstanceAt`, `HyperbolicGroups_RelativeMultiplicity`, `HyperbolicGroups_RelativePartition`, `HyperbolicGroups_RelativePartitionEstimate`, `HyperbolicGroups_RelativePayment`, `HyperbolicGroups_RelativeRadialBoundary`, `HyperbolicGroups_RelativeRawCount`, `HyperbolicGroups_RelativeRawPosition`, `HyperbolicGroups_RelativeSlots`, `HyperbolicGroups_RelativeTopTurns`, `HyperbolicGroups_RelativeTriangleTransport`, `HyperbolicGroups_RelativeTurnTransport`, `HyperbolicGroups_RelativeWeights`, `HyperbolicGroups_RestrictOccurrence`, `HyperbolicGroups_Shape`, `HyperbolicGroups_SimpleLetterPresentation`, `HyperbolicGroups_Template`, `HyperbolicGroups_WalkCell`, `HyperbolicGroups_WalkClasses`, `HyperbolicGroups_WalkConeLink`, `HyperbolicGroups_WalkFacePosition`, `HyperbolicGroups_WalkFanCorner`, `HyperbolicGroups_WalkFanIncoming`, `HyperbolicGroups_WalkFragment`, `HyperbolicGroups_WalkMultiplicity`, `HyperbolicGroups_WalkNormal`, `HyperbolicGroups_WalkPayment`, `HyperbolicGroups_WalkRadialBoundary`, `HyperbolicGroups_WalkRawPosition`, `HyperbolicGroups_WalkTopTurns`, `HyperbolicGroups_WalkTriangleTransport`, `HyperbolicGroups_WalkTurnTransport`, `HyperbolicGroups_WordDisk`.
--
--   **Imports.** It imports the bundles `OAIQ034H000` and `OAIQ034H001` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ034H007`, `OAIQ034H008`, `OAIQ034H009` and `OAIQ034H010`.
-- source:
--   OpenAI, A hyperbolic group with no geometric CAT(0) action (result family 257), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 257; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-hyperbolic-group-with-no-geometric-CAT0-action-September-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry/HyperbolicGroups at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ034H000
import Definitions.Def_OAIQ034H001

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_MetricHexagon
attribute [-instance] _root_.OAI.HyperbolicObstruction.CoreGeometry.instDecidableIsFanVertex
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
instance instDecidableEqVertex : DecidableEq Vertex := instDecidableEqSum

def Adjacent : Vertex → Vertex → Prop
  | .inl r, .inr l => Incident (pointOfRepresentative r) l ∧ (r,l) ≠ (10,4)
  | .inr l, .inl r => Incident (pointOfRepresentative r) l ∧ (r,l) ≠ (10,4)
  | _, _ => False

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

lemma twoPath_ne (τ : TwoPath) : τ.val.1 ≠ τ.val.2 := by
  intro he
  have hlt := τ.property.1
  rw [he] at hlt
  exact (lt_irrefl _ hlt)

end IncidenceTemplate
end HyperbolicObstruction
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_Graph
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeOutgoing _root_.OAI.HyperbolicObstruction.CoreGeometry.instDecidableIsFanVertex
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

def pos (f : Field) : Step (source f) (target f) := ⟨f, true, by simp⟩
def neg (f : Field) : Step (target f) (source f) := ⟨f, false, by simp⟩
end Step

/-- Finite paths, with edges carrying their actual named fields. -/
inductive Path : Vertex → Vertex → Type
  | nil (a : Vertex) : Path a a
  | cons {a b c : Vertex} (s : Step a b) (p : Path b c) : Path a c

namespace Path
variable {a b c : Vertex}
def length : {a b : Vertex} → Path a b → ℕ
  | _, _, .nil _ => 0
  | _, _, .cons _ p => p.length + 1

def fields : {a b : Vertex} → Path a b → List Field
  | _, _, .nil _ => []
  | _, _, .cons s p => s.field :: p.fields

end Path

/-- Core adjacency corresponds to the unique actual core field. -/
def coreStep {a b : CoreGeometry.Vertex} (h : CoreGeometry.Adjacent a b) : Step (.inl a) (.inl b) := by
  cases a with
  | inl r =>
    cases b with
    | inl r' => exact h.elim
    | inr l => exact Step.pos (.inl ⟨(r,l), h⟩)
  | inr l =>
    cases b with
    | inl r => exact Step.neg (.inl ⟨(r,l), h⟩)
    | inr l' => exact h.elim

end MasterGraph
end HyperbolicObstruction
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_GraphAction
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
namespace MasterGraph
open IncidenceTemplate

namespace Step
variable {G L : Type*} [Group G]
def value {a b : Vertex} (s : Step a b) (label : Field → L) (letter : L → G) : G :=
  if s.forward then letter (label s.field) else (letter (label s.field))⁻¹

end Step

namespace Path
variable {G L : Type*} [Group G] {a b c : Vertex}
def eval (label : Field → L) (letter : L → G) : {a b : Vertex} → Path a b → G
  | _, _, .nil _ => 1
  | _, _, .cons s p => s.value label letter * p.eval label letter

end Path

end MasterGraph
end HyperbolicObstruction
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_Presentation
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeOutgoing _root_.OAI.HyperbolicObstruction.CoreGeometry.instDecidableIsFanVertex
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
def IsCore (p : Path a b) : Prop := ∀ f ∈ p.fields, ∃ e : Edge, f = .inl e
end Path

/-- The oriented source four-letter decoration, including the two given core sides. -/
def squareWord {G L : Type*} [Group G] (l : Field → L) (r : L → G) (τ : TwoPath) : G :=
  (first τ).value l r * (second τ).value l r * r (l (.inr (τ,0))) * r (l (.inr (τ,1)))

end MasterGraph

namespace LetterPresentation
open IncidenceTemplate MasterGraph
variable (n : ℕ)

def freeLetter (a : Alphabet n) : FreeGroup (Fin (n+1)) :=
  if a.2 then FreeGroup.of a.1 else (FreeGroup.of a.1)⁻¹

variable (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)

/-- The literal source letter relators: all included fans, all included top
occurrences (with all seven fan slots), and every included square/six-letter
row, even rows that do not occur in any master match. -/
inductive Relator : FreeGroup (Fin (n+1)) → Prop
  | fan (l : Field → Alphabet n) (i : Fin 7)
      (present : w (TableModel.row rowSupport l (.inl i)) = true)
      (v : MasterGraph.Vertex) (p : MasterGraph.Path v v)
      (fields : p.fields.toFinset ⊆ rowSupport (.inl i)) : Relator (p.eval l (freeLetter n))
  | top (l : Field → Alphabet n)
      (present : w (TableModel.row rowSupport l (.inr (.inl ()))) = true)
      (fans : ∀ i : Fin 7, w (TableModel.row rowSupport l (.inl i)) = true)
      (v : MasterGraph.Vertex) (p : MasterGraph.Path v v) (core : p.IsCore) :
      Relator (p.eval l (freeLetter n))
  | square (l : Field → Alphabet n) (τ : TwoPath)
      (present : w (TableModel.row rowSupport l (.inr (.inr τ))) = true) :
      Relator (MasterGraph.squareWord l (freeLetter n) τ)
  | six (x : Fin 6 → Alphabet n) (present : d x = true) :
      Relator ((List.ofFn (freeLetter n ∘ x)).prod)

abbrev Group := PresentedGroup (Relator n w d)

end LetterPresentation
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

def point (i : Fin 7) : Vertex := .inl (.inl i)
def line (l : Fin 7) : Vertex := .inl (.inr l)
instance instDecidableAdjacent (a b : Vertex) : Decidable (Adjacent a b) := by
  rcases a with ((i|l)|⟨⟩) <;> rcases b with ((j|m)|⟨⟩) <;> unfold Adjacent <;> infer_instance


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

namespace IndexedFaceMap
variable {f : Perm D} {t : Perm S} {j : D → S} (h : IndexedFaceMap f t j)
include h

/-- Every indexed face maps ONTO its full target side cycle as well. -/
lemma orbit_surjective (a : D) {s : S} (hs : t.SameCycle (j a) s) :
    ∃ b, f.SameCycle a b ∧ j b = s := by
  obtain ⟨k,rfl⟩ := hs
  exact ⟨(f^k) a,SameCycle.rfl.zpow_right,semiconj_perm_zpow h.commute k a⟩

end IndexedFaceMap
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

namespace Boundary
variable (B : Boundary C L V)

lemma opposite_sq : B.opposite * B.opposite = 1 := by
  apply Equiv.ext
  rintro ⟨c,b,i⟩; cases b <;> rfl

lemma orientation_next (s : B.Side) : (B.next s).2.1 = s.2.1 := rfl

lemma orientation_cycle {s t : B.Side} (h : B.next.SameCycle s t) : s.2.1 = t.2.1 := by
  exact sameCycle_one.mp (semiconj_perm_sameCycle (t := (1 : Perm Bool)) (j := fun s : B.Side => s.2.1) B.orientation_next h)

lemma opposite_cycle (s : B.Side) : ¬ B.next.SameCycle s (B.opposite s) := by
  intro h
  have hh := B.orientation_cycle h
  rcases s with ⟨c,b,i⟩; cases b <;> cases hh

lemma next_start (s : B.Side) : B.start (B.sideLabel (B.next s)) = B.start (B.rev (B.sideLabel s)) := by
  rcases s with ⟨c,b,i⟩
  let : NeZero (B.size c) := ⟨Nat.ne_of_gt (B.positive c)⟩
  cases b with
  | false =>
    simpa [sideLabel,next,B.inv] using (B.closed c ((finRotate (B.size c))⁻¹ i)).symm
  | true => exact B.closed c i

lemma weight_next (w : C → A) (s : B.Side) : B.weight w (B.next s) = B.weight w s := rfl

lemma weight_opposite (w : C → A) (s : B.Side) : B.weight w s + B.weight w (B.opposite s) = 0 := by
  rcases s with ⟨c,b,i⟩; cases b <;> simp [weight,opposite]

/-- The exact indexed oriented cell target constructed from ordinary polygon
boundaries, suitable for `CellPicture.normalize`. -/
def target (w : C → A) (apex : V → Bool)
    (hr : ∀ l, apex (B.start l) = true → apex (B.start (B.rev l)) = false) :
    CellTarget B.Side L V A where
  next := B.next
  opposite := B.opposite
  opposite_sq := B.opposite_sq
  reverse_next := B.reverse_next
  opposite_cycle := B.opposite_cycle
  edge := B.sideLabel
  start := B.start
  rev := B.rev
  rev_rev := B.inv
  edge_opposite := B.edge_opposite
  next_start := B.next_start
  apex := apex
  radial := fun s => hr (B.sideLabel s)
  weight := B.weight w
  weight_next := B.weight_next w
  weight_opposite := B.weight_opposite w

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

inductive Move (R : Set (Word A)) : Word A → Word A → ℕ → Prop
  | free {u v} : FreeGroup.Red.Step u v → Move R u v 0
  | face (l r w) (h : w ∈ R) : Move R (l ++ w ++ r) (l ++ r) 1
  | reverseFace (l r w) (h : w ∈ R) :
      Move R (l ++ FreeGroup.invRev w ++ r) (l ++ r) 1

inductive Homotopy (R : Set (Word A)) : Word A → Word A → ℕ → Prop
  | refl (w) : Homotopy R w w 0
  | move {u v n} : Move R u v n → Homotopy R u v n
  | symm {u v n} : Homotopy R u v n → Homotopy R v u n
  | trans {u v w m n} : Homotopy R u v m → Homotopy R v w n → Homotopy R u w (m+n)

end HyperbolicObstruction.WordPictures
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_PresentationDisk
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeOutgoing _root_.OAI.HyperbolicObstruction.CoreGeometry.instDecidableIsFanVertex
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

def literalSquare (l : Field → Alphabet n) (τ : TwoPath) : List (Alphabet n) :=
  [stepLetter n l (first τ), stepLetter n l (second τ), l (.inr (τ,0)), l (.inr (τ,1))]

end LetterPresentation
end HyperbolicObstruction
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_Occurrence
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

/-- Table types and the incidence of all seven fan slots of every top. Fans
are indexed once, including those used by more than one top. -/
abbrev Shape (s u q : ℕ) := Σ t : Fin u → Fin 7,
  (Fin s → (i : Fin 7) → {b : Fin u // t b = i}) × (Fin q → TwoPath)


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
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeOutgoing
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

/-- Literal field positions in source diagram:rank. -/
abbrev Pos (v : ℕ) := Fin s ⊕ ((Σ b : Fin u, rowSupport (.inl (T.1 b))) ⊕
  ((Σ e : Fin q, squareSupport (T.2.2 e)) ⊕ (Fin v × Fin 6)))

end Shape
end Occurrences
end IncidenceTemplate
end HyperbolicObstruction
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_ActualOccurrenceShape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace HyperbolicObstruction.ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation
attribute [local instance] Classical.propDecidable
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)

noncomputable instance instFintypeTop : Fintype (Top n w) := Fintype.ofFinite _
noncomputable instance instFintypeFan : Fintype (Fan n w) := Fintype.ofFinite _
noncomputable instance instFintypeSquare : Fintype (Square n w) := Fintype.ofFinite _
noncomputable instance instFintypeSix : Fintype (Six n d) := Fintype.ofFinite _

abbrev enumTop := Fintype.equivFin (Top n w)
abbrev enumFan := Fintype.equivFin (Fan n w)
abbrev enumSquare := Fintype.equivFin (Square n w)
abbrev enumSix := Fintype.equivFin (Six n d)

/-- One index for every actual included trial, with all seven fan slots and
no duplication of a top by its boundary cycle or by decoration coordinates. -/
def occurrenceShape : Occurrences.Shape (Fintype.card (Top n w))
    (Fintype.card (Fan n w)) (Fintype.card (Square n w)) :=
  ⟨fun b => ((enumFan n w).symm b).val.1,
    (fun a i => ⟨enumFan n w (slot n w ((enumTop n w).symm a) i), by
      simp only [Equiv.symm_apply_apply]; rfl⟩),
    fun e => ((enumSquare n w).symm e).1⟩

/-- The literal signed values at original field positions. -/
def occurrenceValues : (occurrenceShape n w).Pos (Fintype.card (Six n d)) → Alphabet n
  | .inl a => ((enumTop n w).symm a).val loose
  | .inr (.inl ⟨b,f⟩) => ((enumFan n w).symm b).val.2 f
  | .inr (.inr (.inl ⟨e,f⟩)) => ((enumSquare n w).symm e).2.val f
  | .inr (.inr (.inr (e,i))) => ((enumSix n d).symm e).val i

lemma loose_unique (e : IncidenceTemplate.Edge) (he : isLoose e) : e = loose := by
  exact Subtype.ext he

lemma fan_value_congr {b b' : Fan n w} (hb : b = b') (e : IncidenceTemplate.Edge)
    (he : Sum.inl e ∈ rowSupport (.inl b.val.1))
    (he' : Sum.inl e ∈ rowSupport (.inl b'.val.1)) :
    b.val.2 ⟨.inl e,he⟩ = b'.val.2 ⟨.inl e,he'⟩ := by
  cases hb
  rfl

abbrev OccurrenceTrial := Occurrences.Shape.Trial (Fintype.card (Top n w))
  (Fintype.card (Fan n w)) (Fintype.card (Square n w)) (Fintype.card (Six n d))

end HyperbolicObstruction.ConeSkeleton
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

variable {S : Type v} {C : Type w} {W : Type z} {L : Type k} {V : Type t}
  {A : Type r} [AddCommMonoid A]

attribute [instance] WalkPicture.finite WalkPicture.decEq

namespace WalkPicture
variable {T : WalkCellTarget S C W L V A} (P : WalkPicture.{u} T)

def Simple : Prop := ∀ a b, T.free (T.kind (P.index a)) = true →
  P.pairing.face.SameCycle a b → T.back (P.index a) = T.back (P.index b) → a = b
def NoBigon : Prop := ∀ a, T.free (T.kind (P.index a)) = true →
  P.pairing.face (P.pairing.face a) ≠ a

lemma free_face {x : P.Dart} (hx : T.free (T.kind (P.index x)) = true) :
    T.free (T.kind (P.index (P.pairing.face x))) = true := by
  change T.free ((T.kind ∘ P.index) (P.pairing.face x)) = true
  rw [P.kind]; exact hx

end WalkPicture
end HyperbolicObstruction.PictureSwitch
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

namespace WalkPicture
variable {T : WalkCellTarget S C W L V A} (P : WalkPicture.{u} T)

variable {P}

variable (P)

lemma opposite_frozen {a b : P.Dart} (ha : T.free (T.kind (P.index a)) = false)
    (hop : P.index b = T.opposite (P.index a)) : T.free (T.kind (P.index b)) = false := by
  rw [hop,T.opposite_kind]; exact ha

end WalkPicture
end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_WalkNormal
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

lemma simple_front (hs : P.Simple) {a b : P.Dart}
    (ha : T.free (T.kind (P.index a)) = true)
    (hab : P.pairing.face.SameCycle a b)
    (he : T.front (P.index a) = T.front (P.index b)) : a = b := by
  apply P.pairing.face.symm.injective
  apply hs
  · have hk := P.kind (P.pairing.face.symm a)
    dsimp only [Function.comp_apply] at hk
    rw [Equiv.apply_symm_apply] at hk
    rw [← hk]; exact ha
  · exact hab.symm_apply_left.symm_apply_right
  · have hca := P.closed (P.pairing.face.symm a)
    have hcb := P.closed (P.pairing.face.symm b)
    dsimp only [Function.comp_apply] at hca hcb
    rw [Equiv.apply_symm_apply] at hca hcb
    exact hca.symm.trans (he.trans hcb)

end WalkPicture
end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_WalkRawPosition
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSix _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop
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

/-- Indexed positions, NOT generator labels. Two fields carrying an equal
numerical letter remain distinct positions. -/
abbrev RawPosition := Top n w ⊕ (FanTriangle n w ⊕ ((Square n w × Fin 4) ⊕ (Six n d × Fin 6)))

def rawPosition : WalkStep n w d → RawPosition n w d
  | .inl s => .inl s.1
  | .inr ⟨.inl g,_,_⟩ => .inr (.inl g)
  | .inr ⟨.inr (.inl s),_,i⟩ => .inr (.inr (.inl (s,i)))
  | .inr ⟨.inr (.inr s),_,i⟩ => .inr (.inr (.inr (s,i)))

def looseMacro : MacroGraph.graph.Dart :=
  ⟨(MacroGraph.exceptional,MacroGraph.line 4),rfl⟩

def rawRepresentative : RawPosition n w d → WalkStep n w d
  | .inl a => .inl (a,looseMacro)
  | .inr (.inl g) => .inr ⟨.inl g,true,(1 : Fin 3)⟩
  | .inr (.inr (.inl p)) => .inr ⟨.inr (.inl p.1),true,p.2⟩
  | .inr (.inr (.inr p)) => .inr ⟨.inr (.inr p.1),true,p.2⟩

lemma macro_letter_cases (a : Top n w) (e : MacroGraph.graph.Dart)
    (hr : isLetter n w (macroStep n w a e.adj) = true) :
    e = looseMacro ∨ e = looseMacro.symm := by
  rcases e with ⟨⟨u,v⟩,h⟩
  rcases u with ((i|l)|⟨⟩) <;> rcases v with ((j|m)|⟨⟩)
  · cases h
  · cases hr
  · have hi : i = 3 := h
    subst i
    cases hr
  · cases hr
  · cases h
  · have hl : l = 4 := h
    subst l
    exact Or.inr rfl
  · have hj : j = 3 := h
    subst j
    cases hr
  · have hm : m = 4 := h
    subst m
    exact Or.inl rfl
  · cases h

lemma fan_letter_index (g : FanTriangle n w) (o : Bool) (i : Fin 3)
    (hr : isLetter n w (walkLabel n w d (.inr ⟨.inl g,o,i⟩)) = true) : i = 1 := by
  cases o <;> fin_cases i
  · cases hr
  · rfl
  · cases hr
  · cases hr
  · rfl
  · cases hr

lemma walkOpposite_twice (s : WalkStep n w d) :
    walkOpposite n w d (walkOpposite n w d s) = s := by
  rcases s with s | ⟨c,o,i⟩
  · rfl
  · cases o <;> rfl

lemma raw_step_cases (s : WalkStep n w d) (hr : isLetter n w (walkLabel n w d s) = true) :
    s = rawRepresentative n w d (rawPosition n w d s) ∨
      s = walkOpposite n w d (rawRepresentative n w d (rawPosition n w d s)) := by
  rcases s with ⟨a,e⟩ | ⟨g,o,i⟩
  · rcases macro_letter_cases n w a e hr with he | he
    · subst e; exact Or.inl rfl
    · subst e; exact Or.inr rfl
  · rcases g with g | (q | q)
    · have hi := fan_letter_index n w d g o i hr
      subst i
      cases o
      · exact Or.inr rfl
      · exact Or.inl rfl
    · cases o
      · exact Or.inr rfl
      · exact Or.inl rfl
    · cases o
      · exact Or.inr rfl
      · exact Or.inl rfl

lemma rev_ne (l : Dart n w) : rev n w l ≠ l := by
  intro h
  have hh := congrArg Prod.snd h
  cases hc : l.2 <;> simp [rev,hc] at hh

universe u

end HyperbolicObstruction.ConeSkeleton
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_ActualPosition
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

def squareField (τ : TwoPath) (i : Fin 4) : rowSupport (.inr (.inr τ)) :=
  ⟨![Sum.inl τ.val.1,Sum.inl τ.val.2,Sum.inr (τ,0),Sum.inr (τ,1)] i,by
    fin_cases i <;> simp [rowSupport,squareSupport]⟩

lemma squareField_injective (τ : TwoPath) : Function.Injective (squareField τ) := by
  intro i j h
  have hh := congrArg Subtype.val h
  fin_cases i <;> fin_cases j <;> simp [squareField,twoPath_ne τ,Ne.symm (twoPath_ne τ)] at hh ⊢

lemma squareField_surjective (τ : TwoPath) : Function.Surjective (squareField τ) := by
  rintro ⟨v,hv⟩
  have hh : v = Sum.inl τ.val.1 ∨ v = Sum.inl τ.val.2 ∨
      v = Sum.inr (τ,0) ∨ v = Sum.inr (τ,1) := by simpa [rowSupport,squareSupport] using hv
  rcases hh with hh | hh | hh | hh
  · exact ⟨0,Subtype.ext hh.symm⟩
  · exact ⟨1,Subtype.ext hh.symm⟩
  · exact ⟨2,Subtype.ext hh.symm⟩
  · exact ⟨3,Subtype.ext hh.symm⟩

/-- Reindexing uses the original edge/decoration field, never its label value. -/
def rawToPosition : RawPosition n w d → (occurrenceShape n w).Pos (Fintype.card (Six n d))
  | .inl a => .inl (enumTop n w a)
  | .inr (.inl ⟨b,e⟩) => .inr (.inl ⟨enumFan n w b,⟨.inl e.val,by
      simpa only [occurrenceShape,Equiv.symm_apply_apply,rowSupport,Finset.mem_map,
        Function.Embedding.inl_apply,Sum.inl.injEq,exists_eq_right] using e.property⟩⟩)
  | .inr (.inr (.inl (s,i))) => .inr (.inr (.inl ⟨enumSquare n w s,⟨(squareField s.1 i).val,by
      simpa only [occurrenceShape,Equiv.symm_apply_apply,rowSupport] using (squareField s.1 i).property⟩⟩))
  | .inr (.inr (.inr (s,i))) => .inr (.inr (.inr (enumSix n d s,i)))

lemma rawToPosition_injective : Function.Injective (rawToPosition n w d) := by
  intro x y h
  rcases x with a | (⟨b,e⟩ | (⟨q,i⟩ | ⟨v,i⟩)) <;>
    rcases y with a' | (⟨b',e'⟩ | (⟨q',i'⟩ | ⟨v',i'⟩)) <;>
    simp only [rawToPosition,Sum.inl.injEq,Sum.inr.injEq,Sum.inl_ne_inr,Sum.inr_ne_inl] at h ⊢
  · exact (enumTop n w).injective h
  · have hb : b = b' := (enumFan n w).injective (congrArg Sigma.fst h)
    subst b'
    have hf := eq_of_heq (Sigma.mk.inj_iff.mp h).2
    have he : e = e' := Subtype.ext (Sum.inl.inj (congrArg Subtype.val hf))
    subst e'
    rfl
  · have hq : q = q' := (enumSquare n w).injective (congrArg Sigma.fst h)
    subst q'
    have hf := eq_of_heq (Sigma.mk.inj_iff.mp h).2
    have hv := congrArg Subtype.val hf
    have hi : i = i' := squareField_injective q.1 (Subtype.ext hv)
    exact Prod.ext rfl hi
  · obtain ⟨hv,hi⟩ := Prod.mk.inj h
    exact Prod.ext ((enumSix n d).injective hv) hi

lemma rawToPosition_surjective : Function.Surjective (rawToPosition n w d) := by
  intro p
  rcases p with a | (⟨b,⟨f,hf⟩⟩ | (⟨q,f⟩ | ⟨v,i⟩))
  · exact ⟨.inl ((enumTop n w).symm a),by simp only [rawToPosition,Equiv.apply_symm_apply]⟩
  · rcases f with e | r
    · have he : e ∈ fan (((enumFan n w).symm b).val.1) := by
        simpa only [occurrenceShape,rowSupport,Finset.mem_map,Function.Embedding.inl_apply,
          Sum.inl.injEq,exists_eq_right] using hf
      refine ⟨.inr (.inl ⟨(enumFan n w).symm b,⟨e,he⟩⟩),?_⟩
      simp only [rawToPosition,Sum.inr.injEq,Sum.inl.injEq]
      refine Sigma.ext ((enumFan n w).apply_symm_apply b) ?_
      exact (Subtype.heq_iff_coe_eq (by intro v; simp only [Equiv.apply_symm_apply])).mpr rfl
    · simp [rowSupport] at hf
  · have hf : f.val ∈ rowSupport (.inr (.inr (((enumSquare n w).symm q).1))) := f.property
    obtain ⟨i,hi⟩ := squareField_surjective (((enumSquare n w).symm q).1) ⟨f.val,hf⟩
    refine ⟨.inr (.inr (.inl ((enumSquare n w).symm q,i))),?_⟩
    simp only [rawToPosition,Sum.inr.injEq,Sum.inl.injEq]
    refine Sigma.ext ((enumSquare n w).apply_symm_apply q) ?_
    exact (Subtype.heq_iff_coe_eq (by intro v; simp only [Equiv.apply_symm_apply])).mpr
      (congrArg Subtype.val hi)
  · exact ⟨.inr (.inr (.inr ((enumSix n d).symm v,i))),by simp only [rawToPosition,Equiv.apply_symm_apply]⟩

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
open State

namespace Mark
variable {F O : Type*}
def plain : Mark F → State
  | absent => .absent
  | triangle => .triangle
  | top _ => .dominant

end Mark

end HyperbolicObstruction.FanLink
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_FiniteFanData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.FanLink
open Equiv
namespace Mark
variable {F G : Type*}
def map (e : F ≃ G) : Mark F → Mark G
  | absent => absent
  | triangle => triangle
  | top f => top (e f)
@[simp] lemma map_absent (e : F ≃ G) (m : Mark F) : map e m = absent ↔ m = absent := by cases m <;> simp [map]
@[simp] lemma map_triangle (e : F ≃ G) (m : Mark F) : map e m = triangle ↔ m = triangle := by cases m <;> simp [map]
@[simp] lemma map_top (e : F ≃ G) (m : Mark F) (g : G) : map e m = top g ↔ m = top (e.symm g) := by
  cases m <;> simp [map,Equiv.eq_symm_apply]
end Mark

/-- The same local finite-link data, with natural geometric index types.
`toFin` is only a change of finite coordinates, not an additional assumption. -/
structure IndexedFanData (I F O : Type*) (L : I → Type*) [Fintype I] [Fintype F] [Fintype O]
    [∀ z, Fintype (L z)] where
  next : (z : I) → Equiv.Perm (L z)
  cyclic : ∀ z, IsCyclic (next z)
  mark : (z : I) → L z → Mark F
  line : (z : I) → L z → Bool
  occurrence : F → O
  represented : ∀ z, ∃ i, mark z i ≠ .absent
  card_le : ∀ z, Fintype.card (L z) ≤ 5
  no_fixed : ∀ z i, next z i ≠ i
  bipartite : ∀ z i, mark z i = .triangle → line z i ≠ line z (next z i)
  no_backtrack : ∀ z i, mark z i = .triangle → mark z (next z i) = .triangle → next z (next z i) ≠ i
  no_same_side : ∀ z i f g, mark z i = .top f → mark z (next z i) = .top g → occurrence f ≠ occurrence g
  unique_turn : ∀ (p q : Σ z, L z) f, mark p.1 p.2 = .top f → mark q.1 q.2 = .top f → p = q

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

noncomputable instance instFintypeFace : Fintype P.Face := Fintype.ofFinite _

lemma faceClass_eq {x y : P.Dart} : P.faceClass x = P.faceClass y ↔ P.pairing.face.SameCycle x y :=
  Quotient.eq

lemma faceClass_out (x : P.Face) : P.faceClass x.out = x := Quotient.out_eq _

lemma linkNext_val (z : P.Vertex) (x : P.Link z) : (P.linkNext z x).val = P.pairing.vertex⁻¹ x.val := rfl

lemma link_cyclic (z : P.Vertex) (x y : P.Link z) : ∃ k : ℕ, (P.linkNext z ^ k) x = y := by
  have hh : P.pairing.vertex⁻¹.SameCycle x.val y.val :=
    sameCycle_inv.mpr ((P.vertexClass_eq).mp (x.property.trans y.property.symm))
  have h : (P.linkNext z).SameCycle x y := hh.subtypePerm
  obtain ⟨k,_,_,hk⟩ := h.exists_pow_eq
  exact ⟨k,hk⟩

end WalkPicture
end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_ConeMappedWalk
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSix _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop _root_.OAI.HyperbolicObstruction.PictureSwitch.WalkPicture.instFintypeFace
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

lemma walkKind_cycle {x y : P.Dart} (h : P.pairing.face.SameCycle x y) :
    walkKind n w d (P.index x) = walkKind n w d (P.index y) := by
  exact sameCycle_one.mp (semiconj_perm_sameCycle
    (t := (1 : Perm (WalkKind n w d))) P.kind h)

lemma same_top_face {x y : P.Dart} {a : Top n w} {e : MacroGraph.graph.Dart}
    (hx : P.index x = .inl (a,e)) (h : P.pairing.face.SameCycle x y) :
    ∃ e', P.index y = .inl (a,e') := by
  have hk := walkKind_cycle n w d c hc f P h
  rw [hx] at hk
  cases hy : P.index y with
  | inl s =>
    rw [hy] at hk
    have hs : a = s.1 := Sum.inl.inj hk
    exact ⟨s.2,by rw [hs]⟩
  | inr s => rw [hy] at hk; cases hk

end HyperbolicObstruction.ConeSkeleton
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_MacroRadialIndex
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSix _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop
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

/-- Read only the indexed radial port, not its numerical letter assignment,
back into the subdivided macro template. -/
def radialTemplate : Dart n w → Option (MacroGraph.Vertex × MacroGraph.Vertex)
  | (.inl _,_) => none
  | (.inr ⟨b,v⟩,true) => some (MacroGraph.point b.val.1,
      match v.val with | .inl _ => .inr () | .inr l => .inl (.inr l))
  | (.inr _,false) => none

lemma macroStep_radialTemplate (a : Top n w) (e : MacroGraph.graph.Dart)
    (ha : isApex n w (start n w (macroStep n w a e.adj)) = true) :
    radialTemplate n w (macroStep n w a e.adj) = some e.toProd := by
  rcases e with ⟨⟨u,v⟩,h⟩
  change MacroGraph.Adjacent u v at h
  change isApex n w (start n w (macroStep n w a h)) = true at ha
  change radialTemplate n w (macroStep n w a h) = some (u,v)
  rw [macroStep_start] at ha
  rcases u with ((i|l)|⟨⟩)
  · rcases v with ((j|m)|⟨⟩)
    · exact h.elim
    · rfl
    · have hi : i = 3 := h; subst i; rfl
  · cases ha
  · cases ha

lemma macroStep_radial_injective (a : Top n w) (e k : MacroGraph.graph.Dart)
    (ha : isApex n w (start n w (macroStep n w a e.adj)) = true)
    (h : macroStep n w a e.adj = macroStep n w a k.adj) : e = k := by
  have hb : isApex n w (start n w (macroStep n w a k.adj)) = true := by rw [← h]; exact ha
  have hh := congrArg (radialTemplate n w) h
  rw [macroStep_radialTemplate n w a e ha,macroStep_radialTemplate n w a k hb] at hh
  exact SimpleGraph.Dart.ext e k (Option.some.inj hh)

lemma macroVertex_at_apex (a : Top n w) (u : MacroGraph.Vertex) (b : Fan n w)
    (h : macroVertex n w a u = .inr b) : u = MacroGraph.point b.val.1 := by
  rcases u with ((i|l)|⟨⟩)
  · have hb : slot n w a i = b := Sum.inr.inj h
    have hi := congrArg (fun b : Fan n w => b.val.1) hb
    exact congrArg MacroGraph.point hi
  · cases h
  · cases h

end HyperbolicObstruction.ConeSkeleton
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_WalkFanCorner
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSix _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop _root_.OAI.HyperbolicObstruction.PictureSwitch.WalkPicture.instFintypeFace
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

variable {c hc f}

variable (c hc f)

lemma walk_corner_no_two_step (hm : P.FrozenMapped (walkFrozenTarget n w d c hc f))
    (hred : P.FullyReduced) {x : P.Dart}
    {g h : FanTriangle n w} {o p : Bool}
    (hx : P.index x = frozenCorner n w d g o)
    (hy : P.index (P.pairing.vertex x) = frozenCorner n w d h p) :
    P.pairing.vertex (P.pairing.vertex x) ≠ x := by
  intro hh
  have hxy := walk_corner_ports n w d c hc f P hm hx hy
  have hyx := walk_corner_ports n w d c hc f P hm hy (by rw [hh]; exact hx)
  obtain ⟨rfl,rfl⟩ := reverse_corner_unique n w hxy hyx.symm
  apply hred x
  change P.index (P.pairing.edge x) = walkOpposite n w d (P.index x)
  rw [walk_index_edge_previous n w d c hc f P hm x (by rw [hy]; rfl),hy,hx,
    frozenCorner_reverse]

end HyperbolicObstruction.ConeSkeleton
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_WalkConeLink
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSix _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop _root_.OAI.HyperbolicObstruction.PictureSwitch.WalkPicture.instFintypeFace
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

/-- Consecutive top turns in one normalized apex link cannot belong to the
same top occurrence, even when their simple macro polygons are different. -/
lemma walk_top_adjacent_different (hred : P.FullyReduced) {x : P.Dart}
    {a b : Top n w} {e k : MacroGraph.graph.Dart}
    (hx : P.index x = .inl (a,e)) (hy : P.index (P.pairing.vertex x) = .inl (b,k))
    (ha : isApex n w (start n w (walkLabel n w d (P.index x))) = true) : a ≠ b := by
  intro hab; subst b
  obtain ⟨j,hj⟩ := same_top_face n w d c hc f P hy
    ((SameCycle.rfl (f := P.pairing.face) (x := P.pairing.edge x)).apply_left)
  have hpair := P.paired x
  change walkLabel n w d (P.index (P.pairing.edge x)) = rev n w (walkLabel n w d (P.index x)) at hpair
  rw [hj,hx] at hpair
  change macroStep n w a j.adj = rev n w (macroStep n w a e.adj) at hpair
  have hj' : macroStep n w a j.symm.adj = macroStep n w a e.adj := by
    exact (macroStep_reverse n w a j.adj).trans
      ((congrArg (rev n w) hpair).trans (rev_rev n w _))
  have he : e = j.symm := macroStep_radial_injective n w a e j.symm
    (by rw [hx] at ha; exact ha) hj'.symm
  have hje : j = e.symm := by rw [he]; rfl
  apply hred x
  rw [hj,hx,hje]
  rfl

/-- Two turns of one simple source top face over the same ACTUAL fan are
identical. The argument retains the indexed fan type even if numerical
letters and row fields repeat. -/
lemma walk_top_unique_turn (hs : P.Simple) {x y : P.Dart} {a : Top n w}
    {e : MacroGraph.graph.Dart} (hx : P.index x = .inl (a,e))
    (hxy : P.pairing.face.SameCycle x y) (b : Fan n w)
    (hax : start n w (walkLabel n w d (P.index x)) = .inr b)
    (hay : start n w (walkLabel n w d (P.index y)) = .inr b) : x = y := by
  obtain ⟨k,hk⟩ := same_top_face n w d c hc f P hx hxy
  rw [hx] at hax
  rw [hk] at hay
  change start n w (macroStep n w a e.adj) = .inr b at hax
  change start n w (macroStep n w a k.adj) = .inr b at hay
  have hax := (macroStep_start n w a e.adj).symm.trans hax
  have hay := (macroStep_start n w a k.adj).symm.trans hay
  have he : e.fst = k.fst := (macroVertex_at_apex n w a e.fst b hax).trans
    (macroVertex_at_apex n w a k.fst b hay).symm
  apply P.simple_front hs (by rw [hx]; rfl) hxy
  change walkFront n w d (P.index x) = walkFront n w d (P.index y)
  rw [hx,hk]
  exact congrArg Sum.inl (Prod.ext rfl he)

lemma walk_apex_no_fixed (hm : P.FrozenMapped (walkFrozenTarget n w d c hc f))
    (hred : P.FullyReduced) (x : P.Dart)
    (ha : isApex n w (start n w (walkLabel n w d (P.index x))) = true) :
    P.pairing.vertex x ≠ x := by
  intro he
  rcases walk_apex_cases n w d c hc f P x ha with ⟨a,e,hx⟩ | ⟨g,o,hx⟩
  · exact walk_top_adjacent_different n w d c hc f P hred hx (by rw [he]; exact hx) ha rfl
  · have hports := walk_corner_ports n w d c hc f P hm hx (by rw [he]; exact hx)
    exact corner_bipartite n w g o (congrArg (dartPart n w) hports)

end HyperbolicObstruction.ConeSkeleton
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_WalkFanIncoming
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSix _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop _root_.OAI.HyperbolicObstruction.PictureSwitch.WalkPicture.instFintypeFace
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

lemma walk_triangle_inverse_no_two (hm : P.FrozenMapped (walkFrozenTarget n w d c hc f))
    (hred : P.FullyReduced) {x : P.Dart} {g h : FanTriangle n w} {o p : Bool}
    (hx : P.index x = frozenCorner n w d g o)
    (hy : P.index (P.pairing.vertex⁻¹ x) = frozenCorner n w d h p) :
    P.pairing.vertex⁻¹ (P.pairing.vertex⁻¹ x) ≠ x := by
  intro he
  have hn := walk_corner_no_two_step n w d c hc f P hm hred hy
    (by rw [Perm.inv_def,apply_symm_apply]; exact hx)
  rw [Perm.inv_def,apply_symm_apply] at hn
  have hh := congrArg P.pairing.vertex he
  simp only [Perm.inv_def,apply_symm_apply] at hh
  exact hn hh.symm

end HyperbolicObstruction.ConeSkeleton
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_WalkFragment
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSix _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop
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

noncomputable instance instFintypeSelectedTop : Fintype (SelectedTop n w d c hc f P select b) := Fintype.ofFinite _
noncomputable instance instFintypeApexInstance : Fintype (ApexInstance n w d c hc f P select b) := Fintype.ofFinite _

def selectedOccurrence (F : SelectedTop n w d c hc f P select b) : Top n w :=
  F.property.2.choose

lemma selectedOccurrence_kind (F : SelectedTop n w d c hc f P select b) :
    P.faceKind F.val = .inl (selectedOccurrence n w d c hc f P select b F) :=
  F.property.2.choose_spec.1

lemma mark_absent (z : ApexInstance n w d c hc f P select b) (x : P.Link z.val) :
    fragmentMark n w d c hc f P select b z x = .absent ↔ select (P.faceClass x.val) ≠ true := by
  unfold fragmentMark
  split_ifs <;> simp_all

lemma mark_top_face (z : ApexInstance n w d c hc f P select b) (x : P.Link z.val)
    (F : SelectedTop n w d c hc f P select b)
    (h : fragmentMark n w d c hc f P select b z x = .top F) :
    F.val = P.faceClass x.val := by
  unfold fragmentMark at h
  split_ifs at h with hs ht
  exact congrArg Subtype.val (FanLink.Mark.top.inj h).symm

lemma mark_top_index (z : ApexInstance n w d c hc f P select b) (x : P.Link z.val)
    (F : SelectedTop n w d c hc f P select b)
    (h : fragmentMark n w d c hc f P select b z x = .top F) :
    ∃ e, P.index x.val = .inl (selectedOccurrence n w d c hc f P select b F,e) := by
  have hk := selectedOccurrence_kind n w d c hc f P select b F
  rw [mark_top_face n w d c hc f P select b z x F h] at hk
  change walkKind n w d (P.index x.val) = .inl _ at hk
  cases hx : P.index x.val with
  | inl s =>
    rw [hx] at hk
    change Sum.inl s.1 = Sum.inl _ at hk
    exact ⟨s.2,congrArg Sum.inl (Prod.ext (Sum.inl.inj hk) rfl)⟩
  | inr s => rw [hx] at hk; cases hk

lemma fragment_represented (z : ApexInstance n w d c hc f P select b) :
    ∃ x, fragmentMark n w d c hc f P select b z x ≠ .absent := by
  obtain ⟨x,hx,hs⟩ := z.property.2
  exact ⟨⟨x,hx⟩,fun h => (mark_absent n w d c hc f P select b z ⟨x,hx⟩).mp h hs⟩

lemma fragment_no_fixed (hm : P.FrozenMapped (walkFrozenTarget n w d c hc f))
    (hred : P.FullyReduced) (z : ApexInstance n w d c hc f P select b) (x : P.Link z.val) :
    P.linkNext z.val x ≠ x := by
  intro he
  have he' := congrArg Subtype.val he
  change P.pairing.vertex⁻¹ x.val = x.val at he'
  have hh := congrArg P.pairing.vertex he'
  simp only [Perm.inv_def,apply_symm_apply] at hh
  exact walk_apex_no_fixed n w d c hc f P hm hred x.val
    (instance_apex n w d c hc f P select b z x) hh.symm

lemma fragment_no_backtrack (hm : P.FrozenMapped (walkFrozenTarget n w d c hc f))
    (hred : P.FullyReduced) (z : ApexInstance n w d c hc f P select b) (x : P.Link z.val)
    (hx : fragmentMark n w d c hc f P select b z x = .triangle)
    (hy : fragmentMark n w d c hc f P select b z (P.linkNext z.val x) = .triangle) :
    P.linkNext z.val (P.linkNext z.val x) ≠ x := by
  obtain ⟨g,o,hg⟩ := mark_triangle_corner n w d c hc f P select b z x hx
  obtain ⟨h,p,hh⟩ := mark_triangle_corner n w d c hc f P select b z (P.linkNext z.val x) hy
  intro he
  exact walk_triangle_inverse_no_two n w d c hc f P hm hred hg hh (congrArg Subtype.val he)

lemma fragment_no_same_side (hred : P.FullyReduced)
    (z : ApexInstance n w d c hc f P select b) (x : P.Link z.val)
    (F G : SelectedTop n w d c hc f P select b)
    (hx : fragmentMark n w d c hc f P select b z x = .top F)
    (hy : fragmentMark n w d c hc f P select b z (P.linkNext z.val x) = .top G) :
    selectedOccurrence n w d c hc f P select b F ≠ selectedOccurrence n w d c hc f P select b G := by
  obtain ⟨e,he⟩ := mark_top_index n w d c hc f P select b z x F hx
  obtain ⟨k,hk⟩ := mark_top_index n w d c hc f P select b z (P.linkNext z.val x) G hy
  exact Ne.symm (walk_top_adjacent_different n w d c hc f P hred hk
    (by simpa only [P.linkNext_val,Perm.inv_def,apply_symm_apply] using he)
    (instance_apex n w d c hc f P select b z (P.linkNext z.val x)))

lemma fragment_unique_turn (hs : P.Simple)
    (p q : Σ z : ApexInstance n w d c hc f P select b, P.Link z.val)
    (F : SelectedTop n w d c hc f P select b)
    (hp : fragmentMark n w d c hc f P select b p.1 p.2 = .top F)
    (hq : fragmentMark n w d c hc f P select b q.1 q.2 = .top F) : p = q := by
  obtain ⟨e,he⟩ := mark_top_index n w d c hc f P select b p.1 p.2 F hp
  have hface := (mark_top_face n w d c hc f P select b p.1 p.2 F hp).symm.trans
    (mark_top_face n w d c hc f P select b q.1 q.2 F hq)
  have hd := walk_top_unique_turn n w d c hc f P hs he (P.faceClass_eq.mp hface) b
    (instance_start n w d c hc f P select b p.1 p.2)
    (instance_start n w d c hc f P select b q.1 q.2)
  have hz : p.1 = q.1 := Subtype.ext (p.2.property.symm.trans
    ((congrArg P.vertexClass hd).trans q.2.property))
  rcases p with ⟨z,x⟩; rcases q with ⟨y,k⟩
  dsimp at hz hd
  subst y
  exact congrArg (Sigma.mk z) (Subtype.ext hd)

end HyperbolicObstruction.ConeSkeleton
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_ConeApexProducer
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSix _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop
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

noncomputable instance instFintypeSelectedOccurrence : Fintype (SelectedOccurrence n w d c hc f P select) := Fintype.ofFinite _

variable (b : Fan n w)

def selectedOccurrence' (F : SelectedTop n w d c hc f P select b) :
    SelectedOccurrence n w d c hc f P select :=
  ⟨selectedOccurrence n w d c hc f P select b F,F.val,F.property.1,
    selectedOccurrence_kind n w d c hc f P select b F⟩

/-- The actual selected fragment of an actual normalized genus-zero mapped
picture supplies EVERY field of the local fan-link data. No apex bound,
no triangle-link normality and no contact separation is assumed. -/
def indexedFanData (hs : P.Simple) (hm : P.FrozenMapped (walkFrozenTarget n w d c hc f))
    (hred : P.FullyReduced) (hrad : P.RadialInjective (isApex n w)) :
    FanLink.IndexedFanData (ApexInstance n w d c hc f P select b)
      (SelectedTop n w d c hc f P select b) (SelectedOccurrence n w d c hc f P select)
      (fun z => P.Link z.val) where
  next := fun z => P.linkNext z.val
  cyclic := fun z => P.link_cyclic z.val
  mark := fragmentMark n w d c hc f P select b
  line := fun _ x => dartPart n w (walkLabel n w d (P.index x.val))
  occurrence := selectedOccurrence' n w d c hc f P select b
  represented := fragment_represented n w d c hc f P select b
  card_le := fragment_card n w d c hc f P select b hrad
  no_fixed := fragment_no_fixed n w d c hc f P select b hm hred
  bipartite := fragment_bipartite n w d c hc f P select b hm
  no_backtrack := fragment_no_backtrack n w d c hc f P select b hm hred
  no_same_side := by
    intro z x F G hx hy h
    exact fragment_no_same_side n w d c hc f P select b hred z x F G hx hy (congrArg Subtype.val h)
  unique_turn := fragment_unique_turn n w d c hc f P select b hs

end HyperbolicObstruction.ConeSkeleton
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_IndexedFanCounts
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
attribute [local instance] Classical.propDecidable
namespace Mark
@[simp] lemma plain_map {F G : Type*} (e : F ≃ G) (m : Mark F) :
    (map e m).plain = m.plain := by cases m <;> rfl
end Mark
namespace IndexedFanData
variable {I F O : Type*} {L : I → Type*} [Fintype I] [Fintype F] [Fintype O]
  [∀ z, Fintype (L z)] (D : IndexedFanData I F O L)

def state (z : I) := Mark.plain ∘ D.mark z
def payments : ℕ := ∑ z, P (D.next z) (D.state z) (D.line z)
def isPartial (z : I) : Prop := ∃ i, D.mark z i = .absent
def partialCount : ℕ := ∑ z, if D.isPartial z then 1 else 0
def multiplicity (a : O) : ℕ := Fintype.card {f : F // D.occurrence f = a}
def maxMultiplicity : ℕ := Finset.univ.sup D.multiplicity
def weight : ℕ := max (Fintype.card I) D.maxMultiplicity

end IndexedFanData
end HyperbolicObstruction.FanLink
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_RestrictOccurrence
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeOutgoing _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace HyperbolicObstruction
namespace IncidenceTemplate.Occurrences.Shape

variable {s u q v : ℕ} (T : Shape s u q)

/-- Integer weights on the occurrences, with fan slots retained at every level. -/
structure Weights where
  top : Fin s → ℕ
  fan : Fin u → ℕ
  square : Fin q → ℕ
  six : Fin v → ℕ
  slot : ∀ a i, top a ≤ fan (T.2.1 a i).val

namespace Weights
variable {T}
variable (W : T.Weights (v := v))

def position : T.Pos v → ℕ
  | .inl a => W.top a
  | .inr (.inl ⟨b,_⟩) => W.fan b
  | .inr (.inr (.inl ⟨e,_⟩)) => W.square e
  | .inr (.inr (.inr (e,_))) => W.six e

end Weights
end IncidenceTemplate.Occurrences.Shape
end HyperbolicObstruction
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_FrozenPrevious
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch.WalkPicture
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
universe u v w z k t r
variable {S : Type v} {C : Type w} {W : Type z} {L : Type k} {V : Type t}
  {A : Type r} [AddCommMonoid A]
variable {T : WalkCellTarget S C W L V A} (P : WalkPicture.{u} T)

lemma free_previous {x : P.Dart} :
    T.free (T.kind (P.index (P.pairing.face⁻¹ x))) = T.free (T.kind (P.index x)) := by
  have h := congrArg T.free (P.kind (P.pairing.face⁻¹ x))
  simpa only [Function.comp_apply,Perm.inv_def,apply_symm_apply] using h.symm

lemma frozen_previous_index (B : FrozenTarget T) (hm : P.FrozenMapped B)
    {x : P.Dart} (hx : T.free (T.kind (P.index x)) = false) :
    P.index (P.pairing.face⁻¹ x) = B.next⁻¹ (P.index x) := by
  have hy : T.free (T.kind (P.index (P.pairing.face⁻¹ x))) = false := P.free_previous.trans hx
  have h := hm.commute ⟨P.pairing.face⁻¹ x,hy⟩
  change P.index (P.pairing.face (P.pairing.face⁻¹ x)) = B.next (P.index (P.pairing.face⁻¹ x)) at h
  apply B.next.injective
  simpa only [Perm.inv_def,apply_symm_apply] using h.symm

lemma faceClass_apply (x : P.Dart) : P.faceClass (P.pairing.face x) = P.faceClass x :=
  P.faceClass_eq.mpr (SameCycle.rfl.apply_left)
lemma faceClass_previous (x : P.Dart) : P.faceClass (P.pairing.face⁻¹ x) = P.faceClass x :=
  P.faceClass_eq.mpr (sameCycle_inv.mp (SameCycle.rfl.apply_left))

end HyperbolicObstruction.PictureSwitch.WalkPicture
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_WalkFacePosition
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.PictureSwitch.WalkPicture.instFintypeFace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch.WalkPicture
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
universe u v w z k t r
variable {S : Type v} {C : Type w} {W : Type z} {L : Type k} {V : Type t}
  {A : Type r} [AddCommMonoid A]
variable {T : WalkCellTarget S C W L V A} (P : WalkPicture.{u} T)

lemma free_sameface_not_opposite (hs : P.Simple) (hb : P.NoBigon)
    {x y : P.Dart} (hx : T.free (T.kind (P.index x)) = true)
    (hxy : P.pairing.face.SameCycle x y) : P.index y ≠ T.opposite (P.index x) := by
  intro hop
  have hy : T.free (T.kind (P.index y)) = true := by rw [hop,T.opposite_kind]; exact hx
  have h1 : P.pairing.face x = y := by
    apply P.simple_front hs (P.free_face hx) hxy.apply_left
    rw [hop,T.opposite_front]
    exact P.closed x
  have h2 : P.pairing.face y = x := by
    apply P.simple_front hs (P.free_face hy) hxy.symm.apply_left
    calc
      _ = T.back (P.index y) := P.closed y
      _ = _ := by rw [hop,T.opposite_back]
  exact hb x hx (by rw [h1,h2])

lemma frozen_sameface_not_opposite (B : FrozenTarget T) (hm : P.FrozenMapped B)
    {x y : P.Dart} (hx : T.free (T.kind (P.index x)) = false)
    (hxy : P.pairing.face.SameCycle x y) : P.index y ≠ T.opposite (P.index x) := by
  intro hop
  let x' : P.FrozenDart := ⟨x,hx⟩
  let y' : P.FrozenDart := ⟨y,P.opposite_frozen hx hop⟩
  have hh : P.frozenFace.SameCycle x' y' := hxy.subtypePerm
  have ht := semiconj_perm_sameCycle hm.commute hh
  change B.next.SameCycle (P.index x) (P.index y) at ht
  rw [hop,← B.reverse_eq] at ht
  exact B.opposite_cycle _ ht

lemma normalized_index_inj (hs : P.Simple) (B : FrozenTarget T) (hm : P.FrozenMapped B)
    {x y : P.Dart} (hxy : P.pairing.face.SameCycle x y)
    (he : P.index x = P.index y) : x = y := by
  cases hf : T.free (T.kind (P.index x)) with
  | true => exact P.simple_front hs hf hxy (congrArg T.front he)
  | false =>
    let x' : P.FrozenDart := ⟨x,hf⟩
    let y' : P.FrozenDart := ⟨y,by rw [← he]; exact hf⟩
    have hh : P.frozenFace.SameCycle x' y' := hxy.subtypePerm
    have h := hm.injective hh (show P.index x = P.index y from he)
    exact congrArg Subtype.val h

lemma normalized_sameface_not_opposite (hs : P.Simple) (hb : P.NoBigon)
    (B : FrozenTarget T) (hm : P.FrozenMapped B)
    {x y : P.Dart} (hxy : P.pairing.face.SameCycle x y) :
    P.index y ≠ T.opposite (P.index x) := by
  cases hf : T.free (T.kind (P.index x)) with
  | true => exact P.free_sameface_not_opposite hs hb hf hxy
  | false => exact P.frozen_sameface_not_opposite B hm hf hxy
end HyperbolicObstruction.PictureSwitch.WalkPicture

end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_WalkMultiplicity
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSix _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
universe u
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable {A : Type*} [AddCommGroup A]
variable (c : Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A)
variable (P : WalkPicture.{u} (walkTarget n w d c hc f))
variable (select : P.Face → Bool)

abbrev RawPositionSide (p : RawPosition n w d) := {x : P.Dart // select (P.faceClass x) = true ∧
  isLetter n w (walkLabel n w d (P.index x)) = true ∧ rawPosition n w d (P.index x) = p}

abbrev KindFace (k : WalkKind n w d) := {F : P.Face // select F = true ∧ P.faceKind F = k}

lemma raw_kind (s : WalkStep n w d) : walkKind n w d s =
    walkKind n w d (rawRepresentative n w d (rawPosition n w d s)) := by
  rcases s with ⟨a,e⟩ | ⟨g,o,i⟩
  · rfl
  · rcases g with g | (q | q) <;> rfl

end HyperbolicObstruction.ConeSkeleton
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

abbrev InternalSide := {x : X // raw x ∧ selected x ∧ selected (P.edge x)}

lemma number_ne (x : X) : P.number x ≠ P.number (P.edge x) := by
  intro h
  exact P.edge_ne x ((Fintype.equivFin X).injective h).symm

def contactSide : P.Contact selected raw ⊕ P.Contact selected raw → P.InternalSide selected raw
  | .inl x => ⟨x.val,x.property.1,x.property.2.1,x.property.2.2.1⟩
  | .inr x => ⟨P.edge x.val,(hraw x.val).mpr x.property.1,x.property.2.2.1,by
      rw [P.edge_edge]; exact x.property.2.1⟩

lemma contactSide_injective : Function.Injective (P.contactSide selected raw hraw) := by
  intro x y he
  have hv := congrArg Subtype.val he
  rcases x with x | x <;> rcases y with y | y <;> dsimp only [contactSide] at hv
  · exact congrArg Sum.inl (Subtype.ext hv)
  · change x.val = P.edge y.val at hv
    have h1 := x.property.2.2.2
    rw [hv,P.edge_edge] at h1
    exact False.elim (not_lt_of_ge (le_of_lt y.property.2.2.2) h1)
  · change P.edge x.val = y.val at hv
    have h1 := y.property.2.2.2
    rw [← hv,P.edge_edge] at h1
    exact False.elim (not_lt_of_ge (le_of_lt x.property.2.2.2) h1)
  · exact congrArg Sum.inr (Subtype.ext (P.edge.injective hv))

lemma contactSide_surjective : Function.Surjective (P.contactSide selected raw hraw) := by
  intro y
  by_cases hh : P.number y.val < P.number (P.edge y.val)
  · exact ⟨.inl ⟨y.val,y.property.1,y.property.2.1,y.property.2.2,hh⟩,rfl⟩
  · have hg : P.number (P.edge y.val) < P.number y.val :=
      lt_of_le_of_ne (le_of_not_gt hh) (P.number_ne y.val).symm
    refine ⟨.inr ⟨P.edge y.val,(hraw y.val).mpr y.property.1,y.property.2.2,?_,?_⟩,?_⟩
    · rw [P.edge_edge]; exact y.property.2.1
    · rw [P.edge_edge]; exact hg
    · apply Subtype.ext; exact P.edge_edge y.val

include hraw in
lemma internal_card : Fintype.card (P.InternalSide selected raw) =
    2 * Fintype.card (P.Contact selected raw) := by
  have h := Fintype.card_congr (Equiv.ofBijective _
    ⟨P.contactSide_injective selected raw hraw,P.contactSide_surjective selected raw hraw⟩)
  simpa only [Fintype.card_sum,two_mul] using h.symm

def boundaryInternalSide : P.BoundarySide selected raw ⊕ P.InternalSide selected raw →
    SelectedSide selected raw
  | .inl x => ⟨x.val,x.property.1,x.property.2.1⟩
  | .inr x => ⟨x.val,x.property.1,x.property.2.1⟩

omit [Fintype X] in
lemma boundaryInternalSide_bijective : Function.Bijective (P.boundaryInternalSide selected raw) := by
  constructor
  · intro x y he
    have hv := congrArg Subtype.val he
    rcases x with x | x <;> rcases y with y | y <;> dsimp only [boundaryInternalSide] at hv
    · exact congrArg Sum.inl (Subtype.ext hv)
    · exact False.elim (x.property.2.2 (by rw [hv]; exact y.property.2.2))
    · exact False.elim (y.property.2.2 (by rw [← hv]; exact x.property.2.2))
    · exact congrArg Sum.inr (Subtype.ext hv)
  · intro x
    by_cases h : selected (P.edge x.val)
    · exact ⟨.inr ⟨x.val,x.property.1,x.property.2,h⟩,rfl⟩
    · exact ⟨.inl ⟨x.val,x.property.1,x.property.2,h⟩,rfl⟩

include hraw in
/-- Exact side counting for an arbitrary selection of faces: each kept
internal pairing uses two selected sides, each boundary side one. -/
theorem boundary_contacts_eq : Fintype.card (P.BoundarySide selected raw) +
    2 * Fintype.card (P.Contact selected raw) = Fintype.card (SelectedSide selected raw) := by
  rw [← P.internal_card selected raw hraw,← Fintype.card_sum]
  exact Fintype.card_congr (Equiv.ofBijective _ (P.boundaryInternalSide_bijective selected raw))

end HyperbolicObstruction.PictureSwitch.PictureMap
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_ContactCapacity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch.PictureMap
attribute [local instance] Classical.propDecidable
variable {X Y : Type*} [Fintype X] (P : PictureMap X)
variable (selected raw : X → Prop) (hraw : ∀ x, raw (P.edge x) ↔ raw x)
variable (position : X → Y) (p : Y)

abbrev IncidentContact := {e : P.Contact selected raw // position e.val = p ∨ position (P.edge e.val) = p}
abbrev PositionSide := {x : SelectedSide selected raw // position x.val = p}

def contactEnd (e : P.IncidentContact selected raw position p) :
    P.Contact selected raw ⊕ P.Contact selected raw :=
  if position e.val.val = p then .inl e.val else .inr e.val

lemma contactEnd_position (e : P.IncidentContact selected raw position p) :
    position (P.contactSide selected raw hraw (P.contactEnd selected raw position p e)).val = p := by
  unfold contactEnd
  split_ifs with h
  · exact h
  · exact e.property.resolve_left h

lemma contactEnd_injective : Function.Injective (P.contactEnd selected raw position p) := by
  intro e f h
  have hh := congrArg (Sum.elim id id) h
  simp only [contactEnd,apply_ite,Sum.elim_inl,Sum.elim_inr,id_eq,ite_self] at hh
  exact Subtype.ext hh

end HyperbolicObstruction.PictureSwitch.PictureMap
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_FrozenSideExists
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch.PolygonTarget.Boundary
open Equiv Equiv.Perm
variable {C L V : Type*} (B : Boundary C L V)
lemma side_sameCycle (c : C) (o : Bool) (i j : Fin (B.size c)) :
    B.next.SameCycle ⟨c,o,i⟩ ⟨c,o,j⟩ := by
  have hr : (finRotate (B.size c)).SameCycle i j := by
    by_cases hh : 2 ≤ B.size c
    · apply (isCycle_finRotate_of_le hh).sameCycle
      · exact mem_support.mp (by rw [support_finRotate_of_le hh]; exact Finset.mem_univ i)
      · exact mem_support.mp (by rw [support_finRotate_of_le hh]; exact Finset.mem_univ j)
    · have hij : i = j := Fin.ext (by omega)
      exact hij.sameCycle _
  cases o
  · apply sameCycle_inv.mp
    apply semiconj_perm_sameCycle (f := finRotate (B.size c))
      (j := fun i => (⟨c,false,i⟩ : B.Side)) _ hr
    intro i
    rfl
  · apply semiconj_perm_sameCycle (f := finRotate (B.size c))
      (j := fun i => (⟨c,true,i⟩ : B.Side)) _ hr
    intro i
    rfl
end HyperbolicObstruction.PictureSwitch.PolygonTarget.Boundary

end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_IndexedPayment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
open scoped BigOperators
namespace HyperbolicObstruction.FanLink.IndexedFanData
attribute [local instance] Classical.propDecidable
variable {I F O : Type*} {L : I → Type*} [Fintype I] [Fintype F] [Fintype O]
  [∀ z, Fintype (L z)] (D : IndexedFanData I F O L)

/-- Outgoing and incoming exceptional-port incidences of selected top turns. -/
abbrev PaymentIndex := {p : (Σ z,L z) × Bool //
  (∃ f, D.mark p.1.1 p.1.2 = Mark.top f) ∧
    D.line p.1.1 (if p.2 then p.1.2 else D.next p.1.1 p.1.2) = false}

end HyperbolicObstruction.FanLink.IndexedFanData
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_MacroExceptional
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSix _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HyperbolicObstruction.ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)

def exceptionalMacro : MacroGraph.graph.Dart :=
  ⟨(MacroGraph.point 3,MacroGraph.exceptional),rfl⟩

lemma macro_exceptional_port (a : Top n w) (e : MacroGraph.graph.Dart)
    (ha : isApex n w (start n w (macroStep n w a e.adj)) = true)
    (hp : dartPart n w (macroStep n w a e.adj) = false) : e = exceptionalMacro := by
  have ha := (congrArg (isApex n w) (macroStep_start n w a e.adj)).symm.trans ha
  rcases e with ⟨⟨u,v⟩,h⟩
  rcases u with ((i|l)|⟨⟩)
  · rcases v with ((j|m)|⟨⟩)
    · cases h
    · cases hp
    · have hi : i = 3 := h
      subst i
      rfl
  · cases ha
  · cases ha

lemma exceptional_successor (e : MacroGraph.graph.Dart) (hf : e.fst = MacroGraph.exceptional)
    (hn : e ≠ exceptionalMacro.symm) : e = looseMacro := by
  rcases e with ⟨⟨u,v⟩,h⟩
  change u = MacroGraph.exceptional at hf
  subst u
  rcases v with ((i|l)|⟨⟩)
  · have hi : i = 3 := h
    subst i
    exact False.elim (hn rfl)
  · have hl : l = 4 := h
    subst l
    rfl
  · cases h

lemma exceptional_predecessor (e : MacroGraph.graph.Dart) (hf : e.snd = MacroGraph.exceptional)
    (hn : e ≠ exceptionalMacro) : e = looseMacro.symm := by
  have hh := exceptional_successor e.symm hf (fun he => hn (by
    have ht := congrArg SimpleGraph.Dart.symm he
    exact ht))
  exact congrArg SimpleGraph.Dart.symm hh

universe u

end HyperbolicObstruction.ConeSkeleton
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_IndexedFanCards
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
open scoped BigOperators
namespace HyperbolicObstruction.FanLink.IndexedFanData
attribute [local instance] Classical.propDecidable
variable {I F O : Type*} {L : I → Type*} [Fintype I] [Fintype F] [Fintype O]
  [∀ z, Fintype (L z)] (D : IndexedFanData I F O L)

abbrev TurnIndex := {p : Σ z,L z // ∃ f, D.mark p.1 p.2 = Mark.top f}
abbrev TriangleIndex := {p : Σ z,L z // D.mark p.1 p.2 = Mark.triangle}

abbrev BoundaryIndex := {p : Σ z,L z // (D.state p.1 p.2).active ≠
  (D.state p.1 (D.next p.1 p.2)).active}

end HyperbolicObstruction.FanLink.IndexedFanData
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_WalkRadialBoundary
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSix _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


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
variable (P : WalkPicture.{u} (walkTarget n w d c hc f))
variable (select : P.Face → Bool)

def walkSelected (x : P.Dart) := select (P.faceClass x)
def walkRadial (x : P.Dart) : Prop := isLetter n w (walkLabel n w d (P.index x)) = false

abbrev RadialBoundarySide := P.pairing.BoundarySide (fun x => walkSelected n w d c hc f P select x = true)
  (walkRadial n w d c hc f P)

variable (hs : P.Simple) (hm : P.FrozenMapped (walkFrozenTarget n w d c hc f))
  (hred : P.FullyReduced) (hrad : P.RadialInjective (isApex n w))

abbrev AllBoundaryIndex := Σ b : Fan n w,
  (indexedFanData n w d c hc f P select b hs hm hred hrad).BoundaryIndex

end HyperbolicObstruction.ConeSkeleton
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_WalkPayment
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSix _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


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
variable (P : WalkPicture.{u} (walkTarget n w d c hc f))
variable (select : P.Face → Bool)

variable (hs : P.Simple) (hb : P.NoBigon)
  (hm : P.FrozenMapped (walkFrozenTarget n w d c hc f))
  (hred : P.FullyReduced) (hrad : P.RadialInjective (isApex n w))

abbrev AllPaymentIndex := Σ b : Fan n w,
  (indexedFanData n w d c hc f P select b hs hm hred hrad).PaymentIndex

end HyperbolicObstruction.ConeSkeleton
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_WalkTriangleTransport
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSix _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop
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
variable (hs : P.Simple) (hm : P.FrozenMapped (walkFrozenTarget n w d c hc f))
  (hred : P.FullyReduced) (hrad : P.RadialInjective (isApex n w))

abbrev AllTriangleIndex := Σ b : Fan n w,
  (indexedFanData n w d c hc f P select b hs hm hred hrad).TriangleIndex

end HyperbolicObstruction.ConeSkeleton
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_ActualRawCount
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
variable (hs : P.Simple) (hm : P.FrozenMapped (walkFrozenTarget n w d c hc f))
  (hred : P.FullyReduced) (hrad : P.RadialInjective (isApex n w))

abbrev DecorationSideIndex := Σ k : Square n w ⊕ Six n d,
  KindFace n w d c hc f P select (.inr (.inr k)) × Fin ((frozenBoundary n w d).size (.inr k))

abbrev RawAccountIndex := AllPaymentIndex n w d c hc f P select hs hm hred hrad ⊕
  (AllTriangleIndex n w d c hc f P select hs hm hred hrad ⊕
    DecorationSideIndex n w d c hc f P select)

end HyperbolicObstruction.ConeSkeleton
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_ExteriorTarget
attribute [-instance] _root_.OAI.HyperbolicObstruction.PictureSwitch.WalkPicture.instFintypeFace
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
namespace WalkCellTarget
variable (T : WalkCellTarget S C W L V A)
variable (ell : ℕ) (hell : 0 < ell) (word : Fin ell → L)
  (closed : ∀ i, T.start (word (finRotate ell i)) = T.start (T.rev (word i)))

/-- The outside word is an arbitrary closed edge path, not an attaching word
of a cell of the target. Its second orientation is solely bookkeeping. -/
def exteriorBoundary : PolygonTarget.Boundary Unit L V where
  size := fun _ => ell
  positive := fun _ => hell
  label := fun _ => word
  start := T.start
  rev := T.rev
  inv := T.rev_rev
  closed := fun _ => closed

abbrev ExteriorSide := (T.exteriorBoundary ell hell word closed).Side

/-- Enlarge the indexing types by one protected exterior polygon. Only the
original target's free cone-walk cells may be split. All added side weights
are zero, so the chain is exactly the interior cellular chain. -/
def withExterior : WalkCellTarget (S ⊕ T.ExteriorSide ell hell word closed)
    (C ⊕ Unit) (W ⊕ V) L V A where
  kind := Sum.elim (Sum.inl ∘ T.kind) (fun _ => .inr ())
  free := Sum.elim T.free (fun _ => false)
  front := Sum.elim (Sum.inl ∘ T.front)
    (fun s => .inr (T.start ((T.exteriorBoundary ell hell word closed).sideLabel s)))
  back := Sum.elim (Sum.inl ∘ T.back)
    (fun s => .inr (T.start (T.rev ((T.exteriorBoundary ell hell word closed).sideLabel s))))
  vertex := Sum.elim T.vertex id
  label := Sum.elim T.label (T.exteriorBoundary ell hell word closed).sideLabel
  start := T.start
  rev := T.rev
  rev_rev := T.rev_rev
  front_label := by rintro (s | s); exact T.front_label s; rfl
  back_label := by rintro (s | s); exact T.back_label s; rfl
  opposite := Sum.map T.opposite (T.exteriorBoundary ell hell word closed).opposite
  opposite_kind := by rintro (s | s); exact congrArg Sum.inl (T.opposite_kind s); rfl
  opposite_front := by
    rintro (s | s)
    · exact congrArg Sum.inl (T.opposite_front s)
    · exact congrArg Sum.inr (congrArg T.start ((T.exteriorBoundary ell hell word closed).edge_opposite s))
  opposite_back := by
    rintro (s | s)
    · exact congrArg Sum.inl (T.opposite_back s)
    · dsimp only [Sum.map_inr,Sum.elim_inr]
      rw [(T.exteriorBoundary ell hell word closed).edge_opposite]
      exact congrArg Sum.inr (congrArg T.start (T.rev_rev _))
  opposite_label := by
    rintro (s | s)
    · exact T.opposite_label s
    · exact (T.exteriorBoundary ell hell word closed).edge_opposite s
  loopless := by
    rintro (s | s) h
    · exact Sum.inl_injective.ne (T.loopless s h)
    · cases h
  simple := by
    rintro (s | s) (t | t) h hk hf hb
    · exact congrArg Sum.inl (T.simple s t h (Sum.inl.inj hk) (Sum.inl.inj hf) (Sum.inl.inj hb))
    · cases hk
    · cases h
    · cases h
  weight := Sum.elim T.weight (fun _ => 0)
  opposite_weight := by
    rintro (s | s) h
    · exact T.opposite_weight s h
    · cases h

variable (B : FrozenTarget T)
def exteriorFrozen : FrozenTarget (T.withExterior ell hell word closed) where
  next := Equiv.sumCongr B.next (T.exteriorBoundary ell hell word closed).next
  reverse := Equiv.sumCongr B.reverse (T.exteriorBoundary ell hell word closed).opposite
  reverse_eq := by rintro (s | s); exact congrArg Sum.inl (B.reverse_eq s); rfl
  reverse_sq := by
    apply Equiv.ext
    rintro (s | s)
    · have h := congrArg (fun p : Perm S => p s) B.reverse_sq
      exact congrArg Sum.inl h
    · have h := congrArg (fun p : Perm (T.ExteriorSide ell hell word closed) => p s)
        (T.exteriorBoundary ell hell word closed).opposite_sq
      exact congrArg Sum.inr h
  reverse_next := by
    rintro (s | s)
    · exact congrArg Sum.inl (B.reverse_next s)
    · exact congrArg Sum.inr ((T.exteriorBoundary ell hell word closed).reverse_next s)
  opposite_cycle := by
    let F : S ⊕ T.ExteriorSide ell hell word closed → Quotient (SameCycle.setoid B.next) ⊕ Bool :=
      Sum.elim (Sum.inl ∘ Quotient.mk _) (fun s => .inr s.2.1)
    have hf : ∀ s, F ((Equiv.sumCongr B.next (T.exteriorBoundary ell hell word closed).next) s) = F s := by
      rintro (s | s)
      · exact congrArg Sum.inl (Quotient.sound (SameCycle.rfl (f := B.next) (x := s)).apply_left)
      · rfl
    rintro (s | ⟨a,b,i⟩) h
    · have he := sameCycle_one.mp (semiconj_perm_sameCycle (t := (1 : Perm (Quotient (SameCycle.setoid B.next) ⊕ Bool))) hf h)
      exact B.opposite_cycle s (Quotient.exact (Sum.inl.inj he))
    · have he := sameCycle_one.mp (semiconj_perm_sameCycle (t := (1 : Perm (Quotient (SameCycle.setoid B.next) ⊕ Bool))) hf h)
      cases b <;> cases (Sum.inr.inj he)
  opposite_weight := by
    rintro (s | s)
    · exact B.opposite_weight s
    · exact add_zero _

end WalkCellTarget
end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_PolygonBoundaryList
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch.PolygonTarget.Boundary
open HyperbolicObstruction.PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {C L V : Type*} (B : PolygonTarget.Boundary C L V)

def attachingWord (c : C) : List L := List.ofFn (B.label c)

variable (ell : ℕ) (hell : 0 < ell) (word : Fin ell → L)
  (closed : ∀ i, B.start (word (finRotate ell i)) = B.start (B.rev (word i)))

/-- A single additional outside polygon, with a separate cell index. -/
def withOutside : PolygonTarget.Boundary (C ⊕ Unit) L V where
  size := Sum.elim B.size (fun _ => ell)
  positive := by rintro (c | c); exact B.positive c; exact hell
  label := fun c => match c with | .inl c => B.label c | .inr _ => word
  start := B.start
  rev := B.rev
  inv := B.inv
  closed := by rintro (c | c) i; exact B.closed c i; exact closed i

end HyperbolicObstruction.PictureSwitch.PolygonTarget.Boundary
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_ConeExteriorWalk
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSix _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop _root_.OAI.HyperbolicObstruction.PictureSwitch.WalkPicture.instFintypeFace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HyperbolicObstruction.ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable (ell : ℕ) (hell : 0 < ell) (word : Fin ell → Dart n w)
  (closed : ∀ i, start n w (word (finRotate ell i)) = start n w (rev n w (word i)))
variable {A : Type*} [AddCommGroup A]
variable (c : Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A)

abbrev OutsideCellSide := ((boundary n w d).withOutside ell hell word closed).Side
abbrev exteriorWalkTarget := (walkTarget n w d c hc f).withExterior ell hell word closed
abbrev exteriorWalkFrozen := (walkTarget n w d c hc f).exteriorFrozen ell hell word closed
  (walkFrozenTarget n w d c hc f)

universe u

end HyperbolicObstruction.ConeSkeleton
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

@[simp] lemma word_length (r : G.Dart → A × Bool) {u v : V} (p : G.Walk u v) :
    (word r p).length = p.length := by simp [word]

end HyperbolicObstruction.GraphWordFilling
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_CoreWordGraph
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeOutgoing _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSix _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop _root_.OAI.HyperbolicObstruction.CoreGeometry.instDecidableIsFanVertex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HyperbolicObstruction.CoreWordGraph
open IncidenceTemplate CoreGeometry MasterGraph LetterPresentation SimpleGraph
variable (S : Finset IncidenceTemplate.Edge)

def adj : CoreGeometry.Vertex → CoreGeometry.Vertex → Prop
  | .inl r,.inr l => ∃ e : IncidenceTemplate.Edge, e.val = (r,l) ∧ e ∈ S
  | .inr l,.inl r => ∃ e : IncidenceTemplate.Edge, e.val = (r,l) ∧ e ∈ S
  | _,_ => False

def graph : SimpleGraph CoreGeometry.Vertex where
  Adj := adj S
  symm := ⟨by intro a b h; cases a <;> cases b <;> exact h⟩
  loopless := ⟨by intro a; cases a <;> exact id⟩

lemma core_adj {a b : CoreGeometry.Vertex} (h : (graph S).Adj a b) :
    CoreGeometry.Adjacent a b := by
  cases a <;> cases b <;> try exact h.elim
  all_goals
    obtain ⟨e,he,hm⟩ := h
    have hh := e.property
    rw [he] at hh
    exact hh

def label (n : ℕ) (l : Field → Alphabet n) (e : (graph S).Dart) : Alphabet n :=
  stepLetter n l (coreStep (core_adj S e.adj))

end HyperbolicObstruction.CoreWordGraph
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_FanRoute
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.CoreWordGraph
open IncidenceTemplate CoreGeometry SimpleGraph

lemma base_to_port (i l : Fin 7) (h : IsFanVertex i (.inr l)) :
    (graph (fan i)).Adj (.inl (base i)) (.inr l) := by
  have cert : ∀ i l : Fin 7, IsFanVertex i (.inr l) →
      ∃ e : IncidenceTemplate.Edge, e.val = (base i,l) ∧ e ∈ fan i := by decide
  exact cert i l h

lemma common_port (i : Fin 7) : IsFanVertex i (.inr (common i)) := by
  have cert : ∀ i : Fin 7, IsFanVertex i (.inr (common i)) := by decide
  exact cert i

lemma common_to_rep (i : Fin 7) (r : Fin 11) (h : IsFanVertex i (.inl r)) :
    (graph (fan i)).Adj (.inr (common i)) (.inl r) := by
  have cert : ∀ (i : Fin 7) (r : Fin 11), IsFanVertex i (.inl r) →
      ∃ e : IncidenceTemplate.Edge, e.val = (r,common i) ∧ e ∈ fan i := by decide
  exact cert i r h

/-- The source's fixed fan paths, length at most two, in the actual indexed
fan before its edge labels are identified in the bouquet. -/
def fanRoute (i : Fin 7) (v : FanVertex i) : (graph (fan i)).Walk (.inl (base i)) v.val := by
  rcases v with ⟨r|l,h⟩
  · exact .cons (base_to_port i (common i) (common_port i)) (.cons (common_to_rep i r h) .nil)
  · exact .cons (base_to_port i l h) .nil

end HyperbolicObstruction.CoreWordGraph
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_SimpleLetterPresentation
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeOutgoing _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSix _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop _root_.OAI.HyperbolicObstruction.CoreGeometry.instDecidableIsFanVertex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HyperbolicObstruction.LetterPresentation
open IncidenceTemplate CoreGeometry MasterGraph SimpleGraph
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)

/-- Exactly the source03 finite presentation: all simple cycles of each
included fan and compatible included top graph, plus the two decorations.
The underlying template graph is not quotiented by its random labels. -/
inductive SimpleWordRelator : List (Alphabet n) → Prop
  | fan (l : Field → Alphabet n) (i : Fin 7)
      (present : w (TableModel.row rowSupport l (.inl i)) = true)
      (v : CoreGeometry.Vertex) (p : (CoreWordGraph.graph (fan i)).Walk v v)
      (simple : p.IsCycle) :
      SimpleWordRelator (GraphWordFilling.word (CoreWordGraph.label (fan i) n l) p)
  | top (l : Field → Alphabet n)
      (present : w (TableModel.row rowSupport l (.inr (.inl ()))) = true)
      (fans : ∀ i : Fin 7, w (TableModel.row rowSupport l (.inl i)) = true)
      (v : CoreGeometry.Vertex) (p : (CoreWordGraph.graph Finset.univ).Walk v v)
      (simple : p.IsCycle) :
      SimpleWordRelator (GraphWordFilling.word (CoreWordGraph.label Finset.univ n l) p)
  | square (l : Field → Alphabet n) (τ : TwoPath)
      (present : w (TableModel.row rowSupport l (.inr (.inr τ))) = true) :
      SimpleWordRelator (literalSquare n l τ)
  | six (x : Fin 6 → Alphabet n) (present : d x = true) : SimpleWordRelator (List.ofFn x)

end HyperbolicObstruction.LetterPresentation
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_ConeLetterCollapse
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSix _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HyperbolicObstruction.ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation SimpleGraph
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)

def radialWord (f : Fan n w) (v : FanVertex f.val.1) : List (Alphabet n) :=
  GraphWordFilling.word (CoreWordGraph.label (fan f.val.1) n (extendRow n (.inl f.val.1) f.val.2))
    (CoreWordGraph.fanRoute f.val.1 v)

/-- Literal radial-path collapse of the actual cone one-skeleton. It fixes
all letter edges, and does not identify two indexed radial positions. -/
def collapse : Dart n w → List (Alphabet n)
  | (.inl a,b) => [(a,b)]
  | (.inr ⟨f,v⟩,true) => radialWord n w f v
  | (.inr ⟨f,v⟩,false) => FreeGroup.invRev (radialWord n w f v)

end HyperbolicObstruction.ConeSkeleton
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_MacroGroup
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSix _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HyperbolicObstruction
namespace MacroGraph

lemma route_exists (v : Vertex) : Nonempty (graph.Walk (point 0) v) := by
  rcases v with ((i|l)|⟨⟩)
  · fin_cases i
    · exact ⟨SimpleGraph.Walk.nil⟩
    · exact ⟨(SimpleGraph.Walk.cons (show graph.Adj (point 0) (line 2) from by simp only [graph]; decide) (SimpleGraph.Walk.cons (show graph.Adj (line 2) (point 1) from by simp only [graph]; decide) SimpleGraph.Walk.nil))⟩
    · exact ⟨(SimpleGraph.Walk.cons (show graph.Adj (point 0) (line 1) from by simp only [graph]; decide) (SimpleGraph.Walk.cons (show graph.Adj (line 1) (point 2) from by simp only [graph]; decide) SimpleGraph.Walk.nil))⟩
    · exact ⟨(SimpleGraph.Walk.cons (show graph.Adj (point 0) (line 6) from by simp only [graph]; decide) (SimpleGraph.Walk.cons (show graph.Adj (line 6) (point 3) from by simp only [graph]; decide) SimpleGraph.Walk.nil))⟩
    · exact ⟨(SimpleGraph.Walk.cons (show graph.Adj (point 0) (line 2) from by simp only [graph]; decide) (SimpleGraph.Walk.cons (show graph.Adj (line 2) (point 4) from by simp only [graph]; decide) SimpleGraph.Walk.nil))⟩
    · exact ⟨(SimpleGraph.Walk.cons (show graph.Adj (point 0) (line 1) from by simp only [graph]; decide) (SimpleGraph.Walk.cons (show graph.Adj (line 1) (point 5) from by simp only [graph]; decide) SimpleGraph.Walk.nil))⟩
    · exact ⟨(SimpleGraph.Walk.cons (show graph.Adj (point 0) (line 6) from by simp only [graph]; decide) (SimpleGraph.Walk.cons (show graph.Adj (line 6) (point 6) from by simp only [graph]; decide) SimpleGraph.Walk.nil))⟩
  · fin_cases l
    · exact ⟨(SimpleGraph.Walk.cons (show graph.Adj (point 0) (line 1) from by simp only [graph]; decide) (SimpleGraph.Walk.cons (show graph.Adj (line 1) (point 2) from by simp only [graph]; decide) (SimpleGraph.Walk.cons (show graph.Adj (point 2) (line 0) from by simp only [graph]; decide) SimpleGraph.Walk.nil)))⟩
    · exact ⟨(SimpleGraph.Walk.cons (show graph.Adj (point 0) (line 1) from by simp only [graph]; decide) SimpleGraph.Walk.nil)⟩
    · exact ⟨(SimpleGraph.Walk.cons (show graph.Adj (point 0) (line 2) from by simp only [graph]; decide) SimpleGraph.Walk.nil)⟩
    · exact ⟨(SimpleGraph.Walk.cons (show graph.Adj (point 0) (line 1) from by simp only [graph]; decide) (SimpleGraph.Walk.cons (show graph.Adj (line 1) (point 5) from by simp only [graph]; decide) (SimpleGraph.Walk.cons (show graph.Adj (point 5) (line 3) from by simp only [graph]; decide) SimpleGraph.Walk.nil)))⟩
    · exact ⟨(SimpleGraph.Walk.cons (show graph.Adj (point 0) (line 1) from by simp only [graph]; decide) (SimpleGraph.Walk.cons (show graph.Adj (line 1) (point 2) from by simp only [graph]; decide) (SimpleGraph.Walk.cons (show graph.Adj (point 2) (line 4) from by simp only [graph]; decide) SimpleGraph.Walk.nil)))⟩
    · exact ⟨(SimpleGraph.Walk.cons (show graph.Adj (point 0) (line 1) from by simp only [graph]; decide) (SimpleGraph.Walk.cons (show graph.Adj (line 1) (point 5) from by simp only [graph]; decide) (SimpleGraph.Walk.cons (show graph.Adj (point 5) (line 5) from by simp only [graph]; decide) SimpleGraph.Walk.nil)))⟩
    · exact ⟨(SimpleGraph.Walk.cons (show graph.Adj (point 0) (line 6) from by simp only [graph]; decide) SimpleGraph.Walk.nil)⟩
  · exact ⟨(SimpleGraph.Walk.cons (show graph.Adj (point 0) (line 6) from by simp only [graph]; decide) (SimpleGraph.Walk.cons (show graph.Adj (line 6) (point 3) from by simp only [graph]; decide) (SimpleGraph.Walk.cons (show graph.Adj (point 3) (exceptional) from by simp only [graph]; decide) SimpleGraph.Walk.nil)))⟩

def route (v : Vertex) : graph.Walk (point 0) v := Classical.choice (route_exists v)

end MacroGraph
namespace ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)

lemma macro_darts (a : Top n w) {u : MacroGraph.Vertex}
    (p : MacroGraph.graph.Walk u u) (hp : p.IsCycle) :
    p.darts.map (fun e => macroStep n w a e.adj) = List.ofFn (topSide n w (a,⟨u,⟨p,hp⟩⟩)) := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    have hil : i < p.length := by simpa using hi
    have hid : i < p.darts.length := by simpa only [List.length_map] using hi
    simp only [List.getElem_map,List.getElem_ofFn,topSide]
    have he : p.darts[i]'hid = ⟨⟨p.getVert i,p.getVert (finRotate p.length ⟨i,hil⟩).val⟩,
        (MacroGraph.ofCycle p hp).adjacent ⟨i,hil⟩⟩ := by
      rw [SimpleGraph.Walk.darts_getElem_eq_getVert i hid]
      apply SimpleGraph.Dart.ext
      apply Prod.ext
      · rfl
      · change p.getVert (i+1) = p.getVert (finRotate p.length ⟨i,hil⟩).val
        have hn : 0 < p.length := lt_of_lt_of_le (by decide : 0 < 3) hp.three_le_length
        have : NeZero p.length := ⟨by omega⟩
        rw [finRotate_apply,Fin.val_add]
        have hone : ((1 : Fin p.length) : ℕ) = 1 := by
          change 1 % p.length = 1
          exact Nat.mod_eq_of_lt (by have := hp.three_le_length; omega)
        rw [hone]
        by_cases hh : i+1 < p.length
        · rw [Nat.mod_eq_of_lt hh]
        · have he : i+1 = p.length := by simp only [List.length_map,SimpleGraph.Walk.length_darts] at hi; omega
          rw [he,Nat.mod_self,SimpleGraph.Walk.getVert_length,SimpleGraph.Walk.getVert_zero]
    exact congrArg (fun e : MacroGraph.graph.Dart => macroStep n w a e.adj) he

variable {H : Type*} [_root_.Group H] (c : Dart n w → H)
  (hc : ∀ e, c (rev n w e) = (c e)⁻¹)
  (hcell : ∀ a : Cell n w d, (List.ofFn (fun i => c (side n w d a i))).prod = 1)

def macroValue (a : Top n w) : MacroGraph.graph.Dart → H := fun e => c (macroStep n w a e.adj)
include hc in
lemma macroValue_symm (a : Top n w) (e : MacroGraph.graph.Dart) :
    macroValue n w c a e.symm = (macroValue n w c a e)⁻¹ := by
  exact (congrArg c (macroStep_reverse n w a e.adj)).trans (hc _)

include hcell in
lemma macro_cycle (a : Top n w) (u : MacroGraph.Vertex)
    (p : MacroGraph.graph.Walk u u) (hp : p.IsCycle) :
    GraphGroupWalk.eval (macroValue n w c a) p = 1 := by
  have hf := hcell (.inr (.inl (a,⟨u,⟨p,hp⟩⟩)))
  change (List.ofFn (fun i => c (topSide n w (a,⟨u,⟨p,hp⟩⟩) i))).prod = 1 at hf
  have hm := congrArg (fun l : List (Dart n w) => (l.map c).prod) (macro_darts n w a p hp)
  have hh : ((List.ofFn (topSide n w (a,⟨u,⟨p,hp⟩⟩))).map c).prod = 1 := by
    simpa only [List.map_ofFn,Function.comp_def] using hf
  change (List.map (fun e : MacroGraph.graph.Dart => c (macroStep n w a e.adj)) p.darts).prod = 1
  simpa only [List.map_map,Function.comp_def] using hm.trans hh

def macroPotential (a : Top n w) (v : MacroGraph.Vertex) : H :=
  GraphGroupWalk.eval (macroValue n w c a) (MacroGraph.route v)

include hc hcell in
lemma macroPotential_edge (a : Top n w) {u v : MacroGraph.Vertex} (h : MacroGraph.Adjacent u v) :
    macroPotential n w c a u * c (macroStep n w a h) = macroPotential n w c a v := by
  exact GraphGroupWalk.route_edge (macroValue n w c a) (macroValue_symm n w c hc a)
    (macro_cycle n w d c hcell a) (MacroGraph.route u) (MacroGraph.route v) h

end ConeSkeleton
end HyperbolicObstruction
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_ConePresentationGroup
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSix _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HyperbolicObstruction.ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)

/-- The actual indexed polygon words. Radial edges are not silently equated
or turned into extra letter relators. This bouquet presentation has extra
free factors relative to the graph fundamental group, but the original
letter relations still hold in it, which is all the disk producer needs. -/
abbrev PolygonGroup := PresentedGroup (FreeGroup.mk '' Set.range (boundary n w d).attachingWord)

end HyperbolicObstruction.ConeSkeleton
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_FragmentSlots
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSix _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
open scoped BigOperators
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
variable (P : WalkPicture.{u} (walkTarget n w d c hc f)) (select : P.Face → Bool)

abbrev SelectedTopFace := {F : P.Face // select F = true ∧ ∃ a : Top n w, P.faceKind F = .inl a}

end HyperbolicObstruction.ConeSkeleton
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_WalkTopTurns
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSix _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


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
variable (P : WalkPicture.{u} (walkTarget n w d c hc f))

variable (select : P.Face → Bool)

abbrev FaceApexDart (F : SelectedTopFace n w d c hc f P select) :=
  {x : P.Dart // P.faceClass x = F.val ∧ isApex n w (start n w (walkLabel n w d (P.index x))) = true}

end HyperbolicObstruction.ConeSkeleton
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_WalkTurnTransport
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSix _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


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
variable (P : WalkPicture.{u} (walkTarget n w d c hc f))
variable (select : P.Face → Bool)


variable (hs : P.Simple) (hm : P.FrozenMapped (walkFrozenTarget n w d c hc f))
  (hred : P.FullyReduced) (hrad : P.RadialInjective (isApex n w))

abbrev AllTurnIndex := Σ b : Fan n w,
  (indexedFanData n w d c hc f P select b hs hm hred hrad).TurnIndex

end HyperbolicObstruction.ConeSkeleton
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_PictureDual
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
namespace PictureMap
variable {D : Type*} (P : PictureMap D)

/-- Literal rotation-system duality: faces and vertices exchange, while
individual edge-side copies and their pairing are unchanged. -/
def dual : PictureMap D where
  face := P.vertex
  edge := P.edge
  edge_sq := P.edge_sq
  edge_ne := P.edge_ne

@[simp] lemma dual_edge : P.dual.edge = P.edge := rfl
@[simp] lemma dual_face : P.dual.face = P.vertex := rfl
@[simp] lemma dual_vertex : P.dual.vertex = P.face := by
  change (P.face * P.edge) * P.edge = P.face
  rw [mul_assoc,P.edge_sq,mul_one]
@[simp] lemma dual_dual : P.dual.dual = P := by
  cases P
  simp only [dual,vertex,mul_assoc]
  congr 1
  rename_i f e hs hn
  rw [hs,mul_one]

variable [Fintype D]

variable [DecidableEq D]

@[simp] lemma dual_euler : P.dual.euler = P.euler := by
  simp only [euler,dual_vertex,dual_face]
  omega

end PictureMap
end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_PictureTriangulation
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
variable {D : Type*}
namespace PictureMap
variable (M : PictureMap D)

def starEdgeFun : StarDart D → StarDart D
  | .inl x => .inl (M.edge x)
  | .inr (.inl x) => .inr (.inr (M.face x))
  | .inr (.inr x) => .inr (.inl (M.face⁻¹ x))

lemma starEdge_sq (x : StarDart D) : M.starEdgeFun (M.starEdgeFun x) = x := by
  rcases x with x | (x | x) <;> simp only [starEdgeFun,M.edge_edge,Perm.inv_def,
    Equiv.symm_apply_apply,Equiv.apply_symm_apply]

def starEdge : Perm (StarDart D) where
  toFun := M.starEdgeFun
  invFun := M.starEdgeFun
  left_inv := M.starEdge_sq
  right_inv := M.starEdge_sq

/-- A triangular rotation system obtained by starring every face; old edge
copies are preserved, and each old face has a distinct new center. -/
def triangulation : PictureMap (StarDart D) where
  face := starFace
  edge := M.starEdge
  edge_sq := by ext x; exact M.starEdge_sq x
  edge_ne := by
    rintro (x | (x | x)) h
    · exact M.edge_ne x (Sum.inl.inj h)
    · exact Sum.inr_ne_inl (Sum.inr.inj h)
    · exact Sum.inl_ne_inr (Sum.inr.inj h)

@[simp] lemma triangulation_face_left (x : D) :
    M.triangulation.face (.inl x) = .inr (.inl x) := rfl
@[simp] lemma triangulation_face_middle (x : D) :
    M.triangulation.face (.inr (.inl x)) = .inr (.inr x) := rfl
@[simp] lemma triangulation_face_right (x : D) :
    M.triangulation.face (.inr (.inr x)) = .inl x := rfl
@[simp] lemma triangulation_vertex_left (x : D) :
    M.triangulation.vertex (.inl x) = .inr (.inl (M.edge x)) := rfl
@[simp] lemma triangulation_vertex_middle (x : D) :
    M.triangulation.vertex (.inr (.inl x)) = .inl (M.face x) := rfl
@[simp] lemma triangulation_vertex_right (x : D) :
    M.triangulation.vertex (.inr (.inr x)) = .inr (.inr (M.face⁻¹ x)) := rfl

end PictureMap
end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_RelativePartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
open scoped BigOperators
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {X I : Type*} [Fintype X] [DecidableEq X] [Fintype I]
variable (P : PictureMap X) (active : X → Prop) (part : X → I)

abbrev OutsideContact := {x : X // active x ∧ ¬ active (P.edge x)}
instance instFintypeOutsideContact : Fintype (OutsideContact P active) := Fintype.ofFinite _

end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_CoverBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable

/-- Prefix coordinates really close at the last side. This uses the entire
cell relation, including the wraparound endpoint, not a weakened path equation. -/
lemma group_prefix_rotate {G : Type*} [Group G] {m : ℕ} (p : Fin m → G)
    (hp : (List.ofFn p).prod = 1) (i : Fin m) :
    ((List.ofFn p).take ((finRotate m i).val)).prod =
      ((List.ofFn p).take i.val).prod * p i := by
  cases m with
  | zero => exact Fin.elim0 i
  | succ m =>
    have hs := List.prod_take_succ (List.ofFn p) i.val (by simpa only [List.length_ofFn] using i.isLt)
    have he : (List.ofFn p)[i.val] = p i := List.getElem_ofFn (by simpa only [List.length_ofFn] using i.isLt)
    rw [he] at hs
    by_cases hi : i = Fin.last m
    · subst i
      rw [finRotate_apply,Fin.val_add_one,ite_eq_left rfl]
      have hlen : (Fin.last m).val + 1 = (List.ofFn p).length := by simp only [Fin.val_last,List.length_ofFn]
      rw [hlen,List.take_length,hp] at hs
      simpa only [List.take_zero,List.prod_nil] using hs
    · rw [finRotate_apply,Fin.val_add_one,ite_eq_right hi]
      exact hs

end HyperbolicObstruction.ConeSkeleton
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_NormalFaceFilling
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSix _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop _root_.OAI.HyperbolicObstruction.PictureSwitch.WalkPicture.instFintypeFace _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeOutsideContact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HyperbolicObstruction.ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable (ell : ℕ) (hell : 0 < ell) (word : Fin ell → Dart n w)
  (closed : ∀ i, start n w (word (finRotate ell i)) = start n w (rev n w (word i)))
variable {A : Type*} [AddCommGroup A]
variable (c : Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A)
variable (P : WalkPicture.{0} (exteriorWalkTarget n w d ell hell word closed c hc f))

lemma exterior_same_top {x y : P.Dart} {a : Top n w} {e : MacroGraph.graph.Dart}
    (hx : P.index x = .inl (.inl (a,e))) (h : P.pairing.face.SameCycle x y) :
    ∃ e', P.index y = .inl (.inl (a,e')) := by
  have hk := sameCycle_one.mp (semiconj_perm_sameCycle
    (t := (1 : Perm (WalkKind n w d ⊕ Unit))) P.kind h)
  dsimp only [Function.comp_apply] at hk
  rw [hx] at hk
  cases hy : P.index y with
  | inl s =>
    cases s with
    | inl s =>
      rw [hy] at hk
      have hs : a = s.1 := Sum.inl.inj (Sum.inl.inj hk)
      exact ⟨s.2,by rw [hs]⟩
    | inr s => rw [hy] at hk; cases hk
  | inr s => rw [hy] at hk; cases hk

end HyperbolicObstruction.ConeSkeleton
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_NormalDiskArea
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSix _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HyperbolicObstruction.ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch Equiv Equiv.Perm WordPictures
attribute [local instance] Classical.propDecidable
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)

/-- Only locally PROVED fillings are admitted to this auxiliary relator set.
It is used for derivation substitution, not to alter either presentation. -/
def BoundedConeRelator : Set (List (Dart n w)) :=
  {r | ∃ k ≤ 30, Homotopy (SimpleWordRelator n w d) (r.flatMap (collapse n w)) [] k}

end HyperbolicObstruction.ConeSkeleton
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_LetterNormalPicture
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSix _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HyperbolicObstruction.ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable (ell : ℕ) (word : Fin ell → Alphabet n)

theorem letterWordClosed : ∀ i,
    start n w ((letterDart n w ∘ word) (finRotate ell i)) =
    start n w (rev n w ((letterDart n w ∘ word) i)) := by
  intro i
  exact (start_letter n w _).trans (start_letter n w (inverseLetter n _)).symm

end HyperbolicObstruction.ConeSkeleton
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_RelativeApexLocal
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSix _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeOutsideContact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HyperbolicObstruction.ConeSkeleton.RelDisk
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
universe u
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable (ell : ℕ) (hell : 0 < ell) (word : Fin ell → Alphabet n)
variable {A : Type*} [AddCommGroup A]
variable (c : Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A)
abbrev target := exteriorWalkTarget n w d ell hell (letterDart n w ∘ word)
  (letterWordClosed n w ell word) c hc f
abbrev frozen := exteriorWalkFrozen n w d ell hell (letterDart n w ∘ word)
  (letterWordClosed n w ell word) c hc f
variable (P : WalkPicture.{0} (target n w d ell hell word c hc f))

lemma start_link_constant {x y : P.Dart} (h : P.pairing.vertex.SameCycle x y) :
    start n w ((target n w d ell hell word c hc f).label (P.index x)) = start n w ((target n w d ell hell word c hc f).label (P.index y)) := by
  exact (sameCycle_le_of_apply
    (s := Setoid.ker (fun x => start n w ((target n w d ell hell word c hc f).label (P.index x))))
    (fun x => (P.respects.1 x).symm)) h

lemma apex_interior (x : P.Dart)
    (ha : isApex n w (start n w ((target n w d ell hell word c hc f).label (P.index x))) = true) :
    ∃ s, P.index x = .inl s := by
  cases hx : P.index x with
  | inl s => exact ⟨s,rfl⟩
  | inr s =>
    rcases s with ⟨a,o,i⟩
    rw [hx] at ha
    cases o <;> change false = true at ha <;> cases ha

lemma index_edge_previous (hm : P.FrozenMapped (frozen n w d ell hell word c hc f)) (x : P.Dart)
    (hy : (target n w d ell hell word c hc f).free ((target n w d ell hell word c hc f).kind (P.index (P.pairing.vertex x))) = false) :
    P.index (P.pairing.edge x) = (frozen n w d ell hell word c hc f).next⁻¹ (P.index (P.pairing.vertex x)) := by
  have he : (target n w d ell hell word c hc f).free ((target n w d ell hell word c hc f).kind (P.index (P.pairing.edge x))) = false := by
    have hk := P.kind (P.pairing.edge x)
    change (target n w d ell hell word c hc f).kind (P.index (P.pairing.vertex x)) = (target n w d ell hell word c hc f).kind (P.index (P.pairing.edge x)) at hk
    rw [← hk]; exact hy
  apply (frozen n w d ell hell word c hc f).next.injective
  simp only [Perm.inv_def,apply_symm_apply]
  exact (hm.commute ⟨P.pairing.edge x,he⟩).symm

lemma corner_previous (g : FanTriangle n w) (o : Bool) :
    rev n w ((target n w d ell hell word c hc f).label ((frozen n w d ell hell word c hc f).next⁻¹ (.inl (frozenCorner n w d g o)))) = cornerIn n w g o := by
  cases o <;> rfl
lemma corner_reverse (g : FanTriangle n w) (o : Bool) :
    (frozen n w d ell hell word c hc f).next⁻¹ (.inl (frozenCorner n w d g (!o))) = (target n w d ell hell word c hc f).opposite (.inl (frozenCorner n w d g o)) := by
  cases o <;> rfl
lemma corner_label (g : FanTriangle n w) (o : Bool) :
    (target n w d ell hell word c hc f).label (.inl (frozenCorner n w d g o)) = cornerOut n w g o := by
  cases o <;> rfl

lemma corner_ports (hm : P.FrozenMapped (frozen n w d ell hell word c hc f)) {x : P.Dart}
    {g h : FanTriangle n w} {o p : Bool}
    (hx : P.index x = .inl (frozenCorner n w d g o))
    (hy : P.index (P.pairing.vertex x) = .inl (frozenCorner n w d h p)) :
    cornerOut n w g o = cornerIn n w h p := by
  have he : (target n w d ell hell word c hc f).label (P.index (P.pairing.edge x)) = rev n w ((target n w d ell hell word c hc f).label (P.index x)) := P.paired x
  rw [index_edge_previous n w d ell hell word c hc f P hm x (by rw [hy]; rfl),hy,hx,
    corner_label] at he
  have hh := congrArg (rev n w) he
  rw [corner_previous,rev_rev] at hh
  exact hh.symm

lemma corner_no_two_step (hm : P.FrozenMapped (frozen n w d ell hell word c hc f)) (hred : P.FullyReduced) {x : P.Dart}
    {g h : FanTriangle n w} {o p : Bool}
    (hx : P.index x = .inl (frozenCorner n w d g o))
    (hy : P.index (P.pairing.vertex x) = .inl (frozenCorner n w d h p)) :
    P.pairing.vertex (P.pairing.vertex x) ≠ x := by
  intro hh
  have hxy := corner_ports n w d ell hell word c hc f P hm hx hy
  have hyx := corner_ports n w d ell hell word c hc f P hm hy (by rw [hh]; exact hx)
  obtain ⟨rfl,rfl⟩ := reverse_corner_unique n w hxy hyx.symm
  apply hred x
  rw [index_edge_previous n w d ell hell word c hc f P hm x (by rw [hy]; rfl),hy,hx,corner_reverse]

lemma fan_corner {x : P.Dart} {g : FanTriangle n w} {o : Bool} {i : Fin 3}
    (hx : P.index x = .inl (.inr ⟨.inl g,o,i⟩))
    (ha : isApex n w (start n w ((target n w d ell hell word c hc f).label (P.index x))) = true) :
    P.index x = .inl (frozenCorner n w d g o) := by
  rw [hx]
  have hh := apex_side_corner n w d g o i (by rw [hx] at ha; exact ha)
  cases o <;> fin_cases i <;> first | rfl | cases hh

lemma apex_cases (x : P.Dart)
    (ha : isApex n w (start n w ((target n w d ell hell word c hc f).label (P.index x))) = true) :
    (∃ a e, P.index x = .inl (.inl (a,e))) ∨
      ∃ g o, P.index x = .inl (frozenCorner n w d g o) := by
  obtain ⟨s,hx⟩ := apex_interior n w d ell hell word c hc f P x ha
  cases s with
  | inl s => exact Or.inl ⟨s.1,s.2,hx⟩
  | inr s =>
    rcases s with ⟨g,o,i⟩
    rcases g with g | (s | z)
    · exact Or.inr ⟨g,o,fan_corner n w d ell hell word c hc f P hx ha⟩
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

lemma top_adjacent_different (hred : P.FullyReduced) {x : P.Dart}
    {a b : Top n w} {e k : MacroGraph.graph.Dart}
    (hx : P.index x = .inl (.inl (a,e)))
    (hy : P.index (P.pairing.vertex x) = .inl (.inl (b,k)))
    (ha : isApex n w (start n w ((target n w d ell hell word c hc f).label (P.index x))) = true) : a ≠ b := by
  intro hab; subst b
  obtain ⟨j,hj⟩ := exterior_same_top n w d ell hell (letterDart n w ∘ word)
    (letterWordClosed n w ell word) c hc f P hy
    ((SameCycle.rfl (f := P.pairing.face) (x := P.pairing.edge x)).apply_left)
  have hpair := P.paired x
  change (target n w d ell hell word c hc f).label (P.index (P.pairing.edge x)) = rev n w ((target n w d ell hell word c hc f).label (P.index x)) at hpair
  rw [hj,hx] at hpair
  change macroStep n w a j.adj = rev n w (macroStep n w a e.adj) at hpair
  have hj' : macroStep n w a j.symm.adj = macroStep n w a e.adj := by
    exact (macroStep_reverse n w a j.adj).trans
      ((congrArg (rev n w) hpair).trans (rev_rev n w _))
  have he : e = j.symm := macroStep_radial_injective n w a e j.symm
    (by rw [hx] at ha; exact ha) hj'.symm
  have hje : j = e.symm := by rw [he]; rfl
  apply hred x
  rw [hj,hx,hje]
  rfl

lemma top_unique_turn (hs : P.Simple) {x y : P.Dart} {a : Top n w}
    {e : MacroGraph.graph.Dart} (hx : P.index x = .inl (.inl (a,e)))
    (hxy : P.pairing.face.SameCycle x y) (b : Fan n w)
    (hax : start n w ((target n w d ell hell word c hc f).label (P.index x)) = .inr b)
    (hay : start n w ((target n w d ell hell word c hc f).label (P.index y)) = .inr b) : x = y := by
  obtain ⟨k,hk⟩ := exterior_same_top n w d ell hell (letterDart n w ∘ word)
    (letterWordClosed n w ell word) c hc f P hx hxy
  rw [hx] at hax
  rw [hk] at hay
  change start n w (macroStep n w a e.adj) = .inr b at hax
  change start n w (macroStep n w a k.adj) = .inr b at hay
  have hax := (macroStep_start n w a e.adj).symm.trans hax
  have hay := (macroStep_start n w a k.adj).symm.trans hay
  have he : e.fst = k.fst := (macroVertex_at_apex n w a e.fst b hax).trans
    (macroVertex_at_apex n w a k.fst b hay).symm
  apply P.simple_front hs (by rw [hx]; rfl) hxy
  rw [hx,hk]
  exact congrArg Sum.inl (congrArg Sum.inl (Prod.ext rfl he))

lemma apex_no_fixed (hm : P.FrozenMapped (frozen n w d ell hell word c hc f)) (hred : P.FullyReduced) (x : P.Dart)
    (ha : isApex n w (start n w ((target n w d ell hell word c hc f).label (P.index x))) = true) :
    P.pairing.vertex x ≠ x := by
  intro he
  rcases apex_cases n w d ell hell word c hc f P x ha with ⟨a,e,hx⟩ | ⟨g,o,hx⟩
  · exact top_adjacent_different n w d ell hell word c hc f P hred hx (by rw [he]; exact hx) ha rfl
  · have hports := corner_ports n w d ell hell word c hc f P hm hx (by rw [he]; exact hx)
    exact corner_bipartite n w g o (congrArg (dartPart n w) hports)

lemma link_card (hrad : P.RadialInjective (isApex n w)) (a : P.Dart) (b : Fan n w)
    (ha : start n w ((target n w d ell hell word c hc f).label (P.index a)) = .inr b) :
    Fintype.card {x : P.Dart // P.pairing.vertex.SameCycle a x} ≤ 5 := by
  let j : {x : P.Dart // P.pairing.vertex.SameCycle a x} → Outgoing n w b := fun x =>
    ⟨(target n w d ell hell word c hc f).label (P.index x.val),(start_link_constant n w d ell hell word c hc f P x.property).symm.trans ha⟩
  have hj : Function.Injective j := by
    intro x y hxy
    apply Subtype.ext
    apply hrad x.val y.val
    · change isApex n w (start n w ((target n w d ell hell word c hc f).label (P.index x.val))) = true
      rw [← start_link_constant n w d ell hell word c hc f P x.property,ha]; rfl
    · exact x.property.symm.trans y.property
    · exact congrArg Subtype.val hxy
  exact (Fintype.card_le_of_injective j hj).trans (card_outgoing n w b)

lemma vertex_inverse (x : P.Dart) :
    P.pairing.vertex⁻¹ x = P.pairing.edge (P.pairing.face⁻¹ x) := by
  apply P.pairing.vertex.injective
  rw [Perm.inv_def,apply_symm_apply]
  change x = P.pairing.face (P.pairing.edge (P.pairing.edge (P.pairing.face⁻¹ x)))
  rw [P.pairing.edge_edge,Perm.inv_def,apply_symm_apply]

lemma corner_incoming (hm : P.FrozenMapped (frozen n w d ell hell word c hc f))
    {x : P.Dart} {g : FanTriangle n w} {o : Bool}
    (hx : P.index x = .inl (frozenCorner n w d g o)) :
    (target n w d ell hell word c hc f).label (P.index (P.pairing.vertex⁻¹ x)) = cornerIn n w g o := by
  rw [vertex_inverse]
  have hh := P.paired (P.pairing.face⁻¹ x)
  change (target n w d ell hell word c hc f).label (P.index (P.pairing.edge (P.pairing.face⁻¹ x))) =
    rev n w ((target n w d ell hell word c hc f).label (P.index (P.pairing.face⁻¹ x))) at hh
  rw [hh,P.frozen_previous_index (frozen n w d ell hell word c hc f) hm (by rw [hx]; rfl),hx,corner_previous]

lemma triangle_bipartite (hm : P.FrozenMapped (frozen n w d ell hell word c hc f))
    {x : P.Dart} {g : FanTriangle n w} {o : Bool}
    (hx : P.index x = .inl (frozenCorner n w d g o)) :
    dartPart n w ((target n w d ell hell word c hc f).label (P.index x)) ≠
      dartPart n w ((target n w d ell hell word c hc f).label (P.index (P.pairing.vertex⁻¹ x))) := by
  rw [corner_incoming n w d ell hell word c hc f P hm hx,hx,corner_label]
  exact corner_bipartite n w g o

lemma triangle_inverse_no_two (hm : P.FrozenMapped (frozen n w d ell hell word c hc f))
    (hred : P.FullyReduced) {x : P.Dart} {g h : FanTriangle n w} {o p : Bool}
    (hx : P.index x = .inl (frozenCorner n w d g o))
    (hy : P.index (P.pairing.vertex⁻¹ x) = .inl (frozenCorner n w d h p)) :
    P.pairing.vertex⁻¹ (P.pairing.vertex⁻¹ x) ≠ x := by
  intro he
  have hn := corner_no_two_step n w d ell hell word c hc f P hm hred hy
    (by rw [Perm.inv_def,apply_symm_apply]; exact hx)
  rw [Perm.inv_def,apply_symm_apply] at hn
  have hh := congrArg P.pairing.vertex he
  simp only [Perm.inv_def,apply_symm_apply] at hh
  exact hn hh.symm

end HyperbolicObstruction.ConeSkeleton.RelDisk
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_RelativeFanLink
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSix _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeOutsideContact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HyperbolicObstruction.ConeSkeleton.RelDisk
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
universe u
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable (ell : ℕ) (hell : 0 < ell) (word : Fin ell → Alphabet n)
variable {A : Type*} [AddCommGroup A]
variable (c : Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A)
variable (P : WalkPicture.{0} (target n w d ell hell word c hc f))

variable (select : P.Face → Bool) (b : Fan n w)

/-- ALL selected top polygons incident to this fan occurrence, not only those
whose boundary actually visits it. This implements source03's nominal weight. -/
abbrev SelectedTop := {z : P.Face // select z = true ∧ ∃ a : Top n w,
  P.faceKind z = .inl (.inl a) ∧ ∃ i, slot n w a i = b}

/-- Actual source vertices over this fan, represented in the chosen fragment. -/
abbrev ApexInstance := {z : P.Vertex //
  start n w ((target n w d ell hell word c hc f).label (P.index z.out)) = .inr b ∧
    ∃ x, P.vertexClass x = z ∧ select (P.faceClass x) = true}

noncomputable instance instFintypeSelectedTop : Fintype (SelectedTop n w d ell hell word c hc f P select b) := Fintype.ofFinite _
noncomputable instance instFintypeApexInstance : Fintype (ApexInstance n w d ell hell word c hc f P select b) := Fintype.ofFinite _

def selectedOccurrence (F : SelectedTop n w d ell hell word c hc f P select b) : Top n w :=
  F.property.2.choose

lemma selectedOccurrence_kind (F : SelectedTop n w d ell hell word c hc f P select b) :
    P.faceKind F.val = .inl (.inl (selectedOccurrence n w d ell hell word c hc f P select b F)) :=
  F.property.2.choose_spec.1

lemma instance_start (z : ApexInstance n w d ell hell word c hc f P select b) (x : P.Link z.val) :
    start n w ((target n w d ell hell word c hc f).label (P.index x.val)) = .inr b := by
  have hh : P.pairing.vertex.SameCycle z.val.out x.val :=
    P.vertexClass_eq.mp ((P.vertexClass_out _).trans x.property.symm)
  exact (start_link_constant n w d ell hell word c hc f P hh).symm.trans z.property.1

lemma instance_apex (z : ApexInstance n w d ell hell word c hc f P select b) (x : P.Link z.val) :
    isApex n w (start n w ((target n w d ell hell word c hc f).label (P.index x.val))) = true := by
  rw [instance_start n w d ell hell word c hc f P select b z x]; rfl

def selectedTopAt (z : ApexInstance n w d ell hell word c hc f P select b) (x : P.Link z.val)
    (hs : select (P.faceClass x.val) = true)
    (ht : ∃ a e, P.index x.val = .inl (.inl (a,e))) : SelectedTop n w d ell hell word c hc f P select b := by
  refine ⟨P.faceClass x.val,hs,?_⟩
  obtain ⟨a,e,hx⟩ := ht
  refine ⟨a,?_,?_⟩
  · change (target n w d ell hell word c hc f).kind (P.index x.val) = .inl (.inl a)
    rw [hx]; rfl
  · apply macroVertex_fan_slot n w b a e.fst
    have hh := instance_start n w d ell hell word c hc f P select b z x
    rw [hx] at hh
    exact (macroStep_start n w a e.adj).symm.trans hh

def fragmentMark (z : ApexInstance n w d ell hell word c hc f P select b) (x : P.Link z.val) :
    FanLink.Mark (SelectedTop n w d ell hell word c hc f P select b) :=
  if hs : select (P.faceClass x.val) = true then
    if ht : ∃ a e, P.index x.val = .inl (.inl (a,e)) then
      .top (selectedTopAt n w d ell hell word c hc f P select b z x hs ht)
    else .triangle
  else .absent

lemma mark_absent (z : ApexInstance n w d ell hell word c hc f P select b) (x : P.Link z.val) :
    fragmentMark n w d ell hell word c hc f P select b z x = .absent ↔ select (P.faceClass x.val) ≠ true := by
  unfold fragmentMark
  split_ifs <;> simp_all

lemma mark_top_face (z : ApexInstance n w d ell hell word c hc f P select b) (x : P.Link z.val)
    (F : SelectedTop n w d ell hell word c hc f P select b)
    (h : fragmentMark n w d ell hell word c hc f P select b z x = .top F) :
    F.val = P.faceClass x.val := by
  unfold fragmentMark at h
  split_ifs at h with hs ht
  exact congrArg Subtype.val (FanLink.Mark.top.inj h).symm

lemma mark_top_index (z : ApexInstance n w d ell hell word c hc f P select b) (x : P.Link z.val)
    (F : SelectedTop n w d ell hell word c hc f P select b)
    (h : fragmentMark n w d ell hell word c hc f P select b z x = .top F) :
    ∃ e, P.index x.val = .inl (.inl (selectedOccurrence n w d ell hell word c hc f P select b F,e)) := by
  have hk := selectedOccurrence_kind n w d ell hell word c hc f P select b F
  rw [mark_top_face n w d ell hell word c hc f P select b z x F h] at hk
  change (target n w d ell hell word c hc f).kind (P.index x.val) = .inl (.inl _) at hk
  cases hx : P.index x.val with
  | inl s =>
    cases s with
    | inl s =>
      rw [hx] at hk
      have ha := Sum.inl.inj (Sum.inl.inj hk)
      exact ⟨s.2,congrArg Sum.inl (congrArg Sum.inl (Prod.ext ha rfl))⟩
    | inr s => rw [hx] at hk; cases hk
  | inr s => rw [hx] at hk; cases hk

lemma mark_triangle_corner (z : ApexInstance n w d ell hell word c hc f P select b) (x : P.Link z.val)
    (h : fragmentMark n w d ell hell word c hc f P select b z x = .triangle) :
    ∃ g o, P.index x.val = .inl (frozenCorner n w d g o) := by
  rcases apex_cases n w d ell hell word c hc f P x.val
    (instance_apex n w d ell hell word c hc f P select b z x) with ⟨a,e,hx⟩ | hh
  · have ht : ∃ a e, P.index x.val = .inl (.inl (a,e)) := ⟨a,e,hx⟩
    unfold fragmentMark at h
    split_ifs at h with hs
  · exact hh

lemma fragment_represented (z : ApexInstance n w d ell hell word c hc f P select b) :
    ∃ x, fragmentMark n w d ell hell word c hc f P select b z x ≠ .absent := by
  obtain ⟨x,hx,hs⟩ := z.property.2
  exact ⟨⟨x,hx⟩,fun h => (mark_absent n w d ell hell word c hc f P select b z ⟨x,hx⟩).mp h hs⟩

lemma fragment_card (hrad : P.RadialInjective (isApex n w))
    (z : ApexInstance n w d ell hell word c hc f P select b) : Fintype.card (P.Link z.val) ≤ 5 := by
  rw [P.link_card]
  exact link_card n w d ell hell word c hc f P hrad z.val.out b z.property.1

lemma fragment_no_fixed (hm : P.FrozenMapped (frozen n w d ell hell word c hc f))
    (hred : P.FullyReduced) (z : ApexInstance n w d ell hell word c hc f P select b) (x : P.Link z.val) :
    P.linkNext z.val x ≠ x := by
  intro he
  have he' := congrArg Subtype.val he
  change P.pairing.vertex⁻¹ x.val = x.val at he'
  have hh := congrArg P.pairing.vertex he'
  simp only [Perm.inv_def,apply_symm_apply] at hh
  exact apex_no_fixed n w d ell hell word c hc f P hm hred x.val
    (instance_apex n w d ell hell word c hc f P select b z x) hh.symm

lemma fragment_bipartite (hm : P.FrozenMapped (frozen n w d ell hell word c hc f))
    (z : ApexInstance n w d ell hell word c hc f P select b) (x : P.Link z.val)
    (h : fragmentMark n w d ell hell word c hc f P select b z x = .triangle) :
    dartPart n w ((target n w d ell hell word c hc f).label (P.index x.val)) ≠
      dartPart n w ((target n w d ell hell word c hc f).label (P.index (P.linkNext z.val x).val)) := by
  obtain ⟨g,o,hx⟩ := mark_triangle_corner n w d ell hell word c hc f P select b z x h
  exact triangle_bipartite n w d ell hell word c hc f P hm hx

lemma fragment_no_backtrack (hm : P.FrozenMapped (frozen n w d ell hell word c hc f))
    (hred : P.FullyReduced) (z : ApexInstance n w d ell hell word c hc f P select b) (x : P.Link z.val)
    (hx : fragmentMark n w d ell hell word c hc f P select b z x = .triangle)
    (hy : fragmentMark n w d ell hell word c hc f P select b z (P.linkNext z.val x) = .triangle) :
    P.linkNext z.val (P.linkNext z.val x) ≠ x := by
  obtain ⟨g,o,hg⟩ := mark_triangle_corner n w d ell hell word c hc f P select b z x hx
  obtain ⟨h,p,hh⟩ := mark_triangle_corner n w d ell hell word c hc f P select b z (P.linkNext z.val x) hy
  intro he
  exact triangle_inverse_no_two n w d ell hell word c hc f P hm hred hg hh (congrArg Subtype.val he)

lemma fragment_no_same_side (hred : P.FullyReduced)
    (z : ApexInstance n w d ell hell word c hc f P select b) (x : P.Link z.val)
    (F G : SelectedTop n w d ell hell word c hc f P select b)
    (hx : fragmentMark n w d ell hell word c hc f P select b z x = .top F)
    (hy : fragmentMark n w d ell hell word c hc f P select b z (P.linkNext z.val x) = .top G) :
    selectedOccurrence n w d ell hell word c hc f P select b F ≠ selectedOccurrence n w d ell hell word c hc f P select b G := by
  obtain ⟨e,he⟩ := mark_top_index n w d ell hell word c hc f P select b z x F hx
  obtain ⟨k,hk⟩ := mark_top_index n w d ell hell word c hc f P select b z (P.linkNext z.val x) G hy
  exact Ne.symm (top_adjacent_different n w d ell hell word c hc f P hred hk
    (by simpa only [P.linkNext_val,Perm.inv_def,apply_symm_apply] using he)
    (instance_apex n w d ell hell word c hc f P select b z (P.linkNext z.val x)))

lemma fragment_unique_turn (hs : P.Simple)
    (p q : Σ z : ApexInstance n w d ell hell word c hc f P select b, P.Link z.val)
    (F : SelectedTop n w d ell hell word c hc f P select b)
    (hp : fragmentMark n w d ell hell word c hc f P select b p.1 p.2 = .top F)
    (hq : fragmentMark n w d ell hell word c hc f P select b q.1 q.2 = .top F) : p = q := by
  obtain ⟨e,he⟩ := mark_top_index n w d ell hell word c hc f P select b p.1 p.2 F hp
  have hface := (mark_top_face n w d ell hell word c hc f P select b p.1 p.2 F hp).symm.trans
    (mark_top_face n w d ell hell word c hc f P select b q.1 q.2 F hq)
  have hd := top_unique_turn n w d ell hell word c hc f P hs he (P.faceClass_eq.mp hface) b
    (instance_start n w d ell hell word c hc f P select b p.1 p.2)
    (instance_start n w d ell hell word c hc f P select b q.1 q.2)
  have hz : p.1 = q.1 := Subtype.ext (p.2.property.symm.trans
    ((congrArg P.vertexClass hd).trans q.2.property))
  rcases p with ⟨z,x⟩; rcases q with ⟨y,k⟩
  dsimp at hz hd
  subst y
  exact congrArg (Sigma.mk z) (Subtype.ext hd)

end HyperbolicObstruction.ConeSkeleton.RelDisk
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_RelativeApexProducer
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSix _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HyperbolicObstruction.ConeSkeleton.RelDisk
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
universe u
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable (ell : ℕ) (hell : 0 < ell) (word : Fin ell → Alphabet n)
variable {A : Type*} [AddCommGroup A]
variable (c : Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A)
variable (P : WalkPicture.{0} (target n w d ell hell word c hc f))

variable (select : P.Face → Bool)

abbrev SelectedOccurrence := {a : Top n w // ∃ F : P.Face, select F = true ∧ P.faceKind F = .inl (.inl a)}

noncomputable instance instFintypeSelectedOccurrence : Fintype (SelectedOccurrence n w d ell hell word c hc f P select) := Fintype.ofFinite _

variable (b : Fan n w)

def selectedOccurrence' (F : SelectedTop n w d ell hell word c hc f P select b) :
    SelectedOccurrence n w d ell hell word c hc f P select :=
  ⟨selectedOccurrence n w d ell hell word c hc f P select b F,F.val,F.property.1,
    selectedOccurrence_kind n w d ell hell word c hc f P select b F⟩

/-- The actual selected fragment of an actual normalized genus-zero mapped
picture supplies EVERY field of the local fan-link data. No apex bound,
no triangle-link normality and no contact separation is assumed. -/
def indexedFanData (hs : P.Simple) (hm : P.FrozenMapped (frozen n w d ell hell word c hc f))
    (hred : P.FullyReduced) (hrad : P.RadialInjective (isApex n w)) :
    FanLink.IndexedFanData (ApexInstance n w d ell hell word c hc f P select b)
      (SelectedTop n w d ell hell word c hc f P select b) (SelectedOccurrence n w d ell hell word c hc f P select)
      (fun z => P.Link z.val) where
  next := fun z => P.linkNext z.val
  cyclic := fun z => P.link_cyclic z.val
  mark := fragmentMark n w d ell hell word c hc f P select b
  line := fun _ x => dartPart n w ((target n w d ell hell word c hc f).label (P.index x.val))
  occurrence := selectedOccurrence' n w d ell hell word c hc f P select b
  represented := fragment_represented n w d ell hell word c hc f P select b
  card_le := fragment_card n w d ell hell word c hc f P select b hrad
  no_fixed := fragment_no_fixed n w d ell hell word c hc f P select b hm hred
  bipartite := fragment_bipartite n w d ell hell word c hc f P select b hm
  no_backtrack := fragment_no_backtrack n w d ell hell word c hc f P select b hm hred
  no_same_side := by
    intro z x F G hx hy h
    exact fragment_no_same_side n w d ell hell word c hc f P select b hred z x F G hx hy (congrArg Subtype.val h)
  unique_turn := fragment_unique_turn n w d ell hell word c hc f P select b hs

end HyperbolicObstruction.ConeSkeleton.RelDisk
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_RelativeRadialBoundary
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSix _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace HyperbolicObstruction.ConeSkeleton.RelDisk
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
universe u
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable (ell : ℕ) (hell : 0 < ell) (word : Fin ell → Alphabet n)
variable {A : Type*} [AddCommGroup A]
variable (c : Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A)
variable (P : WalkPicture.{0} (target n w d ell hell word c hc f))

variable (select : P.Face → Bool)

def walkApex (x : P.Dart) := isApex n w (start n w ((target n w d ell hell word c hc f).label (P.index x)))
def walkSelected (x : P.Dart) := select (P.faceClass x)
def walkRadial (x : P.Dart) : Prop := isLetter n w ((target n w d ell hell word c hc f).label (P.index x)) = false

abbrev RadialBoundarySide := P.pairing.BoundarySide (fun x => walkSelected n w d ell hell word c hc f P select x = true)
  (walkRadial n w d ell hell word c hc f P)

lemma walk_apex_previous (x : P.Dart) :
    walkApex n w d ell hell word c hc f P (P.pairing.vertex⁻¹ x) = walkApex n w d ell hell word c hc f P x := by
  exact congrArg (isApex n w) (start_link_constant n w d ell hell word c hc f P
    (sameCycle_inv.mp (SameCycle.rfl.apply_left)))

/-- Tags on actual apex corners are determined by their source dart. -/
lemma apexCorner_injective : Function.Injective
    (fun p : Σ b : Fan n w, Σ z : ApexInstance n w d ell hell word c hc f P select b, P.Link z.val => p.2.2.val) := by
  rintro ⟨b,z,x⟩ ⟨a,y,k⟩ h
  have hb : b = a := Sum.inr.inj ((instance_start n w d ell hell word c hc f P select b z x).symm.trans
    ((congrArg (fun t => start n w ((target n w d ell hell word c hc f).label (P.index t))) h).trans
      (instance_start n w d ell hell word c hc f P select a y k)))
  subst a
  have hz : z = y := Subtype.ext (x.property.symm.trans ((congrArg P.vertexClass h).trans k.property))
  subst y
  exact Sigma.ext rfl (heq_of_eq (Sigma.ext rfl (heq_of_eq (Subtype.ext h))))

variable (hs : P.Simple) (hm : P.FrozenMapped (frozen n w d ell hell word c hc f))
  (hred : P.FullyReduced) (hrad : P.RadialInjective (isApex n w))

abbrev AllBoundaryIndex := Σ b : Fan n w,
  (indexedFanData n w d ell hell word c hc f P select b hs hm hred hrad).BoundaryIndex

end HyperbolicObstruction.ConeSkeleton.RelDisk
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_RelativeInstanceAt
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSix _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace HyperbolicObstruction.ConeSkeleton.RelDisk
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
universe u
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable (ell : ℕ) (hell : 0 < ell) (word : Fin ell → Alphabet n)
variable {A : Type*} [AddCommGroup A]
variable (c : Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A)
variable (P : WalkPicture.{0} (target n w d ell hell word c hc f))

variable (select : P.Face → Bool)

def apexInstanceAt (b : Fan n w) (x : P.Dart)
    (hs : select (P.faceClass x) = true)
    (hx : start n w ((target n w d ell hell word c hc f).label (P.index x)) = .inr b) :
    ApexInstance n w d ell hell word c hc f P select b :=
  ⟨P.vertexClass x,by
    have hh : P.pairing.vertex.SameCycle (P.vertexClass x).out x :=
      P.vertexClass_eq.mp (P.vertexClass_out _)
    exact (start_link_constant n w d ell hell word c hc f P hh).trans hx,
    x,rfl,hs⟩

end HyperbolicObstruction.ConeSkeleton.RelDisk
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_RelativeSlots
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSix _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeOutsideContact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace HyperbolicObstruction.ConeSkeleton.RelDisk
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
universe u
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable (ell : ℕ) (hell : 0 < ell) (word : Fin ell → Alphabet n)
variable {A : Type*} [AddCommGroup A]
variable (c : Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A)
variable (P : WalkPicture.{0} (target n w d ell hell word c hc f))

variable (select : P.Face → Bool)

abbrev SelectedTopFace := {F : P.Face // select F = true ∧ ∃ a : Top n w, P.faceKind F = .inl (.inl a)}
noncomputable instance instFintypeSelectedTopFace : Fintype (SelectedTopFace n w d ell hell word c hc f P select) := Fintype.ofFinite _

end HyperbolicObstruction.ConeSkeleton.RelDisk
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_RelativeTopTurns
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSix _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace HyperbolicObstruction.ConeSkeleton.RelDisk
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
universe u
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable (ell : ℕ) (hell : 0 < ell) (word : Fin ell → Alphabet n)
variable {A : Type*} [AddCommGroup A]
variable (c : Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A)
variable (P : WalkPicture.{0} (target n w d ell hell word c hc f))

variable (select : P.Face → Bool)
abbrev TopTurnDart := {x : P.Dart // select (P.faceClass x) = true ∧
  isApex n w (start n w ((target n w d ell hell word c hc f).label (P.index x))) = true ∧
  (target n w d ell hell word c hc f).free ((target n w d ell hell word c hc f).kind (P.index x)) = true}

abbrev FaceApexDart (F : SelectedTopFace n w d ell hell word c hc f P select) :=
  {x : P.Dart // P.faceClass x = F.val ∧ isApex n w (start n w ((target n w d ell hell word c hc f).label (P.index x))) = true}

end HyperbolicObstruction.ConeSkeleton.RelDisk
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_RelativeTurnTransport
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSix _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace HyperbolicObstruction.ConeSkeleton.RelDisk
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
universe u
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable (ell : ℕ) (hell : 0 < ell) (word : Fin ell → Alphabet n)
variable {A : Type*} [AddCommGroup A]
variable (c : Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A)
variable (P : WalkPicture.{0} (target n w d ell hell word c hc f))

variable (select : P.Face → Bool)

variable (hs : P.Simple) (hm : P.FrozenMapped (frozen n w d ell hell word c hc f))
  (hred : P.FullyReduced) (hrad : P.RadialInjective (isApex n w))

abbrev AllTurnIndex := Σ b : Fan n w,
  (indexedFanData n w d ell hell word c hc f P select b hs hm hred hrad).TurnIndex

end HyperbolicObstruction.ConeSkeleton.RelDisk
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_RelativeFanCapacity
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSix _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace HyperbolicObstruction.ConeSkeleton.RelDisk
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
universe u
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable (ell : ℕ) (hell : 0 < ell) (word : Fin ell → Alphabet n)
variable {A : Type*} [AddCommGroup A]
variable (c : Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A)
variable (P : WalkPicture.{0} (target n w d ell hell word c hc f))

lemma frozenCorner_start (g : FanTriangle n w) (o : Bool) :
    start n w ((target n w d ell hell word c hc f).label (.inl (frozenCorner n w d g o))) = .inr g.1 := by
  rw [corner_label]
  cases o <;> rfl

/-- The same indexed fan field occurs at most once at one normalized apex
instance, INCLUDING opposite triangle orientations. Opposite orientations
would force a canceling two-step vertex link. -/
lemma fan_field_once (hm : P.FrozenMapped (frozen n w d ell hell word c hc f))
    (hred : P.FullyReduced) (hrad : P.RadialInjective (isApex n w))
    {x y : P.Dart} {g : FanTriangle n w} {o p : Bool}
    (hx : P.index x = .inl (frozenCorner n w d g o))
    (hy : P.index y = .inl (frozenCorner n w d g p))
    (hxy : P.pairing.vertex.SameCycle x y) : x = y := by
  have hax : isApex n w (start n w ((target n w d ell hell word c hc f).label (P.index x))) = true := by
    rw [hx,frozenCorner_start]; rfl
  by_cases hop : o = p
  · apply hrad x y hax hxy
    rw [hx,hy,hop]
  · have hprev : ∀ z : P.Dart, P.pairing.vertex.SameCycle (P.pairing.vertex⁻¹ z) z :=
      fun z => sameCycle_inv.mp (SameCycle.rfl (x := z)).apply_left
    have hp : p = !o := by cases o <;> cases p <;> simp_all
    have h1 : P.pairing.vertex⁻¹ x = y := by
      refine hrad _ _ ?_ ((hprev x).trans hxy) ?_
      · change isApex n w (start n w ((target n w d ell hell word c hc f).label (P.index (P.pairing.vertex⁻¹ x)))) = true
        rw [start_link_constant n w d ell hell word c hc f P (hprev x)]
        exact hax
      · rw [corner_incoming n w d ell hell word c hc f P hm hx,hy,corner_label,hp]
        cases o <;> rfl
    have h2 : P.pairing.vertex⁻¹ y = x := by
      refine hrad _ _ ?_ ((hprev y).trans hxy.symm) ?_
      · change isApex n w (start n w ((target n w d ell hell word c hc f).label (P.index (P.pairing.vertex⁻¹ y)))) = true
        rw [start_link_constant n w d ell hell word c hc f P ((hprev y).trans hxy.symm)]
        exact hax
      · rw [corner_incoming n w d ell hell word c hc f P hm hy,hx,corner_label,hp]
        cases o <;> rfl
    exact False.elim (triangle_inverse_no_two n w d ell hell word c hc f P hm hred hx
      (by rw [h1]; exact hy) (by rw [h1,h2]))

end HyperbolicObstruction.ConeSkeleton.RelDisk
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_RelativeRawPosition
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSix _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeOutsideContact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HyperbolicObstruction.ConeSkeleton.RelDisk
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable (ell : ℕ) (hell : 0 < ell) (word : Fin ell → Alphabet n)
variable {A : Type*} [AddCommGroup A]
variable (c : Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A)

/-- The outside has no occurrence position. Its letters are genuine boundary
penalties, and cannot be silently identified with a random row field. -/
def stepPosition : WalkStep n w d ⊕ (walkTarget n w d c hc f).ExteriorSide ell hell
    (letterDart n w ∘ word) (letterWordClosed n w ell word) → Option (RawPosition n w d)
  | .inl s => some (rawPosition n w d s)
  | .inr _ => none

variable (P : WalkPicture.{0} (target n w d ell hell word c hc f))

lemma stepPosition_some {x : P.Dart} {p : RawPosition n w d}
    (hp : stepPosition n w d ell hell word c hc f (P.index x) = some p) :
    ∃ s, P.index x = .inl s ∧ rawPosition n w d s = p := by
  cases hi : P.index x with
  | inl s => exact ⟨s,rfl,Option.some.inj (by rw [hi] at hp; exact hp)⟩
  | inr s => rw [hi] at hp; cases hp

lemma raw_position_once_per_face (hs : P.Simple) (hb : P.NoBigon)
    (hm : P.FrozenMapped (frozen n w d ell hell word c hc f))
    {x y : P.Dart} {p : RawPosition n w d} (hxy : P.pairing.face.SameCycle x y)
    (hx : isLetter n w ((target n w d ell hell word c hc f).label (P.index x)) = true)
    (hy : isLetter n w ((target n w d ell hell word c hc f).label (P.index y)) = true)
    (hpx : stepPosition n w d ell hell word c hc f (P.index x) = some p)
    (hpy : stepPosition n w d ell hell word c hc f (P.index y) = some p) : x = y := by
  obtain ⟨s,hxs,hps⟩ := stepPosition_some n w d ell hell word c hc f P hpx
  obtain ⟨t,hyt,hpt⟩ := stepPosition_some n w d ell hell word c hc f P hpy
  rw [hxs] at hx; rw [hyt] at hy
  have hcx := raw_step_cases n w d s hx
  have hcy := raw_step_cases n w d t hy
  rw [hps] at hcx; rw [hpt] at hcy
  rcases hcx with hcx | hcx <;> rcases hcy with hcy | hcy
  · exact P.normalized_index_inj hs _ hm hxy (by rw [hxs,hyt,hcx,hcy])
  · exact False.elim (P.normalized_sameface_not_opposite hs hb _ hm hxy (by
      rw [hxs,hyt,hcx,hcy]; rfl))
  · exact False.elim (P.normalized_sameface_not_opposite hs hb _ hm hxy.symm (by
      rw [hxs,hyt,hcx,hcy]; rfl))
  · exact P.normalized_index_inj hs _ hm hxy (by rw [hxs,hyt,hcx,hcy])

end HyperbolicObstruction.ConeSkeleton.RelDisk
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_RelativeMultiplicity
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSix _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeOutsideContact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace HyperbolicObstruction.ConeSkeleton.RelDisk
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
universe u
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable (ell : ℕ) (hell : 0 < ell) (word : Fin ell → Alphabet n)
variable {A : Type*} [AddCommGroup A]
variable (c : Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A)
variable (P : WalkPicture.{0} (target n w d ell hell word c hc f))

variable (select : P.Face → Bool)

abbrev RawPositionSide (p : RawPosition n w d) := {x : P.Dart // select (P.faceClass x) = true ∧
  isLetter n w ((target n w d ell hell word c hc f).label (P.index x)) = true ∧ stepPosition n w d ell hell word c hc f (P.index x) = some p}
noncomputable instance instFintypeRawPositionSide (p : RawPosition n w d) : Fintype (RawPositionSide n w d ell hell word c hc f P select p) :=
  Fintype.ofFinite _

abbrev KindFace (k : WalkKind n w d) := {F : P.Face // select F = true ∧ P.faceKind F = .inl k}
noncomputable instance instFintypeKindFace (k : WalkKind n w d) : Fintype (KindFace n w d ell hell word c hc f P select k) :=
  Fintype.ofFinite _

/-- Top loose fields and every decoration field occur at most once in each
selected source face of that occurrence. -/
lemma raw_multiplicity_le_faces (hs : P.Simple) (hb : P.NoBigon)
    (hm : P.FrozenMapped (frozen n w d ell hell word c hc f)) (p : RawPosition n w d) :
    Fintype.card (RawPositionSide n w d ell hell word c hc f P select p) ≤
      Fintype.card (KindFace n w d ell hell word c hc f P select (walkKind n w d (rawRepresentative n w d p))) := by
  let g : RawPositionSide n w d ell hell word c hc f P select p →
      KindFace n w d ell hell word c hc f P select (walkKind n w d (rawRepresentative n w d p)) := fun x =>
    ⟨P.faceClass x.val,x.property.1,by
      obtain ⟨s,hi,hp⟩ := stepPosition_some n w d ell hell word c hc f P x.property.2.2
      change (target n w d ell hell word c hc f).kind (P.index x.val) = _
      rw [hi]
      change Sum.inl (walkKind n w d s) = _
      rw [ConeSkeleton.raw_kind n w d s,hp]⟩
  apply Fintype.card_le_of_injective g
  intro x y h
  apply Subtype.ext
  exact raw_position_once_per_face n w d ell hell word c hc f P hs hb hm
    (P.faceClass_eq.mp (congrArg Subtype.val h)) x.property.2.1 y.property.2.1
    x.property.2.2 y.property.2.2

lemma raw_fan_index {x : P.Dart} {g : FanTriangle n w}
    (hr : isLetter n w ((target n w d ell hell word c hc f).label (P.index x)) = true)
    (hp : stepPosition n w d ell hell word c hc f (P.index x) = some (.inr (.inl g))) :
    ∃ o, P.index x = .inl (.inr ⟨.inl g,o,(1 : Fin 3)⟩) := by
  obtain ⟨s,he,hp⟩ := stepPosition_some n w d ell hell word c hc f P hp
  rw [he] at hr
  cases s with
  | inl s => cases hp
  | inr s =>
    rcases s with ⟨k,o,i⟩
    rcases k with h | (q | q)
    · have hg : h = g := Sum.inl.inj (Sum.inr.inj hp)
      have hi := fan_letter_index n w d h o i hr
      subst h; subst i
      exact ⟨o,he⟩
    · cases hp
    · cases hp

lemma raw_fan_previous (hm : P.FrozenMapped (frozen n w d ell hell word c hc f))
    {x : P.Dart} {g : FanTriangle n w} {o : Bool}
    (hx : P.index x = .inl (.inr ⟨.inl g,o,(1 : Fin 3)⟩)) :
    P.index (P.pairing.face⁻¹ x) = .inl (frozenCorner n w d g o) := by
  rw [P.frozen_previous_index (frozen n w d ell hell word c hc f) hm (by rw [hx]; rfl),hx]
  cases o <;> rfl

lemma raw_fan_previous_start (hm : P.FrozenMapped (frozen n w d ell hell word c hc f))
    (g : FanTriangle n w) (x : RawPositionSide n w d ell hell word c hc f P select (.inr (.inl g))) :
    start n w ((target n w d ell hell word c hc f).label (P.index (P.pairing.face⁻¹ x.val))) = .inr g.1 := by
  obtain ⟨o,ho⟩ := raw_fan_index n w d ell hell word c hc f P x.property.2.1 x.property.2.2
  rw [raw_fan_previous n w d ell hell word c hc f P hm ho,frozenCorner_start]

/-- A fan field's selected copies inject into the ACTUAL represented apex
instances, not into an assumed nominal collection of links. -/
lemma raw_fan_multiplicity_le (hm : P.FrozenMapped (frozen n w d ell hell word c hc f))
    (hred : P.FullyReduced) (hrad : P.RadialInjective (isApex n w)) (g : FanTriangle n w) :
    Fintype.card (RawPositionSide n w d ell hell word c hc f P select (.inr (.inl g))) ≤
      Fintype.card (ApexInstance n w d ell hell word c hc f P select g.1) := by
  let j : RawPositionSide n w d ell hell word c hc f P select (.inr (.inl g)) →
      ApexInstance n w d ell hell word c hc f P select g.1 := fun x =>
    apexInstanceAt n w d ell hell word c hc f P select g.1 (P.pairing.face⁻¹ x.val)
      (by rw [P.faceClass_previous]; exact x.property.1)
      (raw_fan_previous_start n w d ell hell word c hc f P select hm g x)
  apply Fintype.card_le_of_injective j
  intro x y h
  obtain ⟨o,ho⟩ := raw_fan_index n w d ell hell word c hc f P x.property.2.1 x.property.2.2
  obtain ⟨p,hp⟩ := raw_fan_index n w d ell hell word c hc f P y.property.2.1 y.property.2.2
  have hv : P.vertexClass (P.pairing.face⁻¹ x.val) = P.vertexClass (P.pairing.face⁻¹ y.val) :=
    congrArg Subtype.val h
  have hh := fan_field_once n w d ell hell word c hc f P hm hred hrad
    (raw_fan_previous n w d ell hell word c hc f P hm ho) (raw_fan_previous n w d ell hell word c hc f P hm hp)
    (P.vertexClass_eq.mp hv)
  exact Subtype.ext ((P.pairing.face⁻¹).injective hh)

end HyperbolicObstruction.ConeSkeleton.RelDisk
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_RelativeWeights
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace HyperbolicObstruction.ConeSkeleton.RelDisk
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
universe u
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable (ell : ℕ) (hell : 0 < ell) (word : Fin ell → Alphabet n)
variable {A : Type*} [AddCommGroup A]
variable (c : Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A)
variable (P : WalkPicture.{0} (target n w d ell hell word c hc f))

variable (select : P.Face → Bool)
variable (hs : P.Simple) (hm : P.FrozenMapped (frozen n w d ell hell word c hc f))
  (hred : P.FullyReduced) (hrad : P.RadialInjective (isApex n w))

lemma top_count_le_slot (a : Top n w) (i : Fin 7) :
    Fintype.card (KindFace n w d ell hell word c hc f P select (.inl a)) ≤
      (indexedFanData n w d ell hell word c hc f P select (slot n w a i) hs hm hred hrad).weight := by
  by_cases he : Nonempty (KindFace n w d ell hell word c hc f P select (.inl a))
  · let F := Classical.choice he
    let ao : SelectedOccurrence n w d ell hell word c hc f P select := ⟨a,F.val,F.property⟩
    let b := slot n w a i
    let D := indexedFanData n w d ell hell word c hc f P select b hs hm hred hrad
    let g : KindFace n w d ell hell word c hc f P select (.inl a) →
        {H : SelectedTop n w d ell hell word c hc f P select b // D.occurrence H = ao} := fun H =>
      ⟨⟨H.val,H.property.1,a,H.property.2,i,rfl⟩,by
        apply Subtype.ext
        exact Sum.inl.inj (Sum.inl.inj ((selectedOccurrence_kind n w d ell hell word c hc f P select b _).symm.trans H.property.2))⟩
    have hcount : Fintype.card (KindFace n w d ell hell word c hc f P select (.inl a)) ≤ D.multiplicity ao := by
      apply Fintype.card_le_of_injective g
      intro H K h
      exact Subtype.ext (congrArg (fun z => z.val.val) h)
    exact hcount.trans ((Finset.le_sup (f := D.multiplicity) (Finset.mem_univ ao)).trans (le_max_right _ _))
  · have hi : IsEmpty (KindFace n w d ell hell word c hc f P select (.inl a)) := not_nonempty_iff.mp he
    have hzero : Fintype.card (KindFace n w d ell hell word c hc f P select (.inl a)) = 0 := Fintype.card_eq_zero_iff.mpr hi
    rw [hzero]
    exact Nat.zero_le _

lemma indexed_weight_congr {b b' : Fan n w} (h : b = b') :
    (indexedFanData n w d ell hell word c hc f P select b hs hm hred hrad).weight =
    (indexedFanData n w d ell hell word c hc f P select b' hs hm hred hrad).weight := by
  cases h
  rfl

/-- Weights are the literal selected-face multiplicities and maximum of actual
apex count / same-top slot multiplicity. No contact capacity is a field. -/
def actualWeights : (occurrenceShape n w).Weights (v := Fintype.card (Six n d)) where
  top := fun a => Fintype.card (KindFace n w d ell hell word c hc f P select (.inl ((enumTop n w).symm a)))
  fan := fun b => (indexedFanData n w d ell hell word c hc f P select ((enumFan n w).symm b) hs hm hred hrad).weight
  square := fun q => Fintype.card (KindFace n w d ell hell word c hc f P select (.inr (.inr (.inl ((enumSquare n w).symm q)))))
  six := fun q => Fintype.card (KindFace n w d ell hell word c hc f P select (.inr (.inr (.inr ((enumSix n d).symm q)))))
  slot := by
    intro a i
    change _ ≤ (indexedFanData n w d ell hell word c hc f P select
      ((enumFan n w).symm ((enumFan n w) (slot n w ((enumTop n w).symm a) i))) hs hm hred hrad).weight
    rw [indexed_weight_congr n w d ell hell word c hc f P select hs hm hred hrad ((enumFan n w).symm_apply_apply _)]
    exact top_count_le_slot n w d ell hell word c hc f P select hs hm hred hrad _ i

lemma actual_position_capacity (hb : P.NoBigon) (p : RawPosition n w d) :
    Fintype.card (RawPositionSide n w d ell hell word c hc f P select p) ≤
      (actualWeights n w d ell hell word c hc f P select hs hm hred hrad).position (rawToPosition n w d p) := by
  rcases p with a | (g | (⟨q,i⟩ | ⟨q,i⟩))
  · have hh := raw_multiplicity_le_faces n w d ell hell word c hc f P select hs hb hm (.inl a)
    simp only [← Nat.card_eq_fintype_card] at hh
    simpa only [actualWeights,Occurrences.Shape.Weights.position,rawToPosition,Equiv.symm_apply_apply,
      rawRepresentative,walkKind,FanLink.IndexedFanData.weight, ← Nat.card_eq_fintype_card] using hh
  · have hh := raw_fan_multiplicity_le n w d ell hell word c hc f P select hm hred hrad g
    change _ ≤ (indexedFanData n w d ell hell word c hc f P select
      ((enumFan n w).symm ((enumFan n w) g.1)) hs hm hred hrad).weight
    rw [indexed_weight_congr n w d ell hell word c hc f P select hs hm hred hrad ((enumFan n w).symm_apply_apply _)]
    exact hh.trans (le_max_left _ _)
  · have hh := raw_multiplicity_le_faces n w d ell hell word c hc f P select hs hb hm (.inr (.inr (.inl (q,i))))
    simp only [← Nat.card_eq_fintype_card] at hh
    simpa only [actualWeights,Occurrences.Shape.Weights.position,rawToPosition,Equiv.symm_apply_apply,
      rawRepresentative,walkKind,FanLink.IndexedFanData.weight, ← Nat.card_eq_fintype_card] using hh
  · have hh := raw_multiplicity_le_faces n w d ell hell word c hc f P select hs hb hm (.inr (.inr (.inr (q,i))))
    simp only [← Nat.card_eq_fintype_card] at hh
    simpa only [actualWeights,Occurrences.Shape.Weights.position,rawToPosition,Equiv.symm_apply_apply,
      rawRepresentative,walkKind,FanLink.IndexedFanData.weight, ← Nat.card_eq_fintype_card] using hh

end HyperbolicObstruction.ConeSkeleton.RelDisk
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_RelativeContact
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeOutsideContact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace HyperbolicObstruction.ConeSkeleton.RelDisk
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
universe u
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable (ell : ℕ) (hell : 0 < ell) (word : Fin ell → Alphabet n)
variable {A : Type*} [AddCommGroup A]
variable (c : Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A)
variable (P : WalkPicture.{0} (target n w d ell hell word c hc f))

variable (select : P.Face → Bool)

def selectedDart (x : P.Dart) : Prop := select (P.faceClass x) = true
def rawDart (x : P.Dart) : Prop := isLetter n w ((target n w d ell hell word c hc f).label (P.index x)) = true
lemma rawDart_pair (x : P.Dart) : rawDart n w d ell hell word c hc f P (P.pairing.edge x) ↔ rawDart n w d ell hell word c hc f P x := by
  unfold rawDart
  have h : (target n w d ell hell word c hc f).label (P.index (P.pairing.edge x)) = rev n w ((target n w d ell hell word c hc f).label (P.index x)) := P.paired x
  rw [h]
  rfl

abbrev ActualContact := P.pairing.Contact (selectedDart n w d ell hell word c hc f P select) (rawDart n w d ell hell word c hc f P)
abbrev ActualRawSide := PictureMap.SelectedSide (selectedDart n w d ell hell word c hc f P select) (rawDart n w d ell hell word c hc f P)
abbrev ActualRawBoundary := P.pairing.BoundarySide (selectedDart n w d ell hell word c hc f P select) (rawDart n w d ell hell word c hc f P)

/-- Only genuine disk-interior cells belong to a fragment. -/
def InteriorSelection : Prop := ∀ F : P.Face, select F = true → ∃ k, P.faceKind F = .inl k

variable (hsel : InteriorSelection n w d ell hell word c hc f P select)

include hsel in
lemma selected_interior {x : P.Dart} (hx : selectedDart n w d ell hell word c hc f P select x) :
    ∃ s, P.index x = .inl s := by
  obtain ⟨k,hk⟩ := hsel (P.faceClass x) hx
  change (target n w d ell hell word c hc f).kind (P.index x) = .inl k at hk
  cases hi : P.index x with
  | inl s => exact ⟨s,rfl⟩
  | inr s => rw [hi] at hk; cases hk

def selectedStep (x : P.Dart) (hx : selectedDart n w d ell hell word c hc f P select x) :
    WalkStep n w d := (selected_interior n w d ell hell word c hc f P select hsel hx).choose
lemma selectedStep_index (x : P.Dart) (hx : selectedDart n w d ell hell word c hc f P select x) :
    P.index x = .inl (selectedStep n w d ell hell word c hc f P select hsel x hx) :=
  (selected_interior n w d ell hell word c hc f P select hsel hx).choose_spec

def selectedPosition (x : P.Dart) (hx : selectedDart n w d ell hell word c hc f P select x) :
    RawPosition n w d := rawPosition n w d (selectedStep n w d ell hell word c hc f P select hsel x hx)
lemma selectedPosition_eq (x : P.Dart) (hx : selectedDart n w d ell hell word c hc f P select x) :
    stepPosition n w d ell hell word c hc f (P.index x) =
      some (selectedPosition n w d ell hell word c hc f P select hsel x hx) := by
  rw [selectedStep_index n w d ell hell word c hc f P select hsel x hx]
  rfl

def contactLeft (e : ActualContact n w d ell hell word c hc f P select) :=
  rawToPosition n w d (selectedPosition n w d ell hell word c hc f P select hsel e.val e.property.2.1)
def contactRight (e : ActualContact n w d ell hell word c hc f P select) :=
  rawToPosition n w d (selectedPosition n w d ell hell word c hc f P select hsel
    (P.pairing.edge e.val) e.property.2.2.1)

variable (hs : P.Simple) (hm : P.FrozenMapped (frozen n w d ell hell word c hc f))
  (hred : P.FullyReduced) (hrad : P.RadialInjective (isApex n w))

lemma actual_boundary_contacts_eq :
    Fintype.card (ActualRawBoundary n w d ell hell word c hc f P select) +
      2 * Fintype.card (ActualContact n w d ell hell word c hc f P select) =
    Fintype.card (ActualRawSide n w d ell hell word c hc f P select) :=
  P.pairing.boundary_contacts_eq (selectedDart n w d ell hell word c hc f P select) (rawDart n w d ell hell word c hc f P)
    (rawDart_pair n w d ell hell word c hc f P)

end HyperbolicObstruction.ConeSkeleton.RelDisk
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_RelativeFrozenSide
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSix _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeOutsideContact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace HyperbolicObstruction.ConeSkeleton.RelDisk
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
universe u
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable (ell : ℕ) (hell : 0 < ell) (word : Fin ell → Alphabet n)
variable {A : Type*} [AddCommGroup A]
variable (c : Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A)
variable (P : WalkPicture.{0} (target n w d ell hell word c hc f))

lemma frozen_side_exists (hm : P.FrozenMapped (frozen n w d ell hell word c hc f))
    {x : P.Dart} {k : FrozenCell n w d} {o : Bool} {i : Fin ((frozenBoundary n w d).size k)}
    (hx : P.index x = .inl (.inr ⟨k,o,i⟩)) (j : Fin ((frozenBoundary n w d).size k)) :
    ∃ y, P.pairing.face.SameCycle x y ∧ P.index y = .inl (.inr ⟨k,o,j⟩) := by
  let x' : P.FrozenDart := ⟨x,by rw [hx]; rfl⟩
  have hh : (frozen n w d ell hell word c hc f).next.SameCycle (P.index x) (.inl (.inr ⟨k,o,j⟩)) := by
    rw [hx]
    apply semiconj_perm_sameCycle (f := (frozenBoundary n w d).next)
      (j := Sum.inl ∘ Sum.inr) (fun s => rfl) ((frozenBoundary n w d).side_sameCycle k o i j)
  obtain ⟨y,hy,he⟩ := hm.orbit_surjective x' hh
  exact ⟨y.val,sameCycle_subtypePerm.mp hy,he⟩

end HyperbolicObstruction.ConeSkeleton.RelDisk
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_RelativeTriangleTransport
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSix _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeOutsideContact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace HyperbolicObstruction.ConeSkeleton.RelDisk
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
universe u
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable (ell : ℕ) (hell : 0 < ell) (word : Fin ell → Alphabet n)
variable {A : Type*} [AddCommGroup A]
variable (c : Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A)
variable (P : WalkPicture.{0} (target n w d ell hell word c hc f))

variable (select : P.Face → Bool)
variable (hs : P.Simple) (hm : P.FrozenMapped (frozen n w d ell hell word c hc f))
  (hred : P.FullyReduced) (hrad : P.RadialInjective (isApex n w))

abbrev AllTriangleIndex := Σ b : Fan n w,
  (indexedFanData n w d ell hell word c hc f P select b hs hm hred hrad).TriangleIndex
abbrev triangleCorner (p : AllTriangleIndex n w d ell hell word c hc f P select hs hm hred hrad) := p.2.val.2.val

def triangleRawDart (p : AllTriangleIndex n w d ell hell word c hc f P select hs hm hred hrad) : P.Dart :=
  P.pairing.face (triangleCorner n w d ell hell word c hc f P select hs hm hred hrad p)

lemma triangle_selected (p : AllTriangleIndex n w d ell hell word c hc f P select hs hm hred hrad) :
    select (P.faceClass (triangleCorner n w d ell hell word c hc f P select hs hm hred hrad p)) = true := by
  by_contra hh
  have hx := (mark_absent n w d ell hell word c hc f P select p.1 p.2.val.1 p.2.val.2).mpr hh
  have ht := p.2.property
  change fragmentMark n w d ell hell word c hc f P select p.1 p.2.val.1 p.2.val.2 = .triangle at ht
  rw [hx] at ht
  cases ht

lemma triangle_raw_index (p : AllTriangleIndex n w d ell hell word c hc f P select hs hm hred hrad) :
    ∃ g o, P.index (triangleRawDart n w d ell hell word c hc f P select hs hm hred hrad p) =
      .inl (.inr ⟨.inl g,o,(1 : Fin 3)⟩) := by
  obtain ⟨g,o,hx⟩ := mark_triangle_corner n w d ell hell word c hc f P select p.1 p.2.val.1 p.2.val.2 p.2.property
  have he := hm.commute ⟨p.2.val.2.val,by rw [hx]; rfl⟩
  change P.index (P.pairing.face p.2.val.2.val) =
    (frozen n w d ell hell word c hc f).next (P.index p.2.val.2.val) at he
  refine ⟨g,o,?_⟩
  change P.index (P.pairing.face p.2.val.2.val) = _
  rw [he,hx]
  cases o <;> rfl

lemma triangleRawDart_injective : Function.Injective
    (triangleRawDart n w d ell hell word c hc f P select hs hm hred hrad) := by
  intro p q h
  have hh := apexCorner_injective n w d ell hell word c hc f P select
    (a₁ := ⟨p.1,p.2.val⟩) (a₂ := ⟨q.1,q.2.val⟩) (P.pairing.face.injective h)
  rcases p with ⟨b,x⟩; rcases q with ⟨a,y⟩
  have hb : b = a := congrArg Sigma.fst hh
  subst a
  have hv : x.val = y.val := eq_of_heq (Sigma.mk.inj_iff.mp hh).2
  exact Sigma.ext rfl (heq_of_eq (Subtype.ext hv))

abbrev SelectedTriangleFace := {F : P.Face // select F = true ∧
  ∃ g : FanTriangle n w, P.faceKind F = .inl (.inr (.inl g))}
noncomputable instance instFintypeSelectedTriangleFace : Fintype (SelectedTriangleFace n w d ell hell word c hc f P select) := Fintype.ofFinite _

end HyperbolicObstruction.ConeSkeleton.RelDisk
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_RelativeFaceCounts
attribute [-instance] _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeOutsideContact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace HyperbolicObstruction.ConeSkeleton.RelDisk
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
universe u
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable (ell : ℕ) (hell : 0 < ell) (word : Fin ell → Alphabet n)
variable {A : Type*} [AddCommGroup A]
variable (c : Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A)
variable (P : WalkPicture.{0} (target n w d ell hell word c hc f))

variable (select : P.Face → Bool)

lemma count_faces_in {K : Type*} [Fintype K] (g : K → WalkKind n w d) (hg : Function.Injective g) :
    (∑ k, Fintype.card (KindFace n w d ell hell word c hc f P select (g k))) =
      Fintype.card {F : P.Face // select F = true ∧ ∃ k, P.faceKind F = .inl (g k)} := by
  rw [← Fintype.card_sigma]
  let v : (Σ k, KindFace n w d ell hell word c hc f P select (g k)) →
      {F : P.Face // select F = true ∧ ∃ k, P.faceKind F = .inl (g k)} :=
    fun p => ⟨p.2.val,p.2.property.1,p.1,p.2.property.2⟩
  apply Fintype.card_congr (Equiv.ofBijective v ?_)
  constructor
  · rintro ⟨k,F⟩ ⟨l,G⟩ h
    have hFG : F.val = G.val := congrArg Subtype.val h
    have hkl : k = l := hg (Sum.inl.inj (F.property.2.symm.trans ((congrArg P.faceKind hFG).trans G.property.2)))
    subst l
    have hh : F = G := Subtype.ext hFG
    subst G
    rfl
  · rintro ⟨F,hF,k,hk⟩
    exact ⟨⟨k,F,hF,hk⟩,rfl⟩

abbrev SelectedFace := {F : P.Face // select F = true}
noncomputable instance instFintypeSelectedFace : Fintype (SelectedFace n w d ell hell word c hc f P select) := Fintype.ofFinite _

def actualTopCount : ℕ := Fintype.card (SelectedTopFace n w d ell hell word c hc f P select)
def actualTriangleCount : ℕ := Fintype.card (SelectedTriangleFace n w d ell hell word c hc f P select)
def actualSquareCount : ℕ := ∑ q : Square n w, Fintype.card (KindFace n w d ell hell word c hc f P select (.inr (.inr (.inl q))))
def actualSixCount : ℕ := ∑ q : Six n d, Fintype.card (KindFace n w d ell hell word c hc f P select (.inr (.inr (.inr q))))
def actualArea : ℕ := Fintype.card (SelectedFace n w d ell hell word c hc f P select)

lemma sum_top_count : (∑ a : Top n w, Fintype.card (KindFace n w d ell hell word c hc f P select (.inl a))) =
    actualTopCount n w d ell hell word c hc f P select := by
  simpa only [actualTopCount,← Nat.card_eq_fintype_card] using
    count_faces_in n w d ell hell word c hc f P select Sum.inl Sum.inl_injective
lemma sum_triangle_count : (∑ g : FanTriangle n w, Fintype.card (KindFace n w d ell hell word c hc f P select (.inr (.inl g)))) =
    actualTriangleCount n w d ell hell word c hc f P select := by
  simpa only [actualTriangleCount,Function.comp_apply,← Nat.card_eq_fintype_card] using
    count_faces_in n w d ell hell word c hc f P select (Sum.inr ∘ Sum.inl) (Sum.inr_injective.comp Sum.inl_injective)

lemma actual_area_eq (hsel : InteriorSelection n w d ell hell word c hc f P select) : actualArea n w d ell hell word c hc f P select = actualTopCount n w d ell hell word c hc f P select +
    actualTriangleCount n w d ell hell word c hc f P select + actualSquareCount n w d ell hell word c hc f P select +
    actualSixCount n w d ell hell word c hc f P select := by
  have hh := count_faces_in n w d ell hell word c hc f P select id Function.injective_id
  have he : Fintype.card {F : P.Face // select F = true ∧ ∃ k, P.faceKind F = .inl (id k)} =
      actualArea n w d ell hell word c hc f P select := by
    apply Fintype.card_congr
    exact { toFun := fun F => ⟨F.val,F.property.1⟩
            invFun := fun F => ⟨F.val,F.property,(hsel F.val F.property).choose,(hsel F.val F.property).choose_spec⟩
            left_inv := fun _ => rfl
            right_inv := fun _ => rfl }
  rw [he] at hh
  simp only [id_eq,Fintype.sum_sum_type] at hh
  rw [sum_top_count n w d ell hell word c hc f P select,sum_triangle_count n w d ell hell word c hc f P select] at hh
  unfold actualSquareCount actualSixCount
  omega

end HyperbolicObstruction.ConeSkeleton.RelDisk
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_RelativeFaceSide
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSix _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeOutsideContact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace HyperbolicObstruction.ConeSkeleton.RelDisk
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
universe u
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable (ell : ℕ) (hell : 0 < ell) (word : Fin ell → Alphabet n)
variable {A : Type*} [AddCommGroup A]
variable (c : Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A)
variable (P : WalkPicture.{0} (target n w d ell hell word c hc f))

variable (select : P.Face → Bool)
variable (hm : P.FrozenMapped (frozen n w d ell hell word c hc f))

include hm in
lemma frozenFaceSide_exists (k : FrozenCell n w d)
    (F : KindFace n w d ell hell word c hc f P select (.inr k)) (j : Fin ((frozenBoundary n w d).size k)) :
    ∃ y, P.faceClass y = F.val ∧ ∃ o, P.index y = .inl (.inr ⟨k,o,j⟩) := by
  have ho := P.faceClass_out F.val
  have hk : (target n w d ell hell word c hc f).kind (P.index F.val.out) = .inl (.inr k) := by
    change P.faceKind (P.faceClass F.val.out) = _
    rw [ho]
    exact F.property.2
  obtain ⟨o,i,hi⟩ : ∃ (o : Bool) (i : Fin ((frozenBoundary n w d).size k)),
      P.index F.val.out = .inl (.inr ⟨k,o,i⟩) := by
    cases h : P.index F.val.out with
    | inl s =>
      cases s with
      | inl a => rw [h] at hk; cases hk
      | inr s =>
        rcases s with ⟨k',o,i⟩
        rw [h] at hk
        have hh : k' = k := Sum.inr.inj (Sum.inl.inj hk)
        subst k'
        exact ⟨o,i,rfl⟩
    | inr s => rw [h] at hk; cases hk

  obtain ⟨y,hy,he⟩ := frozen_side_exists n w d ell hell word c hc f P hm hi j
  exact ⟨y,((P.faceClass_eq).mpr hy).symm.trans ho,o,he⟩

def frozenFaceDart (k : FrozenCell n w d)
    (F : KindFace n w d ell hell word c hc f P select (.inr k)) (j : Fin ((frozenBoundary n w d).size k)) : P.Dart :=
  (frozenFaceSide_exists n w d ell hell word c hc f P select hm k F j).choose
lemma frozenFaceDart_face (k : FrozenCell n w d)
    (F : KindFace n w d ell hell word c hc f P select (.inr k)) (j : Fin ((frozenBoundary n w d).size k)) :
    P.faceClass (frozenFaceDart n w d ell hell word c hc f P select hm k F j) = F.val :=
  (frozenFaceSide_exists n w d ell hell word c hc f P select hm k F j).choose_spec.1
lemma frozenFaceDart_index (k : FrozenCell n w d)
    (F : KindFace n w d ell hell word c hc f P select (.inr k)) (j : Fin ((frozenBoundary n w d).size k)) :
    ∃ o, P.index (frozenFaceDart n w d ell hell word c hc f P select hm k F j) = .inl (.inr ⟨k,o,j⟩) :=
  (frozenFaceSide_exists n w d ell hell word c hc f P select hm k F j).choose_spec.2
lemma frozenFaceDart_selected (k : FrozenCell n w d)
    (F : KindFace n w d ell hell word c hc f P select (.inr k)) (j : Fin ((frozenBoundary n w d).size k)) :
    select (P.faceClass (frozenFaceDart n w d ell hell word c hc f P select hm k F j)) = true := by
  rw [frozenFaceDart_face]
  exact F.property.1

lemma frozenFaceDart_injective (k : FrozenCell n w d) : Function.Injective
    (fun p : KindFace n w d ell hell word c hc f P select (.inr k) × Fin ((frozenBoundary n w d).size k) =>
      frozenFaceDart n w d ell hell word c hc f P select hm k p.1 p.2) := by
  intro p q h
  apply Prod.ext
  · apply Subtype.ext
    have hf := congrArg P.faceClass h
    simpa only [frozenFaceDart_face] using hf
  · obtain ⟨o,ho⟩ := frozenFaceDart_index n w d ell hell word c hc f P select hm k p.1 p.2
    obtain ⟨o',ho'⟩ := frozenFaceDart_index n w d ell hell word c hc f P select hm k q.1 q.2
    have hh := congrArg P.index h
    rw [ho,ho'] at hh
    have he : (o, p.2) = (o', q.2) := eq_of_heq (Sigma.mk.inj_iff.mp (Sum.inr.inj (Sum.inl.inj hh))).2
    exact congrArg (fun t : Bool × Fin ((frozenBoundary n w d).size k) => t.2) he

end HyperbolicObstruction.ConeSkeleton.RelDisk
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_RelativeExceptional
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeApexInstance _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedOccurrence _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSelectedTop _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSix _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeOutsideContact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace HyperbolicObstruction.ConeSkeleton.RelDisk
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
universe u
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable (ell : ℕ) (hell : 0 < ell) (word : Fin ell → Alphabet n)
variable {A : Type*} [AddCommGroup A]
variable (c : Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A)
variable (P : WalkPicture.{0} (target n w d ell hell word c hc f))

lemma exceptional_next (hs : P.Simple) (hb : P.NoBigon)
    {x : P.Dart} {a : Top n w} (hx : P.index x = .inl (.inl (a,exceptionalMacro))) :
    P.index (P.pairing.face x) = .inl (.inl (a,looseMacro)) := by
  obtain ⟨e,he⟩ := exterior_same_top n w d ell hell (letterDart n w ∘ word) (letterWordClosed n w ell word) c hc f P hx (SameCycle.rfl.apply_right)
  have hh := P.closed x
  change (target n w d ell hell word c hc f).front (P.index (P.pairing.face x)) = (target n w d ell hell word c hc f).back (P.index x) at hh
  rw [he,hx] at hh
  have hf : e.fst = MacroGraph.exceptional := congrArg Prod.snd (Sum.inl.inj (Sum.inl.inj hh))
  have hn : e ≠ exceptionalMacro.symm := by
    intro hh
    apply P.free_sameface_not_opposite hs hb (x := x) (y := P.pairing.face x) (by rw [hx]; rfl)
      (SameCycle.rfl.apply_right)
    rw [he,hx,hh]; rfl
  rw [he,exceptional_successor e hf hn]

lemma exceptional_previous (hs : P.Simple) (hb : P.NoBigon)
    {x : P.Dart} {a : Top n w} (hx : P.index x = .inl (.inl (a,exceptionalMacro.symm))) :
    P.index (P.pairing.face⁻¹ x) = .inl (.inl (a,looseMacro.symm)) := by
  have hxy : P.pairing.face.SameCycle x (P.pairing.face⁻¹ x) :=
    sameCycle_inv.mp (SameCycle.rfl.apply_right)
  obtain ⟨e,he⟩ := exterior_same_top n w d ell hell (letterDart n w ∘ word) (letterWordClosed n w ell word) c hc f P hx hxy
  have hh := P.closed (P.pairing.face⁻¹ x)
  rw [Perm.inv_def,apply_symm_apply] at hh
  change (target n w d ell hell word c hc f).front (P.index x) = (target n w d ell hell word c hc f).back (P.index (P.pairing.face⁻¹ x)) at hh
  rw [he,hx] at hh
  have hf : e.snd = MacroGraph.exceptional := (congrArg Prod.snd (Sum.inl.inj (Sum.inl.inj hh))).symm
  have hn : e ≠ exceptionalMacro := by
    intro hh
    apply P.free_sameface_not_opposite hs hb (x := x) (y := P.pairing.face⁻¹ x) (by rw [hx]; rfl) hxy
    rw [he,hx,hh]; rfl
  rw [he,exceptional_predecessor e hf hn]

end HyperbolicObstruction.ConeSkeleton.RelDisk
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_RelativePayment
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeKindFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeRawPositionSide _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTriangleFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeFan _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSix _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeSquare _root_.OAI.HyperbolicObstruction.ConeSkeleton.instFintypeTop _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeOutsideContact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace HyperbolicObstruction.ConeSkeleton.RelDisk
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
universe u
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable (ell : ℕ) (hell : 0 < ell) (word : Fin ell → Alphabet n)
variable {A : Type*} [AddCommGroup A]
variable (c : Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A)
variable (P : WalkPicture.{0} (target n w d ell hell word c hc f))

variable (select : P.Face → Bool)

lemma top_exceptional_incoming {x : P.Dart} {a : Top n w} {e : MacroGraph.graph.Dart}
    (hx : P.index x = .inl (.inl (a,e)))
    (ha : isApex n w (start n w ((target n w d ell hell word c hc f).label (P.index x))) = true)
    (hl : dartPart n w ((target n w d ell hell word c hc f).label (P.index (P.pairing.vertex⁻¹ x))) = false) :
    P.index (P.pairing.face⁻¹ x) = .inl (.inl (a,exceptionalMacro.symm)) := by
  obtain ⟨k,hk⟩ := exterior_same_top n w d ell hell (letterDart n w ∘ word) (letterWordClosed n w ell word) c hc f P hx
    (sameCycle_inv.mp (SameCycle.rfl.apply_right))
  have hei : (target n w d ell hell word c hc f).label (P.index (P.pairing.vertex⁻¹ x)) =
      rev n w ((target n w d ell hell word c hc f).label (P.index (P.pairing.face⁻¹ x))) := by
    rw [vertex_inverse]
    exact P.paired _
  have hax : isApex n w (start n w ((target n w d ell hell word c hc f).label (P.index (P.pairing.vertex⁻¹ x)))) = true :=
    (walk_apex_previous n w d ell hell word c hc f P x).trans ha
  rw [hei,hk] at hl hax
  have hlab : macroStep n w a k.symm.adj = rev n w (macroStep n w a k.adj) :=
    macroStep_reverse n w a k.adj
  have he : k.symm = exceptionalMacro := macro_exceptional_port n w a k.symm
    (by rw [hlab]; exact hax)
    (by rw [hlab]; exact hl)
  have hh : k = exceptionalMacro.symm := congrArg SimpleGraph.Dart.symm he
  rw [hk,hh]

variable (hs : P.Simple) (hb : P.NoBigon)
  (hm : P.FrozenMapped (frozen n w d ell hell word c hc f))
  (hred : P.FullyReduced) (hrad : P.RadialInjective (isApex n w))

abbrev AllPaymentIndex := Σ b : Fan n w,
  (indexedFanData n w d ell hell word c hc f P select b hs hm hred hrad).PaymentIndex

abbrev paymentCorner (p : AllPaymentIndex n w d ell hell word c hc f P select hs hm hred hrad) := p.2.val.1.2.val
abbrev paymentBool (p : AllPaymentIndex n w d ell hell word c hc f P select hs hm hred hrad) := p.2.val.2

def paymentRawDart (p : AllPaymentIndex n w d ell hell word c hc f P select hs hm hred hrad) : P.Dart :=
  if paymentBool n w d ell hell word c hc f P select hs hm hred hrad p then
    P.pairing.face (paymentCorner n w d ell hell word c hc f P select hs hm hred hrad p)
  else P.pairing.face⁻¹ (P.pairing.face⁻¹ (paymentCorner n w d ell hell word c hc f P select hs hm hred hrad p))

include hb in
lemma payment_raw_index (p : AllPaymentIndex n w d ell hell word c hc f P select hs hm hred hrad) :
    ∃ a, P.index (paymentRawDart n w d ell hell word c hc f P select hs hm hred hrad p) =
      .inl (.inl (a,if paymentBool n w d ell hell word c hc f P select hs hm hred hrad p then looseMacro else looseMacro.symm)) := by
  obtain ⟨F,hF⟩ := p.2.property.1
  obtain ⟨e,he⟩ := mark_top_index n w d ell hell word c hc f P select p.1 p.2.val.1.1 p.2.val.1.2 F hF
  let a := selectedOccurrence n w d ell hell word c hc f P select p.1 F
  refine ⟨a,?_⟩
  have ha := instance_apex n w d ell hell word c hc f P select p.1 p.2.val.1.1 p.2.val.1.2
  have hl := p.2.property.2
  cases ho : paymentBool n w d ell hell word c hc f P select hs hm hred hrad p
  · have hl' : dartPart n w ((target n w d ell hell word c hc f).label (P.index (P.pairing.vertex⁻¹ p.2.val.1.2.val))) = false := by
      simpa only [indexedFanData,ho,Bool.false_eq_true,↓reduceIte,P.linkNext_val] using hl
    have hx := top_exceptional_incoming n w d ell hell word c hc f P he ha hl'
    simpa only [paymentRawDart,ho,Bool.false_eq_true,↓reduceIte] using
      exceptional_previous n w d ell hell word c hc f P hs hb hx
  · have hl' : dartPart n w (macroStep n w a e.adj) = false := by
      simpa only [indexedFanData,ho,↓reduceIte,he,target,exteriorWalkTarget,WalkCellTarget.withExterior,Sum.elim_inl,walkTarget,walkLabel] using hl
    have hh : e = exceptionalMacro := macro_exceptional_port n w a e
      (by simpa only [he,target,exteriorWalkTarget,WalkCellTarget.withExterior,Sum.elim_inl,walkTarget,walkLabel] using ha) hl'
    have hx : P.index p.2.val.1.2.val = .inl (.inl (a,exceptionalMacro)) := by rw [he,hh]
    simpa only [paymentRawDart,ho,↓reduceIte] using
      exceptional_next n w d ell hell word c hc f P hs hb hx

lemma payment_selected (p : AllPaymentIndex n w d ell hell word c hc f P select hs hm hred hrad) :
    select (P.faceClass (paymentRawDart n w d ell hell word c hc f P select hs hm hred hrad p)) = true := by
  obtain ⟨F,hF⟩ := p.2.property.1
  have hf := mark_top_face n w d ell hell word c hc f P select p.1 p.2.val.1.1 p.2.val.1.2 F hF
  have hx : select (P.faceClass p.2.val.1.2.val) = true := by rw [← hf]; exact F.property.1
  unfold paymentRawDart
  split_ifs <;> simpa only [P.faceClass_apply,P.faceClass_previous] using hx

lemma payment_param_injective : Function.Injective (fun p : AllPaymentIndex n w d ell hell word c hc f P select hs hm hred hrad =>
    (paymentCorner n w d ell hell word c hc f P select hs hm hred hrad p,paymentBool n w d ell hell word c hc f P select hs hm hred hrad p)) := by
  rintro ⟨b,⟨⟨⟨z,x⟩,o⟩,hp⟩⟩ ⟨a,⟨⟨⟨y,k⟩,q⟩,hq⟩⟩ hh
  obtain ⟨hx,ho⟩ := Prod.mk.inj hh
  have hv := apexCorner_injective n w d ell hell word c hc f P select (a₁ := ⟨b,z,x⟩) (a₂ := ⟨a,y,k⟩) hx
  have hb : b = a := congrArg Sigma.fst hv
  subst a
  have hz : z = y := congrArg Sigma.fst (eq_of_heq (Sigma.mk.inj_iff.mp hv).2)
  subst y
  have hk : x = k := Subtype.ext hx
  subst k
  change o = q at ho
  subst q
  rfl

include hb in
lemma paymentRawDart_injective : Function.Injective
    (paymentRawDart n w d ell hell word c hc f P select hs hm hred hrad) := by
  intro p q he
  apply payment_param_injective n w d ell hell word c hc f P select hs hm hred hrad
  have ho : paymentBool n w d ell hell word c hc f P select hs hm hred hrad p =
      paymentBool n w d ell hell word c hc f P select hs hm hred hrad q := by
    obtain ⟨a,ha⟩ := payment_raw_index n w d ell hell word c hc f P select hs hb hm hred hrad p
    obtain ⟨b,hb⟩ := payment_raw_index n w d ell hell word c hc f P select hs hb hm hred hrad q
    have hh := congrArg P.index he
    rw [ha,hb] at hh
    have hh' := congrArg (fun t : Top n w × MacroGraph.graph.Dart => t.2.fst) (Sum.inl.inj (Sum.inl.inj hh))
    cases hp : paymentBool n w d ell hell word c hc f P select hs hm hred hrad p <;>
      cases hq : paymentBool n w d ell hell word c hc f P select hs hm hred hrad q <;>
      simp only [hp,hq,Bool.false_eq_true,↓reduceIte] at hh' ⊢
    all_goals cases hh'
  refine Prod.ext ?_ ho
  unfold paymentRawDart at he
  rw [ho] at he
  split_ifs at he
  · exact P.pairing.face.injective he
  · exact (P.pairing.face⁻¹).injective ((P.pairing.face⁻¹).injective he)

end HyperbolicObstruction.ConeSkeleton.RelDisk
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_RelativeRawCount
attribute [-instance] _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedFace _root_.OAI.HyperbolicObstruction.ConeSkeleton.RelDisk.instFintypeSelectedTopFace _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeOutsideContact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace HyperbolicObstruction.ConeSkeleton.RelDisk
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
universe u
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable (ell : ℕ) (hell : 0 < ell) (word : Fin ell → Alphabet n)
variable {A : Type*} [AddCommGroup A]
variable (c : Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A)
variable (P : WalkPicture.{0} (target n w d ell hell word c hc f))

variable (select : P.Face → Bool)
variable (hs : P.Simple) (hm : P.FrozenMapped (frozen n w d ell hell word c hc f))
  (hred : P.FullyReduced) (hrad : P.RadialInjective (isApex n w))

abbrev DecorationSideIndex := Σ k : Square n w ⊕ Six n d,
  KindFace n w d ell hell word c hc f P select (.inr (.inr k)) × Fin ((frozenBoundary n w d).size (.inr k))

def decorationRawDart (p : DecorationSideIndex n w d ell hell word c hc f P select) : P.Dart :=
  frozenFaceDart n w d ell hell word c hc f P select hm (.inr p.1) p.2.1 p.2.2

lemma decorationRawDart_injective : Function.Injective
    (decorationRawDart n w d ell hell word c hc f P select hm) := by
  rintro ⟨k,F,j⟩ ⟨k',F',j'⟩ hh
  obtain ⟨o,ho⟩ := frozenFaceDart_index n w d ell hell word c hc f P select hm (.inr k) F j
  obtain ⟨o',ho'⟩ := frozenFaceDart_index n w d ell hell word c hc f P select hm (.inr k') F' j'
  have he := congrArg P.index hh
  change P.index (frozenFaceDart n w d ell hell word c hc f P select hm (.inr k) F j) =
    P.index (frozenFaceDart n w d ell hell word c hc f P select hm (.inr k') F' j') at he
  rw [ho,ho'] at he
  have hk : k = k' := Sum.inr.inj (congrArg Sigma.fst (Sum.inr.inj (Sum.inl.inj he)))
  subst k'
  exact Sigma.ext rfl (heq_of_eq (frozenFaceDart_injective n w d ell hell word c hc f P select hm (.inr k) hh))

lemma decorationRawDart_raw (p : DecorationSideIndex n w d ell hell word c hc f P select) :
    rawDart n w d ell hell word c hc f P (decorationRawDart n w d ell hell word c hc f P select hm p) := by
  obtain ⟨o,ho⟩ := frozenFaceDart_index n w d ell hell word c hc f P select hm (.inr p.1) p.2.1 p.2.2
  unfold rawDart decorationRawDart
  rw [ho]
  rcases p with ⟨k,F,j⟩
  rcases k with k | k
  · change Fin 4 at j
    fin_cases j <;> cases o <;> rfl
  · cases o <;> rfl

abbrev RawAccountIndex := AllPaymentIndex n w d ell hell word c hc f P select hs hm hred hrad ⊕
  (AllTriangleIndex n w d ell hell word c hc f P select hs hm hred hrad ⊕
    DecorationSideIndex n w d ell hell word c hc f P select)

def accountDart : RawAccountIndex n w d ell hell word c hc f P select hs hm hred hrad → P.Dart :=
  Sum.elim (paymentRawDart n w d ell hell word c hc f P select hs hm hred hrad)
    (Sum.elim (triangleRawDart n w d ell hell word c hc f P select hs hm hred hrad)
      (decorationRawDart n w d ell hell word c hc f P select hm))

lemma accountDart_injective (hb : P.NoBigon) : Function.Injective
    (accountDart n w d ell hell word c hc f P select hs hm hred hrad) := by
  intro p q hh
  have hi := congrArg P.index hh
  rcases p with p | (p | p) <;> rcases q with q | (q | q)
  all_goals dsimp only [accountDart,Sum.elim,decorationRawDart] at hh hi
  · exact congrArg Sum.inl (paymentRawDart_injective n w d ell hell word c hc f P select hs hb hm hred hrad hh)
  · obtain ⟨a,ha⟩ := payment_raw_index n w d ell hell word c hc f P select hs hb hm hred hrad p
    obtain ⟨g,o,hg⟩ := triangle_raw_index n w d ell hell word c hc f P select hs hm hred hrad q
    change P.index (paymentRawDart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ p) = _ at hi
    rw [ha,hg] at hi; cases hi
  · obtain ⟨a,ha⟩ := payment_raw_index n w d ell hell word c hc f P select hs hb hm hred hrad p
    obtain ⟨o,hg⟩ := frozenFaceDart_index n w d ell hell word c hc f P select hm (.inr q.1) q.2.1 q.2.2
    change P.index (paymentRawDart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ p) = _ at hi
    rw [ha,hg] at hi; cases hi
  · obtain ⟨a,ha⟩ := payment_raw_index n w d ell hell word c hc f P select hs hb hm hred hrad q
    obtain ⟨g,o,hg⟩ := triangle_raw_index n w d ell hell word c hc f P select hs hm hred hrad p
    change P.index (triangleRawDart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ p) = _ at hi
    rw [ha,hg] at hi; cases hi
  · exact congrArg (Sum.inr ∘ Sum.inl) (triangleRawDart_injective n w d ell hell word c hc f P select hs hm hred hrad hh)
  · obtain ⟨g,o,hg⟩ := triangle_raw_index n w d ell hell word c hc f P select hs hm hred hrad p
    obtain ⟨o',hk⟩ := frozenFaceDart_index n w d ell hell word c hc f P select hm (.inr q.1) q.2.1 q.2.2
    change P.index (triangleRawDart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ p) = _ at hi
    rw [hg,hk] at hi
    have he := congrArg Sigma.fst (Sum.inr.inj (Sum.inl.inj hi))
    cases he
  · obtain ⟨a,ha⟩ := payment_raw_index n w d ell hell word c hc f P select hs hb hm hred hrad q
    obtain ⟨o,hg⟩ := frozenFaceDart_index n w d ell hell word c hc f P select hm (.inr p.1) p.2.1 p.2.2
    change P.index (frozenFaceDart _ _ _ _ _ _ _ _ _ _ _ _ _ p.2.1 p.2.2) = _ at hi
    rw [ha,hg] at hi; cases hi
  · obtain ⟨g,o,hg⟩ := triangle_raw_index n w d ell hell word c hc f P select hs hm hred hrad q
    obtain ⟨o',hk⟩ := frozenFaceDart_index n w d ell hell word c hc f P select hm (.inr p.1) p.2.1 p.2.2
    change P.index (frozenFaceDart _ _ _ _ _ _ _ _ _ _ _ _ _ p.2.1 p.2.2) = _ at hi
    rw [hg,hk] at hi
    have he := congrArg Sigma.fst (Sum.inr.inj (Sum.inl.inj hi))
    cases he
  · exact congrArg (Sum.inr ∘ Sum.inr) (decorationRawDart_injective n w d ell hell word c hc f P select hm hh)

lemma accountDart_selected (p : RawAccountIndex n w d ell hell word c hc f P select hs hm hred hrad) :
    selectedDart n w d ell hell word c hc f P select (accountDart n w d ell hell word c hc f P select hs hm hred hrad p) := by
  rcases p with p | (p | p)
  · exact payment_selected n w d ell hell word c hc f P select hs hm hred hrad p
  · change select (P.faceClass (P.pairing.face _)) = true
    rw [P.faceClass_apply]
    exact triangle_selected n w d ell hell word c hc f P select hs hm hred hrad p
  · exact frozenFaceDart_selected n w d ell hell word c hc f P select hm (.inr p.1) p.2.1 p.2.2

lemma accountDart_raw (hb : P.NoBigon)
    (p : RawAccountIndex n w d ell hell word c hc f P select hs hm hred hrad) :
    rawDart n w d ell hell word c hc f P (accountDart n w d ell hell word c hc f P select hs hm hred hrad p) := by
  rcases p with p | (p | p)
  · obtain ⟨a,ha⟩ := payment_raw_index n w d ell hell word c hc f P select hs hb hm hred hrad p
    change isLetter n w ((target n w d ell hell word c hc f).label (P.index (paymentRawDart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ p))) = true
    rw [ha]
    cases ho : paymentBool n w d ell hell word c hc f P select hs hm hred hrad p <;> rfl
  · obtain ⟨g,o,hg⟩ := triangle_raw_index n w d ell hell word c hc f P select hs hm hred hrad p
    change isLetter n w ((target n w d ell hell word c hc f).label (P.index (triangleRawDart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ p))) = true
    rw [hg]
    cases o <;> rfl
  · exact decorationRawDart_raw n w d ell hell word c hc f P select hm p

end HyperbolicObstruction.ConeSkeleton.RelDisk
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_RelativeFragment
attribute [-instance] _root_.OAI.HyperbolicObstruction.PictureSwitch.instFintypeOutsideContact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace HyperbolicObstruction.ConeSkeleton.RelDisk
open IncidenceTemplate.Occurrences.Shape
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
universe u
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable (ell : ℕ) (hell : 0 < ell) (word : Fin ell → Alphabet n)
variable {A : Type*} [AddCommGroup A]
variable (c : Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A)
variable (P : WalkPicture.{0} (target n w d ell hell word c hc f))

variable (select : P.Face → Bool)
variable (hsel : InteriorSelection n w d ell hell word c hc f P select)
variable (hs : P.Simple) (hm : P.FrozenMapped (frozen n w d ell hell word c hc f))
  (hred : P.FullyReduced) (hrad : P.RadialInjective (isApex n w))

def actualFanWeight := ∑ b : Fan n w, (indexedFanData n w d ell hell word c hc f P select b hs hm hred hrad).weight
def actualPayments := ∑ b : Fan n w, (indexedFanData n w d ell hell word c hc f P select b hs hm hred hrad).payments
def actualPartialCount := ∑ b : Fan n w, (indexedFanData n w d ell hell word c hc f P select b hs hm hred hrad).partialCount
def actualBoundary := Fintype.card (ActualRawBoundary n w d ell hell word c hc f P select) +
  Fintype.card (RadialBoundarySide n w d ell hell word c hc f P select)

end HyperbolicObstruction.ConeSkeleton.RelDisk
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_RelativePartitionEstimate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace HyperbolicObstruction.ConeSkeleton.RelDisk

section
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
universe u
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable (ell : ℕ) (hell : 0 < ell) (word : Fin ell → Alphabet n)
variable {A : Type*} [AddCommGroup A]
variable (c : Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A)
variable (P : WalkPicture.{0} (target n w d ell hell word c hc f))

lemma actual_boundary_card (select : P.Face → Bool) :
    actualBoundary n w d ell hell word c hc f P select =
      Fintype.card {x : P.Dart // select (P.faceClass x) = true ∧
        select (P.faceClass (P.pairing.edge x)) ≠ true} := by
  rw [actualBoundary,← Fintype.card_sum]
  let g : ActualRawBoundary n w d ell hell word c hc f P select ⊕ RadialBoundarySide n w d ell hell word c hc f P select →
      {x : P.Dart // select (P.faceClass x) = true ∧ select (P.faceClass (P.pairing.edge x)) ≠ true} :=
    Sum.elim (fun x => ⟨x.val,x.property.2⟩) (fun x => ⟨x.val,x.property.2⟩)
  apply Fintype.card_congr (Equiv.ofBijective g ?_)
  constructor
  · intro x y h
    have he := congrArg Subtype.val h
    rcases x with x | x <;> rcases y with y | y
    · exact congrArg Sum.inl (Subtype.ext he)
    · have hx := x.property.1
      have hy := y.property.1
      change x.val = y.val at he
      dsimp only [rawDart] at hx
      dsimp only [walkRadial] at hy
      rw [he,hy] at hx
      cases hx
    · have hx := x.property.1
      have hy := y.property.1
      change x.val = y.val at he
      dsimp only [rawDart] at hy
      dsimp only [walkRadial] at hx
      rw [he,hy] at hx
      cases hx
    · exact congrArg Sum.inr (Subtype.ext he)
  · rintro ⟨x,hx,he⟩
    cases hr : isLetter n w ((target n w d ell hell word c hc f).label (P.index x)) with
    | false => exact ⟨.inr ⟨x,hr,hx,he⟩,rfl⟩
    | true => exact ⟨.inl ⟨x,hr,hx,he⟩,rfl⟩

end

open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch Equiv Equiv.Perm
open scoped BigOperators
open Occurrences.Shape
attribute [local instance] Classical.propDecidable
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable (ell : ℕ) (hell : 0 < ell) (word : Fin ell → Alphabet n)
variable {A : Type*} [AddCommGroup A]
variable (c : Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A)
variable (P : WalkPicture.{0} (target n w d ell hell word c hc f))

/-- Literal interior cells: the exterior cell kind is not selected. -/
def Interior (F : P.Face) : Prop := ∃ k, P.faceKind F = .inl k
abbrev InteriorFace := {F : P.Face // Interior n w d ell hell word c hc f P F}

end HyperbolicObstruction.ConeSkeleton.RelDisk
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_LiftedBasis
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
universe u v

/-- One (unoriented) elementary top triangle per actual macro edge. The finite
vertex numbering only chooses signs; it does not identify different edges. -/
abbrev MacroCell := {e : Sym2 MacroGraph.Vertex // e ∈ MacroGraph.graph.edgeSet}

def macroCell (e : MacroGraph.graph.Dart) : MacroCell := ⟨e.edge,e.edge_mem⟩
lemma macroCell_symm (e : MacroGraph.graph.Dart) : macroCell e.symm = macroCell e := by
  apply Subtype.ext
  exact e.edge_symm

def macroOrientation (e : MacroGraph.graph.Dart) : ℤ :=
  if Fintype.equivFin MacroGraph.Vertex e.fst < Fintype.equivFin MacroGraph.Vertex e.snd
    then 1 else -1

lemma macroOrientation_symm (e : MacroGraph.graph.Dart) :
    macroOrientation e.symm = -macroOrientation e := by
  have hne : Fintype.equivFin MacroGraph.Vertex e.fst ≠ Fintype.equivFin MacroGraph.Vertex e.snd :=
    fun h => e.fst_ne_snd ((Fintype.equivFin _).injective h)
  change (if Fintype.equivFin MacroGraph.Vertex e.snd < Fintype.equivFin MacroGraph.Vertex e.fst
    then (1:ℤ) else -1) = - (if Fintype.equivFin MacroGraph.Vertex e.fst <
      Fintype.equivFin MacroGraph.Vertex e.snd then 1 else -1)
  rcases lt_or_gt_of_ne hne with h | h
  · rw [ite_eq_left h,ite_eq_right (not_lt_of_ge h.le)]
  · rw [ite_eq_left h,ite_eq_right (not_lt_of_ge h.le)]; norm_num

variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool) (G : Type v)

/-- Integral chains with independent coordinates for every deck translate of
an elementary top triangle, fan triangle, square, or six-cell. No topological
realization or equation on these chains is part of the definition. -/
abbrev LiftedCellularChain := (G × ((Top n w × MacroCell) ⊕ FrozenCell n w d)) →₀ ℤ

end HyperbolicObstruction.ConeSkeleton
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_ElementaryCone
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

lemma macroCell_representative (c : MacroCell) :
    ∃ e : MacroGraph.graph.Dart, macroCell e = c ∧ macroOrientation e = 1 := by
  have h : ∃ e : MacroGraph.graph.Dart, macroCell e = c := by
    rcases c with ⟨c,hc⟩
    induction c using Sym2.inductionOn with
    | hf a b => exact ⟨⟨(a,b),hc⟩,rfl⟩
  obtain ⟨e,he⟩ := h
  by_cases ho : macroOrientation e = 1
  · exact ⟨e,he,ho⟩
  · refine ⟨e.symm,(macroCell_symm e).trans he,?_⟩
    rw [macroOrientation_symm]
    have hn : macroOrientation e = -1 := by
      have hh : macroOrientation e = 1 ∨ macroOrientation e = -1 := by
        unfold macroOrientation
        split_ifs <;> simp
      exact hh.resolve_left ho
    rw [hn]; norm_num

/-- A canonical positive orientation, with exactly ONE elementary triangle
per unoriented macro edge. No redundant simple-cycle disks are introduced. -/
def macroCellDart (c : MacroCell) : MacroGraph.graph.Dart := (macroCell_representative c).choose

variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)

/-- The actual pre-compression finite incidence data:
old fan apices, separate top apices, every labelled radial edge, and elementary
triangles. This data is not claimed to be a constructed topological CW space. -/
abbrev ElementaryVertex := Vertex n w ⊕ Top n w
abbrev ElementaryEdge := Edge n w ⊕ (Top n w × MacroGraph.Vertex)
abbrev ElementaryDart := ElementaryEdge n w × Bool
abbrev ElementaryCell := (Top n w × MacroCell) ⊕ FrozenCell n w d

def elementaryOld (e : Dart n w) : ElementaryDart n w := (.inl e.1,e.2)
def elementaryRev (e : ElementaryDart n w) : ElementaryDart n w := (e.1,!e.2)
def elementaryStart : ElementaryDart n w → ElementaryVertex n w
  | (.inl e,b) => .inl (start n w (e,b))
  | (.inr a,true) => .inr a.1
  | (.inr a,false) => .inl (macroVertex n w a.1 a.2)

lemma elementaryRev_rev (e : ElementaryDart n w) :
    elementaryRev n w (elementaryRev n w e) = e := by
  rcases e with ⟨e,b⟩; cases b <;> rfl

/-- The three literal sides of a top cone triangle, including its two new
radial edges; arbitrary repeated OLD endpoints remain allowed. -/
def elementaryTriangle (a : Top n w) (e : MacroGraph.graph.Dart) : Fin 3 → ElementaryDart n w :=
  ![(.inr (a,e.fst),true), elementaryOld n w (macroStep n w a e.adj), (.inr (a,e.snd),false)]

lemma elementaryTriangle_closed (a : Top n w) (e : MacroGraph.graph.Dart) (i : Fin 3) :
    elementaryStart n w (elementaryTriangle n w a e (finRotate 3 i)) =
      elementaryStart n w (elementaryRev n w (elementaryTriangle n w a e i)) := by
  fin_cases i
  · change Sum.inl (start n w (macroStep n w a e.adj)) = Sum.inl (macroVertex n w a e.fst)
    exact congrArg Sum.inl (macroStep_start n w a e.adj)
  · change Sum.inl (macroVertex n w a e.snd) = Sum.inl (start n w (rev n w (macroStep n w a e.adj)))
    exact congrArg Sum.inl (macroStep_end n w a e.adj).symm
  · rfl

def elementarySize : ElementaryCell n w d → ℕ
  | .inl _ => 3
  | .inr a => (frozenBoundary n w d).size a

def elementarySide : (a : ElementaryCell n w d) → Fin (elementarySize n w d a) → ElementaryDart n w
  | .inl a => elementaryTriangle n w a.1 (macroCellDart a.2)
  | .inr a => fun i => elementaryOld n w ((frozenBoundary n w d).label a i)

/-- Full boundary certificate for the actual elementary two-cells. -/
def elementaryBoundary : PolygonTarget.Boundary (ElementaryCell n w d) (ElementaryDart n w)
    (ElementaryVertex n w) where
  size := elementarySize n w d
  positive := by rintro (a|a); exact Nat.zero_lt_succ _; exact (frozenBoundary n w d).positive a
  label := elementarySide n w d
  start := elementaryStart n w
  rev := elementaryRev n w
  inv := elementaryRev_rev n w
  closed := by
    rintro (a|a) i
    · exact elementaryTriangle_closed n w a.1 (macroCellDart a.2) i
    · exact congrArg Sum.inl ((frozenBoundary n w d).closed a i)

variable {G : Type*} [Group G] (v : Dart n w → G)
  (hv : ∀ e, v (rev n w e) = (v e)⁻¹)
  (hcell : ∀ a : Cell n w d, (List.ofFn (fun i => v (side n w d a i))).prod = 1)

/-- Extension to the actual top radial edges. Deck coordinates of a top lift
are measured at its apex, so all of its elementary triangles have the same
apex coordinate used by `LiftedCellularChain`. -/
def elementaryVoltage : ElementaryDart n w → G
  | (.inl e,b) => v (e,b)
  | (.inr a,true) => macroPotential n w v a.1 a.2
  | (.inr a,false) => (macroPotential n w v a.1 a.2)⁻¹

include hv in
lemma elementaryVoltage_rev (e : ElementaryDart n w) :
    elementaryVoltage n w v (elementaryRev n w e) = (elementaryVoltage n w v e)⁻¹ := by
  rcases e with ⟨e|a,b⟩
  · exact hv (e,b)
  · cases b <;> simp [elementaryVoltage,elementaryRev]

include hv hcell in
lemma elementaryVoltage_triangle (a : Top n w) (e : MacroGraph.graph.Dart) :
    (List.ofFn (fun i => elementaryVoltage n w v (elementaryTriangle n w a e i))).prod = 1 := by
  have he := macroPotential_edge n w d v hv hcell a e.adj
  simp only [elementaryTriangle,List.ofFn_succ,List.ofFn_zero,Matrix.cons_val_zero,Matrix.cons_val_succ,
    List.prod_cons,List.prod_nil,elementaryOld,elementaryVoltage,mul_one]
  rw [← mul_assoc,he,mul_inv_cancel]

include hv hcell in
lemma elementaryVoltage_cell (a : ElementaryCell n w d) :
    (List.ofFn (fun i => elementaryVoltage n w v (elementarySide n w d a i))).prod = 1 := by
  rcases a with a|a
  · exact elementaryVoltage_triangle n w d v hv hcell a.1 (macroCellDart a.2)
  · exact hcell (frozenCell n w d a)

end HyperbolicObstruction.ConeSkeleton
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_ElementaryCover
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
variable {G : Type*} [Group G] (v : Dart n w → G)
  (hv : ∀ e, v (rev n w e) = (v e)⁻¹)
  (hcell : ∀ a : Cell n w d, (List.ofFn (fun i => v (side n w d a i))).prod = 1)

/-- Deck offset from the specified basepoint of each literal elementary cell.
For a triangle, that basepoint is its top apex; for a frozen cell it is the
initial vertex of the fixed boundary indexing. -/
def elementaryOffset (a : ElementaryCell n w d) (i : Fin (elementarySize n w d a)) : G :=
  ((List.ofFn (fun j => elementaryVoltage n w v (elementarySide n w d a j))).take i.val).prod

include hv hcell in
lemma elementaryOffset_next (a : ElementaryCell n w d) (i : Fin (elementarySize n w d a)) :
    elementaryOffset n w d v a (finRotate _ i) =
      elementaryOffset n w d v a i * elementaryVoltage n w v (elementarySide n w d a i) :=
  group_prefix_rotate _ (elementaryVoltage_cell n w d v hv hcell a) i

/-- Literal elementary boundary incidence in the voltage cover, at every deck
translate, including the wraparound side. No covering-space or CW-realization
assertion is made by this finite incidence construction. -/
def elementaryLiftedBoundary : PolygonTarget.Boundary
    (G × ElementaryCell n w d) (G × ElementaryDart n w) (G × ElementaryVertex n w) where
  size a := elementarySize n w d a.2
  positive a := (elementaryBoundary n w d).positive a.2
  label a i := (a.1 * elementaryOffset n w d v a.2 i, elementarySide n w d a.2 i)
  start e := (e.1, elementaryStart n w e.2)
  rev e := (e.1 * elementaryVoltage n w v e.2, elementaryRev n w e.2)
  inv e := by
    apply Prod.ext
    · simp only [elementaryVoltage_rev n w v hv,mul_inv_cancel_right]
    · exact elementaryRev_rev n w e.2
  closed a i := by
    apply Prod.ext
    · exact (congrArg (a.1 * ·) (elementaryOffset_next n w d v hv hcell a.2 i)).trans
        (mul_assoc _ _ _).symm
    · exact (elementaryBoundary n w d).closed a.2 i

end HyperbolicObstruction.ConeSkeleton
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
namespace PictureSwitch

/-! Literal radial triangulation of the free polygon faces of a finite map.
This section concerns genuine permutations; no topological genus assertion is
included in the input. -/

/-! Exact contraction of radial triangle stars. -/
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {D : Type*} [Fintype D] [DecidableEq D]

/-- The three roles are old side (0), incoming radial side (1), and outgoing
radial side (2). Frozen polygons have only old sides. These are local incidence
conditions on an existing side-pairing, not a genus or chain assumption. -/
structure TriangleMarking (M : PictureMap D) where
  top : D → Bool
  role : D → Fin 3
  top_face : ∀ x, top (M.face x) = top x
  frozen : ∀ x, top x = false → role x = 0
  turn : ∀ x, top x = true → role (M.face x) = finRotate 3 (role x)
  period : ∀ x, top x = true → M.face (M.face (M.face x)) = x
  edge0 : ∀ x, role x = 0 → role (M.edge x) = 0
  edge1 : ∀ x, role x = 1 → role (M.edge x) = 2
  edge2 : ∀ x, role x = 2 → role (M.edge x) = 1

namespace TriangleMarking
variable {M : PictureMap D} (H : TriangleMarking M)
abbrev Base := {x // H.role x = 0}

end TriangleMarking
end PictureSwitch

/-! Local elementary triangle incidence induces the exact radial contraction. -/
namespace ConeSkeleton

section
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable {G : Type*} [Group G] (v : Dart n w → G)
  (hv : ∀ e, v (rev n w e) = (v e)⁻¹)
  (hcell : ∀ a : Cell n w d, (List.ofFn (fun i => v (side n w d a i))).prod = 1)

abbrev ElementaryLiftSide := (elementaryLiftedBoundary n w d v hv hcell).Side

def elementaryTop (s : ElementaryLiftSide n w d v hv hcell) : Bool :=
  match s.1.2 with
  | .inl _ => true
  | .inr _ => false

def elementaryRole : ElementaryDart n w → Fin 3
  | (.inl _,_) => 0
  | (.inr _,false) => 1
  | (.inr _,true) => 2

def elementarySideRole (s : ElementaryLiftSide n w d v hv hcell) : Fin 3 :=
  elementaryRole n w ((elementaryLiftedBoundary n w d v hv hcell).sideLabel s).2

lemma elementaryRole_frozen (s : ElementaryLiftSide n w d v hv hcell)
    (h : elementaryTop n w d v hv hcell s = false) :
    elementarySideRole n w d v hv hcell s = 0 := by
  rcases s with ⟨⟨g,c|c⟩,b,i⟩
  · cases h
  · cases b <;> rfl

lemma elementaryRole_turn (s : ElementaryLiftSide n w d v hv hcell)
    (h : elementaryTop n w d v hv hcell s = true) :
    elementarySideRole n w d v hv hcell ((elementaryLiftedBoundary n w d v hv hcell).next s) =
      finRotate 3 (elementarySideRole n w d v hv hcell s) := by
  rcases s with ⟨⟨g,c|c⟩,b,i⟩
  · cases b <;> fin_cases i <;> rfl
  · cases h

lemma elementaryTop_period (s : ElementaryLiftSide n w d v hv hcell)
    (h : elementaryTop n w d v hv hcell s = true) :
    (elementaryLiftedBoundary n w d v hv hcell).next
      ((elementaryLiftedBoundary n w d v hv hcell).next
        ((elementaryLiftedBoundary n w d v hv hcell).next s)) = s := by
  rcases s with ⟨⟨g,c|c⟩,b,i⟩
  · cases b <;> fin_cases i <;> rfl
  · cases h

lemma elementaryRole_rev0 (e : ElementaryDart n w) (h : elementaryRole n w e = 0) :
    elementaryRole n w (elementaryRev n w e) = 0 := by
  rcases e with ⟨e|e,b⟩
  · rfl
  · cases b <;> cases h
lemma elementaryRole_rev1 (e : ElementaryDart n w) (h : elementaryRole n w e = 1) :
    elementaryRole n w (elementaryRev n w e) = 2 := by
  rcases e with ⟨e|e,b⟩
  · cases h
  · cases b <;> first | rfl | cases h
lemma elementaryRole_rev2 (e : ElementaryDart n w) (h : elementaryRole n w e = 2) :
    elementaryRole n w (elementaryRev n w e) = 1 := by
  rcases e with ⟨e|e,b⟩
  · cases h
  · cases b <;> first | rfl | cases h

variable {A : Type*} [AddCommGroup A] (weight : G × ElementaryCell n w d → A)

/-- Raw cellular target: coefficients always identify actual lifted elementary
cells; the boolean used here only disables unrelated normalization machinery. -/
def elementaryRawTarget := (elementaryLiftedBoundary n w d v hv hcell).target
  weight (fun _ => false) (by intro l h; cases h)

variable (P : CellPicture (elementaryRawTarget n w d v hv hcell weight))

def elementaryMarking : TriangleMarking P.pairing where
  top x := elementaryTop n w d v hv hcell (P.index x)
  role x := elementarySideRole n w d v hv hcell (P.index x)
  top_face x := by rw [P.mapped.commute]; rfl
  frozen x h := elementaryRole_frozen n w d v hv hcell (P.index x) h
  turn x h := by rw [P.mapped.commute]; exact elementaryRole_turn n w d v hv hcell (P.index x) h
  period x h := by
    apply P.mapped.injective (SameCycle.rfl.apply_left.apply_left.apply_left)
    rw [P.mapped.commute,P.mapped.commute,P.mapped.commute]
    exact elementaryTop_period n w d v hv hcell (P.index x) h
  edge0 x h := by
    change elementaryRole n w (((elementaryLiftedBoundary n w d v hv hcell).sideLabel
      (P.index (P.pairing.edge x))).2) = 0
    have he := congrArg Prod.snd (P.respects.2 x)
    change ((elementaryLiftedBoundary n w d v hv hcell).sideLabel (P.index (P.pairing.edge x))).2 =
      elementaryRev n w ((elementaryLiftedBoundary n w d v hv hcell).sideLabel (P.index x)).2 at he
    rw [he]
    exact elementaryRole_rev0 n w _ h
  edge1 x h := by
    change elementaryRole n w (((elementaryLiftedBoundary n w d v hv hcell).sideLabel
      (P.index (P.pairing.edge x))).2) = 2
    have he := congrArg Prod.snd (P.respects.2 x)
    change ((elementaryLiftedBoundary n w d v hv hcell).sideLabel (P.index (P.pairing.edge x))).2 =
      elementaryRev n w ((elementaryLiftedBoundary n w d v hv hcell).sideLabel (P.index x)).2 at he
    rw [he]
    exact elementaryRole_rev1 n w _ h
  edge2 x h := by
    change elementaryRole n w (((elementaryLiftedBoundary n w d v hv hcell).sideLabel
      (P.index (P.pairing.edge x))).2) = 1
    have he := congrArg Prod.snd (P.respects.2 x)
    change ((elementaryLiftedBoundary n w d v hv hcell).sideLabel (P.index (P.pairing.edge x))).2 =
      elementaryRev n w ((elementaryLiftedBoundary n w d v hv hcell).sideLabel (P.index x)).2 at he
    rw [he]
    exact elementaryRole_rev2 n w _ h

end

/-! Exact deck coordinates on the old and two radial sides of every triangle. -/

/-! Every genuine elementary genus-zero picture contracts to the unchanged
macro/frozen target, preserving the literal original-group deck coordinates. -/

section
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable {G : Type*} [Group G] (v : Dart n w → G)
  (hv : ∀ e, v (rev n w e) = (v e)⁻¹)
  (hcell : ∀ a : Cell n w d, (List.ofFn (fun i => v (side n w d a i))).prod = 1)
variable {A : Type*} [AddCommGroup A] (weight : G × ElementaryCell n w d → A)
  (P : CellPicture (elementaryRawTarget n w d v hv hcell weight))

abbrev ElementaryBases := (elementaryMarking n w d v hv hcell weight P).Base

end

/-! The radial contraction preserves every independent lifted elementary-cell
coefficient, not just an augmentation or a projection to the old edges. -/

/-! Every genus-zero picture over the literal elementary lifted-cell boundary
has zero FULL cellular chain, by exact radial contraction. -/
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch
attribute [local instance] Classical.propDecidable
universe u v z

end ConeSkeleton

/-! Lifting actual word homotopies to the voltage cover, with the negative
orientation based at the positive lift's initial endpoint. -/

/-!
The actual elementary triangles imply the compressed cone polygon equations.
Unlike the redundant polygon bouquet, this presentation retains exactly the
elementary indexed top triangles.
-/

section
namespace ConeSkeleton
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch
attribute [local instance] Classical.propDecidable

variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
variable {H : Type*} [_root_.Group H] (c : ElementaryDart n w → H)
  (hc : ∀ e, c (elementaryRev n w e) = (c e)⁻¹)
  (hcell : ∀ a : ElementaryCell n w d,
    (List.ofFn (fun i => c (elementarySide n w d a i))).prod = 1)

/-- The literal edge-bouquet presentation of the elementary cells. -/
abbrev ElementaryPolygonGroup := PresentedGroup
  (FreeGroup.mk '' Set.range (elementaryBoundary n w d).attachingWord)

def elementaryPolygonValue (e : ElementaryDart n w) : ElementaryPolygonGroup n w d :=
  PresentedGroup.mk _ (FreeGroup.mk [e])

end ConeSkeleton
end

namespace ConeSkeleton

open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch SimpleGraph
attribute [local instance] Classical.propDecidable

variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)

abbrev elementaryOldValue (e : Dart n w) : ElementaryPolygonGroup n w d :=
  elementaryPolygonValue n w d (elementaryOld n w e)

lemma base_fanVertex (i : Fin 7) : IsFanVertex i (.inl (CoreWordGraph.base i)) := by
  have hh : ∀ i : Fin 7, IsFanVertex i (.inl (CoreWordGraph.base i)) := by decide
  exact hh i

def fanBase (i : Fin 7) : FanVertex i := ⟨.inl (CoreWordGraph.base i),base_fanVertex i⟩

/-- The gauge at an old apex is its literal radial edge to the fixed fan base.
The bouquet vertex has gauge one. -/
def oldGauge : Vertex n w → ElementaryPolygonGroup n w d
  | .inl _ => 1
  | .inr f => elementaryOldValue n w d (.inr ⟨f,fanBase f.val.1⟩,true)

/-- The gauge at a top apex is based at the fixed macro root. -/
def elementaryGauge : ElementaryVertex n w → ElementaryPolygonGroup n w d
  | .inl v => oldGauge n w d v
  | .inr a => elementaryPolygonValue n w d (.inr (a,MacroGraph.point 0),true) *
      oldGauge n w d (macroVertex n w a (MacroGraph.point 0))

end ConeSkeleton

/-! Actual genus-zero disks for every closed elementary loop in the original
letter voltage cover. No cycle-representation or asphericity hypothesis. -/

namespace ConeSkeleton

/-! Signed-edge encoding preserves all individual cell identities and the
closed-picture chain. Sphere vanishing therefore applies to indexed disks. -/

/-! Actual integral boundaries for the uncompressed cone cells. -/
open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch

variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)

abbrev LetterC₂ := LiftedCellularChain n w d (LetterPresentation.Group n w d)
abbrev LetterC₁ := (LetterPresentation.Group n w d × ElementaryEdge n w) →₀ ℤ

end ConeSkeleton

/-! No reselection: the same final arrays already have the precise uniform
lifted-picture estimate. Apply the new disk-chain left inverse to those arrays. -/

/-! The actual elementary incidence data now defines an actual finite
barycentric polyhedron. This file proves compactness and connectivity only;
no CW-universal-cover comparison is smuggled in as a structure field. -/

namespace ConeSkeleton
open CoreGeometry IncidenceTemplate LetterPresentation FinitePolyhedron
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)
attribute [local instance] Classical.propDecidable
local instance instDecidableEqElementaryVertex : DecidableEq (ElementaryVertex n w) := Classical.decEq _
local instance instDecidableEqElementaryEdge : DecidableEq (ElementaryEdge n w) := Classical.decEq _
local instance instDecidableEqElementaryCell : DecidableEq (ElementaryCell n w d) := Classical.decEq _

def elementaryPolygonData : FinitePolygonModel.Data
    (ElementaryVertex n w) (ElementaryEdge n w) (ElementaryCell n w d) where
  size := elementarySize n w d
  positive := (elementaryBoundary n w d).positive
  side := elementarySide n w d
  start := elementaryStart n w
  closed := (elementaryBoundary n w d).closed

abbrev elementarySimplicialComplex := (elementaryPolygonData n w d).complex

def elementaryBaseVertex : (elementaryPolygonData n w d).Vertex :=
  (elementaryPolygonData n w d).old (.inl (.inl ()))

end ConeSkeleton

/-! Restricting any flat voltage on the actual triangulation to the original
indexed graph. Literal cap triangles prove every original boundary relation. -/

/-! Genuine continuous fundamental groups are generated by the finite edges. -/

/-! New subdivision, collar and cone edges do not create fundamental-group
generators. This concerns the actual barycentric realization. -/

/-! The literal polygon presentation maps to the actual pi1, and its tree
normalization has no hidden van Kampen hypothesis. -/

/-! Identification of the actual finite elementary polyhedron's pi1 with the
original letter presentation, using actual path classes and voltage covers. -/

namespace ConeSkeleton

section
open CoreGeometry IncidenceTemplate LetterPresentation FinitePolyhedron FinitePolygonModel
attribute [local instance] Classical.propDecidable
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)

local instance instDecidableEqElementaryVertex_1 : DecidableEq (ElementaryVertex n w) := Classical.decEq _
local instance instDecidableEqElementaryEdge_1 : DecidableEq (ElementaryEdge n w) := Classical.decEq _
local instance instDecidableEqElementaryCell_1 : DecidableEq (ElementaryCell n w d) := Classical.decEq _

abbrev elementaryRoot : ElementaryVertex n w := .inl (.inl ())

def elementaryCoreRoutes (v : Vertex n w) :
    Path.Homotopic.Quotient
      (vertex (elementarySimplicialComplex n w d) ((elementaryPolygonData n w d).old (elementaryRoot n w)))
      (vertex (elementarySimplicialComplex n w d) ((elementaryPolygonData n w d).old (.inl v))) := by
  rcases v with u|f
  · cases u
    exact .refl _
  · exact ((elementaryPolygonData n w d).graphChain (.inl (.inr ⟨f,fanBase f.val.1⟩),true)).pathClass.symm

/-- Only literal radial edges are chosen as old-vertex routes. -/
def elementaryOldRoutes : (elementaryPolygonData n w d).OldRoutes (elementaryRoot n w)
  | .inl v => elementaryCoreRoutes n w d v
  | .inr a => (elementaryCoreRoutes n w d (macroVertex n w a (MacroGraph.point 0))).trans
      ((elementaryPolygonData n w d).graphChain (.inr (a,MacroGraph.point 0),true)).pathClass.symm

@[simp] lemma elementaryOldRoutes_root :
    elementaryOldRoutes n w d (elementaryRoot n w) = .refl _ := rfl

abbrev ElementaryPiOne := RootedPaths.PiOne (K := elementarySimplicialComplex n w d)
  (elementaryBaseVertex n w d)

end

/-! Injectivity of the actual pi1 comparison, detected by the genuine
voltage covering. -/

open CoreGeometry IncidenceTemplate LetterPresentation FinitePolyhedron FinitePolygonModel
attribute [local instance] Classical.propDecidable

end ConeSkeleton

/-! The actual voltage cover is universal whenever its proved monodromy
comparison is bijective. No simple-connectivity premise on the total space
is substituted for the producer. -/

/-! The literal voltage bundle is an actual simply connected covering
of the actual finite polygon realization. We construct its connectivity from
monodromy, rather than naming an abstract universal cover as a hypothesis. -/

/-! Exact higher homotopy identification for the constructed simply connected
voltage covering of the actual frozen finite polyhedron. -/

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

namespace ConeSkeleton

/-! Infinitude can be obtained without a topological Euler theorem: the many
six-letter cells alone inject into the original letter-edge module of any
finite cover. Their cardinality exceeds the number of original generators. -/

open IncidenceTemplate CoreGeometry LetterPresentation
attribute [local instance] Classical.propDecidable
variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)

abbrev OriginalEdgeChain := (LetterPresentation.Group n w d × Fin (n+1)) →₀ ℤ

end ConeSkeleton

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


