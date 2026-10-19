-- Prove2me | Definitions.Def_OAI_GroupTheory_Hyperbolic_LiftedFilling
-- name    : OAI_GroupTheory_Hyperbolic_LiftedFilling
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T06:53:59.519472+00:00
-- url     : https://prove2.me/theorems/53c217f8-2953-4219-9af5-c0293055c78b
-- title:
--   Lifting edge words and fillings to the Cayley complex
-- statement:
--   Group coordinates for oriented edges of a block presentation $\Gamma$, used to lift fillings.
--
--   1. **Values.** An oriented edge $e$ has value $\mathrm{val}(e)=g_e$ or $g_e^{-1}$ according to its sign, where $g_e$ is the generator; flipping inverts the value. A word $e_1\cdots e_n$ has value $\prod_k\mathrm{val}(e_k)\in\Gamma$.
--   2. **Lifted edges.** A lifted edge is a pair $(e,g)$ with $g\in\Gamma$, and a lifted vertex is a pair (vertex, group element); the target of $(e,g)$ is $(\mathrm{target}(e),g)$. Flipping is
--   $$
--   (e,g)\mapsto\bigl(\bar e,\ g\,\mathrm{val}(e)^{-1}\bigr).
--   $$
--   A lifted face is a triangle face whose three corners are glued at equal group coordinates.
--   3. **Lifting words.** From a starting element $g$, the word $e_1e_2\cdots$ lifts to
--   $$
--   (e_1,\ g\,\mathrm{val}(e_1)),\ (e_2,\ g\,\mathrm{val}(e_1)\mathrm{val}(e_2)),\ \dots,
--   $$
--   which has the same length and forgets to the original word.
--   4. **Forgetting.** Dropping group coordinates turns a filling by lifted faces into a filling by ordinary faces with the same darts, boundary and active count. Conversely, a dipole of the forgotten filling lifts to a dipole of the lifted filling.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Hyperbolic/LiftedFilling.lean

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Hyperbolic/LiftedFilling.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the TorsionFreeHyperbolic mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_TorsionFreeHyperbolic
import Definitions.Def_OAI_GroupTheory_Hyperbolic_MatrixRank
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Incidence
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Presentation
import Definitions.Def_OAI_GroupTheory_Hyperbolic_WordPaths
import Definitions.Def_OAI_GroupTheory_Hyperbolic_PermutationCycles
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Planarity
import Definitions.Def_OAI_GroupTheory_Hyperbolic_RePairing
import Definitions.Def_OAI_GroupTheory_Hyperbolic_TriangleFilling
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Words
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Dipoles
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Ribbons
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Links

namespace OAI

namespace Release075.BlockPresentation
open CategoryTheory
variable {I B : Type} {r : ℕ} (d : BlockPresentation I B r)

/-- The signed displacement of an oriented original edge, with the two tree
edges already killed in the actual presentation. -/
def edgeValue (e : d.OrientedEdge) : d.GroupType :=
  if e.2 then d.edge e.1 else (d.edge e.1)⁻¹

@[simp] theorem edgeValue_flip (e : d.OrientedEdge) :
    d.edgeValue (d.flipEdge e) = (d.edgeValue e)⁻¹ := by
  rcases e with ⟨e,s⟩
  cases s <;> simp [edgeValue,flipEdge]

def wordValue (w : List d.OrientedEdge) : d.GroupType := (w.map d.edgeValue).prod

@[simp] theorem wordValue_nil : d.wordValue [] = 1 := rfl
@[simp] theorem wordValue_cons (e : d.OrientedEdge) (w : List d.OrientedEdge) :
    d.wordValue (e::w) = d.edgeValue e * d.wordValue w := rfl
@[simp] theorem wordValue_append (u v : List d.OrientedEdge) :
    d.wordValue (u++v) = d.wordValue u * d.wordValue v := by
  simp only [wordValue,List.map_append,List.prod_append]

abbrev LiftedEdge := d.OrientedEdge × d.GroupType
abbrev LiftedVertex := d.Vertex × d.GroupType

def liftedFlip (e : d.LiftedEdge) : d.LiftedEdge :=
  (d.flipEdge e.1,e.2 * (d.edgeValue e.1)⁻¹)

def liftedTarget (e : d.LiftedEdge) : d.LiftedVertex := (d.edgeTarget e.1,e.2)

@[simp] theorem liftedFlip_flip (e : d.LiftedEdge) :
    d.liftedFlip (d.liftedFlip e) = e := by
  rcases e with ⟨e,g⟩
  simp [liftedFlip]

/-- A genuine lift of a triangular face: all three corners are glued at the
same group coordinates, not merely at the same original vertex colors. -/
def LiftedFace (a b c : d.LiftedEdge) : Prop :=
  d.TriangleFace a.1 b.1 c.1 ∧
  d.liftedTarget (d.liftedFlip b) = d.liftedTarget a ∧
  d.liftedTarget (d.liftedFlip c) = d.liftedTarget b ∧
  d.liftedTarget (d.liftedFlip a) = d.liftedTarget c

def liftWord (g : d.GroupType) : List d.OrientedEdge → List d.LiftedEdge
  | [] => []
  | e::w => (e,g*d.edgeValue e)::liftWord (g*d.edgeValue e) w

@[simp] theorem liftWord_nil (g : d.GroupType) : d.liftWord g [] = [] := rfl
@[simp] theorem liftWord_cons (g : d.GroupType) (e : d.OrientedEdge) (w) :
    d.liftWord g (e::w) = (e,g*d.edgeValue e)::d.liftWord (g*d.edgeValue e) w := rfl

@[simp] theorem liftWord_length (g : d.GroupType) (w) :
    (d.liftWord g w).length = w.length := by
  induction w generalizing g with
  | nil => rfl
  | cons e w ih => simp only [liftWord,List.length_cons,ih]

@[simp] theorem liftWord_forget (g : d.GroupType) (w) :
    (d.liftWord g w).map Prod.fst = w := by
  induction w generalizing g with
  | nil => rfl
  | cons e w ih => simp only [liftWord,List.map_cons,ih]

end Release075.BlockPresentation

namespace Release075.TriangleFilling
open Equiv PermCycles
variable {I B : Type} {r : ℕ} {d : BlockPresentation I B r}
variable {w : List d.LiftedEdge}

/-- Forgetting group coordinates keeps every dart, incidence, boundary and
planar component. The metric labels can therefore be tracked through reduction. -/
def forgetLift (D : TriangleFilling d.liftedFlip d.liftedTarget d.LiftedFace w) :
    TriangleFilling d.flipEdge d.edgeTarget d.TriangleFace (w.map Prod.fst) where
  Dart := D.Dart
  reverse := D.reverse
  next := D.next
  reverse_involutive := D.reverse_involutive
  reverse_ne := D.reverse_ne
  label a := (D.label a).1
  reverse_label a := congrArg Prod.fst (D.reverse_label a)
  color_next a := congrArg Prod.fst (D.color_next a)
  planar := D.planar
  boundary := D.boundary
  boundary_cycle := D.boundary_cycle
  boundary_word := by
    simpa only [List.map_map,Function.comp_def] using congrArg (List.map Prod.fst) D.boundary_word
  triangular a ha hb := let ht := D.triangular a ha hb; ⟨ht.1,ht.2.1,ht.2.2.1⟩

@[simp] theorem forgetLift_activeCount
    (D : TriangleFilling d.liftedFlip d.liftedTarget d.LiftedFace w) :
    D.forgetLift.activeCount = D.activeCount := rfl

/-- Matching opposite face labels at a shared lifted edge forces matching group
coordinates on the other two edges. Thus reduction cannot hide a downstairs dipole. -/
def Dipole.lift {D : TriangleFilling d.liftedFlip d.liftedTarget d.LiftedFace w}
    (P : D.forgetLift.Dipole) : D.Dipole := by
  have hn (j) : D.next (P.dart j) = P.dart (dipoleFace j) := P.next_dart j
  have hc (j) : d.liftedTarget (d.liftedFlip (D.label (P.dart (dipoleFace j)))) =
      d.liftedTarget (D.label (P.dart j)) := by
    have hh := D.color_next (P.dart j)
    change d.liftedTarget (D.label (D.reverse (D.next (P.dart j)))) =
      d.liftedTarget (D.label (P.dart j)) at hh
    exact (congrArg d.liftedTarget (D.reverse_label (P.dart (dipoleFace j)))).symm.trans
      (by simpa only [hn] using hh)
  have hrev : D.label (P.dart 3) = d.liftedFlip (D.label (P.dart 0)) := by
    rw [← P.reverse_zero]
    exact D.reverse_label _
  have h0 := hc 0
  have h5 := hc 5
  simp only [dipoleFace_zero] at h0
  simp only [dipoleFace_five,hrev,d.liftedFlip_flip] at h5
  have h51 : D.label (P.dart 5) = d.liftedFlip (D.label (P.dart 1)) :=
    Prod.ext P.label51 (congrArg (fun x : d.LiftedVertex => x.2) (h5.symm.trans h0.symm))
  have h1 := hc 1
  have h4 := hc 4
  simp only [dipoleFace_one] at h1
  simp only [dipoleFace_four,h51,d.liftedFlip_flip] at h4
  have h42 : D.label (P.dart 4) = d.liftedFlip (D.label (P.dart 2)) :=
    Prod.ext P.label42 (congrArg (fun x : d.LiftedVertex => x.2) (h4.symm.trans h1.symm))
  exact {
    dart := P.dart
    next_dart := P.next_dart
    reverse_zero := P.reverse_zero
    not_boundary := P.not_boundary
    active := P.active
    color10 := fun h => P.color10 (congrArg Prod.fst h)
    color21 := fun h => P.color21 (congrArg Prod.fst h)
    label51 := h51
    label42 := h42 }

end Release075.TriangleFilling

namespace Release075.MarkedLineData
variable {q r : ℕ} [Fact q.Prime] (d : MarkedLineData q r) (hr : 0 < r)
variable {w : List (d.presentation hr).LiftedEdge}

end Release075.MarkedLineData

end OAI


