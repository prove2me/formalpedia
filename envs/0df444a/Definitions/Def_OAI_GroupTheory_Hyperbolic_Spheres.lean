-- Prove2me | Definitions.Def_OAI_GroupTheory_Hyperbolic_Spheres
-- name    : OAI_GroupTheory_Hyperbolic_Spheres
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T06:55:52.881051+00:00
-- url     : https://prove2.me/theorems/af935f1e-242c-4e0d-bf77-fc656704c404
-- title:
--   Triangulated spheres and their dipoles
-- statement:
--   Closed triangulated surfaces of genus zero, recorded as labelled combinatorial maps.
--
--   1. **Triangle spheres.** A triangle sphere over an edge alphabet consists of:
--   - a finite set of darts with a fixed-point-free reverse involution $r$ and a face permutation $n$ forming a planar map (possibly with several components);
--   - labels with $\mathrm{label}(ra)=\mathrm{flip}(\mathrm{label}(a))$ and a colour constant along $rn$.
--   Every face is a triangle in the face relation:
--   $$
--   n^3a=a,\quad na\ne a,\quad \mathrm{face}\bigl(\mathrm{label}(a),\mathrm{label}(na),\mathrm{label}(n^2a)\bigr).
--   $$
--   There is no distinguished outer face.
--   2. **Dipoles.** A dipole is a pair of faces sharing an edge with mirrored labels and the usual colour conditions, as for fillings.
--   3. **Angles.** Vertices are the cycles of $rn$. A colouring of $V$ by $\{0,1,2\}$ paints each vertex, and the vertex angle is $3$ or $1$ (for colour $0$ or not) times the number of corners at the vertex.
--   4. **Corner sums.** For $F:E^3\to M$ into an abelian group, the corner sum evaluates $F$ at every oriented corner $(\mathrm{label}(a),\mathrm{label}(na),\mathrm{label}(n^2a))$.
--   5. **Lifting.** A sphere with lifted labels forgets to an ordinary one, and dipoles of the forgotten sphere lift.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Hyperbolic/Spheres.lean

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Hyperbolic/Spheres.lean by skeleton subtraction
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
import Definitions.Def_OAI_GroupTheory_Hyperbolic_LiftedFilling

namespace OAI

namespace Release075
open Equiv PermCycles

/-- A finite labelled spherical map, possibly with several connected components.
All faces are triangles; there is no distinguished outer face. -/
structure TriangleSphere {E V : Type} (flip : E → E) (color : E → V)
    (face : E → E → E → Prop) where
  Dart : Type
  [dartFintype : Fintype Dart]
  reverse : Perm Dart
  next : Perm Dart
  reverse_involutive : Function.Involutive reverse
  reverse_ne : ∀ a, reverse a ≠ a
  label : Dart → E
  reverse_label : ∀ a, label (reverse a) = flip (label a)
  color_next : ∀ a, color (label ((reverse*next) a)) = color (label a)
  planar : PlanarMap reverse next
  triangular : ∀ a, (next^3) a = a ∧ next a ≠ a ∧
    face (label a) (label (next a)) (label ((next^2) a))

attribute [instance] TriangleSphere.dartFintype

namespace TriangleSphere
attribute [local instance] Classical.propDecidable Classical.decEq
variable {E V : Type} {flip : E → E} {color : E → V} {face : E → E → E → Prop}
variable (D : TriangleSphere flip color face)

structure Dipole where
  dart : Fin 6 ↪ D.Dart
  next_dart : ∀ j, D.next (dart j) = dart (dipoleFace j)
  reverse_zero : D.reverse (dart 0) = dart 3
  color10 : color (D.label (dart 1)) ≠ color (D.label (dart 0))
  color21 : color (D.label (dart 2)) ≠ color (D.label (dart 1))
  label51 : D.label (dart 5) = flip (D.label (dart 1))
  label42 : D.label (dart 4) = flip (D.label (dart 2))

abbrev vertexPerm : Perm D.Dart := D.reverse*D.next

noncomputable def paint (q : V → Fin 3) : Cycles D.vertexPerm → Fin 3 :=
  descend D.vertexPerm (fun a => q (color (D.label a)))
    (fun a => congrArg q (D.color_next a))

@[simp] theorem paint_cl (q : V → Fin 3) (a : D.Dart) :
    D.paint q (cl D.vertexPerm a) = q (color (D.label a)) := descend_cl _ _ _ _

noncomputable def vertexAngle (q : V → Fin 3) (v : Cycles D.vertexPerm) : ℝ :=
  TriangleRibbon.weight (D.paint q v) * Fintype.card {a : D.Dart // cl D.vertexPerm a = v}

end TriangleSphere
end Release075

namespace Release075.MarkedLineData
open Equiv PermCycles
variable {q r : ℕ} [Fact q.Prime] (d : MarkedLineData q r) (hr : 0 < r)

end Release075.MarkedLineData

namespace Release075.TriangleSphere
open Equiv PermCycles
attribute [local instance] Classical.propDecidable Classical.decEq
variable {E V M : Type} [AddCommGroup M]
variable {flip : E → E} {color : E → V} {face : E → E → E → Prop}

/-- Evaluate once at every oriented corner. For cyclic face values this is three
 times the ordinary integral face chain; no unproved chain-complex property is used. -/
def cornerSum (D : TriangleSphere flip color face) (F : E → E → E → M) : M :=
  ∑ a, F (D.label a) (D.label (D.next a)) (D.label ((D.next^2) a))

end Release075.TriangleSphere

namespace Release075.TriangleSphere
open Equiv PermCycles
variable {I B : Type} {r : ℕ} {d : BlockPresentation I B r}

def forgetLift (D : TriangleSphere d.liftedFlip d.liftedTarget d.LiftedFace) :
    TriangleSphere d.flipEdge d.edgeTarget d.TriangleFace where
  Dart := D.Dart
  reverse := D.reverse
  next := D.next
  reverse_involutive := D.reverse_involutive
  reverse_ne := D.reverse_ne
  label a := (D.label a).1
  reverse_label a := congrArg Prod.fst (D.reverse_label a)
  color_next a := congrArg Prod.fst (D.color_next a)
  planar := D.planar
  triangular a := let ht := D.triangular a; ⟨ht.1,ht.2.1,ht.2.2.1⟩

/-- Matching opposite face labels at a shared lifted edge forces matching group
coordinates on the other two edges. Thus reduction cannot hide a downstairs dipole. -/
def Dipole.lift {D : TriangleSphere d.liftedFlip d.liftedTarget d.LiftedFace}
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
    color10 := fun h => P.color10 (congrArg Prod.fst h)
    color21 := fun h => P.color21 (congrArg Prod.fst h)
    label51 := h51
    label42 := h42 }

end Release075.TriangleSphere

namespace Release075.MarkedLineData
variable {q r : ℕ} [Fact q.Prime] (d : MarkedLineData q r) (hr : 0 < r)

end Release075.MarkedLineData

end OAI


