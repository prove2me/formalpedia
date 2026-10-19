-- Prove2me | Definitions.Def_OAI_GroupTheory_Hyperbolic_FullChains
-- name    : OAI_GroupTheory_Hyperbolic_FullChains
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T07:08:35.452284+00:00
-- url     : https://prove2.me/theorems/054f4f2a-5e06-49d8-96dd-09ca6dd1e2ee
-- title:
--   Translation-equivariance of chains and face chains
-- statement:
--   The left action of the presented group $\Gamma$ on lifted edges and on the chains of the triangle complex.
--
--   1. **Translation.** For $g\in\Gamma$, translation $(e,x)\mapsto(e,gx)$ acts on lifted edges and lifted vertices. It is an action, commutes with flipping, and preserves lifted faces.
--   2. **Equivariance.** Edge chains, positive atoms, ordered and cyclic face evaluations, and both boundary maps commute with translation:
--   $$
--   \partial_i(g\cdot c)=g\cdot\partial_i(c)\qquad(i=1,2).
--   $$
--   The augmentation of every $\partial_1$-boundary is $0$, and the chain of a lifted word is additive under concatenation and equivariant.
--   3. **Face chains.** A full filling of a lifted word has all triangles when every non-boundary dart lies on a lifted triangular face. Its face chain is
--   $$
--   \mathrm{faceChain}(D)=-\,\mathrm{trace}_D(\text{ordered evaluation})\in C_2 .
--   $$
--   Translating all labels by $g$ gives a full filling of the translated word whose face chain is $g\cdot\mathrm{faceChain}(D)$, and rotating the boundary leaves the face chain unchanged.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Hyperbolic/FullChains.lean

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Hyperbolic/FullChains.lean by skeleton subtraction
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
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Spheres
import Definitions.Def_OAI_GroupTheory_Hyperbolic_FullFilling
import Definitions.Def_OAI_GroupTheory_Hyperbolic_FullGluing
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Chains
import Definitions.Def_OAI_GroupTheory_Hyperbolic_CyclicAction

namespace OAI

namespace Release075.BlockPresentation
attribute [local instance] Classical.propDecidable Classical.decEq
variable {I B : Type} {r : ℕ} (d : BlockPresentation I B r)

def shiftEdge (g : d.GroupType) (e : d.LiftedEdge) : d.LiftedEdge := (e.1,g*e.2)
def shiftVertex (g : d.GroupType) (x : d.LiftedVertex) : d.LiftedVertex := (x.1,g*x.2)

@[simp] theorem shiftEdge_one (e : d.LiftedEdge) : d.shiftEdge 1 e = e := by
  simp [shiftEdge]

@[simp] theorem shiftEdge_mul (g h : d.GroupType) (e : d.LiftedEdge) :
    d.shiftEdge (g*h) e = d.shiftEdge g (d.shiftEdge h e) := by
  simp only [shiftEdge,mul_assoc]

@[simp] theorem shiftEdge_flip (g : d.GroupType) (e : d.LiftedEdge) :
    d.shiftEdge g (d.liftedFlip e) = d.liftedFlip (d.shiftEdge g e) := by
  simp only [shiftEdge,liftedFlip,mul_assoc]

@[simp] theorem shiftEdge_target (g : d.GroupType) (e : d.LiftedEdge) :
    d.liftedTarget (d.shiftEdge g e) = d.shiftVertex g (d.liftedTarget e) := rfl

theorem LiftedFace.shift {a b c : d.LiftedEdge} (h : d.LiftedFace a b c) (g : d.GroupType) :
    d.LiftedFace (d.shiftEdge g a) (d.shiftEdge g b) (d.shiftEdge g c) := by
  refine ⟨h.1,?_,?_,?_⟩
  all_goals rw [← shiftEdge_flip,shiftEdge_target,shiftEdge_target]
  · exact congrArg (d.shiftVertex g) h.2.1
  · exact congrArg (d.shiftVertex g) h.2.2.1
  · exact congrArg (d.shiftVertex g) h.2.2.2

@[simp] theorem edgeChain_shift (g : d.GroupType) (e : d.LiftedEdge) :
    d.edgeChain (d.shiftEdge g e) = chainShift g (d.edgeChain e) := by
  unfold edgeChain
  change (if e.1.2 then _ else _) = _
  split_ifs <;> simp [shiftEdge,liftedFlip,chainShift_single,mul_assoc]

@[simp] theorem positiveAtom_shift (g : d.GroupType) (a b c : d.LiftedEdge) :
    d.positiveAtom (d.shiftEdge g a) (d.shiftEdge g b) (d.shiftEdge g c) =
      chainShift g (d.positiveAtom a b c) := by
  unfold positiveAtom
  change (if h : d.PositiveFace (a.1,b.1,c.1) then _ else _) = _
  split_ifs <;> simp [shiftEdge,chainShift_single]

@[simp] theorem orderedEval_shift (g : d.GroupType) (a b c : d.LiftedEdge) :
    d.orderedEval (d.shiftEdge g a) (d.shiftEdge g b) (d.shiftEdge g c) =
      chainShift g (d.orderedEval a b c) := by
  simp only [orderedEval,←shiftEdge_flip,positiveAtom_shift,map_sub]

@[simp] theorem faceEval_shift (g : d.GroupType) (a b c : d.LiftedEdge) :
    d.faceEval (d.shiftEdge g a) (d.shiftEdge g b) (d.shiftEdge g c) =
      chainShift g (d.faceEval a b c) := by
  simp only [faceEval,orderedEval_shift,map_add]

@[simp] theorem boundary₁_shift (g : d.GroupType) (c : d.C₁) :
    d.boundary₁ (chainShift g c) = chainShift g (d.boundary₁ c) := by
  have he : d.boundary₁.comp (chainShift g).toLinearMap =
      (chainShift g).toLinearMap.comp d.boundary₁ := by
    apply Finsupp.lhom_ext
    intro ⟨e,x⟩ n
    simp [boundary₁,chainShift_single,mul_assoc]
  exact LinearMap.congr_fun he c

@[simp] theorem boundary₂_shift (g : d.GroupType) (c : d.C₂) :
    d.boundary₂ (chainShift g c) = chainShift g (d.boundary₂ c) := by
  have he : d.boundary₂.comp (chainShift g).toLinearMap =
      (chainShift g).toLinearMap.comp d.boundary₂ := by
    apply Finsupp.lhom_ext
    intro ⟨t,x⟩ n
    simp only [LinearMap.comp_apply,LinearEquiv.coe_coe,chainShift_single,boundary₂,
      Finsupp.linearCombination_single,map_smul,map_add]
    simp only [← d.edgeChain_shift,shiftEdge,mul_assoc]
  exact LinearMap.congr_fun he c

@[simp] theorem augmentation_boundary₁ (c : d.C₁) :
    FreeChain.augmentation (d.boundary₁ c) = 0 := by
  have he : FreeChain.augmentation.comp d.boundary₁ = 0 := by
    apply Finsupp.lhom_ext
    intro ⟨e,x⟩ n
    simp [boundary₁]
  exact LinearMap.congr_fun he c

@[simp] theorem wordChain_append (u v : List d.LiftedEdge) :
    d.wordChain (u++v) = d.wordChain u + d.wordChain v := by
  simp [wordChain]

@[simp] theorem wordChain_shift (g : d.GroupType) (w : List d.LiftedEdge) :
    d.wordChain (w.map (d.shiftEdge g)) = chainShift g (d.wordChain w) := by
  simp only [wordChain,List.map_map,Function.comp_def,edgeChain_shift,map_list_sum]

end Release075.BlockPresentation

namespace Release075.FullFilling
attribute [local instance] Classical.propDecidable Classical.decEq
variable {I B : Type} {r : ℕ} {d : BlockPresentation I B r}
variable {w : List d.LiftedEdge} (D : FullFilling d.liftedFlip d.liftedTarget d.LiftedFace w)

def AllTriangles : Prop := ∀ a, a ∉ D.boundary → (D.next^3) a = a ∧ D.next a ≠ a ∧
  d.LiftedFace (D.label a) (D.label (D.next a)) (D.label ((D.next^2) a))

noncomputable def faceChain : d.C₂ := -D.trace d.orderedEval

noncomputable abbrev shift (g : d.GroupType) :
    FullFilling d.liftedFlip d.liftedTarget d.LiftedFace (w.map (d.shiftEdge g)) where
  Dart := D.Dart
  reverse := D.reverse
  next := D.next
  reverse_involutive := D.reverse_involutive
  reverse_ne := D.reverse_ne
  label a := d.shiftEdge g (D.label a)
  reverse_label a := by rw [D.reverse_label,d.shiftEdge_flip]
  color_next a := by simp only [d.shiftEdge_target,D.color_next]
  planar := D.planar
  boundary := D.boundary
  boundary_cycle := D.boundary_cycle
  boundary_word := by
    simpa only [List.map_map,Function.comp_def] using
      congrArg (List.map (d.shiftEdge g)) D.boundary_word
  cells := by
    intro a ha
    rcases D.cells a ha with ht | ht
    · exact Or.inl ⟨ht.1,ht.2.1,ht.2.2.shift d g⟩
    · exact Or.inr ht

@[simp] theorem faceChain_rotate (n : ℕ) : (D.rotate n).faceChain = D.faceChain := by
  rw [faceChain,trace_rotate,faceChain]

@[simp] theorem faceChain_shift (g : d.GroupType) :
    (D.shift g).faceChain = chainShift g D.faceChain := by
  unfold faceChain
  rw [map_neg]
  apply congrArg Neg.neg
  calc
    (D.shift g).trace d.orderedEval =
        D.trace (fun a b c => chainShift g (d.orderedEval a b c)) := by
      unfold trace
      apply Finset.sum_congr rfl
      intro a _
      split_ifs <;> simp only [BlockPresentation.orderedEval_shift]
    _ = chainShift g (D.trace d.orderedEval) :=
      (D.trace_map d.orderedEval (chainShift g).toAddMonoidHom).symm

end Release075.FullFilling

namespace Release075.MarkedLineData
variable {q r : ℕ} [Fact q.Prime] (d : MarkedLineData q r) (hr : 0 < r)

end Release075.MarkedLineData

end OAI


