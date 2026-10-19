-- Prove2me | Definitions.Def_OAI_GroupTheory_Hyperbolic_Words
-- name    : OAI_GroupTheory_Hyperbolic_Words
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T06:45:26.185709+00:00
-- url     : https://prove2.me/theorems/ff1778e1-e751-485d-8edf-78574708dfa8
-- title:
--   Edge words, oriented edges and the triangle faces of a block presentation
-- statement:
--   Words in an edge alphabet and the oriented-edge combinatorics of the triangle complex of a block presentation.
--
--   1. **Words.** For an alphabet $E$ with a flip and a vertex map `color` (the target of an edge), a word is a path from $a$ to $b$ when its letters are consecutive edges, i.e. the target of each letter is the source $\mathrm{color}(\mathrm{flip}(e))$ of the next one. The reverse of a word is
--   $$
--   \overline{e_1\cdots e_n}=\mathrm{flip}(e_n)\cdots\mathrm{flip}(e_1).
--   $$
--   Two words $p,q$ are filled between when the loop $p\,\overline q$ admits a triangle filling.
--   2. **Oriented edges.** For a block presentation, an oriented edge is an edge with a sign; flipping changes the sign. Its target is one of the three vertices $o,v,w$ ($x$-edges run $v\to w$, $l$-edges $o\to v$, $r$-edges $o\to w$). Paths in the symmetrized quiver give words of oriented edges, compatible with composition and reversal.
--   3. **Triangle faces.** For each label $i$ in block $b$ and $u,v<r$ the triangle with sides $l=l_{b,u,c_1(i)+v}$, $x=x_{i,u,v}$ and $r=r_{b,v,c_2(i)+u}$ gives the face relation on the cyclic rotations of the boundary words
--   $$
--   (l,\ x,\ \bar r)\qquad\text{and}\qquad(\bar l,\ r,\ \bar x).
--   $$
--   The vertices $o,v,w$ are coloured $0,1,2$, and the three sides of every face have pairwise distinct targets.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Hyperbolic/Words.lean

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Hyperbolic/Words.lean by skeleton subtraction
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

namespace OAI

namespace Release075
attribute [local instance] Classical.propDecidable Classical.decEq
variable {E V : Type} {flip : E → E} {color : E → V} {face : E → E → E → Prop}

inductive WordPath (flip : E → E) (color : E → V) : V → V → List E → Prop
  | nil (v : V) : WordPath flip color v v []
  | cons (e : E) {v : V} {w : List E} : WordPath flip color (color e) v w →
      WordPath flip color (color (flip e)) v (e::w)

def reverseWord (flip : E → E) (w : List E) : List E := w.reverse.map flip

@[simp] theorem reverseWord_nil : reverseWord flip [] = [] := rfl
@[simp] theorem reverseWord_cons (e : E) (w : List E) :
    reverseWord flip (e::w) = reverseWord flip w ++ [flip e] := by
  simp [reverseWord]
@[simp] theorem reverseWord_append (w z : List E) :
    reverseWord flip (w++z) = reverseWord flip z ++ reverseWord flip w := by
  simp [reverseWord]

namespace WordPath
variable {a b c : V} {u v : List E}

end WordPath

namespace Fillable
variable (hi : Function.Involutive flip)
-- [generator] dropped: variable (hn : ∀ e, color e ≠ color (flip e))

end Fillable

/-- Filling the two paths glued along their common endpoints. -/
def FilledBetween (flip : E → E) (color : E → V) (face : E → E → E → Prop)
    (p q : List E) : Prop := Fillable flip color face (p++reverseWord flip q)

namespace FilledBetween
variable (hi : Function.Involutive flip)
-- [generator] dropped: variable (hn : ∀ e, color e ≠ color (flip e))
-- [generator] dropped: variable (hf : ∀ a b c, face a b c → face (flip a) (flip c) (flip b))
variable {a b c d : V} {p q r u v : List E}

end FilledBetween
end Release075

namespace Release075.BlockPresentation
open CategoryTheory
variable {I B : Type} {r : ℕ} (d : BlockPresentation I B r)

abbrev OrientedEdge := d.Edge × Bool

def flipEdge : d.OrientedEdge → d.OrientedEdge := fun ⟨e,s⟩ => (e,!s)

@[simp] theorem flipEdge_flipEdge (e : d.OrientedEdge) : d.flipEdge (d.flipEdge e) = e := by
  rcases e with ⟨e,s⟩
  cases s <;> rfl

def edgeTarget : d.OrientedEdge → d.Vertex
  | (.inl _, true) => .w
  | (.inl _, false) => .v
  | (.inr (.inl _), true) => .v
  | (.inr (.inl _), false) => .o
  | (.inr (.inr _), true) => .w
  | (.inr (.inr _), false) => .o

def arrowLabel {a c : d.Vertex} : d.Arrow a c → d.Edge
  | .x e => .inl e
  | .l e => .inr (.inl e)
  | .rr e => .inr (.inr e)

def orientedLabel {a c : Quiver.Symmetrify d.Vertex} (f : a ⟶ c) : d.OrientedEdge :=
  match f with
  | .inl e => (d.arrowLabel e,true)
  | .inr e => (d.arrowLabel e,false)

@[simp] theorem orientedLabel_reverse {a c : Quiver.Symmetrify d.Vertex} (f : a ⟶ c) :
    d.orientedLabel (Quiver.reverse f) = d.flipEdge (d.orientedLabel f) := by
  change d.Arrow a c ⊕ d.Arrow c a at f
  cases f <;> rfl

@[simp] theorem orientedLabel_target {a c : Quiver.Symmetrify d.Vertex} (f : a ⟶ c) :
    d.edgeTarget (d.orientedLabel f) = c := by
  change d.Arrow a c ⊕ d.Arrow c a at f
  rcases f with f|f
  · change d.Arrow a c at f
    cases f <;> rfl
  · change d.Arrow c a at f
    cases f <;> rfl

@[simp] theorem orientedLabel_source {a c : Quiver.Symmetrify d.Vertex} (f : a ⟶ c) :
    d.edgeTarget (d.flipEdge (d.orientedLabel f)) = a := by
  rw [← d.orientedLabel_reverse]
  exact d.orientedLabel_target _

def rawWord {a : Quiver.Symmetrify d.Vertex} :
    ∀ {c : Quiver.Symmetrify d.Vertex},
      @Quiver.Path (Quiver.Symmetrify d.Vertex) (Quiver.symmetrifyQuiver d.Vertex) a c →
        List d.OrientedEdge
  | _, .nil => []
  | _, .cons p f => rawWord p ++ [d.orientedLabel f]

@[simp] theorem rawWord_nil (a : d.RawPaths) : d.rawWord (𝟙 a) = [] := rfl

@[simp] theorem rawWord_comp {a b c : d.RawPaths} (p : a ⟶ b) (q : b ⟶ c) :
    d.rawWord (p ≫ q) = d.rawWord p ++ d.rawWord q := by
  change @Quiver.Path (Quiver.Symmetrify d.Vertex) (Quiver.symmetrifyQuiver d.Vertex) b c at q
  induction q with
  | nil =>
    change d.rawWord p = d.rawWord p ++ []
    exact (List.append_nil _).symm
  | cons q f ih =>
    change d.rawWord (p ≫ q) ++ [d.orientedLabel f] =
      d.rawWord p ++ (d.rawWord q ++ [d.orientedLabel f])
    rw [ih,List.append_assoc]

theorem rawWord_path_comp {a b c : Quiver.Symmetrify d.Vertex}
    (p : Quiver.Path a b) (q : Quiver.Path b c) :
    d.rawWord (p.comp q) = d.rawWord p ++ d.rawWord q := by
  induction q with
  | nil => exact (List.append_nil _).symm
  | cons q f ih =>
    change d.rawWord (p.comp q) ++ [d.orientedLabel f] =
      d.rawWord p ++ (d.rawWord q ++ [d.orientedLabel f])
    rw [ih,List.append_assoc]

@[simp] theorem rawWord_toPath {a c : Quiver.Symmetrify d.Vertex} (f : a ⟶ c) :
    d.rawWord f.toPath = [d.orientedLabel f] := rfl

@[simp] theorem rawWord_reverse {a c : Quiver.Symmetrify d.Vertex}
    (p : Quiver.Path a c) :
    d.rawWord p.reverse = reverseWord d.flipEdge (d.rawWord p) := by
  change @Quiver.Path (Quiver.Symmetrify d.Vertex) (Quiver.symmetrifyQuiver d.Vertex) a c at p
  induction p with
  | nil => rfl
  | cons p f ih =>
    change d.rawWord (Quiver.Path.comp (Quiver.reverse f).toPath p.reverse) =
      reverseWord d.flipEdge (d.rawWord p ++ [d.orientedLabel f])
    rw [d.rawWord_path_comp,d.rawWord_toPath,d.orientedLabel_reverse,ih]
    simp only [reverseWord_append,reverseWord_cons,reverseWord_nil,List.nil_append]

def orientedL (b : B) (i : (d.block b).labels) (u v : Fin r) : d.OrientedEdge :=
  (.inr (.inl ⟨b,u,((d.block b).coordinates i).1 + (v.val : ZMod (d.block b).s)⟩),true)
def orientedX (i : I) (u v : Fin r) : d.OrientedEdge := (.inl (i,u,v),true)
def orientedR (b : B) (i : (d.block b).labels) (u v : Fin r) : d.OrientedEdge :=
  (.inr (.inr ⟨b,v,((d.block b).coordinates i).2 + (u.val : ZMod (d.block b).t)⟩),true)

inductive TriangleFace : d.OrientedEdge → d.OrientedEdge → d.OrientedEdge → Prop
  | pos₀ (b : B) (i : (d.block b).labels) (u v : Fin r) :
    TriangleFace (d.orientedL b i u v) (d.orientedX i u v) (d.flipEdge (d.orientedR b i u v))
  | pos₁ (b : B) (i : (d.block b).labels) (u v : Fin r) :
    TriangleFace (d.orientedX i u v) (d.flipEdge (d.orientedR b i u v)) (d.orientedL b i u v)
  | pos₂ (b : B) (i : (d.block b).labels) (u v : Fin r) :
    TriangleFace (d.flipEdge (d.orientedR b i u v)) (d.orientedL b i u v) (d.orientedX i u v)
  | neg₀ (b : B) (i : (d.block b).labels) (u v : Fin r) :
    TriangleFace (d.flipEdge (d.orientedL b i u v)) (d.orientedR b i u v) (d.flipEdge (d.orientedX i u v))
  | neg₁ (b : B) (i : (d.block b).labels) (u v : Fin r) :
    TriangleFace (d.orientedR b i u v) (d.flipEdge (d.orientedX i u v)) (d.flipEdge (d.orientedL b i u v))
  | neg₂ (b : B) (i : (d.block b).labels) (u v : Fin r) :
    TriangleFace (d.flipEdge (d.orientedX i u v)) (d.flipEdge (d.orientedL b i u v)) (d.orientedR b i u v)

end Release075.BlockPresentation

namespace Release075.BlockPresentation
variable {I B : Type} {r : ℕ} (d : BlockPresentation I B r)

def vertexColor : d.Vertex ≃ Fin 3 where
  toFun | .o => 0 | .v => 1 | .w => 2
  invFun j := if j = 0 then .o else if j = 1 then .v else .w
  left_inv a := by cases a <;> rfl
  right_inv j := by fin_cases j <;> rfl

theorem TriangleFace.colors {a b c : d.OrientedEdge} (h : d.TriangleFace a b c) :
    d.edgeTarget a ≠ d.edgeTarget b ∧ d.edgeTarget b ≠ d.edgeTarget c ∧
    d.edgeTarget c ≠ d.edgeTarget a := by
  cases h <;> simp [orientedL,orientedX,orientedR,flipEdge,edgeTarget]

end Release075.BlockPresentation

end OAI


