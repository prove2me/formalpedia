-- Prove2me | Definitions.Def_ThreeColorFloodIt_FixedHeight_trees
-- name    : ThreeColorFloodIt_FixedHeight_trees
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:50:37.377068+00:00
-- url     : https://prove2.me/theorems/f506a7be-6d7c-4dac-b343-3d8ed6d889fc
-- title:
--   Admissible painting trees and full local tree templates
-- statement:
--   The finite rooted-tree carrier reuses the published parent-map model. Ancestors include the node itself. An owner map assigns each graph vertex to its last stroke, and
--   $$S_x=\{v:x\text{ is an ancestor of }\pi(v)\}.$$
--   Admissible trees require matching owner colors, different actual parent-child colors, nonempty connected global regions, comparable owners of adjacent vertices, and exclusion of the upper owner's color on the full lower path including its endpoint. A node may own no vertex directly.
--
--   Local templates require a lowest-common-ancestor root and every node to lie on an owner path. They impose the edge conditions inside the window, without local region connectivity. Marked/key nodes, skeleton chains, forbidden boundary colors, exact region trees of normalized plans, painting orders and actual reverse-region moves are recorded separately. These are the common interfaces of normalization, local enumeration and reversal.
-- source:
--   Zhou, Three-Color Free-Flood-It on Fixed-Height Grids Is Polynomial-Time Solvable, STOC 2027 submission #31, supplied 2026 preprint, SHA-256 222ec38f7c30952eda9e86f87b16e8d7dfc93aa0b6b9705ac931e1b56017d280, printed p. 8 (PDF 9), Definitions 9 and 11; §2.1; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/31.pdf Additional locations: printed pp. 3–4 (PDF 4–5), §2.1 (graphs and rooted trees); printed p. 9 (PDF 10), Definition 11 (local templates).

import Definitions.Def_ThreeColorFloodIt_FixedHeight_game
import Definitions.Def_HarelTarjan_Compressed_RootedTree

set_option autoImplicit false

namespace ThreeColorFloodIt.FixedHeight

/-- A finite node count packages the published rooted-tree model. No coloring,
degree, depth or owner condition is bundled with this general tree. -/
structure RootedTree where
  size : ℕ
  data : HarelTarjan.Compressed.RootedTree (Fin size)

def RootedTree.root (T : RootedTree) : Fin T.size := T.data.root
def RootedTree.parent (T : RootedTree) : Fin T.size → Fin T.size := T.data.parent
def Child (T : RootedTree) (x y : Fin T.size) : Prop :=
  y ≠ T.root ∧ T.parent y = x
def Ancestor (T : RootedTree) : Fin T.size → Fin T.size → Prop :=
  Relation.ReflTransGen (Child T)
def StrictAncestor (T : RootedTree) (x y : Fin T.size) : Prop :=
  Ancestor T x y ∧ x ≠ y
def Comparable (T : RootedTree) (x y : Fin T.size) : Prop :=
  Ancestor T x y ∨ Ancestor T y x
def IsLCA (T : RootedTree) (A : Set (Fin T.size)) (r : Fin T.size) : Prop :=
  A.Nonempty ∧ (∀ x ∈ A, Ancestor T r x) ∧
    ∀ y, (∀ x ∈ A, Ancestor T y x) → Ancestor T y r

structure TreeData (V C : Type) where
  tree : RootedTree
  color : Fin tree.size → C
  owner : V → Fin tree.size

def Region {V C : Type} (T : TreeData V C) (x : Fin T.tree.size) : Set V :=
  {v | Ancestor T.tree x (T.owner v)}
def Owned {V C : Type} (T : TreeData V C) (x : Fin T.tree.size) : Set V :=
  {v | T.owner v = x}

/-- The descendant endpoint is included in the forbidden-color path. -/
def EdgeConstraint {V C : Type} (G : SimpleGraph V) (T : TreeData V C) : Prop :=
  ∀ u v, G.Adj u v → Comparable T.tree (T.owner u) (T.owner v) ∧
    (StrictAncestor T.tree (T.owner u) (T.owner v) →
      ∀ x, StrictAncestor T.tree (T.owner u) x →
        Ancestor T.tree x (T.owner v) → T.color x ≠ T.color (T.owner u))

def DifferentParents {V C : Type} (T : TreeData V C) : Prop :=
  ∀ x, x ≠ T.tree.root → T.color x ≠ T.color (T.tree.parent x)

def Admissible {V : Type} (G : SimpleGraph V) (f : V → Fin 3)
    (T : TreeData V (Fin 3)) : Prop :=
  (∀ v, T.color (T.owner v) = f v) ∧ DifferentParents T ∧
    (∀ x, ConnectedSet G (Region T x)) ∧ EdgeConstraint G T

/-- The normalized plan's region tree, before any edge constraint is assumed. -/
def RegionTreeOf {V : Type} (ps : List (Stroke V (Fin 3)))
    (T : TreeData V (Fin 3)) (e : Fin T.tree.size ≃ Fin ps.length) : Prop :=
  (∀ x, Region T x = (ps.get (e x)).1 ∧ T.color x = (ps.get (e x)).2) ∧
  (∀ v, v ∈ LastPainted ps (e (T.owner v))) ∧
  (∀ x, x ≠ T.tree.root →
    ∀ y, (ps.get (e x)).1 ⊂ (ps.get (e y)).1 →
      (ps.get (e (T.tree.parent x))).1 ⊆ (ps.get (e y)).1)

/-- Definition 11 does not require the root to be marked, nor any local region
to be connected. Connectivity is imposed on the named window graph only. -/
def LocalTemplate {V : Type} (G : SimpleGraph V) (f : V → Fin 3)
    (K : TreeData V (Fin 3)) : Prop :=
  (∀ v, K.color (K.owner v) = f v) ∧ DifferentParents K ∧
  IsLCA K.tree (Set.range K.owner) K.tree.root ∧
  (∀ x, ∃ v, Ancestor K.tree x (K.owner v)) ∧ EdgeConstraint G K

def Marked {V C : Type} (K : TreeData V C) (x : Fin K.tree.size) : Prop :=
  ∃ v, K.owner v = x
def Key {V C : Type} (K : TreeData V C) (x : Fin K.tree.size) : Prop :=
  Marked K x ∨ ∃ y z, y ≠ z ∧ Child K.tree x y ∧ Child K.tree x z

/-- A skeleton edge with its possibly empty internal chain in path order. -/
def SkeletonChain {V C : Type} (K : TreeData V C)
    (xs : List (Fin K.tree.size)) (a b : Fin K.tree.size) : Prop :=
  Key K a ∧ Key K b ∧
  (a :: (xs ++ [b])).IsChain (Child K.tree) ∧
  ∀ x ∈ xs, ¬ Key K x

def Forbidden {V : Type} (G : SimpleGraph V) (f : V → Fin 3)
    (L : Set V) : Set (Fin 3) := {a | ∃ u ∉ L, f u = a ∧ ∃ v ∈ L, G.Adj u v}

def ParentOrder {V C : Type} (T : TreeData V C)
    (order : List (Fin T.tree.size)) : Prop :=
  order.Nodup ∧ (∀ x, x ∈ order) ∧
    ∀ i j : Fin order.length, StrictAncestor T.tree (order.get i) (order.get j) → i < j

def TreePlan {V C : Type} (T : TreeData V C)
    (order : List (Fin T.tree.size)) : List (Stroke V C) :=
  order.map fun x => (Region T x, T.color x)

/-- Records the actual reverse regions and colors, rather than merely the
existence of some successful sequence of the right length. -/
def Reverses {V : Type} (G : SimpleGraph V) (T : TreeData V (Fin 3))
    (nodes : List (Fin T.tree.size)) (g : V → Fin 3) : Prop :=
  ∃ ms : List (Move V (Fin 3)), ms.length = nodes.length ∧
    (∀ i : Fin ms.length, ∃ x, nodes[i.val]? = some x ∧
      x ≠ T.tree.root ∧ (ms.get i).2 = T.color (T.tree.parent x)) ∧
    ∃ states : Fin (ms.length + 1) → V → Fin 3,
      states 0 = g ∧
      (∀ i : Fin ms.length, ∃ x, nodes[i.val]? = some x ∧
        Component G (states i.castSucc) (ms.get i).1 = Region T x ∧
        (ms.get i).2 ≠ states i.castSucc (ms.get i).1 ∧
        states i.succ = recolor G (states i.castSucc) (ms.get i)) ∧
      (∀ v, states (Fin.last ms.length) v = T.color T.tree.root)

end ThreeColorFloodIt.FixedHeight


