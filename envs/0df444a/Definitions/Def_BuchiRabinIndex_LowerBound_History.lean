-- Prove2me | Definitions.Def_BuchiRabinIndex_LowerBound_History
-- name    : BuchiRabinIndex_LowerBound_History
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T06:31:49.059752+00:00
-- url     : https://prove2.me/theorems/066afb5e-df78-480b-87a9-cad65447cd17
-- title:
--   History trees and the five-step partial successor
-- statement:
--   A history tree consists of a rooted ordered tree and nonempty labels in $2^Q$. Sibling labels are disjoint, and every label properly contains the union of its children’s labels. The own set is
--   $$\operatorname{ow}(x)=l(x)\setminus\bigcup_{xi\in T}l(xi).$$
--
--   The successor implements all five steps of §2.3: expansion by a new rightmost child, horizontal removal using the unmodified expanded older-sibling labels, deletion of empty nodes, deletion of descendants of resetting nodes, and compression by surviving sibling counts plus one. Labels are uniquely extended by empty sets off the tree. A validity subtype enforces the tree and label conditions. The conversion into the subtype uses a validity check; it does not assume that the transformation preserves validity.
--
--   The initial tree labels the root by $Q_0$. Empty initial labels and a transition deleting the root give no history. Successors use Option, with no added sink. Both annotation sets contain old nodes only, as in Remark 8. On nested resets, only the topmost one survives to be accepting; deleted old descendants are unstable, and compression replaces accepting annotations on renamed nodes by unstable annotations.
--
--   This gives the concrete transition structure used throughout the mission.
-- source:
--   Cong Tian, Runzhe Ma, Wensheng Wang, Zhenhua Duan, Büchi Determinization with Optimal States and Square Root Index Improvement, STOC 2027 submission #1731 (October 2026), Definition 5, p. 6; §2.3 Steps 1–5, pp. 6–8; Remark 8, p. 9; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1731.pdf

import Definitions.Def_BuchiRabinIndex_LowerBound_Nodes
import Definitions.Def_BuchiRabinIndex_LowerBound_Automata

set_option autoImplicit false

namespace BuchiRabinIndex.LowerBound
noncomputable section
open scoped Classical

/-- Labelled finite tree data, normalized to empty labels outside its node set. -/
structure TreeData (Q : Type) where
  nodes : Finset Node
  label : Node → Finset Q

def childLabels {Q : Type} (H : TreeData Q) (x : Node) : Finset Q :=
  (children H.nodes x).biUnion H.label

def own {Q : Type} (H : TreeData Q) (x : Node) : Finset Q :=
  H.label x \ childLabels H x

def Valid {Q : Type} (H : TreeData Q) : Prop :=
  Ordered H.nodes ∧ [] ∈ H.nodes ∧
  (∀ x, x ∉ H.nodes → H.label x = ∅) ∧
  (∀ x ∈ H.nodes, (H.label x).Nonempty) ∧
  (∀ p i j, p ++ [i] ∈ H.nodes → p ++ [j] ∈ H.nodes → i ≠ j →
    Disjoint (H.label (p ++ [i])) (H.label (p ++ [j]))) ∧
  (∀ x ∈ H.nodes, childLabels H x ⊂ H.label x)

abbrev History (Q : Type) := {H : TreeData Q // Valid H}

def asHistory {Q : Type} (H : TreeData Q) : Option (History Q) :=
  if h : Valid H then some ⟨H, h⟩ else none

def initialData {Q Sigma : Type} (B : NBW Q Sigma) : TreeData Q :=
  ⟨{[]}, fun x => if x = [] then B.initial else ∅⟩

def initialHistory {Q Sigma : Type} (B : NBW Q Sigma) : Option (History Q) :=
  asHistory (initialData B)

/-- Step 1: add a rightmost child at every old node. -/
def expand {Q Sigma : Type} (B : NBW Q Sigma) (H : TreeData Q) (σ : Sigma) : TreeData Q :=
  let next := fun x => (H.label x).biUnion fun q => B.delta q σ
  let T := H.nodes ∪ H.nodes.image (fun x => x ++ [degree H.nodes x + 1])
  ⟨T, fun x => if x ∈ H.nodes then next x else
    if x ∈ T then next x.dropLast ∩ B.accepting else ∅⟩

/-- Step 2: use the original expanded labels in every older-sibling test. -/
def horizontal {Q : Type} (H : TreeData Q) : TreeData Q :=
  ⟨H.nodes, fun x => (H.label x).filter fun q =>
    ¬ ∃ p i v j, x = p ++ i :: v ∧ 0 < j ∧ j < i ∧
      p ++ [j] ∈ H.nodes ∧ q ∈ H.label (p ++ [j])⟩

/-- Step 3. -/
def removeEmpty {Q : Type} (H : TreeData Q) : TreeData Q :=
  let T := H.nodes.filter fun x => (H.label x).Nonempty
  ⟨T, fun x => if x ∈ T then H.label x else ∅⟩

def resetNodes {Q : Type} (H : TreeData Q) : Finset Node :=
  H.nodes.filter fun x => H.label x = childLabels H x

/-- Step 4: keep the topmost resetting nodes, remove their proper descendants. -/
def prune {Q : Type} (H : TreeData Q) : TreeData Q :=
  let T := H.nodes.filter fun x =>
    ¬ ∃ p ∈ resetNodes H, p.IsPrefix x ∧ p ≠ x
  ⟨T, fun x => if x ∈ T then H.label x else ∅⟩

/-- Step 5, with positive child indices. -/
def compress (T : Finset Node) (x : Node) : Node :=
  (List.range x.length).map fun k =>
    (T.filter fun y => ∃ j, y = x.take k ++ [j] ∧ j < x[k]!).card + 1

def compressed {Q : Type} (H : TreeData Q) : TreeData Q :=
  ⟨H.nodes.image (compress H.nodes), fun x =>
    (H.nodes.filter fun y => compress H.nodes y = x).biUnion H.label⟩

def stage3 {Q Sigma : Type} (B : NBW Q Sigma) (H : TreeData Q) (σ : Sigma) : TreeData Q :=
  removeEmpty (horizontal (expand B H σ))

def stage4 {Q Sigma : Type} (B : NBW Q Sigma) (H : TreeData Q) (σ : Sigma) : TreeData Q :=
  prune (stage3 B H σ)

/-- No successor when the root dies; the validity check constructs the subtype. -/
def successor {Q Sigma : Type} (B : NBW Q Sigma) (H : History Q) (σ : Sigma) : Option (History Q) :=
  asHistory (compressed (stage4 B H.val σ))

/-- Remark 8: both sets refer exclusively to source nodes. -/
def unstable {Q Sigma : Type} (B : NBW Q Sigma) (H : History Q) (σ : Sigma) : Finset Node :=
  let K := stage4 B H.val σ
  H.val.nodes.filter fun x => x ∉ K.nodes ∨ compress K.nodes x ≠ x

def acceptingNodes {Q Sigma : Type} (B : NBW Q Sigma) (H : History Q) (σ : Sigma) : Finset Node :=
  let K := stage4 B H.val σ
  H.val.nodes.filter fun x => x ∈ resetNodes (stage3 B H.val σ) ∧
    x ∈ K.nodes ∧ compress K.nodes x = x

end
end BuchiRabinIndex.LowerBound


