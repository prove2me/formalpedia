-- Prove2me | Definitions.Def_AccelNewtonDinkelbach_Supplement_Grapevine
-- name    : AccelNewtonDinkelbach_Supplement_Grapevine
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T01:00:25.444169+00:00
-- url     : https://prove2.me/theorems/d73c1f71-118b-5567-aa76-99e81599da1a
-- title:
--   Algorithm 2 (Grapevine) on the split graph $G_u$
-- statement:
--   **Grapevine** performs one simultaneous label-correcting update at every node for each of $|V|$ rounds, records an arbitrary minimizing violated outgoing arc, and traces a walk backward through the recorded predecessors. The relation retains every allowed tie-break. The split graph $G_u$ redirects every arc entering $u$ to a new node $u'$ carrying the parameter $\delta$.
--
--   This definition supplies the output labels, the traced walk, and shortest-path cost used by the oracle lemmas.
-- source:
--   Dadush, Koh, Natura, Végh, arXiv:2004.08634v4, Algorithm 2, p.13, and split graph G_u, p.14

import Mathlib
import Definitions.Def_AccelNewtonDinkelbach_Supplement_M2VPI

namespace AccelNewtonDinkelbach.Supplement

set_option autoImplicit false

namespace M2VPI

variable {n m : ℕ} (M : M2VPI n m)

abbrev SplitNode (n : ℕ) := Option (Fin n)

def splitTail (e : Fin m) : SplitNode n := some (M.tail e)
def splitHead (u : Fin n) (e : Fin m) : SplitNode n :=
  if M.head e = u then none else some (M.head e)

def IsSplitWalkEdges (A : Fin m → Prop) (u : Fin n) : SplitNode n → SplitNode n →
    List (Fin m) → Prop
  | s, t, [] => s = t
  | s, t, e :: es => A e ∧ M.splitTail e = s ∧ IsSplitWalkEdges A u (M.splitHead u e) t es

structure SplitWalk (A : Fin m → Prop) (u : Fin n) where
  start : SplitNode n
  finish : SplitNode n
  edges : List (Fin m)
  valid : M.IsSplitWalkEdges A u start finish edges

namespace SplitWalk

variable {M : M2VPI n m} {A : Fin m → Prop} {u : Fin n}

def verticesFrom (M : M2VPI n m) (u : Fin n) : SplitNode n → List (Fin m) → List (SplitNode n)
  | s, [] => [s]
  | s, e :: es => s :: verticesFrom M u (M.splitHead u e) es

def vertices (P : M.SplitWalk A u) := verticesFrom M u P.start P.edges
def walkCost (P : M.SplitWalk A u) : ℝ := M2VPI.Walk.cost M P.edges
def walkGain (P : M.SplitWalk A u) : ℝ := M2VPI.Walk.gain M P.edges
noncomputable def yCost (P : M.SplitWalk A u) (y : SplitNode n → EReal) : EReal :=
  (P.walkCost : EReal) + (P.walkGain : EReal) * y P.finish
def IsPath (P : M.SplitWalk A u) : Prop := P.vertices.Nodup
def IsShortest (P : M.SplitWalk A u) (y : SplitNode n → EReal) : Prop :=
  P.IsPath ∧ ∀ Q : M.SplitWalk A u, Q.start = P.start → Q.finish = P.finish → P.yCost y ≤ Q.yCost y

end SplitWalk

/-- One simultaneous Bellman update of Grapevine. -/
noncomputable def grapevineUpdate (A : Fin m → Prop) (u : Fin n)
    (y : SplitNode n → EReal) (v : SplitNode n) : EReal :=
  sInf ({y v} ∪ {z | ∃ e, A e ∧ M.splitTail e = v ∧
    z = (M.cost e : EReal) + (M.gain e : EReal) * y (M.splitHead u e)})

def IsPred (A : Fin m → Prop) (u : Fin n) (y y' : SplitNode n → EReal)
    (pred : SplitNode n → Option (Fin m)) : Prop :=
  (∀ v, y' v = M.grapevineUpdate A u y v) ∧
  ∀ v, if y' v < y v then
    ∃ e, pred v = some e ∧ A e ∧ M.splitTail e = v ∧
      y' v = (M.cost e : EReal) + (M.gain e : EReal) * y (M.splitHead u e)
  else pred v = none

def traceEdges (u : Fin n) (pred : ℕ → SplitNode n → Option (Fin m)) :
    ℕ → SplitNode n → List (Fin m)
  | 0, _ => []
  | k + 1, v => match pred (k + 1) v with
    | none => traceEdges u pred k v
    | some e => e :: traceEdges u pred k (M.splitHead u e)

/-- Algorithm 2, including all tie-breaks. -/
def Grapevine (A : Fin m → Prop) (u : Fin n) (input output : SplitNode n → EReal)
    (P : M.SplitWalk A u) : Prop :=
  let N := Fintype.card (SplitNode n)
  ∃ (ys : ℕ → SplitNode n → EReal) (pred : ℕ → SplitNode n → Option (Fin m)),
    ys 0 = input ∧
    (∀ i < N, M.IsPred A u (ys i) (ys (i + 1)) (pred (i + 1))) ∧
    output = ys N ∧ P.start = some u ∧ P.edges = traceEdges M u pred N (some u)

end M2VPI

end AccelNewtonDinkelbach.Supplement


