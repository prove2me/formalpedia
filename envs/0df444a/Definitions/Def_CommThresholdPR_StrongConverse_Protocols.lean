-- Prove2me | Definitions.Def_CommThresholdPR_StrongConverse_Protocols
-- name    : CommThresholdPR_StrongConverse_Protocols
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:26:05.655573+00:00
-- url     : https://prove2.me/theorems/46cf3040-7442-4d0c-ad8a-636339fddf67
-- title:
--   Finite randomized binary communication trees and their execution
-- statement:
--   A protocol consists of a finite public random seed, a binary communication tree for each seed, private local message kernels, and independent local output kernels at the leaves. There is no uniform bound on the finite public alphabet, tree size, number of rounds or private sampling alphabets.
--
--   $$\operatorname{IC}_{\mu}(\pi)=I(X;T\mid Y,R_{\rm pub})+I(Y;T\mid X,R_{\rm pub}).$$
--   Execution samples the joint input, the independent public seed, and then only the sender's local kernel at each public node. The behavioral kernels encode independent finite private tapes: pre-sample all local input/node choices independently; conversely use the posterior private-tape law at each local history. Public history controls both sender and stopping. The padded finite trace records actual transmitted bits and termination; its padding conveys no extra information. Cost is the maximum number of actual bits over all inputs and positive-probability random executions, independent of the input law. Finite auxiliary symbols have an explicit unary binary encoding. This module provides a general two-party protocol interface.
-- source:
--   Daiki Suruga, The Exact Communication Threshold for Parallel Repetition, STOC 2027 submission #304 (October 2026), §§2.1–2.2, p. 7; Construction 5.1, pp. 16–17, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/304.pdf

import Definitions.Def_CommThresholdPR_StrongConverse_FiniteInfo

noncomputable section

namespace CommThresholdPR.StrongConverse

/-- A binary communication tree (§2.1, p.7). The shape, including the sender
and termination, is public. Kernels are sampled privately and independently.
This is the behavioral representation of finite private random tapes: one may
pre-sample the finite table of choices for every local input and public node.
Conversely, conditioning a private tape on its owner's input and earlier public
bits gives these kernels. Thus there is no bound on finite tape alphabets or
rounds, and no public revelation of private choices. -/
inductive BinaryTree (X Y A B : Type) where
  | leaf (a : X → PMF A) (b : Y → PMF B)
  | alice (bit : X → PMF Bool) (zero one : BinaryTree X Y A B)
  | bob (bit : Y → PMF Bool) (zero one : BinaryTree X Y A B)

namespace BinaryTree
variable {X Y A B : Type}

def height : BinaryTree X Y A B → ℕ
  | .leaf _ _ => 0
  | .alice _ l r => 1 + max l.height r.height
  | .bob _ l r => 1 + max l.height r.height

def run : BinaryTree X Y A B → X → Y → PMF (List Bool × A × B)
  | .leaf a b, x, y => (a x).bind fun av => (b y).map fun bv => ([], av, bv)
  | .alice bit l r, x, y => (bit x).bind fun v =>
      (if v then r.run x y else l.run x y).map fun z => (v :: z.1, z.2)
  | .bob bit l r, x, y => (bit y).bind fun v =>
      (if v then r.run x y else l.run x y).map fun z => (v :: z.1, z.2)

def senderAt : BinaryTree X Y A B → List Bool → Option Bool
  | .leaf _ _, _ => none
  | .alice _ _ _, [] => some true
  | .bob _ _ _, [] => some false
  | .alice _ l r, v :: h => if v then r.senderAt h else l.senderAt h
  | .bob _ l r, v :: h => if v then r.senderAt h else l.senderAt h

/-- Fixed finite carrier for a transcript. The extra position is always none
on an actual execution. Padded none values convey no additional bits. -/
abbrev Trace (t : BinaryTree X Y A B) := Fin (t.height + 1) → Option Bool

def finiteRun (t : BinaryTree X Y A B) (x : X) (y : Y) : PMF (t.Trace × A × B) :=
  (t.run x y).map fun z => (fun i => z.1[i.val]?, z.2)

/-- Send a finite symbol by a unary, prefix-free binary encoding. Zero-mass
branches use the original conditional row as a normalized fallback. -/
def sendAliceList {C : Type} [Nonempty C] (k : C → BinaryTree X Y A B) :
    List C → (X → PMF C) → BinaryTree X Y A B
  | [], _ => by classical exact k (Classical.arbitrary C)
  | c :: cs, p => by
      classical
      exact .alice (fun x => (p x).map (fun v => decide (v = c)))
        (sendAliceList k cs (fun x => condition (p x) (· ≠ c))) (k c)

def sendBobList {C : Type} [Nonempty C] (k : C → BinaryTree X Y A B) :
    List C → (Y → PMF C) → BinaryTree X Y A B
  | [], _ => by classical exact k (Classical.arbitrary C)
  | c :: cs, p => by
      classical
      exact .bob (fun y => (p y).map (fun v => decide (v = c)))
        (sendBobList k cs (fun y => condition (p y) (· ≠ c))) (k c)

def sendAlice {C : Type} [Fintype C] [Nonempty C]
    (p : X → PMF C) (k : C → BinaryTree X Y A B) : BinaryTree X Y A B := by
  classical
  exact sendAliceList k (Finset.univ : Finset C).toList p

def sendBob {C : Type} [Fintype C] [Nonempty C]
    (p : Y → PMF C) (k : C → BinaryTree X Y A B) : BinaryTree X Y A B := by
  classical
  exact sendBobList k (Finset.univ : Finset C).toList p

end BinaryTree

/-- Public randomness has an arbitrary finite alphabet; it is sampled before
and independently of the input and all private kernel choices. -/
structure Protocol (X Y A B : Type) where
  publicSize : ℕ
  publicLaw : PMF (Fin publicSize)
  tree : Fin publicSize → BinaryTree X Y A B

namespace Protocol
variable {X Y A B : Type}

def History (π : Protocol X Y A B) := (r : Fin π.publicSize) × (π.tree r).Trace

instance (π : Protocol X Y A B) : Fintype π.History :=
  inferInstanceAs (Fintype ((r : Fin π.publicSize) × (Fin ((π.tree r).height + 1) → Option Bool)))

def law (π : Protocol X Y A B) (μ : PMF (X × Y)) :
    PMF (Record X Y A B π.History) :=
  μ.bind fun xy => π.publicLaw.bind fun r =>
    ((π.tree r).finiteRun xy.1 xy.2).map fun z =>
      ⟨xy.1, xy.2, z.2.1, z.2.2, ⟨r, z.1⟩⟩

/-- Actual maximum, including only possible public/private executions, over
all input pairs. It is independent of the chosen input law. -/
def cost [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (π : Protocol X Y A B) : ℕ := by
  classical
  exact Finset.univ.sup fun xy : X × Y =>
    Finset.univ.sup fun r : Fin π.publicSize =>
      Finset.univ.sup fun z : (π.tree r).Trace × A × B =>
        if π.publicLaw r ≠ 0 ∧ (π.tree r).finiteRun xy.1 xy.2 z ≠ 0 then
          (Finset.univ.filter fun i => (z.1 i).isSome).card else 0

def info [Fintype X] [Fintype Y] (π : Protocol X Y A B) (μ : PMF (X × Y)) : ℝ :=
  cmi (π.law μ) Record.x Record.v (fun z => (z.y, z.v.1)) +
  cmi (π.law μ) Record.y Record.v (fun z => (z.x, z.v.1))

/-- Encode any finite public alphabet, without a cardinality bound. -/
def withPublic {U : Type} [Fintype U] (p : PMF U)
    (t : U → BinaryTree X Y A B) : Protocol X Y A B :=
  ⟨Fintype.card U, p.map (Fintype.equivFin U), fun r => t ((Fintype.equivFin U).symm r)⟩

def privateTree (t : BinaryTree X Y A B) : Protocol X Y A B :=
  withPublic (PMF.pure ()) (fun _ : Unit => t)

end Protocol
end CommThresholdPR.StrongConverse

namespace CommThresholdPR.StrongConverse
namespace Protocol
variable {X Y A B : Type}
def bits (π : Protocol X Y A B) (v : π.History) : List Bool :=
  (List.ofFn v.2).filterMap id

def prefixEvent (π : Protocol X Y A B) (r : Fin π.publicSize) (h : List Bool)
    (z : Record X Y A B π.History) : Prop :=
  z.v.1 = r ∧ h.IsPrefix (π.bits z.v)

def nextEvent (π : Protocol X Y A B) (h : List Bool) (b : Bool)
    (z : Record X Y A B π.History) : Prop := (π.bits z.v)[h.length]? = some b
end Protocol
end CommThresholdPR.StrongConverse


