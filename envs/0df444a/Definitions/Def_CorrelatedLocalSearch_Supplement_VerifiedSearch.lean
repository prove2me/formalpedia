-- Prove2me | Definitions.Def_CorrelatedLocalSearch_Supplement_VerifiedSearch
-- name    : CorrelatedLocalSearch_Supplement_VerifiedSearch
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T02:02:19.843724+00:00
-- url     : https://prove2.me/theorems/511b7b30-a7b1-41f3-8c73-c7ab386aedec
-- title:
--   Verified predecessor search, raw majority blocks and sufficient threshold $s_c$
-- statement:
--   For primitive comparison correctness probability $p>1/2$, let $\ell(p)$ be the least odd repetition count whose independent majority is correct with probability greater than $2^{-1/3}$. Three majority blocks form one move. Their favorable and adverse powered masses are $a_s,b_s$; $s_c$ is the unique solution of $2\sqrt{a_{s_c}b_{s_c}}=1$ and $\lambda=\sqrt{a_{s_c}/b_{s_c}}$. The model records ordered predecessor trees and the exact Appendix F schedule, including half-open intervals, dummy queries, and all $3\ell$ primitive queries per move.
-- source:
--   Xu, Local Search with Correlated Randomness, arXiv:2607.17469 (sha256 17e00d69…), §5 pp.13–14 and App. F pp.40–41 (PDF pp.15–16, 42–43)

import Mathlib
import Definitions.Def_CorrelatedLocalSearch_Supplement_GeneralSource

set_option autoImplicit false

namespace CorrelatedLocalSearch.Supplement

open MeasureTheory
open scoped ENNReal BigOperators

/-- Independent primitive comparison-error law: error probability `1-p`. -/
noncomputable def errorPi (p : Real) : Bool -> Real
  | false => p
  | true => 1 - p

/-- Reference probability that an odd block of `ell` primitive answers has correct majority. -/
noncomputable def majorityCorrectMass (p : Real) (ell : Nat) : Real :=
  ∑ j ∈ Finset.Icc (ell / 2 + 1) ell,
    Nat.choose ell j * p ^ j * (1 - p) ^ (ell - j)

/-- The least odd repetition count whose independent majority correctness exceeds `2^(-1/3)`. -/
noncomputable def repetitionCount (p : Real) : Nat :=
  sInf {ell : Nat | Odd ell ∧ 2 ^ (-(1 : Real) / 3) < majorityCorrectMass p ell}

/-- A raw block is favorable when all three consecutive majority votes are correct. -/
def IsFavorableBlock (ell : Nat) (e : List Bool) : Prop :=
  e.length = 3 * ell ∧ ∀ block : Fin 3,
    ((e.drop (block.val * ell)).take ell).count false > ell / 2

open Classical in
/-- Powered mass of favorable raw blocks. -/
noncomputable def searchA (p s : Real) : Real :=
  let ell := repetitionCount p
  ∑ e : Fin (3 * ell) -> Bool,
    if IsFavorableBlock ell (List.ofFn e) then wordMass (errorPi p) (List.ofFn e) ^ s else 0

open Classical in
/-- Powered mass of all other raw blocks. -/
noncomputable def searchB (p s : Real) : Real :=
  let ell := repetitionCount p
  ∑ e : Fin (3 * ell) -> Bool,
    if IsFavorableBlock ell (List.ofFn e) then 0 else wordMass (errorPi p) (List.ofFn e) ^ s

/-- The unique sufficient threshold `s_c` solving `2 sqrt(a_s b_s)=1`. -/
noncomputable def searchThreshold (p : Real) : Real :=
  sInf {s : Real | 0 ≤ s ∧ 2 * Real.sqrt (searchA p s * searchB p s) ≤ 1}

/-- `lambda=sqrt(a_{s_c}/b_{s_c})`. -/
noncomputable def searchLambda (p : Real) : Real :=
  Real.sqrt (searchA p (searchThreshold p) / searchB p (searchThreshold p))

/-- An ordered binary search tree with leaves labelled by the predecessor intervals. -/
structure OrderedSearchTree where
  Node : Type
  finiteNode : Fintype Node
  root : Node
  parent : Node -> Node
  leftChild : Node -> Node
  rightChild : Node -> Node
  splitKey : Node -> Real
  depth : Node -> Nat
  leafLabel : Node -> Option Nat
  intervalLower : Node -> WithBot Real
  intervalUpper : Node -> WithTop Real

attribute [instance] OrderedSearchTree.finiteNode

def TargetInLeafInterval (tree : OrderedSearchTree) (u : tree.Node) (x : Real) : Prop :=
  tree.intervalLower u ≤ (x : WithBot Real) ∧ (x : WithTop Real) < tree.intervalUpper u

/-- The structural meaning of "an ordered binary search tree whose leaves represent the
predecessor intervals."  Internal-node intervals are split into half-open child intervals, and
every non-root node is one of its parent's children. -/
def IsOrderedPredecessorTree (tree : OrderedSearchTree) : Prop :=
  tree.depth tree.root = 0 ∧ tree.parent tree.root = tree.root ∧
  tree.intervalLower tree.root = ⊥ ∧ tree.intervalUpper tree.root = ⊤ ∧
  (∀ u, tree.leafLabel u = none ->
    tree.leftChild u ≠ tree.rightChild u ∧
    tree.parent (tree.leftChild u) = u ∧ tree.parent (tree.rightChild u) = u ∧
    tree.depth (tree.leftChild u) = tree.depth u + 1 ∧
    tree.depth (tree.rightChild u) = tree.depth u + 1 ∧
    tree.intervalLower (tree.leftChild u) = tree.intervalLower u ∧
    tree.intervalUpper (tree.leftChild u) = (tree.splitKey u : WithTop Real) ∧
    tree.intervalLower (tree.rightChild u) = (tree.splitKey u : WithBot Real) ∧
    tree.intervalUpper (tree.rightChild u) = tree.intervalUpper u) ∧
  (∀ u, u ≠ tree.root -> tree.depth (tree.parent u) + 1 = tree.depth u ∧
    (u = tree.leftChild (tree.parent u) ∨ u = tree.rightChild (tree.parent u))) ∧
  ∀ u i, tree.leafLabel u = some i ->
    ¬ ∃ v, tree.parent v = u ∧ v ≠ u

noncomputable def searchConfidenceLength (p D eta : Real) : Nat :=
  max 1 (Nat.ceil (Real.logb (searchLambda p) (D / eta)))

/-- A location in the Appendix F walk.  `chainPosition = 0` is an original tree node; positive
positions are on the verification chain attached to a leaf. -/
structure SearchLocation (tree : OrderedSearchTree) where
  node : tree.Node
  chainPosition : Nat

def IsSearchEndpoint (tree : OrderedSearchTree) (p D eta : Real)
    (q : SearchLocation tree) : Prop :=
  (tree.leafLabel q.node).isSome = true ∧
    q.chainPosition = tree.depth q.node + searchConfidenceLength p D eta

/-- Majority error in one logical comparison.  `true` raw bits are primitive errors. -/
def majorityError (ell : Nat) (e : List Bool) : Bool :=
  decide (ell / 2 < e.count true)

/-- The three consecutive length-`ell` raw-error blocks consumed at move `m`. -/
def searchRawBlock (ell m block : Nat) (omega : Nat -> Bool) : List Bool :=
  List.ofFn (fun i : Fin ell => omega (m * (3 * ell) + block * ell + i.val))

def noisyComparison (truth error : Bool) : Bool := truth.xor error

open Classical in
/-- One exact Appendix F move.  All three majority blocks are supplied before the move.  Infinite
boundaries and the third comparison at a leaf/chain node are dummy queries: their raw bits are
consumed by `searchRawBlock` but their answers are ignored. -/
noncomputable def verifiedSearchStep (tree : OrderedSearchTree) (p D eta target : Real)
    (q : SearchLocation tree) (blocks : Fin 3 -> List Bool) : SearchLocation tree :=
  if IsSearchEndpoint tree p D eta q then q else
  let ell := repetitionCount p
  let lowerTruth := decide (target < (tree.intervalLower q.node).unbotD target)
  let upperTruth := decide (target < (tree.intervalUpper q.node).untopD target)
  let lowerAnswer := noisyComparison lowerTruth (majorityError ell (blocks 0))
  let upperAnswer := noisyComparison upperTruth (majorityError ell (blocks 1))
  let lowerOK := if tree.intervalLower q.node = ⊥ then true else !lowerAnswer
  let upperOK := if tree.intervalUpper q.node = ⊤ then true else upperAnswer
  if lowerOK && upperOK then
    if _hleaf : (tree.leafLabel q.node).isSome = true then
      ⟨q.node, q.chainPosition + 1⟩
    else
      let splitTruth := decide (target < tree.splitKey q.node)
      let splitAnswer := noisyComparison splitTruth (majorityError ell (blocks 2))
      ⟨if splitAnswer then tree.leftChild q.node else tree.rightChild q.node, 0⟩
  else if q.chainPosition = 0 then
    ⟨if q.node = tree.root then tree.root else tree.parent q.node, 0⟩
  else ⟨q.node, q.chainPosition - 1⟩

/-- State after `m` moves of the exact verified walk.  Each move consumes all `3*ell(p)` raw
primitive-error symbols, including dummy comparisons and comparisons rendered unnecessary by an
earlier failed verification majority. -/
noncomputable def verifiedSearchState (tree : OrderedSearchTree) (p D eta target : Real)
    (omega : Nat -> Bool) : Nat -> SearchLocation tree
  | 0 => ⟨tree.root, 0⟩
  | m + 1 =>
      let q := verifiedSearchState tree p D eta target omega m
      verifiedSearchStep tree p D eta target q
        (fun block => searchRawBlock (repetitionCount p) m block.val omega)

/-- Primitive-query count, with top when no chain endpoint is ever reached. -/
noncomputable def verifiedSearchQueries (tree : OrderedSearchTree) (p D eta target : Real)
    (omega : Nat -> Bool) : ℕ∞ :=
  ⨅ (m : Nat) (_h : IsSearchEndpoint tree p D eta
      (verifiedSearchState tree p D eta target omega m)),
    (3 * repetitionCount p * m : ℕ∞)

open Classical in
/-- Label returned at the first reached chain endpoint; `none` means nontermination. -/
noncomputable def verifiedSearchAnswer (tree : OrderedSearchTree) (p D eta target : Real)
    (omega : Nat -> Bool) : Option Nat :=
  if h : ∃ m, IsSearchEndpoint tree p D eta
      (verifiedSearchState tree p D eta target omega m) then
    tree.leafLabel (verifiedSearchState tree p D eta target omega (Nat.find h)).node
  else none

/-- The concrete Appendix F algorithm is completely determined by the ordered tree and the
parameters `p,D,eta`; its answer and query-count functions are the definitions above. -/
structure VerifiedSearchAlgorithm (tree : OrderedSearchTree) where
  p : Real
  D : Real
  eta : Real

def UsesAppendixFSchedule {tree : OrderedSearchTree} (p D eta : Real)
    (A : VerifiedSearchAlgorithm tree) : Prop := A.p = p ∧ A.D = D ∧ A.eta = eta

noncomputable def VerifiedSearchAlgorithm.queries {tree : OrderedSearchTree}
    (A : VerifiedSearchAlgorithm tree) : Real -> (Nat -> Bool) -> ℕ∞ :=
  verifiedSearchQueries tree A.p A.D A.eta

noncomputable def VerifiedSearchAlgorithm.answer {tree : OrderedSearchTree}
    (A : VerifiedSearchAlgorithm tree) : Real -> (Nat -> Bool) -> Option Nat :=
  verifiedSearchAnswer tree A.p A.D A.eta

/-- Main catalog declaration for verified noisy predecessor search. -/
abbrev VerifiedSearch (tree : OrderedSearchTree) := VerifiedSearchAlgorithm tree

end CorrelatedLocalSearch.Supplement


