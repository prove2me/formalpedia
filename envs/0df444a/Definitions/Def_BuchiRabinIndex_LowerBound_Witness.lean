-- Prove2me | Definitions.Def_BuchiRabinIndex_LowerBound_Witness
-- name    : BuchiRabinIndex_LowerBound_Witness
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T06:33:40.10599+00:00
-- url     : https://prove2.me/theorems/1061aa67-6b8d-4df0-a4cd-8ee417808c71
-- title:
--   Canonical histories, effect letters, and witness cycles
-- statement:
--   For a nonempty ordered tree $T$ with at most $n$ nodes, enumerate its nodes in preorder as $\tau_1,\ldots,\tau_k$. The canonical history $H(T)$ assigns own state $q_i$ to $\tau_i$, with each label the states assigned to its descendants. A simple history has singleton own sets. The identity, generation, permutation, acceptance and deletion letters are literal finite transition relations.
--
--   For a node $x$, the word $A_x$ returns from $H(C(x))$ to itself using the paper’s acceptance and restoring letters. For $y\notin C(x)$, the word $W_x^y$ inserts the preorder list of $C(y)\setminus C(x)$, then deletes that list in reverse order. Every insertion permutation is explicit, including the full-tree accepting permutation. Each restoring letter maps the current own state of the $j$th node to $q_j$; no unspecified bijection is assumed. Set $W_x^y=\varnothing$ when $y\in C(x)$ and define
--   $$W_x=\bigcup_{y\in S\setminus\{x\}}W_x^y,\qquad C_x=W_x\cup A_x.$$
--
--   The cycle sets are the actual edges traversed by those words. Construction returns an optional valid history, so no artificial history is supplied for an empty or oversized input. The effect predicate merely states an exact successor equation, simplicity, and exact accepting and unstable annotation sets; it assumes no effect theorem.
-- source:
--   Cong Tian, Runzhe Ma, Wensheng Wang, Zhenhua Duan, Büchi Determinization with Optimal States and Square Root Index Improvement, STOC 2027 submission #1731 (October 2026), §6.3, Lemma 38, p. 27; witness constructions and Lemmas 39–41, p. 28; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1731.pdf

import Definitions.Def_BuchiRabinIndex_LowerBound_Rabin

set_option autoImplicit false

namespace BuchiRabinIndex.LowerBound
noncomputable section
open scoped Classical

/-- H(T): descendants carry their preorder-assigned own states. -/
def canonicalData (n : ℕ) (T : Finset Node) : TreeData (Fin n) :=
  ⟨T, fun x => if x ∈ T then Finset.univ.filter fun q =>
    ∃ y ∈ T, x.IsPrefix y ∧ q.val = rank T y else ∅⟩

def Htree (n : ℕ) (T : Finset Node) : Option (History (Fin n)) :=
  asHistory (canonicalData n T)

def Simple {Q : Type} (H : History Q) : Prop :=
  ∀ x ∈ H.val.nodes, (own H.val x).card = 1

def stateSet {Q : Type} (H : TreeData Q) : Finset Q := H.label []

def owner {Q : Type} (H : TreeData Q) (p : Q) : Node :=
  if h : ∃ x ∈ H.nodes, p ∈ own H x then Classical.choose h else []

def lastState (n : ℕ) (hn : 1 ≤ n) : Fin n := ⟨n - 1, by omega⟩

/-- Total extension of finite permutations; used only on the indicated source state set. -/
def stateAt (n : ℕ) (hn : 1 ≤ n) (i : ℕ) : Fin n :=
  ⟨i % n, Nat.mod_lt _ (by omega)⟩

def idLetter {n : ℕ} (P : Finset (Fin n)) : Letter n := P.image fun p => (p, p)

def permLetter {n : ℕ} (P : Finset (Fin n)) (π : Fin n → Fin n) : Letter n :=
  P.image fun p => (p, π p)

def genLetter {n : ℕ} (hn : 1 ≤ n) (P : Finset (Fin n)) (p : Fin n) : Letter n :=
  insert (p, lastState n hn) (idLetter P)

def accLetter {n : ℕ} (hn : 1 ≤ n) (P : Finset (Fin n)) (s : Fin n) : Letter n :=
  insert (s, lastState n hn) (idLetter (P.erase s))

def delLetter {n : ℕ} (P : Finset (Fin n)) (s : Fin n) : Letter n :=
  idLetter (P.erase s)

def delPrimeLetter {n : ℕ} (hn : 1 ≤ n) (P : Finset (Fin n)) (s : Fin n) : Letter n :=
  insert (lastState n hn, s) (idLetter ((P.erase s).erase (lastState n hn)))

def mapData {Q R : Type} (H : TreeData Q) (π : Q → R) : TreeData R :=
  ⟨H.nodes, fun x => (H.label x).image π⟩

def generatedData {n : ℕ} (hn : 1 ≤ n) (H : TreeData (Fin n)) (p : Fin n) : TreeData (Fin n) :=
  let z := owner H p ++ [degree H.nodes (owner H p) + 1]
  ⟨insert z H.nodes, fun x => H.label x ∪
    if x.IsPrefix z then {lastState n hn} else ∅⟩

def deletedData {n : ℕ} (H : TreeData (Fin n)) (z : Node) (s : Fin n) : TreeData (Fin n) :=
  ⟨H.nodes.erase z, fun x => if x = z then ∅ else (H.label x).erase s⟩

def deletedPrimeData {n : ℕ} (hn : 1 ≤ n) (H : TreeData (Fin n)) (z : Node) (s : Fin n) : TreeData (Fin n) :=
  mapData (deletedData H z s) (fun p => if p = lastState n hn then s else p)

/-- Source's bijection restoring the j-th preorder own state to q_j. -/
def restoringLetter (n : ℕ) (T : Finset Node) (H : TreeData (Fin n)) : Letter n :=
  Finset.univ.filter fun e => ∃ x ∈ T, e.1 ∈ own H x ∧ e.2.val = rank T x

/-- Sorting by preorder traversal, without postulating a chosen enumeration. -/
def enumerateNodes (T : Finset Node) : List Node :=
  T.toList.mergeSort (fun x y => decide (x = y ∨ PreLt x y))

def canonicalStates (n : ℕ) (T : Finset Node) : Finset (Fin n) :=
  Finset.univ.filter fun q => q.val < T.card

/-- A_x, as a word, including the special full-tree self-loop. -/
def acceptingWord (n : ℕ) (hn : 1 ≤ n) (x : Node) : List (Letter n) :=
  let T := chain x
  let P := canonicalStates n T
  let s := stateAt n hn (T.card - 1)
  if T.card < n then
    [accLetter hn P s,
     permLetter (insert (lastState n hn) (P.erase s))
       (fun q => if q = lastState n hn then s else q)]
  else [idLetter P]

/-- The i-th intermediate U_i, with zero-based list positions. -/
def intermediate (x y : Node) (i : ℕ) : Finset Node :=
  chain x ∪ ((enumerateNodes (chain y \ chain x)).take i).toFinset

/-- Phase 1: gen followed by the explicit insertion permutation, when required. -/
def insertBlock (n : ℕ) (hn : 1 ≤ n) (x y : Node) (i : ℕ) : List (Letter n) :=
  let z := (enumerateNodes (chain y \ chain x))[i]!
  let T := intermediate x y i
  let U := insert z T
  let P := canonicalStates n T
  let p := stateAt n hn (rank T z.dropLast)
  let m := rank U z
  let π := fun q : Fin n =>
    if q = lastState n hn then stateAt n hn m
    else if m ≤ q.val ∧ q.val < T.card then stateAt n hn (q.val + 1) else q
  [genLetter hn P p] ++
    if U.card < n ∨ m ≠ n - 1 then [permLetter (insert (lastState n hn) P) π] else []

/-- Phase 2: the sole del' case and the explicitly computed restoring bijection. -/
def deleteBlock (n : ℕ) (hn : 1 ≤ n) (x y : Node) (i : ℕ) : List (Letter n) :=
  let z := (enumerateNodes (chain y \ chain x))[i]!
  let T := intermediate x y i
  let U := insert z T
  let H := canonicalData n U
  let P := canonicalStates n U
  let s := stateAt n hn (rank U z)
  if U.card = n ∧ s ≠ lastState n hn then
    [delPrimeLetter hn P s, restoringLetter n T (deletedPrimeData hn H z s)]
  else [delLetter P s, restoringLetter n T (deletedData H z s)]

/-- W_x^y, as an explicit finite letter sequence. -/
def connectingWord (n : ℕ) (hn : 1 ≤ n) (x y : Node) : List (Letter n) :=
  if y ∈ chain x then [] else
    let positions := List.range (chain y \ chain x).card
    positions.flatMap (insertBlock n hn x y) ++
      positions.reverse.flatMap (deleteBlock n hn x y)

def Acycle (n : ℕ) (hn : 1 ≤ n) (x : Node) : Set (Edge (Fin n) (Letter n)) :=
  wordEdges (fullBuchi n hn) (Htree n (chain x)) (acceptingWord n hn x)

def Wxy (n : ℕ) (hn : 1 ≤ n) (x y : Node) : Set (Edge (Fin n) (Letter n)) :=
  wordEdges (fullBuchi n hn) (Htree n (chain x)) (connectingWord n hn x y)

def Wx (n : ℕ) (hn : 1 ≤ n) (S : Finset Node) (x : Node) : Set (Edge (Fin n) (Letter n)) :=
  ⋃ y ∈ S.erase x, Wxy n hn x y

def Ccycle (n : ℕ) (hn : 1 ≤ n) (S : Finset Node) (x : Node) : Set (Edge (Fin n) (Letter n)) :=
  Wx n hn S x ∪ Acycle n hn x

/-- Exact successor, simplicity, and both annotation sets. -/
def Effect {n : ℕ} (hn : 1 ≤ n) (H : History (Fin n)) (σ : Letter n)
    (K : TreeData (Fin n)) (a u : Finset Node) : Prop :=
  ∃ H', successor (fullBuchi n hn) H σ = some H' ∧ H'.val = K ∧
    Simple H' ∧ acceptingNodes (fullBuchi n hn) H σ = a ∧
    unstable (fullBuchi n hn) H σ = u

end
end BuchiRabinIndex.LowerBound


