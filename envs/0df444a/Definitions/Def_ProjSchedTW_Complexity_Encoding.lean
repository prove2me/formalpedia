-- Prove2me | Definitions.Def_ProjSchedTW_Complexity_Encoding
-- name    : ProjSchedTW_Complexity_Encoding
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T01:35:47.818539+00:00
-- url     : https://prove2.me/theorems/2f846c7f-91ec-4143-bb7b-5d0e82cc19c9
-- title:
--   Binary instance codes, and the languages PARTITION, SUBSET SUM and SIMPLE MAX CUT
-- statement:
--   This file fixes how instances are written as strings, and defines the three source problems of the reductions in Neumann, Schwindt and Zimmermann (proofs of Theorem 2.12.1, Proposition 2.5.4 and Proposition 3.4.2, all citing Garey and Johnson, 1979).
--
--   **Alphabet and numbers.** Instances are strings over the four-letter alphabet $\Sigma=\{0,1,-,\#\}$. A natural number $k$ is written by its binary digits, least significant first and without leading zeros (so $0$ is the empty digit string), followed by the separator $\#$. An integer $z$ is written as a minus sign if $z<0$, followed by the code of $|z|$. A list of numbers is the concatenation of their codes. Every number is thus written with $O(\log(|z|+2))$ symbols, so the length of a code is the usual binary size of an instance.
--
--   **PARTITION.** An instance is a list of sizes $s(1),\dots,s(\nu)\in\mathbb N$. It is a yes-instance iff the index set $\mathcal I=\{1,\dots,\nu\}$ can be split into two sets $\mathcal I'$ and $\mathcal I''=\mathcal I\setminus\mathcal I'$ with
--   $$\sum_{i\in\mathcal I'} s(i)=\sum_{i\in\mathcal I''} s(i).$$
--   The language PARTITION is the set of codes $s(1)\,s(2)\cdots s(\nu)$ of yes-instances.
--
--   **SUBSET SUM.** An instance is a list of sizes $s(1),\dots,s(\nu)\in\mathbb N$ and a threshold $M\in\mathbb N$; it is a yes-instance iff some $A\subseteq\{1,\dots,\nu\}$ has $\sum_{i\in A}s(i)=M$. The language consists of the codes $M\,s(1)\cdots s(\nu)$ of yes-instances.
--
--   **SIMPLE MAX CUT.** An instance is a simple undirected graph $G$ on the nodes $\{1,\dots,\nu\}$ and a number $M\in\mathbb N$. For $A\subseteq V^G$ let $\mathrm{cut}(A)$ be the number of edges of $G$ with one end in $A$ and the other in its complement. The instance is a yes-instance iff $\mathrm{cut}(A)\ge M$ for some $A$. It is coded as $\nu$, then the adjacency matrix row by row ($1$ for an edge, $0$ otherwise), then $M$.
--
--   These are the languages whose NP-completeness the mission takes as hypotheses (Karp, 1972; Garey and Johnson, 1979), and the target alphabet of every scheduling language of the mission.
--
--   **Formalization Note** Languages, the class NP, polynomial-time reductions and NP-completeness are those of the published definition file `CookPvsNP_defs` (Cook's one-tape Turing machines). Binary digits come from Mathlib's `Nat.bits`. Nodes and indices are `Fin ν`, so index $i$ of the book is `i - 1` here. Adjacency is decided classically.
-- source:
--   Neumann, Schwindt & Zimmermann, Project Scheduling with Time Windows and Scarce Resources, 2nd ed., Springer 2003, p. 131 (PARTITION, proof of Theorem 2.12.1), p. 48 (SUBSET SUM, proof of Proposition 2.5.4), p. 241 (SIMPLE MAX CUT, proof of Proposition 3.4.2); problem definitions after Garey & Johnson, Computers and Intractability, 1979

import Mathlib
import Definitions.Def_CookPvsNP_defs

namespace ProjSchedTW.Complexity

open CookPvsNP

/-! # Binary encodings and the three source problems of the reductions

Neumann, Schwindt & Zimmermann reduce from PARTITION (proof of Theorem 2.12.1, p. 131), from
SUBSET SUM (proof of Proposition 2.5.4, p. 48) and from SIMPLE MAX CUT (proof of Proposition
3.4.2, p. 241), all "cf. Garey and Johnson, 1979". Instances are written over a four-letter
alphabet, every number in binary, so that the size of an instance is the length of its code. -/

/-- The four-letter alphabet of instance codes: the binary digits `0`, `1`, a minus sign, and a
separator that ends the code of each number. -/
inductive BSym where
  | zero
  | one
  | minus
  | sep
  deriving DecidableEq

instance : Fintype BSym where
  elems := {BSym.zero, BSym.one, BSym.minus, BSym.sep}
  complete := by intro x; cases x <;> simp

instance : Nonempty BSym := ⟨BSym.zero⟩

/-- A natural number `k` in binary: its binary digits, least significant first and without
leading zeros (`Nat.bits`; the empty digit string for `k = 0`), followed by a separator. -/
def encNat (k : ℕ) : List BSym :=
  (Nat.bits k).map (fun b => if b then BSym.one else BSym.zero) ++ [BSym.sep]

/-- An integer `z` in binary: a minus sign if `z < 0`, then the binary code of `|z|`. -/
def encInt (z : ℤ) : List BSym :=
  (if z < 0 then [BSym.minus] else []) ++ encNat z.natAbs

/-- A list of natural numbers, each in binary, one after the other. -/
def encNats (xs : List ℕ) : List BSym := xs.flatMap encNat

/-- A list of integers, each in binary, one after the other. -/
def encInts (xs : List ℤ) : List BSym := xs.flatMap encInt

/-! ## PARTITION -/

/-- A PARTITION instance with sizes `s(1), …, s(ν) ∈ ℕ` (the list `s`, `ν = s.length`) is a
yes-instance iff the index set can be split into two parts `I'`, `I''` of equal total size. -/
def PartitionYes (s : List ℕ) : Prop :=
  ∃ A : Finset (Fin s.length), ∑ i ∈ A, s.get i = ∑ i ∈ Aᶜ, s.get i

/-- The PARTITION language: binary codes `s(1) s(2) … s(ν)` of the yes-instances. -/
def partitionLang : Lang BSym :=
  { w | ∃ s : List ℕ, PartitionYes s ∧ w = encNats s }

/-! ## SUBSET SUM -/

/-- A SUBSET SUM instance with sizes `s(1), …, s(ν) ∈ ℕ` and threshold `M ∈ ℕ` is a
yes-instance iff some subset of the indices has total size exactly `M`. -/
def SubsetSumYes (s : List ℕ) (M : ℕ) : Prop :=
  ∃ A : Finset (Fin s.length), ∑ i ∈ A, s.get i = M

/-- The SUBSET SUM language: binary codes `M s(1) … s(ν)` of the yes-instances. -/
def subsetSumLang : Lang BSym :=
  { w | ∃ (s : List ℕ) (M : ℕ), SubsetSumYes s M ∧ w = encNats (M :: s) }

/-! ## SIMPLE MAX CUT -/

open Classical in
/-- The number of edges of the simple graph `G` on the nodes `Fin ν` that join a node of `A` to
a node of its complement (each edge `{i, j}` counted once, as the pair with `i < j`). -/
noncomputable def cutSize {ν : ℕ} (G : SimpleGraph (Fin ν)) (A : Finset (Fin ν)) : ℕ :=
  (Finset.univ.filter fun e : Fin ν × Fin ν =>
    e.1 < e.2 ∧ G.Adj e.1 e.2 ∧ (e.1 ∈ A ↔ e.2 ∉ A)).card

/-- A SIMPLE MAX CUT instance, a graph `G` and a number `M`, is a yes-instance iff there is a
partition of the nodes into `A` and its complement with at least `M` edges between the parts. -/
def MaxCutYes {ν : ℕ} (G : SimpleGraph (Fin ν)) (M : ℕ) : Prop :=
  ∃ A : Finset (Fin ν), M ≤ cutSize G A

open Classical in
/-- The code of a SIMPLE MAX CUT instance: `ν`, the adjacency matrix row by row (`1` for an edge,
`0` otherwise), then `M`, all in binary. -/
noncomputable def maxCutCode {ν : ℕ} (G : SimpleGraph (Fin ν)) (M : ℕ) : List BSym :=
  encNats ([ν] ++ (List.ofFn fun i : Fin ν => List.ofFn fun j : Fin ν =>
    if G.Adj i j then 1 else 0).flatten ++ [M])

/-- The SIMPLE MAX CUT language: codes of the yes-instances. -/
def maxCutLang : Lang BSym :=
  { w | ∃ (ν : ℕ) (G : SimpleGraph (Fin ν)) (M : ℕ), MaxCutYes G M ∧ w = maxCutCode G M }

end ProjSchedTW.Complexity


