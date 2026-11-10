-- Prove2me | Definitions.Def_GoldsteinMCSP_Hardness_Strings
-- name    : GoldsteinMCSP_Hardness_Strings
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T17:11:34.927201+00:00
-- url     : https://prove2.me/theorems/87df8424-989c-4d9d-a0eb-de0db4082dd0
-- title:
--   Unsigned, signed and multiset common partitions and separator strings
-- statement:
--   Letters have arbitrary natural-number labels. Words are finite lists and families are indexed lists of words retaining repeated components. Related unsigned words have equal multiplicities of every letter. The two-copy predicate bounds each letter count by two. Cut partitions enumerate all decompositions into nonempty contiguous blocks, including the empty decomposition of the empty word. A common partition is a pair of such decompositions with the same blocks up to permutation, including multiplicities. Its objective is the block count, and the optimum is the minimum over the explicitly enumerated finite feasible set; it is zero on unrelated inputs, which are excluded by the theorem domains.
--
--   A signed letter is a label and a sign bit. Negating a block reverses it and flips every sign. Signed common partitions use a bijection of block positions, each matched block being equal or reverse-negated. Signed relatedness counts underlying labels, ignoring signs. Family partitions cut each component separately and then compare the collected blocks by permutation; their optimum is the attained minimum on related families.
--
--   For a list of separator pairs (x_i,y_i), the separated word places x_i y_i after component i; absent components on the shorter side are empty. Swapping each separator pair gives exactly the second string in equation (1). Freshness means all separator symbols are distinct and absent from both families. Letter-preserving position bijections and the count of consecutive positions whose images fail to be consecutive in the same order are also defined.
-- source:
--   Goldstein, Kolman and Zheng (2005), Minimum Common String Partition Problem: Hardness and Approximations, EJC 12, R50, DOI 10.37236/1947, Section 1 and Section 1.1, printed/PDF pp. 2–6, equation (1)

import Mathlib

namespace GoldsteinMCSP.Hardness

abbrev Word := List ℕ
abbrev Family := List Word
abbrev SignedLetter := ℕ × Bool
abbrev SignedWord := List SignedLetter

/-- All cut partitions, with no empty blocks; the empty word has one partition, []. -/
def cuts {α : Type} : List α → List (List (List α))
  | [] => [[]]
  | a :: w => (cuts w).flatMap fun p =>
      match p with
      | [] => [[[a]]]
      | b :: bs => [[a] :: b :: bs, (a :: b) :: bs]

def related (a b : Word) : Prop := a.Perm b

def twoCopies (a : Word) : Bool := a.all (fun x => a.count x ≤ 2)

def common (a b : Word) (p q : List Word) : Prop :=
  p ∈ cuts a ∧ q ∈ cuts b ∧ p.Perm q

/-- Minimum of a nonempty finite list; zero on the empty list (invalid inputs only). -/
def least (xs : List ℕ) : ℕ :=
  match xs with
  | [] => 0
  | x :: rest => rest.foldl min x

def commonSizes (a b : Word) : List ℕ :=
  (cuts a).flatMap fun p => (cuts b).filterMap fun q =>
    if p.Perm q then some p.length else none

def optimum (a b : Word) : ℕ := least (commonSizes a b)

def reverseSigned (w : SignedWord) : SignedWord :=
  w.reverse.map fun x => (x.1, !x.2)

/-- An explicit index bijection, preserving repetitions; each block can be reversed and flipped. -/
def signedCommon (a b : SignedWord) (p q : List SignedWord) : Prop :=
  p ∈ cuts a ∧ q ∈ cuts b ∧
  ∃ σ : Fin p.length ≃ Fin q.length,
    ∀ i, p.get i = q.get (σ i) ∨ p.get i = reverseSigned (q.get (σ i))

def signedRelated (a b : SignedWord) : Prop :=
  (a.map Prod.fst).Perm (b.map Prod.fst)

/-- Enumerate partitions within each component, never across a component boundary. -/
def familyCuts : Family → List (List Word)
  | [] => [[]]
  | a :: as => (cuts a).flatMap fun p => (familyCuts as).map (p ++ ·)

def familyCommon (a b : Family) (p q : List Word) : Prop :=
  p ∈ familyCuts a ∧ q ∈ familyCuts b ∧ p.Perm q

def familyOptimum (a b : Family) : ℕ := least <|
  (familyCuts a).flatMap fun p => (familyCuts b).filterMap fun q =>
    if p.Perm q then some p.length else none

/-- Equation (1); missing components on the shorter side contribute no letters. -/
def separated (a : Family) (s : List (ℕ × ℕ)) : Word :=
  ((List.range (s.length + 1)).map fun i =>
    a.getD i [] ++ match s[i]? with
      | none => []
      | some (x,y) => [x,y]).flatten

def freshSeparators (a b : Family) (s : List (ℕ × ℕ)) : Prop :=
  let labels := s.flatMap fun xy => [xy.1, xy.2]
  labels.Nodup ∧ ∀ x ∈ labels, x ∉ a.flatten ∧ x ∉ b.flatten

/-- Position bijections and their actual adjacency breaks, including length zero. -/
def preservesLetters (a b : Word) (σ : Fin a.length ≃ Fin b.length) : Prop :=
  ∀ i, a.get i = b.get (σ i)

def breakCount (a b : Word) (σ : Fin a.length ≃ Fin b.length) : ℕ :=
  ((List.finRange a.length).filter fun i =>
    if h : i.val + 1 < a.length then
      (σ ⟨i.val + 1, h⟩).val != (σ i).val + 1
    else false).length

end GoldsteinMCSP.Hardness


