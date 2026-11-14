-- Prove2me | Definitions.Def_KSATSingleFlip_Connect_SparseFlip
-- name    : KSATSingleFlip_Connect_SparseFlip
-- status  : Definition
-- author  : @wcysai
-- created : 2026-11-13T07:23:06.640831+00:00
-- url     : https://prove2.me/theorems/b4f929da-6fda-4d8d-b2b7-5208627b5b9e
-- title:
--   Sparse clauses and compact flip-list paths
-- statement:
--   A sparse width-$k$ clause stores $k$ distinct variable indices and their signs, and an ordered sparse formula stores one such record per clause occurrence. Its semantic interpretation is an option-valued clause in the existing random k-SAT model. A compact path stores an initial assignment followed by the ordered list of variable indices to flip; expanding it by successive flips yields its assignment sequence. Abstract word counts are supplied for the sparse input and compact output. These are representation definitions only: they do not define an operational word-RAM or assert a running time.
-- source:
--   Wang, Yin, Yu, Zhang, Single-Variable Connectivity in Random k-SAT, model on printed p. 2 and compact flip-list path representation on printed p. 32 (PDF p. 34), STOC 2027 submission #737, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/737.pdf

import Definitions.Def_KSATSingleFlip_Connect_Model

noncomputable section
open scoped Classical BigOperators
namespace KSATSingleFlip.Connect

/-- A proper width-k clause stored as k distinct variable indices and k signs.
Each index and sign is one abstract word; this is a data representation, not
yet an operational word-RAM model. -/
structure SparseClause (n k : ℕ) where
  index : Fin k ↪ Fin n
  sign : Fin k → Bool

/-- Sparse formula: m clause records, preserving order and multiplicity. -/
abbrev SparseFormula (n k m : ℕ) := Fin m → SparseClause n k

/-- Interpret a sparse clause in the paper's option-valued clause semantics. -/
def SparseClause.toClause {n k : ℕ} (C : SparseClause n k) : GClause (Fin n) :=
  fun v => if h : ∃ i, C.index i = v then some (C.sign (Classical.choose h)) else none

/-- Satisfaction directly on a sparse clause. -/
def SparseClause.Sat {n k : ℕ} (C : SparseClause n k) (x : Fin n → Bool) : Prop :=
  ∃ i, C.sign i = x (C.index i)

/-- Translate the ordered sparse clause collection to the formula model. -/
def sparseFormulaSemantics {n k m : ℕ} (F : SparseFormula n k m) : GFormula (Fin n) :=
  List.ofFn fun j => (F j).toClause

/-- Compact path: initial assignment and the ordered list of variables to flip,
as in the paper's implementation on printed p. 32. -/
structure FlipListPath (n : ℕ) where
  initial : Fin n → Bool
  flips : List (Fin n)

/-- Full sequence of assignments determined by the compact representation. -/
def FlipListPath.states {n : ℕ} (p : FlipListPath n) : List (Fin n → Bool) :=
  p.flips.scanl (fun x v => flip x v) p.initial

/-- Last assignment determined by the compact representation. -/
def FlipListPath.terminal {n : ℕ} (p : FlipListPath n) : Fin n → Bool :=
  p.flips.foldl (fun x v => flip x v) p.initial

/-- All states of a compact path satisfy the given formula. -/
def FlipListPath.Satisfies {n : ℕ} (p : FlipListPath n) (Φ : GFormula (Fin n)) : Prop :=
  ∀ x ∈ p.states, FSat x Φ

/-- Abstract word count for n,k,m, m sparse clauses, the start assignment,
and one requested variable. No runtime conclusion is asserted. -/
def sparseFlipInputWords (n k m : ℕ) : ℕ := 4 + 2 * k * m + n

/-- Abstract word count for initial assignment, flip-list length and indices. -/
def FlipListPath.wordCount {n : ℕ} (p : FlipListPath n) : ℕ := n + 1 + p.flips.length

end KSATSingleFlip.Connect


