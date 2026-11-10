-- Prove2me | Definitions.Def_RevRedSAT_encCNF
-- name    : RevRedSAT_encCNF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:45:48.144699+00:00
-- url     : https://prove2.me/theorems/1c8248b3-3acd-4e06-8347-18e365e4e3cd
-- title:
--   CNF codes, clause width, occurring variables and distinct clauses
-- statement:
--   A CNF formula over the variables $0,\dots,n-1$ is a list of clauses, each a list of literals $(i,b)$; the literal $(i,b)$ is true under an assignment $a$ when $a(i)=b$ (the platform's `MainResults.CNF n`). This module fixes:
--
--   1. **the code** $|F|$: the formula is written as $n$ followed by the list of its clauses, each clause the list of its literals, a literal $(i,b)$ as $i$ in self-delimiting binary followed by the bit $b$; $|F|$ is the length of this word (§3, p.27);
--   2. **the width**: the largest number of distinct literals in a clause ("The width of a clause is its number of literals, after repeated literals within that clause are removed", App. C.5, p.94), $0$ for the formula with no clauses;
--   3. **$N$**, the number of distinct variables occurring in some literal, and **$M$**, the number of distinct clauses compared as sets of literals (§4.1, p.28);
--   4. the number of literal occurrences, and satisfaction of $\varphi$ by an assignment $a$: every clause contains a literal $(i,b)$ with $a(i)=b$.
--
--   A 3-CNF formula is a formula of width at most $3$.
--
--   **Formalization Note** The code is injective; clause order and literal order are part of the formula, and a formula may declare variables that do not occur.
-- source:
--   Kundu, Panolan, Saurabh, Xue, Zehavi, Reverse Reductions: From Faster SAT to Subexponential Algorithms, STOC 2027 submission (held manuscript, sha256 7bf9a5af…), §3, p.27 (encodings, width); §4.1, p.28 (N, M); App. C.5, p.94 (width after removing repeated literals)

import Mathlib
import Definitions.Def_MainResults
import Definitions.Def_RSListDecodingCapacity_AllRates_Encoding

set_option autoImplicit false

namespace RevRedSAT

open RSListDecodingCapacity.AllRates

/-- The code of a literal `(i, b)` (variable `i`, sign `b`; `b = true` is the positive literal):
`i` in self-delimiting binary followed by the bit `b`. -/
def encLit {n : ℕ} (l : MainResults.Lit n) : List Bool := encNat l.1.val ++ [l.2]

/-- **The explicit binary code of a CNF formula.**
Kundu, Panolan, Saurabh, Xue, Zehavi, *Reverse Reductions: From Faster SAT to Subexponential
Algorithms*, STOC 2027 submission (held manuscript, sha256 7bf9a5af…), §3, p.27: "We write |I| and
|F| for the lengths of the explicit binary encodings of an instance I and a formula F".

A formula `φ : MainResults.CNF n` (a list of clauses, each a list of literals over the variables
`0, …, n − 1`) is written as `n` followed by the list of its clauses, each clause the list of its
literal codes. `|F|` is the length of this word.

**Formalization Note** The code is injective and self-delimiting; clause order and literal order are
part of the formula. -/
def encCNF {n : ℕ} (φ : MainResults.CNF n) : List Bool :=
  encNat n ++ encList (encList encLit) φ

/-- **Clause width** (§3, p.27: "A CNF formula has width at most d if every clause contains at most
d literals"; App. C.5, p.94: "The width of a clause is its number of literals, after repeated
literals within that clause are removed"): the largest number of distinct literals of a clause,
`0` for the formula with no clauses. -/
def width {n : ℕ} (φ : MainResults.CNF n) : ℕ :=
  (φ.map fun C => C.toFinset.card).foldr max 0

/-- **The number `N` of occurring variables** (§4.1, p.28: "F is a CNF formula with N occurring
variables"): the number of distinct variables that appear in some literal. -/
def occVars {n : ℕ} (φ : MainResults.CNF n) : ℕ :=
  (φ.flatMap fun C => C.map Prod.fst).toFinset.card

/-- **The number `M` of distinct clauses** (§4.1, p.28: "M distinct clauses"): clauses are compared
as sets of literals. -/
def distinctClauses {n : ℕ} (φ : MainResults.CNF n) : ℕ :=
  (φ.map List.toFinset).toFinset.card

/-- The number of literal occurrences of `φ` (the total length of its clauses). -/
def litOcc {n : ℕ} (φ : MainResults.CNF n) : ℕ :=
  (φ.map List.length).sum

/-- The assignment `a` satisfies `φ`: every clause has a literal `(i, b)` with `a i = b`. -/
def SatBy {n : ℕ} (a : Fin n → Bool) (φ : MainResults.CNF n) : Prop :=
  ∀ C ∈ φ, ∃ l ∈ C, a l.1 = l.2

end RevRedSAT


