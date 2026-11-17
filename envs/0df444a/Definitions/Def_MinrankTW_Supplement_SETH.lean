-- Prove2me | Definitions.Def_MinrankTW_Supplement_SETH
-- name    : MinrankTW_Supplement_SETH
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:04:54.918131+00:00
-- url     : https://prove2.me/theorems/95221ab2-0467-4ecb-8df6-d2c307edc8f0
-- title:
--   The Strong Exponential Time Hypothesis on the logarithmic-cost RAM
-- statement:
--   A **CNF formula** on $N$ Boolean variables is a list of clauses, each clause a list of literals $x_j$ or $\neg x_j$; it is a **$d$-CNF** if every clause has at most $d$ literals, and **satisfiable** if some assignment makes a literal of every clause true.
--
--   The **Strong Exponential Time Hypothesis** (SETH) asserts: for every $\delta>0$ there is a clause width $d$ such that no deterministic algorithm decides satisfiability of $d$-CNF formulas on $N$ variables in time
--   $$
--   2^{(1-\delta)N}\,\mathrm{poly}(L),
--   $$
--   where $L$ is the length of the encoded formula.
--
--   This is the hypothesis of the conditional lower bound (Theorem 6).
--
--   **Formalization Note** Algorithms are programs of the published logarithmic-cost RAM `MinrankTW.RAM`, with total cost at most $C\,2^{(1-\delta)N}(L+1)^k$ for constants $C,k$, answering in cell $0$ ($1$ exactly on satisfiable formulas). The formula is written as $[N,m]$ followed, clause by clause, by its length and the pairs (variable, sign). The polynomial is in the input length: with repeated clauses a formula is arbitrarily long, and a bound polynomial in $N$ alone would exclude every algorithm for a trivial reason.
-- source:
--   Perles–Weinstein, Efficient Algorithms for Minrank and Index Coding for Low-Treewidth Graphs, STOC 2027 submission (manuscript sha256 32a91384…), §B.1, p.19 (SETH, citing Impagliazzo–Paturi 2001)

import Mathlib
import Definitions.Def_MinrankTW_RAM

namespace MinrankTW.Supplement

/-!
# The Strong Exponential Time Hypothesis on the logarithmic-cost RAM

Perles–Weinstein, *Efficient Algorithms for Minrank and Index Coding for Low-Treewidth Graphs*,
STOC 2027 submission manuscript (sha256 32a91384…c57991), §B.1, p.19: "Here SETH asserts that for
every δ > 0, some fixed clause width d rules out a 2^{(1−δ)N} poly(N) algorithm for d-SAT [IP01]."

**Formalization Note**
* A CNF on `N` variables is a list of clauses, a clause a list of literals (a variable `Fin N` and a
  sign). It is a `d`-CNF when every clause has at most `d` literals. Empty clauses and repeated
  clauses or literals are allowed, with their usual meaning.
* `CNF.code` is the RAM input: `[N, m]` and then, clause by clause, its length followed by the pairs
  `(variable, sign)` (sign `1` for a positive literal). Cell `i` holds the `i`-th entry.
* Algorithms are deterministic programs of the published `MinrankTW.RAM` (the machine of Theorem 6),
  with total logarithmic cost at most `C·2^{(1−δ)N}·(L + 1)^k`, `L` the length of the code, deciding
  satisfiability in cell `0` (`1` exactly on satisfiable formulas). The polynomial is in the input
  length, not in `N` alone: with repeated clauses a formula is arbitrarily long, and a bound
  `2^{(1−δ)N} poly(N)` would exclude every algorithm for a trivial reason.
-/

/-- A literal on `N` variables. -/
structure Lit (N : ℕ) where
  var : Fin N
  pos : Bool

/-- A CNF formula on `N` variables: a list of clauses. -/
abbrev CNF (N : ℕ) := List (List (Lit N))

/-- The value of a literal under the assignment `x`. -/
def Lit.eval {N : ℕ} (x : Fin N → Bool) (l : Lit N) : Bool :=
  if l.pos then x l.var else !(x l.var)

/-- Some assignment makes a literal of every clause true. -/
def CNF.Satisfiable {N : ℕ} (φ : CNF N) : Prop :=
  ∃ x : Fin N → Bool, ∀ cl ∈ φ, ∃ l ∈ cl, l.eval x = true

/-- The RAM input of a CNF formula. -/
def CNF.code {N : ℕ} (φ : CNF N) : List ℕ :=
  [N, φ.length] ++ φ.flatMap fun cl =>
    cl.length :: cl.flatMap fun l => [(l.var : ℕ), if l.pos then 1 else 0]

/-- **SETH** (p.19): for every `δ > 0` there is a clause width `d` such that no deterministic
program decides `d`-SAT on `N` variables within cost `C·2^{(1−δ)N}·(L + 1)^k`. -/
def SETH : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ d : ℕ, ¬ ∃ (P : List Instr) (C k : ℕ),
    ∀ (N : ℕ) (φ : CNF N), (∀ cl ∈ φ, cl.length ≤ d) →
      HaltsWithin P (fun i => φ.code.getD i 0)
        ⌊(C : ℝ) * (2 : ℝ) ^ ((1 - δ) * (N : ℝ)) * ((φ.code.length : ℝ) + 1) ^ k⌋₊
        (fun out => out 0 = 1 ↔ φ.Satisfiable)

end MinrankTW.Supplement


