-- Prove2me | Definitions.Def_CircTrichotomy_Vocab
-- name    : CircTrichotomy_Vocab
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:58:06.91555+00:00
-- url     : https://prove2.me/theorems/0ae43cc9-7e81-46c3-ae7a-df609d558ba1
-- title:
--   Terms and numerical vocabularies: $\mathrm{arb}$ and $<,+\omega,\mathrm{mod},\min,\max$
-- statement:
--   A word $w=a_0\cdots a_{n-1}$ is a structure on the positions $\{0,\dots,n-1\}$ with letter predicates $P_a$. A predicate or constant is **numerical** if its interpretation depends only on the length $n$. A **numerical vocabulary** is a set of numerical constants and predicates; terms of the one-variable logics are the variable $x$ or a constant.
--
--   1. $\mathrm{arb}$: all numerical predicates and all numerical constants (a constant picks a position in $[0,n-1]$ for each length $n$).
--   2. $<,+\omega,\mathrm{mod},\min,\max$: the order $x<y$; the successor relations $x+j=y$ ($j\ge0$); the modular predicates $x\equiv r \bmod k$ ($k\ge1$); the constants $\min=0$ and $\max=n-1$.
--
--   **Formalization Note** A predicate is its interpretation $R_n\subseteq[0,n-1]^r$ for each length $n$, packaged with its arity. Letter predicates and equality are always available.
-- source:
--   Göller, Manuel, A Circuit Complexity Trichotomy For Regular Languages, arXiv:2611.03615 (version of November 3, 2026, sha256 5bef1791…), §A.5, pp.19–20

import Mathlib

set_option autoImplicit false

namespace CircTrichotomy

/-- A term of the one-variable logics: the variable `x` or a numerical constant. A numerical
constant is given by its interpretation `c n` on words of length `n` (Göller, Manuel, *A Circuit Complexity Trichotomy For Regular Languages*, arXiv:2611.03615 (version of November 3, 2026, sha256 5bef1791…), §A.5, p.20: "A
predicate or constant is numerical if its interpretation only depends on the domain"). -/
inductive NTerm where
  /-- the variable `x` -/
  | var : NTerm
  /-- a numerical constant with interpretation `c n ∈ [0, n − 1]` on words of length `n` -/
  | const (c : ℕ → ℕ) : NTerm

/-- Value of a term on a word of length `n` when `x` is assigned the position `a`. -/
def NTerm.eval (n a : ℕ) : NTerm → ℕ
  | var => a
  | const c => c n

/-- **A numerical vocabulary** (§A.5, pp.19–20): a set of numerical constants and a set of
numerical predicates. An `r`-ary numerical predicate is given by its interpretation
`R n : (Fin r → ℕ) → Prop` on the positions `[0, n − 1]` of words of length `n`; it is packaged with
its arity as `⟨r, R⟩`. Letter predicates `P_a` and equality are not part of a vocabulary: they are
always available. -/
structure Vocab where
  /-- the numerical constants -/
  consts : Set (ℕ → ℕ)
  /-- the numerical predicates, with their arities -/
  rels : Set (Σ r : ℕ, ℕ → (Fin r → ℕ) → Prop)

/-- **`arb`** (§A.5, p.20): "By arb we denote the class of all arbitrary numerical predicates and
constants." Every numerical predicate; every numerical constant whose value on words of length
`n ≥ 1` is a position `< n`. -/
def arbVocab : Vocab where
  consts := {c | ∀ n : ℕ, 0 < n → c n < n}
  rels := Set.univ

/-- **The vocabulary `<, +ω, mod, min, max`** (§A.5, pp.19–20): "The constant symbols min and max
denote the first and the last positions of the word, respectively. The binary predicate < denotes
the order on the positions. For k ≥ 0, the binary relation +k, written as x + k = y, holds if and
only if y is the k-th successor of x. The collection of all such successor relations is denoted in
the vocabulary by +ω. For r, k ∈ ℕ with k ≥ 1, the unary modular predicate x ≡ r mod k is true at
a position j if j ≡ r mod k. The collection of modular predicates is denoted by mod in the
vocabulary." -/
def ordVocab : Vocab where
  consts := {fun _ => 0, fun n => n - 1}
  rels := {⟨2, fun _ a => a 0 < a 1⟩} ∪ {R | ∃ j : ℕ, R = ⟨2, fun _ a => a 0 + j = a 1⟩} ∪
    {R | ∃ k r : ℕ, 0 < k ∧ R = ⟨1, fun _ a => a 0 % k = r % k⟩}

end CircTrichotomy


