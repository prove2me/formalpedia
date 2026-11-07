-- Prove2me | Definitions.Def_ReadTwiceCount_Formula
-- name    : ReadTwiceCount_Formula
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:38:47.854331+00:00
-- url     : https://prove2.me/theorems/7e98b8c7-a6e7-42d6-b98f-28e06d8bceae
-- title:
--   CNF formulas with multiplicities, read-twice, normalized, and the count $Z(F)$
-- statement:
--   A **formula** on the explicitly listed universe $\{0,\dots,M-1\}$ of $M$ Boolean variables is a list of clauses, and a **clause** is a list of literals. A literal $(v,b)$ is true under an assignment $\sigma:\{0,\dots,M-1\}\to\{0,1\}$ exactly when $\sigma(v)=b$; so $(v,1)$ is $v$ and $(v,0)$ is $\neg v$. A clause holds when one of its literals is true (the empty clause never holds), and $\sigma\models F$ when every clause holds.
--
--   1. The number of **occurrences** of a variable $v$ in $F$ is counted with multiplicity over all clauses: a clause $(x\vee x)$ contributes two occurrences of $x$.
--   2. $F$ is **read-twice** if every variable has at most two occurrences, with any signs.
--   3. $F$ is **normalized** if no clause contains a literal twice and no clause contains a variable with both signs.
--   4. The **count** is
--   $$Z(F)=\#\{\sigma:\sigma\models F\},$$
--   over all $2^M$ assignments of the universe.
--
--   Unit clauses, empty clauses, repeated literals, repeated clauses and free variables are all allowed in a formula: normalization is a property the algorithm establishes for its states, not an assumption on the input.
--
--   **Formalization Note** The universe size $M$ is a parameter of the type `Formula M`; literals are pairs in `Fin M × Bool`. Lists keep multiplicities, which the read-twice condition and the encoding length depend on.
-- source:
--   He, A Deterministic Approximation Scheme for Counting Read-Twice CNF Assignments, STOC 2027 submission (manuscript sha256 7a2a9dcd…), Theorem 1.1, p.1; §2, p.2

import Mathlib

namespace ReadTwiceCount

/-- A literal on the universe `Fin M`: the pair `(v, b)` is the literal that is true under an
assignment `σ` exactly when `σ v = b`. So `(v, true)` is `v` and `(v, false)` is `¬v`. -/
abbrev Lit (M : ℕ) := Fin M × Bool

/-- **An unweighted Boolean CNF formula on an explicitly listed universe of `M` variables.**
He, *A Deterministic Approximation Scheme for Counting Read-Twice CNF Assignments*, STOC 2027
submission (manuscript sha256 7a2a9dcd…), Theorem 1.1, p.1, and §2, p.2.

A formula is a list of clauses, and a clause is a list of literals.

**Formalization Note** Lists keep multiplicities: repeated literals inside a clause, repeated
clauses, tautological clauses, unit clauses, empty clauses and free variables are all allowed, as in
the paper's input ("Occurrences are counted with multiplicity in the input", p.2). The universe size
`M` is a parameter of the type; states derived from a formula keep the same universe. -/
structure Formula (M : ℕ) where
  /-- The clauses, in input order. -/
  clauses : List (List (Lit M))
  deriving DecidableEq

namespace Formula

variable {M : ℕ}

/-- `F.eval σ` is `true` iff every clause of `F` contains a literal that is true under `σ`.
The empty clause is false; the formula with no clauses is true. -/
def eval (F : Formula M) (σ : Fin M → Bool) : Bool :=
  F.clauses.all fun C => C.any fun l => σ l.1 == l.2

/-- `σ ⊨ F`. -/
def Satisfies (F : Formula M) (σ : Fin M → Bool) : Prop := F.eval σ = true

/-- The number of occurrences of the variable `v` in `F`, **counted with multiplicity** over all
clauses (He, STOC 2027 submission, manuscript sha256 7a2a9dcd…, §2, p.2). -/
def occ (F : Formula M) (v : Fin M) : ℕ :=
  (F.clauses.map fun C => C.countP fun l => l.1 = v).sum

end Formula

/-- **Read-twice.** "At most two total literal occurrences of each variable" (He, STOC 2027
submission, manuscript sha256 7a2a9dcd…, Theorem 1.1, p.1): every variable occurs at most twice,
counted with multiplicity, with any signs. -/
def ReadTwice {M : ℕ} (F : Formula M) : Prop := ∀ v : Fin M, F.occ v ≤ 2

/-- **Normalized** (He, STOC 2027 submission, manuscript sha256 7a2a9dcd…, §2, p.2: "We first
delete tautological clauses and collapse repeated literals within each clause … Subsequent formulas
are normalized in this sense"): no clause contains a literal twice, and no clause contains a
variable with both signs. This is a standing assumption on the algorithm's states, never on its
input. -/
def Normalized {M : ℕ} (F : Formula M) : Prop :=
  ∀ C ∈ F.clauses, C.Nodup ∧ ∀ v : Fin M, ¬((v, true) ∈ C ∧ (v, false) ∈ C)

/-- **The count `Z(F) = #{σ : σ ⊨ F}`** over all `2^M` assignments of the universe (He, STOC 2027
submission, manuscript sha256 7a2a9dcd…, Theorem 1.1, display (1), p.1). -/
def Z {M : ℕ} (F : Formula M) : ℕ :=
  (Finset.univ.filter fun σ : Fin M → Bool => F.eval σ = true).card

end ReadTwiceCount


