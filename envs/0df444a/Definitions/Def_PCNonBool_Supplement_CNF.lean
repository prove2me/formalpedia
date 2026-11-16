-- Prove2me | Definitions.Def_PCNonBool_Supplement_CNF
-- name    : PCNonBool_Supplement_CNF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:25:35.605196+00:00
-- url     : https://prove2.me/theorems/97b4fc38-8b0f-4ea2-8878-ce7fa804af7d
-- title:
--   CNF formulas, variables and satisfiability
-- statement:
--   A **literal** over Boolean variables $x_0,x_1,\dots$ is $x_v$ or its negation $\neg x_v$; a **clause** is a disjunction of literals and a **CNF formula** $F=\bigwedge_{i=1}^m F_i$ a conjunction of clauses. We write $|F|=m$ for the number of clauses and $\mathrm{Vars}(F)$ for the set of variables occurring in $F$; $F$ is an **$n$-variable** formula when $|\mathrm{Vars}(F)|=n$. An assignment $\alpha$ satisfies $F$ if every clause contains a literal made true by $\alpha$, and $F$ is **satisfiable** if some assignment satisfies it.
--
--   These are the inputs and outputs of the reduction in Theorem 7.1.
--
--   **Formalization Note** Variables are natural numbers, a clause is a list of pairs $(v,\text{sign})$ and a formula a list of clauses; only occurring variables are counted.
-- source:
--   Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, On the Power of Polynomial Calculus over Non-Boolean Domains, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), §3.3, pp.10–11 (PDF pp.13–14); §7, p.50 (PDF p.53)

import Mathlib

namespace PCNonBool.Supplement

/-- A literal over the Boolean variables `x_0, x_1, …` (Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, *On the Power of Polynomial Calculus over Non-Boolean Domains*, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), §3.3, p.10 (PDF p.13)): `(v, true)`
is the literal `x_v` and `(v, false)` is its negation `¬x_v`. -/
abbrev Lit : Type := ℕ × Bool

/-- A clause: a disjunction of literals, given as a list (§3.3, p.10). -/
abbrev Clause : Type := List Lit

/-- A CNF formula `F = ⋀_{i=1}^m F_i`: the list of its clauses (§3.3, p.11 (PDF p.14);
Definition 7.2, p.51 (PDF p.54)). Its number of clauses `|F|` (p.50 (PDF p.53)) is the length of
the list. -/
abbrev CNF : Type := List Clause

/-- `Vars(F)`, the set of variables occurring in the CNF formula `F` (p.11 (PDF p.14)). An
"`n`-variable CNF formula" has `n = |Vars(F)|`. -/
def CNF.vars (Φ : CNF) : Finset ℕ := (Φ.flatten.map Prod.fst).toFinset

/-- The assignment `α` satisfies the CNF formula `Φ`: every clause contains a literal made true by
`α` (`x_v` is true iff `α v = true`, `¬x_v` is true iff `α v = false`). -/
def Satisfies (α : ℕ → Bool) (Φ : CNF) : Prop := ∀ C ∈ Φ, ∃ l ∈ C, α l.1 = l.2

/-- The CNF formula `Φ` is satisfiable: some assignment satisfies it. -/
def Satisfiable (Φ : CNF) : Prop := ∃ α : ℕ → Bool, Satisfies α Φ

/-- The CNF formula `Φ` has `n` variables (`|Vars(Φ)| = n`) and `m` clauses (`|Φ| = m`).

**Formalization Note** Variables are natural numbers; only the variables that occur count.
A clause is a list, so it may repeat a literal or contain both `x_v` and `¬x_v`; the semantics
(`Satisfies`) and the polynomial encodings are those of the set of its literals. -/
def CNF.numVars (Φ : CNF) : ℕ := Φ.vars.card

end PCNonBool.Supplement


