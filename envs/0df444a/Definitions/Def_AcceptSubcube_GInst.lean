-- Prove2me | Definitions.Def_AcceptSubcube_GInst
-- name    : AcceptSubcube_GInst
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:56:50.727863+00:00
-- url     : https://prove2.me/theorems/89e094f1-a1e2-4b4e-8824-391efc9d2b5d
-- title:
--   Raw Boolean CSP instances and their structural predicates
-- statement:
--   A **Boolean CSP instance** on $n$ variables $x_0,\dots,x_{n-1}$ is a finite list of constraints. Each constraint is a pair consisting of a **scope**, a list of variable indices $(v_0,\dots,v_{d-1})$, and a **truth table** listing the value of its predicate $P:\{0,1\}^d\to\{0,1\}$ on every local pattern $y$, the pattern $y$ being stored at position $\sum_i 2^i y_i$.
--
--   The structural requirements used in the paper are separate predicates on this raw type:
--
--   1. **well formed**: every scope consists of distinct indices $<n$ and every table has $2^d$ entries;
--   2. **$k$-uniform**: every scope has $k$ variables; **arity at most $k$**; **no empty scope**;
--   3. **scope-unique**: no two constraints share the same variable set (at most one predicate per scope, §4);
--   4. **complete of arity $k$**: well formed, $k$-uniform, scope-unique, and every $k$-subset $E\subseteq[n]$ is the scope of a constraint, so that each $E\in\binom{[n]}{k}$ carries exactly one predicate $P_E$ (pp.2, 9);
--   5. **rejects some pattern**: every table contains a $0$ (auxiliary instances, p.9);
--   6. **nontrivial**: every table contains a $0$ and a $1$ (pp.2, 9).
--
--   An algorithm's output, a list of bits $Y$, is read as the assignment $x_i = Y_i$ (with $0$ past the end).
--
--   These are the inputs of every algorithm of the mission: complete instances (§§1–3, 5), instances with at most one predicate per scope (§4), and CSPs of bounded arity (Lemma 3.6).
--
--   **Formalization Note** One raw type serves all sections so that machines can read it; malformed inputs are representable and may receive any output. Variable order inside a scope is irrelevant: the table is read through the same order.
-- source:
--   Cai, Jiang, Liu, Accepting Subcubes and the Approximability of Complete Boolean Min-CSPs, STOC 2027 submission (manuscript sha256 66626baf…), §2, p.9 (instances), p.2 (completeness), §4 p.15 (at most one predicate per k-scope), Lemma 3.6 p.14 (arity at most k, no empty scopes)

import Mathlib

namespace AcceptSubcube

/-- **Raw Boolean CSP instance** (input of every algorithm of the mission).

Cai, Jiang, Liu, *Accepting Subcubes and the Approximability of Complete Boolean Min-CSPs*,
STOC 2027 submission (manuscript sha256 66626baf…), §2, p.9: "An input on [n] has exactly one
unweighted predicate P_E : {0,1}^E → {0,1} for each E ∈ ([n] choose k)"; §4, p.15 ("at most one
unweighted predicate per k-scope"); Lemma 3.6, p.14 ("an unweighted Boolean CSP of arity at most
k").

`n` is the number of variables `0, …, n−1`; each constraint is a pair (scope, truth table): the
scope is a list of variable indices, and the table lists the predicate's value on every local
pattern, the pattern `y` being stored at index `Σ_i 2^i·y_i` (`patIdx`).

**Formalization Note.** One raw type serves all sections; the structural requirements of each
section (complete, at most one predicate per scope, arity bounds, nontrivial predicates) are the
separate predicates below, so that malformed inputs are representable (an algorithm may give them
any output). The order of the variables inside a scope is irrelevant to every notion of the mission
(the table is read through the same order). -/
structure GInst where
  /-- number of variables -/
  n : ℕ
  /-- constraints: scope (variable indices) and truth table -/
  cons : List (List ℕ × List Bool)

/-- Index of a local pattern `y = (y_0, …, y_{d−1})` in a truth table: `Σ_i 2^i·y_i`. -/
def patIdx : List Bool → ℕ
  | [] => 0
  | b :: bs => (if b then 1 else 0) + 2 * patIdx bs

/-- Value of the predicate of constraint `c = (scope, table)` under an assignment `x` of the
variables (`false` if the table is too short, which never happens for well-formed instances). -/
def evalTab (c : List ℕ × List Bool) (x : ℕ → Bool) : Bool :=
  c.2.getD (patIdx (c.1.map x)) false

/-- An assignment `x : Fin n → Bool` read on all of `ℕ` (`false` outside `[n]`). -/
def extA {n : ℕ} (x : Fin n → Bool) : ℕ → Bool :=
  fun v => if h : v < n then x ⟨v, h⟩ else false

/-- An algorithm's output list `Y` read as an assignment of `I` (`Y_i`, `false` past the end). -/
def asg (I : GInst) (Y : List Bool) : Fin I.n → Bool :=
  fun i => Y.getD i false

namespace GInst

/-- Every scope consists of distinct variables `< n`, and every table has `2^{|scope|}` entries. -/
def WellFormed (I : GInst) : Prop :=
  ∀ c ∈ I.cons, (∀ v ∈ c.1, v < I.n) ∧ c.1.Nodup ∧ c.2.length = 2 ^ c.1.length

/-- Every scope has exactly `k` variables. -/
def Uniform (k : ℕ) (I : GInst) : Prop :=
  ∀ c ∈ I.cons, c.1.length = k

/-- Every scope has at most `k` variables (Lemma 3.6, "arity at most k"). -/
def MaxArity (k : ℕ) (I : GInst) : Prop :=
  ∀ c ∈ I.cons, c.1.length ≤ k

/-- No scope is empty (Lemma 3.6, "no empty scopes"). -/
def NoEmptyScope (I : GInst) : Prop :=
  ∀ c ∈ I.cons, c.1 ≠ []

/-- At most one predicate per variable set (§4, p.15: "at most one unweighted predicate per
k-scope"). -/
def ScopeUnique (I : GInst) : Prop :=
  I.cons.Pairwise (fun c d => c.1.toFinset ≠ d.1.toFinset)

/-- **Complete `k`-CSP** (p.2, p.9): well formed, `k`-uniform, one predicate per scope, and every
`k`-subset of `[n]` is the scope of a constraint. (For auxiliary instances "completeness refers to
scope coverage", p.9; predicates are restricted separately by `RejectsSome`/`Nontrivial`.) -/
def IsComplete (k : ℕ) (I : GInst) : Prop :=
  I.WellFormed ∧ I.Uniform k ∧ I.ScopeUnique ∧
    ∀ E : Finset ℕ, E ⊆ Finset.range I.n → E.card = k → ∃ c ∈ I.cons, c.1.toFinset = E

/-- Every predicate rejects at least one pattern (p.9, p.11). -/
def RejectsSome (I : GInst) : Prop :=
  ∀ c ∈ I.cons, false ∈ c.2

/-- Every predicate is nontrivial: it accepts and rejects at least one pattern (p.2, p.9). For a
well-formed instance every table entry is the value at some pattern. -/
def Nontrivial (I : GInst) : Prop :=
  ∀ c ∈ I.cons, true ∈ c.2 ∧ false ∈ c.2

end GInst

end AcceptSubcube


