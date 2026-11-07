-- Prove2me | Definitions.Def_CorrelatedLocalSearch_Clause
-- name    : CorrelatedLocalSearch_Clause
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:37:37.85144+00:00
-- url     : https://prove2.me/theorems/ada0f017-072b-4e5a-a9cd-b8b5ed9971f5
-- title:
--   $k$-CNF clauses with ordered literals, satisfaction and strong witnesses
-- statement:
--   A **clause** of a $k$-CNF on $n$ variables is an ordered tuple of $k$ literals $(\ell_0,\dots,\ell_{k-1})$ on $k$ distinct variables; the literal $\ell_i=(v_i,b_i)$ is true under an assignment $x\in\{0,1\}^n$ when $x_{v_i}=b_i$. A clause is **violated** by $x$ when all $k$ of its literals are false. A formula $\Phi$ is a finite list of clauses, satisfied by $x$ when no clause of $\Phi$ is violated. For an integer $r$, an assignment $x^*$ is a **strong witness** of $\Phi$ when it makes at least $r$ literals true in every clause:
--   $$
--   \#\{i : x^*_{v_i}=b_i\}\ \ge\ r\quad\text{for every clause of }\Phi .
--   $$
--   A formula with a strong witness is **strongly $r$-satisfiable**.
--
--   The fixed order of the literals matters: the walk of Theorem 4.1 flips the variable of the literal whose position is the next source symbol.
--
--   **Formalization Note** A clause is a map $\mathrm{Fin}\,k\to\mathrm{Fin}\,n\times\mathrm{Bool}$ with injective variable component; a formula is a `List` of clauses (repetition and overlap allowed). True literals are counted by position with `Set.ncard`.
-- source:
--   Xu, Local Search with Correlated Randomness, arXiv:2607.17469 (sha256 17e00d69…), §4 'The promise and the walk', p.9 (PDF p.11)

import Mathlib

set_option autoImplicit false

namespace CorrelatedLocalSearch

/-- A clause of a `k`-CNF on `n` variables with a fixed ordering of its literals
(Xu, *Local Search with Correlated Randomness*, arXiv:2607.17469 (sha256 17e00d69…), §4
"The promise and the walk", p.9): `lit i = (v, b)` is the `i`-th literal, on variable `v`,
true under an assignment `x` exactly when `x v = b`. "Clauses use `k` distinct variables":
the variable map is injective.

**Formalization Note** The order of `Fin k` is the paper's "fixed ordering of its literals",
which the source symbol indexes. -/
structure Clause (k n : ℕ) where
  /-- The `i`-th literal: its variable and its sign (`true` = positive literal). -/
  lit : Fin k → Fin n × Bool
  /-- The `k` literals use `k` distinct variables. -/
  inj : Function.Injective (fun i => (lit i).1)

/-- A clause is violated by `x` when all `k` of its literals are false under `x`. -/
def Clause.Violated {k n : ℕ} (C : Clause k n) (x : Fin n → Bool) : Prop :=
  ∀ i : Fin k, x (C.lit i).1 ≠ (C.lit i).2

/-- The formula `Φ` (a finite list of clauses) is satisfied by `x` when no clause of `Φ` is
violated by `x`.

**Formalization Note** A formula is a `List` of clauses; repeated or overlapping clauses are
allowed ("there is no restriction on clause overlap", p.9). -/
def Satisfies {k n : ℕ} (Φ : List (Clause k n)) (x : Fin n → Bool) : Prop :=
  ∀ C ∈ Φ, ¬ C.Violated x

/-- `x∗` is a strong witness of the `k`-CNF `Φ` for the parameter `r`: it makes at least `r`
literals true in each clause (Xu, arXiv:2607.17469 (sha256 17e00d69…), §4, p.9: "A `k`-CNF is
strongly `r`-satisfiable if some assignment `x∗` makes at least `r` literals true in each
clause … We call such an `x∗` a strong witness").

**Formalization Note** Literals are counted by position `i : Fin k`; since variables are
distinct, this is the number of true literals. -/
def IsStrongWitness {k n : ℕ} (r : ℕ) (Φ : List (Clause k n)) (xs : Fin n → Bool) : Prop :=
  ∀ C ∈ Φ, r ≤ Set.ncard {i : Fin k | xs (C.lit i).1 = (C.lit i).2}

end CorrelatedLocalSearch


