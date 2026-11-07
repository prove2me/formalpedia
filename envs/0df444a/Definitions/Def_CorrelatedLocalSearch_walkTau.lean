-- Prove2me | Definitions.Def_CorrelatedLocalSearch_walkTau
-- name    : CorrelatedLocalSearch_walkTau
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:38:28.166005+00:00
-- url     : https://prove2.me/theorems/feb50acb-595c-42a7-a74c-cb629b3fe9f7
-- title:
--   The promise-SAT walk driven by a tape and its flip count $\tau$
-- statement:
--   Fix a $k$-CNF $\Phi$ on $n$ variables, an initial assignment $x_0$ and a **clause selector**: a deterministic rule that, before step $t$, sees the prefix $\omega\!\restriction\!t$ of the tape read so far (and hence the current assignment) and returns a clause. The selector is **valid** for $\Phi$ when, on every assignment that does not satisfy $\Phi$, it returns a clause of $\Phi$ violated by that assignment.
--
--   The walk sets $x_0$ as given and, at step $t$: if $x_t$ satisfies $\Phi$ the walk has stopped and $x_{t+1}=x_t$; otherwise it takes the clause $C$ chosen by the selector and flips the variable of the literal of $C$ at position $\omega_t$. The flip count is
--   $$
--   \tau(\omega)=\min\{t\ge 0 : x_t \text{ satisfies } \Phi\}\in\mathbb N\cup\{\infty\},
--   $$
--   with $\tau=\infty$ when the walk never satisfies $\Phi$.
--
--   This is the algorithm whose robustness Theorem 4.1 states.
--
--   **Formalization Note** The selector has type `List (Fin k) → (Fin n → Bool) → Clause k n`: a function of the prefix read so far, so it cannot anticipate, and it has no private randomness. Validity is required on every pair (prefix, assignment); this loses no selector, since an unsatisfying assignment always has a violated clause, so a selector valid on the histories the walk reaches can be redefined elsewhere without changing any run. $\tau$ takes values in `ℕ∞`.
-- source:
--   Xu, Local Search with Correlated Randomness, arXiv:2607.17469 (sha256 17e00d69…), §2 'Selectors, termination, and covers', pp.5–6, and §4 'The promise and the walk' and Theorem 4.1, p.9 (PDF pp.7–8, 11)

import Mathlib
import Definitions.Def_CorrelatedLocalSearch_SourceClass
import Definitions.Def_CorrelatedLocalSearch_Clause

set_option autoImplicit false

namespace CorrelatedLocalSearch

/-- A deterministic nonanticipating clause selector (Xu, *Local Search with Correlated
Randomness*, arXiv:2607.17469 (sha256 17e00d69…), §2 "Selectors, termination, and covers",
p.5, and §4, p.9): before step `t` it sees the tape prefix `ω↾t` read so far (which determines
the whole history) and the current assignment, and returns a clause.

**Formalization Note** The selector is a function of the prefix read so far, never of the
whole tape, so it cannot anticipate; it has no private randomness. The current assignment is a
redundant argument (it is a function of the prefix). -/
abbrev Selector (k n : ℕ) : Type := List (Fin k) → (Fin n → Bool) → Clause k n

/-- A selector is valid for `Φ` when, on every unsatisfying assignment, it returns a clause of
`Φ` that the assignment violates ("the algorithm chooses any violated clause", p.9).

**Formalization Note** Validity is required on every pair `(w, x)`, reachable or not. This
loses no selector: an unsatisfying `x` always has a violated clause in `Φ`, so a selector that
is valid on the histories the walk reaches can be redefined off them without changing any run. -/
def IsValidSelector {k n : ℕ} (Φ : List (Clause k n)) (sel : Selector k n) : Prop :=
  ∀ (w : List (Fin k)) (x : Fin n → Bool), ¬ Satisfies Φ x → sel w x ∈ Φ ∧ (sel w x).Violated x

/-- Flip variable `v` of the assignment `x`. -/
def flipVar {n : ℕ} (x : Fin n → Bool) (v : Fin n) : Fin n → Bool :=
  Function.update x v (!x v)

open Classical in
/-- One step of the walk after the prefix `pre`, at assignment `x`, on reading the symbol `a`:
if `x` satisfies `Φ` the walk has stopped; otherwise it flips the variable of the `a`-th literal
of the clause `sel pre x` (p.9: it "flips the variable indexed, under a fixed ordering of its
literals, by the next source symbol"). -/
noncomputable def walkStep {k n : ℕ} (Φ : List (Clause k n)) (sel : Selector k n)
    (pre : List (Fin k)) (x : Fin n → Bool) (a : Fin k) : Fin n → Bool :=
  if Satisfies Φ x then x else flipVar x ((sel pre x).lit a).1

/-- Run the walk from assignment `x` after the prefix `pre` on the symbols of `rest`. -/
noncomputable def walkRun {k n : ℕ} (Φ : List (Clause k n)) (sel : Selector k n) :
    List (Fin k) → (Fin n → Bool) → List (Fin k) → (Fin n → Bool)
  | _, x, [] => x
  | pre, x, a :: rest => walkRun Φ sel (pre ++ [a]) (walkStep Φ sel pre x a) rest

/-- The assignment `x_{|w|}` of the walk started at `x₀` after reading the word `w`. -/
noncomputable def walkState {k n : ℕ} (Φ : List (Clause k n)) (sel : Selector k n)
    (x₀ : Fin n → Bool) (w : List (Fin k)) : Fin n → Bool :=
  walkRun Φ sel [] x₀ w

/-- The number `τ` of variable flips of the promise-SAT walk until the formula is satisfied
(Xu, arXiv:2607.17469 (sha256 17e00d69…), Theorem 4.1, p.9: "τ counts variable flips until the
formula is satisfied"; §2, p.6: "the number of updates the algorithm makes"): the least `t`
such that the assignment after reading `ω↾t` satisfies `Φ`.

**Formalization Note** `τ` is valued in `ℕ∞`, with `τ = ⊤` when the walk never satisfies `Φ`
(the infimum of the empty set). One source symbol is read per flip. -/
noncomputable def walkTau {k n : ℕ} (Φ : List (Clause k n)) (sel : Selector k n)
    (x₀ : Fin n → Bool) (ω : ℕ → Fin k) : ℕ∞ :=
  ⨅ (t : ℕ) (_ : Satisfies Φ (walkState Φ sel x₀ (tapePrefix ω t))), (t : ℕ∞)

end CorrelatedLocalSearch


