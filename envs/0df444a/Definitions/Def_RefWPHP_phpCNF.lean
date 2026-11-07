-- Prove2me | Definitions.Def_RefWPHP_phpCNF
-- name    : RefWPHP_phpCNF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:02:04.490546+00:00
-- url     : https://prove2.me/theorems/dda6b44d-75c8-472b-afe9-d460d935a4e5
-- title:
--   The pigeonhole formulas $\mathrm{PHP}^M_N$ as a set of cedents
-- statement:
--   The **pigeonhole formula** $\mathrm{PHP}^M_N$ has the variables $p_{i,j}$ for pigeons $i \in [M]$ and holes $j \in [N]$, and the clauses
--
--   $$
--   \bigvee_{j\in[N]} p_{i,j} \quad (i\in[M]), \qquad\qquad \neg p_{i,j} \vee \neg p_{i',j} \quad (i, i'\in[M],\ i\ne i',\ j\in[N]).
--   $$
--
--   These are the totality axioms (PHP-1) and the injectivity axioms (PHP-2); together they falsely claim an injective map from $[M]$ to $[N]$. Theorem 3.2 produces refutations of this formula with $M = L$ and $N = \lfloor s/D\rfloor$.
--
--   **Formalization Note** Each clause is the cedent of its literals (p.15: a CNF is collected into a set of cedents), so every axiom has depth $0$. Pigeons and holes are $0$-based.
-- source:
--   Arteche, Resolution Lower Bounds versus the Weak Pigeonhole Principle, STOC 2027 submission (held manuscript, sha256 ee75d7f1…), §3, (PHP-1), (PHP-2), p.19 (PDF p.21)

import Mathlib
import Definitions.Def_RefWPHP_IsPKDerivation

namespace RefWPHP

open PKFormula

/-- The pigeonhole formulas PHP^M_N of N. Arteche, *Resolution Lower Bounds versus the Weak
Pigeonhole Principle*, STOC 2027 submission (held manuscript, sha256 ee75d7f1…), §3, p.19, as a set
of cedents over the variables `p_{i,j} = (i, j)`, `i ∈ [M]` (pigeons), `j ∈ [N]` (holes):

* (PHP-1) `⋁_{j ∈ [N]} p_{i,j}` for every `i ∈ [M]`;
* (PHP-2) `¬p_{i,j} ∨ ¬p_{i',j}` for all `i ≠ i'` and `j ∈ [N]`.

**Formalization Note.** Each clause is the cedent of its literals (p.15: a CNF is collected into
a set of cedents), so every axiom has depth 0. Pigeons and holes are 0-based (`Fin M`, `Fin N`).
-/
def phpCNF (M N : ℕ) : Set (Cedent (Fin M × Fin N)) :=
  {Γ | (∃ i : Fin M, Γ = (List.finRange N).map fun j => pos (i, j)) ∨
       (∃ (i i' : Fin M) (j : Fin N), i ≠ i' ∧ Γ = [neg (i, j), neg (i', j)])}

end RefWPHP


