-- Prove2me | Definitions.Def_RefWPHP_Supplement_ontoPhpCNF
-- name    : RefWPHP_Supplement_ontoPhpCNF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T22:19:59.966278+00:00
-- url     : https://prove2.me/theorems/d8e08167-fc37-4c27-8a51-96ac665df47e
-- title:
--   The onto pigeonhole formulas $\mathrm{ontoPHP}^M_N$ as a set of cedents
-- statement:
--   For $M, N \in \mathbb N$, the formula $\mathrm{ontoPHP}^M_N$ has the variables $p_{i,j}$, $i \in [M]$ (pigeons), $j \in [N]$ (holes), and consists of the clauses of $\mathrm{PHP}^M_N$,
--
--   1. (PHP-1) $\bigvee_{j \in [N]} p_{i,j}$ for every $i \in [M]$,
--   2. (PHP-2) $\neg p_{i,j} \vee \neg p_{i',j}$ for all $i \ne i'$ and $j \in [N]$,
--
--   together with the **onto axioms**
--
--   $$
--   \text{(PHP-3)}\qquad \bigvee_{i \in [M]} p_{i,j} \qquad \text{for every } j \in [N].
--   $$
--
--   It states that a map from $M$ pigeons to $N$ holes is total, injective and surjective, and is the target of the paper's reduction in $\mathrm{Res}(k)$ (Theorem 3.6) and of Hypothesis 1.9.
--
--   **Formalization Note** The clauses (PHP-1) and (PHP-2) are the base mission's `phpCNF M N`. Each clause is the cedent of its literals (depth 0); pigeons and holes are 0-based.
-- source:
--   Arteche, Resolution Lower Bounds versus the Weak Pigeonhole Principle, STOC 2027 submission (held manuscript, sha256 ee75d7f1…), §3, (PHP-1)–(PHP-3), p.19 (PDF p.21)

import Mathlib
import Definitions.Def_RefWPHP_phpCNF

namespace RefWPHP

namespace Supplement

open PKFormula

/-- The onto pigeonhole formulas `ontoPHP^M_N` of N. Arteche, *Resolution Lower Bounds versus the
Weak Pigeonhole Principle*, STOC 2027 submission (held manuscript, sha256 ee75d7f1…), §3, p.19
(PDF 21): the clauses (PHP-1) and (PHP-2) of `PHP^M_N` (the base mission's `phpCNF M N`) together
with the onto axioms

* (PHP-3) `⋁_{i ∈ [M]} p_{i,j}` for every `j ∈ [N]`,

as a set of cedents over the variables `p_{i,j} = (i, j)`.

**Formalization Note.** Each onto axiom is the cedent of its literals, so it has depth 0, as in
the base `phpCNF`. Pigeons and holes are 0-based. -/
def ontoPhpCNF (M N : ℕ) : Set (Cedent (Fin M × Fin N)) :=
  phpCNF M N ∪ {Γ | ∃ j : Fin N, Γ = (List.finRange M).map fun i => pos (i, j)}

end Supplement

end RefWPHP


