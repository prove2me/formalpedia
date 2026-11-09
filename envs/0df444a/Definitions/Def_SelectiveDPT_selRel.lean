-- Prove2me | Definitions.Def_SelectiveDPT_selRel
-- name    : SelectiveDPT_selRel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:49:41.09481+00:00
-- url     : https://prove2.me/theorems/e7852ba6-cdd4-47f2-a83d-ed18a792baf5
-- title:
--   Selective direct product relation $R^{(k,m)}$
-- statement:
--   Let $R \subseteq X^\iota \times Y$ be a relation and $k, m \ge 0$. The **selective direct product relation** $R^{(k,m)}$ relates an $m$-copy input $(x_1, \dots, x_m)$ to a list $((i_1, y_1), \dots, (i_k, y_k))$ of (copy, answer) pairs if and only if
--
--   1. the copy indices $i_1, \dots, i_k \in [m]$ are pairwise distinct, and
--   2. $(x_{i_j}, y_j) \in R$ for every $j \in [k]$.
--
--   For a function $f$, $f^{(k,m)}$ is $R^{(k,m)}$ for the graph of $f$. The algorithm chooses the $k$ copies it answers after its queries; the other $m-k$ copies are not checked.
--
--   **Formalization Note** The paper writes "$i_1 \ne i_2 \ne \cdots \ne i_k$" and identifies the indices with a $k$-subset of $[m]$; the list is an ordered $k$-tuple with injective copy indices.
-- source:
--   Beame–Kornerup–Whitmeyer, Strong Selective and List-Decoding Direct Product Theorems for Quantum Query Complexity, arXiv:2609.26678, Definition 1.1, p.3; §2.2, p.10

import Mathlib
import Definitions.Def_SelectiveDPT_copy

namespace SelectiveDPT

/-- The selective direct product relation `R^(k,m)` (arXiv:2609.26678, Definition 1.1, p.3): given
a relation `R ⊆ X^n × Y`, `R^(k,m)` is the relation on `(X^n)^m × ([m] × Y)^k` with
`((x_1, …, x_m), ((i_1, y_1), …, (i_k, y_k))) ∈ R^(k,m)` iff `(x_{i_j}, y_j) ∈ R` for all `j ∈ [k]`
and `i_1 ≠ i_2 ≠ ⋯ ≠ i_k`. For a function `f`, `f^(k,m)` is `R^(k,m)` for the graph of `f`.

**Formalization Note.** "`i_1 ≠ i_2 ≠ ⋯ ≠ i_k`" is read as pairwise distinct (the indices form a
set `K ∈ ([m] choose k)`, §2.2, p.10): the output is an ordered `k`-tuple of (copy, answer) pairs
whose copy indices form an injective map `Fin k → Fin m`. The indices are part of the output, so
the algorithm chooses which copies to answer after its queries. Only the chosen copies are
checked. -/
def selRel {ι Y α : Type*} (k m : ℕ) (R : (ι → α) → Y → Prop) :
    (Fin m × ι → α) → (Fin k → Fin m × Y) → Prop :=
  fun x o => Function.Injective (fun j => (o j).1) ∧ ∀ j, R (copy x (o j).1) (o j).2

end SelectiveDPT


