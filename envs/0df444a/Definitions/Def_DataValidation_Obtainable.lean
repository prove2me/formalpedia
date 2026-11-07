-- Prove2me | Definitions.Def_DataValidation_Obtainable
-- name    : DataValidation_Obtainable
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:46:22.997793+00:00
-- url     : https://prove2.me/theorems/a0a9dc29-7773-4066-9a94-a2848f5ab6a1
-- title:
--   Obtainable edge sets
-- statement:
--   A set $R\subseteq E$ is **obtainable** if its elements can be ordered $e_1,\dots,e_k$ so that $e_1\in R(E)$ and
--
--   $$e_t\in R(E\setminus\{e_1,\dots,e_{t-1}\})\qquad\text{for every }t\in\{2,\dots,k\}.$$
--
--   The empty set is obtainable. Obtainability is the static criterion for a set of edges to be removable by some probing policy.
--
--   **Formalization Note** The order is a duplicate-free list, and membership in the transitive reductions forces $R\subseteq E$.
-- source:
--   Tinguely, van der Heijden, Approximation and Hardness for the Data Validation Problem, arXiv:2611.06773 (sha256 6595f819…), §3, p.6

import Definitions.Def_DataValidation_transReduction

set_option autoImplicit false

namespace DataValidation

/-- `R` is **obtainable** from `E`: its elements can be ordered `e₁, …, e_k` so that
`e₁ ∈ R(E)` and `e_t ∈ R(E ∖ {e₁, …, e_{t-1}})` for every `t ∈ {2, …, k}`. arXiv:2611.06773
(sha256 6595f819…), §3, p.6.

**Formalization Note.** The order is a duplicate-free list `l`; `l.take i` holds the edges before
position `i`, and `i = 0` is the page's condition `e₁ ∈ R(E)`. Membership in the transitive reduction
forces `R ⊆ E`. The empty set is obtainable. -/
def Obtainable {V : Type*} [DecidableEq V] (E R : Finset (V × V)) : Prop :=
  ∃ l : List (V × V), l.Nodup ∧ l.toFinset = R ∧
    ∀ (i : ℕ) (hi : i < l.length), l[i] ∈ transReduction (E \ (l.take i).toFinset)

end DataValidation


