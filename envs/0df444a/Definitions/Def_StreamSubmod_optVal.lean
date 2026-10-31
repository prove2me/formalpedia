-- Prove2me | Definitions.Def_StreamSubmod_optVal
-- name    : StreamSubmod_optVal
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:25:13.178762+00:00
-- url     : https://prove2.me/theorems/e5f221f1-0272-44ba-9cc1-a5b8874fb5fe
-- title:
--   The optimal value $f(\mathrm{OPT})$ under a cardinality constraint
-- statement:
--   Let $V$ be a finite ground set, $f:2^V\to\mathbb R$ a set function and $k$ a natural number. The optimal value of the problem of maximizing $f$ subject to the cardinality constraint $k$ is
--
--   $$
--   f(\mathrm{OPT})=\max\{f(S): S\subseteq V,\ |S|\le k\}.
--   $$
--
--   Every statement of this development compares the value of an algorithm's output with this number.
--
--   **Formalization Note** The ground set is a `Fintype`, and the maximum is a finite one over a nonempty family, since the empty set is always feasible.
-- source:
--   Alaluf, Ene, Feldman, Nguyen & Suh, An Optimal Streaming Algorithm for Submodular Maximization with a Cardinality Constraint, arXiv:1911.12959v3, §2, p.5 (the problem), and Theorem 1, p.14

import Mathlib

namespace StreamSubmod

/-- The optimal value `f(OPT) = max {f(S) : S ⊆ V, |S| ≤ k}` of the problem of maximizing a set
function subject to a cardinality constraint (Alaluf, Ene, Feldman, Nguyen & Suh, An Optimal
Streaming Algorithm for Submodular Maximization with a Cardinality Constraint, arXiv:1911.12959v3,
§2, p.5, and Theorem 1, p.14).

**Formalization Note.** The ground set `V` is the `Fintype` `E`, subsets are `Finset E`. The maximum
is a finite one, taken over the nonempty family of feasible sets (`∅` is always feasible), so no
junk value of a real supremum can occur. -/
noncomputable def optVal {E : Type} [Fintype E] (f : Finset E → ℝ) (k : ℕ) : ℝ :=
  (Finset.univ.filter fun S : Finset E => S.card ≤ k).sup' ⟨∅, by simp⟩ f

end StreamSubmod


