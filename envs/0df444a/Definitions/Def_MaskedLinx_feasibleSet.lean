-- Prove2me | Definitions.Def_MaskedLinx_feasibleSet
-- name    : MaskedLinx_feasibleSet
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:39:21.3889+00:00
-- url     : https://prove2.me/theorems/2fd96e1d-ad89-4854-acf7-d7137dbbb895
-- title:
--   Feasible set $P(n,s)=\{x\in\mathbb R^n : e^\top x=s,\ 0\le x\le e\}$ of the linx relaxation
-- statement:
--   Let $N$ be a finite ground set of $n$ indices and let $s$ be a natural number. The feasible set of the linx relaxation is
--
--   $$P(n,s)=\{x\in\mathbb R^N : e^\top x=s,\ 0\le x\le e\},$$
--
--   where $e$ is the all-ones vector. It is the continuous relaxation of the set of indicator vectors of $s$-element subsets $S\subseteq N$, which are its vertices.
--
--   The set is nonempty exactly when $0\le s\le n$; for $0<s<n$ the uniform point $\tfrac{s}{n}e$ lies in its relative interior.
--
--   **Formalization Note** The ground set is an arbitrary finite type `ι` (the theorems use `Fin n`, or a subtype of `Fin n` for subproblems); `s` is a natural number cast to $\mathbb R$.
-- source:
--   Chen, Fampa, Lee, Masking Anstreicher's linx bound for improved entropy bounds, arXiv:2106.02980v1, §1, definition of P(n,s) after display (1), p.2

import Mathlib

namespace MaskedLinx

/-- **The feasible set `P(n,s)` of the linx relaxation.**
Chen, Fampa, Lee, *Masking Anstreicher's linx bound for improved entropy bounds*,
arXiv:2106.02980v1, §1, text after display (1), p.2:
"P(n,s) := {x ∈ ℝⁿ : e⊤x = s, 0 ≤ x ≤ e}".

`feasibleSet ι s` is the set of `x : ι → ℝ` with `∑ i, x i = s` and `0 ≤ x i ≤ 1` for every `i`.

**Formalization Note.** The ground set `N = {1, …, n}` is an arbitrary finite index type `ι`
(the milestones use `ι = Fin n`, 0-based, or a subtype of `Fin n` for the subproblems of
Theorem 2.8). The cardinality `s` is a natural number, cast to `ℝ`. -/
def feasibleSet (ι : Type*) [Fintype ι] (s : ℕ) : Set (ι → ℝ) :=
  {x | ∑ i, x i = (s : ℝ) ∧ ∀ i, 0 ≤ x i ∧ x i ≤ 1}

end MaskedLinx


