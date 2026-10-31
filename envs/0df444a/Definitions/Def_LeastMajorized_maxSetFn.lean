-- Prove2me | Definitions.Def_LeastMajorized_maxSetFn
-- name    : LeastMajorized_maxSetFn
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:47:37.5918+00:00
-- url     : https://prove2.me/theorems/dbb0a613-7692-4e98-a606-5c40eb854091
-- title:
--   The set function $f(A)=\max_{x\in C}x(A)$ of a set $C$
-- statement:
--   For a set $C\subseteq\mathbb R^n$ define the set function
--
--   $$
--   f_C(A):=\max_{x\in C}\,x(A),\qquad A\in 2^N .
--   $$
--
--   Lemma 15 shows that $f_C$ is submodular under a nested-sum condition, and Theorem 5 characterizes when $C=B(f_C)$.
--
--   **Formalization Note** The maximum is the real supremum `sSup` of $\{x(A)\mid x\in C\}$. For nonempty compact $C$ (the only case in which the statements of the mission are non-vacuous) the supremum is attained and equals the paper's maximum. For $C=\emptyset$ Lean's value is $\sup\emptyset=0$; the paper's maximum is undefined there, and every statement that uses $f_C$ is false or vacuous for $C=\emptyset$ regardless of this value.
-- source:
--   Schoot Uiterkamp, A characterization of simultaneous optimization, majorization, and (bi)submodular polyhedra, arXiv:2201.06596v2, Lemma 15, p.16; Theorem 5, p.18

import Mathlib

namespace LeastMajorized

/-- **The set function of a set `C`**, Schoot Uiterkamp, arXiv:2201.06596v2, Lemma 15, p.16 and
Theorem 5, p.18: `f(A) := max_{x∈C} x(A)` for `A ∈ 2^N`, where `x(A) = Σ_{i∈A} xᵢ`.

**Formalization Note** The maximum is `sSup` of the real set `{x(A) | x ∈ C}`. For a nonempty
compact `C` (Theorem 5) or a nonempty closed bounded `C` (Lemma 15, whose hypothesis forces
`C ≠ ∅`), this set is nonempty, compact and its supremum is attained, so `sSup` is the paper's
maximum. For `C = ∅` the value is Lean's junk `sSup ∅ = 0`; the paper's max is undefined there,
and every statement of the mission is false or vacuous for `C = ∅` independently of this value
(see the mission's notes). -/
noncomputable def maxSetFn {n : ℕ} (C : Set (Fin n → ℝ)) (A : Finset (Fin n)) : ℝ :=
  sSup ((fun x : Fin n → ℝ => ∑ i ∈ A, x i) '' C)

end LeastMajorized


