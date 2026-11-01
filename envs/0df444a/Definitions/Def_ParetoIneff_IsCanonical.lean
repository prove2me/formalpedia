-- Prove2me | Definitions.Def_ParetoIneff_IsCanonical
-- name    : ParetoIneff_IsCanonical
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:23:58.368383+00:00
-- url     : https://prove2.me/theorems/7182327f-a983-4a29-bd62-58f9d9bc4c6c
-- title:
--   Canonical cost vector
-- statement:
--   A true cost vector for one task is **canonical** if it is a permutation of $(1,\alpha,\infty,\dots,\infty)$: a unique *fast* machine has cost $1$, a unique *slow* machine has cost $\alpha$, and each of the remaining *dummy* machines carries one of the high pairwise distinct values.
--
--   For $\alpha>1$ a canonical vector has no ties, so anonymity applies to it. That is the point of the construction.
--
--   **Formalization Note** All canonical vectors share one dummy list, so any two are permutations of each other, as the proof of Claim 4 uses.
-- source:
--   Filos-Ratsikas, Giannakopoulos, Lazos, The Pareto frontier of inefficiency in mechanism design, arXiv:1809.03454v7 (24 Feb 2021), https://arxiv.org/abs/1809.03454v7, proof of Theorem 6, p.13

import Mathlib

open NNReal

namespace ParetoIneff

/-- A **canonical** true cost vector for a task, arXiv:1809.03454v7, p.13: a permutation of
`(1, α, ∞, …, ∞)`. Machine `fast` has cost `1`, machine `slow ≠ fast` has cost `α`, and the other
`n − 2` machines (the **dummy** machines) carry the dummy processing times `d`, each exactly once.

**Formalization Note** All canonical vectors share the one dummy list `d`, so any two canonical
vectors are permutations of each other, as the proof of Claim 4 (p.14) uses. When `d` is an
`IsDummyList` and `α > 1`, the machines with cost `1` and `α` are unique and the vector has no
ties. The bijection `e` matches the dummy values to the machines other than `fast` and `slow`. -/
def IsCanonical {n : ℕ} (α : ℝ) (d : Fin (n - 2) → ℝ≥0) (v : Fin n → ℝ≥0) (fast slow : Fin n) :
    Prop :=
  fast ≠ slow ∧ v fast = 1 ∧ v slow = α.toNNReal ∧
    ∃ e : Fin (n - 2) ≃ {i : Fin n // i ≠ fast ∧ i ≠ slow}, ∀ k, v (e k) = d k

end ParetoIneff


