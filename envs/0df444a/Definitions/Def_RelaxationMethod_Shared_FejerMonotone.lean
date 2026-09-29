-- Prove2me | Definitions.Def_RelaxationMethod_Shared_FejerMonotone
-- name    : RelaxationMethod_Shared_FejerMonotone
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T16:28:24.282043+00:00
-- url     : https://prove2.me/theorems/faa4ff01-dc3a-412d-bd7a-947e0f102a2c
-- title:
--   Fejér-monotone sequences (2.1)–(2.2)
-- statement:
--   Let $A$ be a set of points of $E_n$. An infinite sequence $q_0, q_1, q_2, \dots$ of points outside $A$ is **Fejér-monotone with respect to $A$** if consecutive points are distinct and the sequence approaches $A$ point-wise:
--   $$q_\nu \neq q_{\nu+1}, \qquad |q_\nu - a| \geqslant |q_{\nu+1} - a| \quad \text{for all } a \in A,\ \nu = 0, 1, \dots$$
--
--   Every infinite run of the relaxation method with $0 < \lambda \leqslant 2$ is Fejér-monotone with respect to the solution polytope, and Lemma 1 describes the limiting behaviour of all such sequences.
--
--   It serves chunk 02-low-dim (Motzkin–Schoenberg p. 397, §4, (2.1)–(2.2); used by Lemma 1, Case 2, p. 397, and by the Fejér-monotonicity of infinite relaxation runs, §1 pp. 393–394 and §5 p. 398) and chunk 03-convex-domain (p. 397, §4, (2.1)–(2.2); used by Lemma 1, Case 1, p. 397, and by the Fejér-monotonicity of the reflexion process with respect to a closed bounded convex set, §10, p. 403).
--
--   **Formalization Note** The set $A$ is an arbitrary set of `EuclideanSpace ℝ (Fin n)`; the paper states the notion for the polytope (1.4) and applies it in §10 to a closed bounded convex set. The condition "outside $A$" is part of the definition. Condition (2.2) is non-strict, as on the printed page.
-- source:
--   Motzkin and Schoenberg, The relaxation method for linear inequalities, Canad. J. Math. 6 (1954), DOI 10.4153/CJM-1954-038-x, p. 397, §4, (2.1)–(2.2)

import Mathlib

namespace RelaxationMethod.Shared

/-- A sequence `q_0, q_1, …` is **Fejér-monotone** with respect to a set `A` (§4, p. 397):
every `q_ν` lies outside `A`, consecutive points are distinct (2.1), and the distance to every
point of `A` is non-increasing, `|q_ν - a| ⩾ |q_{ν+1} - a|` for all `a ∈ A` (2.2). -/
def IsFejerMonotone {n : ℕ} (A : Set (EuclideanSpace ℝ (Fin n)))
    (q : ℕ → EuclideanSpace ℝ (Fin n)) : Prop :=
  (∀ ν, q ν ∉ A) ∧ (∀ ν, q ν ≠ q (ν + 1)) ∧
    ∀ a ∈ A, ∀ ν, dist (q (ν + 1)) a ≤ dist (q ν) a

end RelaxationMethod.Shared


