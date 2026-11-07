-- Prove2me | Definitions.Def_ApproxDegComp_levelMat
-- name    : ApproxDegComp_levelMat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:31:01.106482+00:00
-- url     : https://prove2.me/theorems/8756256a-2b0f-4e51-ad8a-ece082aa7edd
-- title:
--   The matrix $A=\sum_{k=0}^m\min\{k,d\}\,E_k$
-- statement:
--   Given matrices $E_0,\dots,E_m$ on $\mathbb R^{\mathcal X}$ and $d\in\mathbb N$, put $\tau_k=\min\{k,d\}$ and
--
--   $$A=\sum_{k=0}^m\tau_kE_k .$$
--
--   When the $E_k$ are orthogonal projectors summing to the identity (as in Lemma 20), $A$ is real symmetric with eigenvalues among $\tau_0,\dots,\tau_m$.
--
--   **Formalization Note** The projector properties are hypotheses of the statements that use $A$, not part of the definition.
-- source:
--   Pednekar–Podder, On the Composition Theorem for Approximate Degree, Randomized and Exact Quantum Query Complexity, STOC 2027 submission (manuscript sha256 b9a66c7fdb2afdb57851f3734661cd2140455987b17e2a1e2400586be814092b), Lemma 20, p.22

import Mathlib

namespace ApproxDegComp

/-- **The matrix** `A = Σ_{k=0}^m τ_k E_k` **with** `τ_k = min{k, d}` (Lemma 20, p.22).
Pednekar–Podder, *On the Composition Theorem for Approximate Degree, Randomized and Exact
Quantum Query Complexity*, STOC 2027 submission (manuscript sha256 b9a66c7f…), Lemma 20, p.22: "a real symmetric matrix A = Σ_{k=0}^m τ_k E_k where τ_k = min{k, d}".

`levelMat E d` is the combination of the matrices `E 0, …, E m` on `ℝ^X` with the weights
`min{k, d}`.

**Formalization Note** The index `k` runs over `Fin (m+1) = {0, …, m}`; that the `E_k` are
orthogonal projectors is a hypothesis of each statement, not part of this definition. -/
def levelMat {m : ℕ} {X : Type} [Fintype X] (E : Fin (m + 1) → Matrix X X ℝ) (d : ℕ) :
    Matrix X X ℝ :=
  ∑ k : Fin (m + 1), ((min (k : ℕ) d : ℕ) : ℝ) • E k

end ApproxDegComp


