-- Prove2me | Definitions.Def_MonoTestDAG_HasExponents
-- name    : MonoTestDAG_HasExponents
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:09:27.612655+00:00
-- url     : https://prove2.me/theorems/eb834334-e2b9-412d-b8d7-1b0a6e6646e0
-- title:
--   Reachability exponents $(c,d)$ up to slack $\delta$
-- statement:
--   A DAG $G$ on $n$ vertices has reachability exponents $(c,d)$ up to slack $\delta$ if
--   $$
--   n^{c-\delta}\le m\le n^{c+\delta},\qquad n^{d-\delta}\le\ell\le n^{d+\delta}.
--   $$
--   This is the form in which the paper proves its lower bounds, and the uniform form of $m=n^{c+o(1)}$, $\ell=n^{d+o(1)}$.
--
--   **Formalization Note.** Exponents are real powers of $n$. At $n=0$ they vanish, so every statement using this predicate also bounds $n$ from below.
-- source:
--   Yoshida, Testing Monotonicity of Real-Valued Functions on DAGs, arXiv:2602.15341 (sha256 454609db…), Corollary 5.10, p.34 and proof of Theorem 1.1(ii), p.35

import Mathlib
import Definitions.Def_MonoTestDAG_numTC
import Definitions.Def_MonoTestDAG_numTR

namespace MonoTestDAG

/-- The DAG `G = (V, E)` has reachability exponents `(c, d)` up to the slack `δ`:
`n^{c−δ} ≤ m ≤ n^{c+δ}` and `n^{d−δ} ≤ ℓ ≤ n^{d+δ}`, with `n = |V|`, `m` the number of edges of
the transitive reduction and `ℓ` the number of edges of the transitive closure.

Yoshida, *Testing Monotonicity of Real-Valued Functions on DAGs*, arXiv:2602.15341
(sha256 454609db…), Corollary 5.10, p.34 and the proof of Theorem 1.1(ii), p.35.

**Formalization Note.** Exponents are `Real.rpow` on `(n : ℝ)`. This is the uniform form of the
`m = n^{c+o(1)}`, `ℓ = n^{d+o(1)}` of Theorem 1.1. At `n = 0` the powers vanish, so every statement
using this predicate also has a lower bound on `n`. -/
def HasExponents {V : Type} [Fintype V] (E : V → V → Prop) (c d δ : ℝ) : Prop :=
  (Fintype.card V : ℝ) ^ (c - δ) ≤ (numTR E : ℝ) ∧ (numTR E : ℝ) ≤ (Fintype.card V : ℝ) ^ (c + δ) ∧
  (Fintype.card V : ℝ) ^ (d - δ) ≤ (numTC E : ℝ) ∧ (numTC E : ℝ) ≤ (Fintype.card V : ℝ) ^ (d + δ)

end MonoTestDAG


