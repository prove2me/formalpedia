-- Prove2me | Definitions.Def_XOSMax_activeIndices
-- name    : XOSMax_activeIndices
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:23:40.80299+00:00
-- url     : https://prove2.me/theorems/59ce33db-fe38-40e8-8dea-4a57c13d002a
-- title:
--   The index set $I(X)$ of clauses attaining $f$ at $X$
-- statement:
--   Given a representation $w_1,\dots,w_k$ of $f$ and a set $X$, the index set of the clauses that attain the maximum at $X$ is
--   $$
--   I(X):=\{\,i\in[k]\ :\ f_i(X)=f(X)\,\},\qquad f_i(X)=\sum_{v\in X}w_i(v).
--   $$
--   The paper's analysis follows how $I$ shrinks as a set grows: this is how a clique is identified from oracle answers.
--
--   **Formalization Note** $I(X)$ depends on the representation as well as on $f$. The paper's $I(v)$ is `activeIndices w f {v}`.
-- source:
--   Filmus, Kawase, Kobayashi & Yamaguchi, Tight Approximation for Unconstrained XOS Maximization, arXiv:1811.09045v3, §2, p.3, "we define I(X)"

import Mathlib

namespace XOSMax

/-- The index set `I(X) := { i | fᵢ(X) = f(X) }` of the clauses attaining `f` at `X`
(Filmus, Kawase, Kobayashi & Yamaguchi, arXiv:1811.09045v3, §2, p.3, "we define I(X)").

**Formalization Note** `I(X)` depends on the representation `w` as well as on `f`. The paper's
`I(v)` is `activeIndices w f {v}`. -/
noncomputable def activeIndices {E : Type} {k : ℕ} (w : Fin k → E → ℝ) (f : Finset E → ℝ)
    (X : Finset E) : Finset (Fin k) :=
  Finset.univ.filter fun i => ∑ v ∈ X, w i v = f X

end XOSMax


