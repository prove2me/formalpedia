-- Prove2me | Definitions.Def_GeoSemialgCSP_alphaStar
-- name    : GeoSemialgCSP_alphaStar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:47:37.941358+00:00
-- url     : https://prove2.me/theorems/c52a73ac-f8e4-44e3-b567-20739f88beb9
-- title:
--   Best biased random assignment value $\alpha^*_P$
-- statement:
--   Let $X\subseteq\mathbb R^d$ and let $P$ be a $k$-ary predicate. The value of the **best biased random assignment** is
--   $$\alpha^*_P=\sup_\mu\ \mathbb E_{(X_1,\dots,X_k)\sim\mu^{\otimes k}}\bigl[P(X_1,\dots,X_k)\bigr],$$
--   the supremum over all finitely supported probability distributions $\mu$ on $X$, with $X_1,\dots,X_k$ independent with law $\mu$.
--
--   It is the benchmark of approximation resistance: an assignment drawn independently from $\mu$ at every variable achieves $\alpha^*_P$ in expectation on every instance.
--
--   **Formalization Note** $\mu$ is given by atoms $x_1,\dots,x_n\in X$ and a probability vector $w$; repeated atoms are allowed. The supremum is a real `sSup`; the set is bounded by $1$ and nonempty when $X\ne\emptyset$ (the value is $0$ only when $X=\emptyset$).
-- source:
--   Arvanitakis, Chatziafratis, Makarychev, Hardness of Approximation for Semialgebraic CSPs, manuscript (STOC 2027 submission, held version sha256 ee702c42…), §3 Setup, p.7 (PDF p.8)

import Mathlib
import Definitions.Def_GeoSemialgCSP_E
import Definitions.Def_GeoSemialgCSP_multilin

namespace GeoSemialgCSP

/-- **Value of the best biased random assignment.** Arvanitakis, Chatziafratis, Makarychev, *Hardness of Approximation for Semialgebraic CSPs*,
manuscript (STOC 2027 submission, held version sha256 ee702c42…), §3 Setup, printed p.7 (PDF p.8):
`α*_P = sup_μ E_{(X₁,…,X_k) ∼ μ^{⊗k}} P(X₁, …, X_k)`, the supremum over all finitely supported
probability distributions `μ` on `X`.

**Formalization Note.** A finitely supported `μ` is given by atoms `x : Fin n → X` and masses
`w ∈ stdSimplex ℝ (Fin n)`; repeated atoms are allowed and change nothing. The expectation is the
multilinear extension of `a ↦ 1_S(x ∘ a)` at `(w, …, w)`. The set of values is bounded by `1`, and
nonempty when `X` is nonempty, so the real `sSup` is the supremum (it would be `0` only for
`X = ∅`). -/
noncomputable def alphaStar {k d : ℕ} (X : Set (E d)) (S : Set (Fin k → E d)) : ℝ :=
  sSup {v : ℝ | ∃ (n : ℕ) (x : Fin n → E d) (w : Fin n → ℝ), (∀ i, x i ∈ X) ∧
    w ∈ stdSimplex ℝ (Fin n) ∧ v = multilin (fun a => S.indicator 1 (x ∘ a)) (fun _ => w)}

end GeoSemialgCSP


