-- Prove2me | Definitions.Def_RQCMoments_christoffel
-- name    : RQCMoments_christoffel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T04:08:12.928068+00:00
-- url     : https://prove2.me/theorems/e55fc912-86cb-41af-a03d-c14d68365242
-- title:
--   Christoffel function $\lambda_{\nu,\ell}$
-- statement:
--   Let $\nu$ be a finite measure on $\mathbb R$ and $\ell\ge 1$ an integer. The **Christoffel function** of $\nu$ with index $\ell$ is
--   $$
--   \lambda_{\nu,\ell}(x)=\min_{\deg p\le \ell-1,\ p(x)=1}\ \int_{\mathbb R} p(t)^2\,d\nu(t),\qquad x\in\mathbb R,
--   $$
--   the minimum taken over real polynomials. The index $\ell$ is the number of quadrature nodes, so the admissible polynomials have degree at most $\ell-1$.
--
--   This variational quantity equals the Gauss weight at a node (Lemma 4.1) and has the closed form $1/\sum_{j<\ell}q_j(x)^2$ (Lemma 4.2); comparison of measures transfers upper bounds on it.
--
--   **Formalization Note** The minimum is written as an infimum over the admissible values; it is attained (Lemma 4.2). Only polynomials with $\nu$-integrable square are admissible, so no junk integral $0$ enters; for a finite measure $p\equiv 1$ is admissible, so the set is nonempty and bounded below by $0$. Statements use $\ell\ge 1$.
-- source:
--   S.-H. Hung, Random Quantum Circuits Beyond Moment Matching, arXiv:2610.02135 (held version, sha256 079e7da3…), (52) and the convention below it, pp.21–22 (PDF pp.23–24)

import Mathlib

set_option autoImplicit false

open MeasureTheory

namespace RQCMoments

/-- The Christoffel function (Hung, *Random Quantum Circuits Beyond Moment Matching*, arXiv:2610.02135 (held version, sha256 079e7da3…), (52), p.21, and the convention on p.22):
`λ_{ν,ℓ}(x) = min { ∫ p(t)² dν(t) : deg p ≤ ℓ − 1, p(x) = 1 }`.

**Formalization Note** Polynomials are real. The minimum is written as an infimum (`sInf`) over
the admissible values; the paper shows it is attained (Lemma 4.2). Only polynomials with
`ν`-integrable square are admissible, so a non-integrable `p²` never contributes Lean's junk
integral `0`; for a finite measure `p ≡ 1` is admissible, so the set is nonempty and bounded
below by `0`. The index `ℓ` is the number of quadrature nodes; statements use `ℓ ≥ 1` (for
`ℓ = 0` the natural-number subtraction `ℓ − 1 = 0` would admit constants). -/
noncomputable def christoffel (ν : Measure ℝ) (ℓ : ℕ) (x : ℝ) : ℝ :=
  sInf {r : ℝ | ∃ p : Polynomial ℝ, p.natDegree ≤ ℓ - 1 ∧ p.eval x = 1 ∧
    Integrable (fun t => (p.eval t) ^ 2) ν ∧ r = ∫ t, (p.eval t) ^ 2 ∂ν}

end RQCMoments


