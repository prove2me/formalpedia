-- Prove2me | Definitions.Def_AvgCaseTI_hullProb
-- name    : AvgCaseTI_hullProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:42:19.284952+00:00
-- url     : https://prove2.me/theorems/95751185-1b1e-44f4-aaec-9cfb4fcd87cf
-- title:
--   Probability that a random $n$-dimensional matrix code has a one-dimensional hull
-- statement:
--   For a finite field $\mathbb F_q$, let $\mathcal A$ be a uniformly random $n$-dimensional subspace of $\mathrm M(n,q)$. Then
--   $$
--   \Pr[\dim H(\mathcal A)=1]=\frac{|\{\mathcal C\le\mathrm M(n,q):\dim\mathcal C=n,\ \dim H(\mathcal C)=1\}|}{|\{\mathcal C\le\mathrm M(n,q):\dim\mathcal C=n\}|},
--   $$
--   where $H$ is the trace-form hull. This is the probability that the first step of the algorithm of Theorem 1.1 succeeds on the slice code of a random algebra.
-- source:
--   Li, Li, Qiao, Tao, Wang, On the average-case complexity landscape for Tensor-Isomorphism-complete problems over finite fields, arXiv:2604.00591 (held version sha256 baf552e1…), Proposition 3.3, p.16 (PDF p.18)

import Mathlib
import Definitions.Def_AvgCaseTI_hull

set_option autoImplicit false

namespace AvgCaseTI

/-- **`Pr[dim H(A) = 1]` for a uniformly random `n`-dimensional matrix code `A ≤ M(n, q)`.**

Li, Li, Qiao, Tao, Wang, arXiv:2604.00591 (held version sha256 baf552e1…), Proposition 3.3, p.16
(PDF p.18): "Let A be a uniformly random n-dimensional subspace of M(n, q)."

`hullProb K n` is the number of `n`-dimensional subspaces `C ≤ M(n, K)` with `dim H(C) = 1`,
divided by the number of all `n`-dimensional subspaces.

**Formalization Note.** Over a finite field there are finitely many subspaces, so `Nat.card` is the
true count and the denominator is positive (`n ≤ n²`). -/
noncomputable def hullProb (K : Type*) [Field K] (n : ℕ) : ℝ :=
  (Nat.card {C : Submodule K (Mat K n) //
      Module.finrank K C = n ∧ Module.finrank K (hull C) = 1} : ℝ) /
    Nat.card {C : Submodule K (Mat K n) // Module.finrank K C = n}

end AvgCaseTI


