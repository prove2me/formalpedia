-- Prove2me | Definitions.Def_PlantedIQP_moment
-- name    : PlantedIQP_moment
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:22:07.114532+00:00
-- url     : https://prove2.me/theorems/c33e78c4-3786-4edb-877f-6645d0dadad0
-- title:
--   Normalized moments $m_k$ of $M(n)$
-- statement:
--   For $k\ge1$ and the law $M(n)$ with cubic-part distribution $D$, the **normalized moment** is
--
--   $$
--   m_k=2^{nk}\,\mathbb E_{f\leftarrow M(n)}\,p_f(0)^k .
--   $$
--
--   $m_2$ and $m_3$ control the mean and the variance of the XEB estimator (Lemma 35).
-- source:
--   Bläser, Gullans, Hangleiter, Liu, Qiao, Verifiable quantum advantage based on polynomials with planted structures, arXiv:2609.39918 (sha256 6e261694…), Lemma 30, Eq. (24), p.20

import Mathlib
import Definitions.Def_PlantedIQP_distributions
import Definitions.Def_PlantedIQP_amplitude

set_option autoImplicit false

namespace PlantedIQP

/-!
# Normalized moments `m_k` of `M(n)`

Bläser et al., arXiv:2609.39918 (sha256 6e261694…), Lemma 30, p.20: "For k = 1, 2, 3, the normalized
moments of M(n) are bounded as m_k := 2^{nk} E_{f←M(n)} p_f^k(0) = (2k − 1)!! + o(1)".

**Formalization Note.** `M(n)` depends on the cubic-part law `D` (`mixM D`), so `moment n k D` takes
`D` as an argument; the expectation is the finite sum `Σ_f mixM D f · p_f(0)^k`.
-/

/-- `m_k = 2^{nk} E_{f←M(n)} p_f(0)^k`, for `M(n)` with cubic-part law `D` (Lemma 30). -/
noncomputable def moment (n k : ℕ) (D : PMF (CubicPoly n)) : ℝ :=
  (2 : ℝ) ^ (n * k) * ∑ f : CubicPoly n, mixM D f * pf f 0 ^ k

end PlantedIQP


