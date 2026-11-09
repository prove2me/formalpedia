-- Prove2me | Definitions.Def_SharpConsist_RT
-- name    : SharpConsist_RT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:09:37.054099+00:00
-- url     : https://prove2.me/theorems/0cb1cc7e-a72b-482f-873b-0dbbd7c11570
-- title:
--   The limiting ratio $R(T)$
-- statement:
--   For a real parameter $T$,
--   $$R(T)=\frac{T^2+2}{T^2+2T+2}.$$
--   The denominator is positive for every real $T$. Theorem 5.1 shows that $R(T)$ is the limit of the approximation achievable against the hard instances with parameter $T$, and that $T=\sqrt2$ minimizes it on $[7/5,3/2]$ with $R(\sqrt2)=2-\sqrt2$.
--
--   **Formalization Note.** $R$ is defined by this formula, not as $w(1)$; the identity $w(1)=R(T)$ is part of the milestone for Eq. (5.3).
-- source:
--   Fu–Zhang–Tao, A Sharp Barrier of Consistent Submodular Maximization, arXiv:2609.09986 (held version, sha256 874ec76c…), Theorem 5.1, p.12

import Mathlib

namespace SharpConsist

/-- The **limiting ratio** `R(T) = (T² + 2)/(T² + 2T + 2)` of Theorem 5.1. Fu–Zhang–Tao,
arXiv:2609.09986 (held version, sha256 874ec76c…), Theorem 5.1, p.12.

**Formalization Note.** `R` is this rational function, not `w(1)`; that `w(1) = R(T)` is part of the
milestone for Eq. (5.3). The denominator is positive for every real `T`. -/
noncomputable def RT (T : ℝ) : ℝ := (T ^ 2 + 2) / (T ^ 2 + 2 * T + 2)

end SharpConsist


