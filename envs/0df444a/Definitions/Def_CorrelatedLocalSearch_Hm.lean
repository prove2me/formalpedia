-- Prove2me | Definitions.Def_CorrelatedLocalSearch_Hm
-- name    : CorrelatedLocalSearch_Hm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:38:18.111057+00:00
-- url     : https://prove2.me/theorems/94db95b4-b0ae-4220-a0c5-6fc23630a050
-- title:
--   The harmonic function $H_m(d)=\frac{d}{m}\lambda^{d-m}$
-- statement:
--   For a barrier $m\ge1$ and $0\le d\le m$,
--   $$
--   H_m(d)=\frac{d}{m}\,\lambda^{d-m},
--   $$
--   with $\lambda=\sqrt{r/(k-r)}$. It is the function that pays for prefixes first reaching potential $m$ in the proof of Lemma C.1: it vanishes at $0$, equals one at the barrier, and is harmonic for the two-sided comparison with weights $a=\lambda/2$, $b=1/(2\lambda)$.
--
--   **Formalization Note** The exponent $d-m$ is an integer power (`zpow`); the function is defined for every natural $d$ and used on $0\le d\le m$.
-- source:
--   Xu, Local Search with Correlated Randomness, arXiv:2607.17469 (sha256 17e00d69…), App. C.1, proof of Lemma C.1, p.22 (PDF p.24)

import Mathlib
import Definitions.Def_CorrelatedLocalSearch_sStar

set_option autoImplicit false

namespace CorrelatedLocalSearch

/-- The harmonic function `H_m(d) = (d/m) λ^{d−m}` for first-hit prefixes
(Xu, *Local Search with Correlated Randomness*, arXiv:2607.17469 (sha256 17e00d69…), App. C.1,
proof of Lemma C.1, p.22), with `λ = √(r/(k−r))` of (8).

**Formalization Note** The exponent `d − m` is an integer (`zpow`); the paper uses the
function on `0 ≤ d ≤ m`, the statements about it restrict to that range. -/
noncomputable def Hm (k r m d : ℕ) : ℝ :=
  ((d : ℝ) / m) * lam k r ^ ((d : ℤ) - m)

end CorrelatedLocalSearch


