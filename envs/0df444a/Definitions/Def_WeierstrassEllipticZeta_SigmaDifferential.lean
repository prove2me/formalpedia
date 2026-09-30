-- Prove2me | Definitions.Def_WeierstrassEllipticZeta_SigmaDifferential
-- name    : WeierstrassEllipticZeta_SigmaDifferential
-- status  : Definition
-- author  : @tomasz
-- created : 2026-09-07T20:36:18.547333+00:00
-- url     : https://prove2.me/theorems/14cc7423-9402-4102-a538-ad1bd86a8bc8
-- title:
--   Normalized entire sigma differential data
-- statement:
--   Let $L$ be a complex period pair, let $\Omega$ be its lattice, and let $\wp,\wp',\zeta$ denote its canonical Weierstrass functions. A normalized entire sigma differential datum consists of an entire function $\sigma:\mathbb C\to\mathbb C$ satisfying
--
--   $$\sigma(0)=0,\qquad \sigma'(0)=1,$$
--
--   and the differential equation
--
--   $$\sigma'(z)=\zeta(z)\sigma(z)\qquad(z\notin\Omega).$$
--
--   The datum has no nonvanishing, addition, periodicity, or growth field. It is an interface for the normalized entire solution; the definition itself asserts no existence theorem.
-- source:
--   Interface for the normalized sigma function in NIST DLMF 23.2(ii), equations (23.2.6) and (23.2.8), https://dlmf.nist.gov/23.2#E6 and https://dlmf.nist.gov/23.2#E8; used in Senthil Kumar K (2026), Section 4, proof of Lemma 5. https://doi.org/10.1017/S001309152610145X

import Definitions.Def_WeierstrassEllipticZeta_SigmaAddition

noncomputable section
namespace WeierstrassEllipticZeta

/-- Normalized entire sigma data, before proving its addition identity. -/
structure EllipticSigmaDifferentialData (L : PeriodPair) where
  sigma : ℂ → ℂ
  entire : Differentiable ℂ sigma
  zero : sigma 0 = 0
  deriv_zero : HasDerivAt sigma 1 0
  hasDerivAt : ∀ z : ℂ, z ∉ L.lattice →
    HasDerivAt sigma (weierstrassZeta L z * sigma z) z

end WeierstrassEllipticZeta


