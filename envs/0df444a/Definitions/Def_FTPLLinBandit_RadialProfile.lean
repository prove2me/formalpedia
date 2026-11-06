-- Prove2me | Definitions.Def_FTPLLinBandit_RadialProfile
-- name    : FTPLLinBandit_RadialProfile
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:00:17.742058+00:00
-- url     : https://prove2.me/theorems/f8ba4c2d-221a-4429-b7e1-d8a20d46ccf5
-- title:
--   The three radial laws of Tables 2 and 4: Gaussian, radial Laplace, Student-$t_2$
-- statement:
--   The paper uses three radial perturbation laws, listed in Table 2 (initializers $\rho_1$ for random weighting) and Table 4 (elliptical families $P_\Sigma$):
--
--   1. **Gaussian**;
--   2. **radial Laplace**;
--   3. **multivariate Student-$t_2$**.
--
--   This finite type names the three rows; their radial profiles are given by the definition `radialFn`. Table 2's caption notes that its laws are "essentially those in Table 4 with $\Sigma=\lambda I$".
-- source:
--   Wei, Follow the Perturbed Leader for Linear Bandits: √T Regret over General Action Sets, arXiv:2610.17818, Appendix B, Tables 2 and 4, p.21

import Mathlib

namespace FTPLLinBandit

/-- **The three radial laws of Tables 2 and 4.** Wei, arXiv:2610.17818, Appendix B, Tables 2 and
4, p.21: the Gaussian, the radial Laplace and the multivariate Student-t₂ perturbation laws. The
profile function of each constructor is `radialFn`.

**Formalization Note.** The constructors only name the three rows of the tables; Table 2 (the
random-weighting initializer `ρ₁ = P_{λI}`) and Table 4 (the elliptical family `P_Σ`) use the same
three profiles ("The distributions listed here are essentially those in Table 4 with Σ = λI",
Table 2 caption). -/
inductive RadialProfile
  | gaussian
  | radialLaplace
  | studentT2
  deriving DecidableEq

end FTPLLinBandit


