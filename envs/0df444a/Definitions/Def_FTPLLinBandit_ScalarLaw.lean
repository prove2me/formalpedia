-- Prove2me | Definitions.Def_FTPLLinBandit_ScalarLaw
-- name    : FTPLLinBandit_ScalarLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:00:30.298043+00:00
-- url     : https://prove2.me/theorems/e7ac7db0-2e41-4bb4-a468-6ce31110609b
-- title:
--   The two scalar weight laws of Table 3: Gaussian and Laplace
-- statement:
--   The random-weighting perturbations draw scalar weights $\xi$ from one of the two **mean-zero scalar increment laws** of Table 3:
--
--   1. **Gaussian**, $\varphi(\xi)\propto e^{-\xi^2/2}$;
--   2. **Laplace**, $\varphi(\xi)\propto e^{-|\xi|}$.
--
--   This finite type names the two rows; their normalized densities are given by `scalarDens`.
-- source:
--   Wei, Follow the Perturbed Leader for Linear Bandits: √T Regret over General Action Sets, arXiv:2610.17818, Appendix B, Table 3, p.21

import Mathlib

namespace FTPLLinBandit

/-- **The two scalar weight laws of Table 3.** Wei, arXiv:2610.17818, Appendix B, Table 3, p.21:
"Mean-zero scalar increment laws": Gaussian, `φ(ξ) ∝ e^{−ξ²/2}`, and Laplace, `φ(ξ) ∝ e^{−|ξ|}`.
The density of each constructor is `scalarDens`. -/
inductive ScalarLaw
  | gaussian
  | laplace
  deriving DecidableEq

end FTPLLinBandit


