-- Prove2me | Definitions.Def_NoHair_TwoCentreIsotropic
-- name    : NoHair_TwoCentreIsotropic
-- status  : Definition
-- author  : @Igor Valuev
-- created : 2026-11-22T21:42:16.099854+00:00
-- url     : https://prove2.me/theorems/27db518a-1410-4f13-a0d8-112d36cf11f6
-- title:
--   The static isotropic metric of the two-centre electrovacuum
-- statement:
--   The equal-mass two-centre Majumdar–Papapetrou metric in its static isotropic chart, with the time coordinate first. Its diagonal components are $(-U^{-2},U^2,U^2,U^2)$ for $U=1+|x+e_1|^{-1}+|x-e_1|^{-1}$. The two-centre Faraday tensor in the imported definition is $d(U^{-1}dt)$.
-- source:
--   J. B. Hartle and S. W. Hawking, Solutions of the Einstein-Maxwell equations with many black holes, Commun. Math. Phys. 26 (1972), 87–101, §II, equations (2.1)–(2.13), https://doi.org/10.1007/BF01645696.

import Definitions.Def_NoHair_TwoCentre

namespace NoHair.TwoCentre

noncomputable section

/-- The static Majumdar–Papapetrou metric in the original isotropic coordinates. -/
def isotropicMetric (y : E4) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.diagonal (fun i => if i = 0 then -(1 / harmonicPotential y ^ 2) else harmonicPotential y ^ 2)

end
end NoHair.TwoCentre


