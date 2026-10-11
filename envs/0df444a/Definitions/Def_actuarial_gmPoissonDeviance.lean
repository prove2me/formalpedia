-- Prove2me | Definitions.Def_actuarial_gmPoissonDeviance
-- name    : actuarial_gmPoissonDeviance
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T17:59:38.656563+00:00
-- url     : https://prove2.me/theorems/1142a208-eb6e-44a5-ac06-472b7b7a9660
-- title:
--   Claims deviance, premium relativity and model comparison: gmPoissonDeviance
-- statement:
--   Poisson model deviance at positive counts, independently calculated from likelihoods. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
--
--   Mathematical relation:
--
--   $$
--   D_{\text{Poi}}=2\left[y\log\left(\frac{y}{\mu}\right)-(y-\mu)\right]
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 373. J. A. Nelder and R. W. M. Wedderburn (1972), Generalized Linear Models, JRSS A 135:370–384, https://doi.org/10.2307/2344614; actuarial practice in casualty generalized linear models https://www.casact.org/sites/default/files/2021-03/05-Goldburd-Khare-Tevet.pdf. Parent topic: Positive insurance exposure offsets, Poisson log-link likelihood and score, Fisher information, deviance and multiplicative premium relativities. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://doi.org/10.2307/2344614

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_gmPoissonLogLike
import Definitions.Def_actuarial_gmSaturatedLike

namespace ActuarialValuation

noncomputable def gmPoissonDeviance (claims expected : ℝ) : ℝ := 2*(gmSaturatedLike claims-gmPoissonLogLike claims expected)

end ActuarialValuation


