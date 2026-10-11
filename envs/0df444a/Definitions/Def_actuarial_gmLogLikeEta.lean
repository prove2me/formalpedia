-- Prove2me | Definitions.Def_actuarial_gmLogLikeEta
-- name    : actuarial_gmLogLikeEta
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-10T17:58:50.775582+00:00
-- url     : https://prove2.me/theorems/82633480-6bd5-4ba7-8fb9-04e7f819e7a3
-- title:
--   Poisson log-likelihood, score and information: gmLogLikeEta
-- statement:
--   Poisson regression log-likelihood with an exposure offset. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
--
--   Mathematical relation:
--
--   $$
--   \ell(\eta)=y\log(Ee^\eta)-Ee^\eta,\quad U(\eta)=y-Ee^\eta
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 373. J. A. Nelder and R. W. M. Wedderburn (1972), Generalized Linear Models, JRSS A 135:370–384, https://doi.org/10.2307/2344614; actuarial practice in casualty generalized linear models https://www.casact.org/sites/default/files/2021-03/05-Goldburd-Khare-Tevet.pdf. Parent topic: Positive insurance exposure offsets, Poisson log-link likelihood and score, Fisher information, deviance and multiplicative premium relativities. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://doi.org/10.2307/2344614

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_gmMean
import Definitions.Def_actuarial_gmPoissonLogLike

namespace ActuarialValuation

noncomputable def gmLogLikeEta (claims exposure eta : ℝ) : ℝ := gmPoissonLogLike claims (gmMean exposure eta)

end ActuarialValuation


