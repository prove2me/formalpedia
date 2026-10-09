-- Prove2me | Definitions.Def_actuarial_finiteEntropicOptimalCost
-- name    : actuarial_finiteEntropicOptimalCost
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-09T08:55:06.900581+00:00
-- url     : https://prove2.me/theorems/357e6a12-fb60-4e02-8fad-67a5697ed69f
-- title:
--   Least finite-menu entropic reinsurance cost
-- statement:
--   Select the minimum combined quoted reinsurance premium and entropic retained-loss risk among a finite nonempty set of retention choices.
--
--   **Mathematical statement**
--
--   $$
--   J^\star_\gamma=\min_{a\in A}[q(\alpha_a)+\rho_\gamma(r(Z,\alpha_a))]
--   $$
-- source:
--   Tsanakas and Desli (2003), Risk measures and theories of choice, British Actuarial Journal 9(4), 959-991, exponential premium principle, https://doi.org/10.1017/S1357321700004414; Baeuerle and Glauner (2022), Markov decision processes with recursive risk measures, European Journal of Operational Research 296(3), 953-966, https://doi.org/10.1016/j.ejor.2021.04.030; Baeuerle and Glauner (2021), Minimizing spectral risk measures applied to Markov decision processes, https://doi.org/10.1007/s00186-021-00746-w, section 2 entropic risk definition

import Mathlib
import Definitions.Def_actuarial_finiteEntropicRetentionCost
open MeasureTheory

namespace ActuarialValuation

noncomputable def finiteEntropicOptimalCost
  {Ω A : Type*} [Fintype Ω] [Fintype A] [Nonempty A]
  (w z : Ω → ℝ) (reinsurancePremium : ℝ → ℝ)
  (retention : A → ℝ) (gamma : ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty
    (fun a : A => finiteEntropicRetentionCost w z
      reinsurancePremium gamma (retention a))

end ActuarialValuation


