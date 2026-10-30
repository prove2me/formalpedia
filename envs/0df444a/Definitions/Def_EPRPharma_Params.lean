-- Prove2me | Definitions.Def_EPRPharma_Params
-- name    : EPRPharma_Params
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:03:26.191401+00:00
-- url     : https://prove2.me/theorems/27b144db-2efa-4a7d-bc26-a46ca6b6ded2
-- title:
--   Parameters $(\alpha,\beta,o_d,u_p,k,\epsilon_e,\epsilon_s)$ of the EPR model
-- statement:
--   A parameter vector of the pharmaceutical EPR model collects seven real numbers:
--
--   1. the promotional cost constants $\alpha$ and $\beta$, so that promotional efforts $\eta_d$ (aimed at the doctor) and $\eta_p$ (aimed at the patient) cost the producer $\alpha\eta_d^2$ and $\beta\eta_p^2$;
--   2. the unit over-prescription disutility $o_d$ of the doctor;
--   3. the unit health benefit $u_p$ of the medicine;
--   4. the unit collection cost $k$;
--   5. the unit environmental disutility $\epsilon_e$ and the unit social disutility $\epsilon_s$ of medicine that ends up in the environment or remains uncollected.
--
--   These are the exogenous data of every statement of the mission.
--
--   **Formalization Note** The fields are named `alpha`, `beta`, `od`, `up`, `k`, `epsE`, `epsS`. Signs are imposed separately by `Params.Standing`.
-- source:
--   Alev, Atasu, Toktay, Zhang, Extended Producer Responsibility for Pharmaceuticals, SSRN 2693169 (2020 posting), §3, pp. 9–13 (unnumbered)

import Mathlib

namespace EPRPharma

/-- **Parameters of the EPR model for pharmaceuticals.**
Alev, Atasu, Toktay, Zhang, *Extended Producer Responsibility for Pharmaceuticals*, SSRN 2693169 (2020 posting), §3, pp. 9–13 (unnumbered):
the promotional cost constants `alpha` = α and `beta` = β of the producer's costs αη_d² and βη_p²
(p. 11), the unit over-prescription disutility to the doctor `od` = o_d (p. 10), the unit health
benefit `up` = u_p (p. 9), the unit collection cost `k` (p. 12), and the unit environmental and
social disutilities `epsE` = ε_e and `epsS` = ε_s (p. 13).

**Formalization Note.** All parameters are real numbers; their signs are the separate predicate
`Params.Standing`. ASCII field names are used because `α`, `β` read as type variables. -/
structure Params where
  /-- α, promotional cost constant for the effort η_d aimed at the doctor (p. 11). -/
  alpha : ℝ
  /-- β, promotional cost constant for the effort η_p aimed at the patient (p. 11). -/
  beta : ℝ
  /-- o_d, unit over-prescription disutility to the doctor (p. 10). -/
  od : ℝ
  /-- u_p, unit health benefit of the medicine (p. 9). -/
  up : ℝ
  /-- k, unit collection cost (p. 12). -/
  k : ℝ
  /-- ε_e, unit environmental disutility (p. 13). -/
  epsE : ℝ
  /-- ε_s, unit social disutility (p. 13). -/
  epsS : ℝ

end EPRPharma


