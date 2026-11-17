-- Prove2me | Definitions.Def_FairReplay_Supplement_fourWayEnv
-- name    : FairReplay_Supplement_fourWayEnv
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:45:21.104206+00:00
-- url     : https://prove2.me/theorems/c0332d44-dc7a-4d0b-a8e3-c91b250e54c8
-- title:
--   Four-way synchronized replay at arbitrary thresholds
-- statement:
--   One **four-way synchronized replay round** at a fairness edge $(u,v)$ draws one tape $U\sim\mathrm{Unif}[0,1]$ and reveals the ordered raw outputs
--   $$\big(P_0(u;U),\,P_1(u;U),\,P_0(v;U),\,P_1(v;U)\big)$$
--   of threshold programs with given old thresholds $(o_u,o_v)$ and new thresholds $(a,b)$. Rounds use independent tapes.
--
--   This environment, with any thresholds, is the observation model of the thresholded-replay results (Theorem 10.5).
--
--   **Formalization Note** A single-action sequential-sampling environment whose round law is the published `FairReplay.fourWayLaw`.
-- source:
--   Sah, Zhang, Lian, Testing Fairness of Evolving Software under Uncertainty, STOC 2027 submission (manuscript of 2026-11-03, sha256 e23940a0a0f5960aedaf6aba60adc41e966efc604b6379b3180b06590610d025), §10.3, p.15 (PDF p.17)

import Mathlib
import Definitions.Def_BanditTrajectory
import Definitions.Def_FairReplay_fourWayModel

open MeasureTheory

namespace FairReplay.Supplement

/-- **Four-way synchronized replay at arbitrary thresholds** (Sah, Zhang, Lian, *Testing Fairness of
Evolving Software under Uncertainty*, STOC 2027 submission, manuscript of 2026-11-03,
sha256 e23940a0…, §10.3, p.15 (PDF p.17): "Each round reveals the ordered raw four-way
transcript").

`fourWayEnv old new` is the sequential-sampling environment with one action, the four-way round at
the edge `(u, v)`, whose coded observation `(P0(u;U), P1(u;U), P0(v;U), P1(v;U))` has the published
law `fourWayLaw old new` (old thresholds `old 0, old 1`, new thresholds `new 0, new 1` at `u, v`).

**Formalization Note** The published `fourWayModel` fixes the thresholds of Theorem 10.4; this
environment takes any thresholds, as Theorem 10.5 needs. -/
noncomputable def fourWayEnv (old new : Fin 2 → ℝ) : BanditAlgorithm.StochasticBandit 1 where
  P _ := fourWayLaw old new
  prob _ := inferInstance

end FairReplay.Supplement


