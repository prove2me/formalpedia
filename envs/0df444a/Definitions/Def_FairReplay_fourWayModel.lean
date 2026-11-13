-- Prove2me | Definitions.Def_FairReplay_fourWayModel
-- name    : FairReplay_fourWayModel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-12T06:48:06.487526+00:00
-- url     : https://prove2.me/theorems/f12c7a89-c8fa-4284-84c1-cf9fa51f3610
-- title:
--   Four-way counterfactual replay model of the one-edge family
-- statement:
--   Fix reals $p,s,d$ and a fairness edge $(u,v)$. A **four-way replay round** draws one tape value $U\sim\mathrm{Unif}[0,1]$ and observes the ordered outputs
--
--   $$
--   X=\bigl(P_0(u;U),\,P_1(u;U),\,P_0(v;U),\,P_1(v;U)\bigr)
--   $$
--
--   of the threshold programs with old thresholds $(p_{0,u},p_{0,v})=(p,p)$ and new thresholds
--
--   1. $(p_{1,u},p_{1,v})=(p+s,\;p+s)$ under the null hypothesis $H_0$, and
--   2. $(p_{1,u},p_{1,v})=(p+s+d,\;p+s)$ under the alternative $H_1$.
--
--   So both new thresholds carry the common shift $s$, and the alternative adds the differential effect $d$ at $u$. The model is the sequential-sampling environment with a single action, the four-way round, whose observation law is the image of the uniform tape under $U\mapsto\mathrm{code}(X)$; rounds are independent.
--
--   **Formalization Note** The endpoint $u$ is index $0$; the Boolean `alt` selects $H_1$. Round laws are pushforwards of the tape, never hand-written lists of atoms.
-- source:
--   Sah, Zhang, Lian, Testing Fairness of Evolving Software under Uncertainty, STOC 2027 submission (manuscript of 2026-11-03, sha256 e23940a0a0f5960aedaf6aba60adc41e966efc604b6379b3180b06590610d025), Theorem 10.4, p.14 (PDF p.16); §10.2, p.12 (PDF p.14); §10 'Observation primitives', p.11

import Mathlib
import Definitions.Def_BanditTrajectory
import Definitions.Def_FairReplay_thresholdOut
import Definitions.Def_FairReplay_uniformTape
import Definitions.Def_FairReplay_obsCode

open MeasureTheory

namespace FairReplay

/-- The four ordered raw outputs of one four-way (edge-synchronized) replay round at the edge
`(u, v)` on the tape value `U`: `(P0(u;U), P1(u;U), P0(v;U), P1(v;U))`, for threshold programs
with old thresholds `old 0, old 1` and new thresholds `new 0, new 1` at `u, v`. -/
noncomputable def fourWayObs (old new : Fin 2 → ℝ) (U : ℝ) : Fin 4 → Bool :=
  ![thresholdOut (old 0) U, thresholdOut (new 0) U, thresholdOut (old 1) U,
    thresholdOut (new 1) U]

lemma measurable_fourWayObs (old new : Fin 2 → ℝ) :
    Measurable (fun U : ℝ => fourWayObs old new U) := by
  rw [measurable_pi_iff]
  intro i
  fin_cases i <;> simp [fourWayObs] <;> exact measurable_thresholdOut _

/-- The law of the coded observation of one four-way round: the image of the uniform tape
under `U ↦ obsCode (fourWayObs old new U)`. -/
noncomputable def fourWayLaw (old new : Fin 2 → ℝ) : Measure ℝ :=
  uniformTape.map (fun U => obsCode (fourWayObs old new U))

instance fourWayLaw.instIsProbabilityMeasure (old new : Fin 2 → ℝ) :
    IsProbabilityMeasure (fourWayLaw old new) :=
  Measure.isProbabilityMeasure_map
    (measurable_obsCode.comp (measurable_fourWayObs old new)).aemeasurable

/-- **Four-way counterfactual replay model of the one-edge family** (Sah, Zhang, Lian, *Testing
Fairness of Evolving Software under Uncertainty*, STOC 2027 submission, manuscript of 2026-11-03,
sha256 e23940a0…, Theorem 10.4, p.14 (PDF p.16), with §10.2, p.12 and the observation primitives of
§10, p.11): "The old thresholds are (p, p); the null new thresholds are (p+s, p+s), and the
alternative new thresholds are (p + s + d, p + s). Vertex-paired and four-way rounds reveal their
ordered raw outputs, and tapes are independent across rounds."

`fourWayModel p s d alt` is the sequential-sampling environment with a single action, the
four-way round at the edge `(u, v)`. Its observation is the coded ordered vector
`(P0(u;U), P1(u;U), P0(v;U), P1(v;U))` of the threshold programs on one uniform tape value `U`,
with old thresholds `(p, p)` and new thresholds `(p + s, p + s)` under the null (`alt = false`)
and `(p + s + d, p + s)` under the alternative (`alt = true`).

**Formalization Note** The edge's endpoint `u` (index `0`) is the one that may receive the
differential effect `d`. A four-way tester has exactly one action (`Fin 1`). The law of a round is
the image of the uniform tape on `[0, 1]`, not a list of atoms; observations are passed to the
model through the injective code `obsCode`. -/
noncomputable def fourWayModel (p s d : ℝ) (alt : Bool) : BanditAlgorithm.StochasticBandit 1 where
  P _ := fourWayLaw ![p, p] (if alt then ![p + s + d, p + s] else ![p + s, p + s])
  prob _ := inferInstance

end FairReplay


