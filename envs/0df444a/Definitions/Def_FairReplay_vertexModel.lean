-- Prove2me | Definitions.Def_FairReplay_vertexModel
-- name    : FairReplay_vertexModel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-12T06:48:07.009368+00:00
-- url     : https://prove2.me/theorems/5dd8e8ff-321b-4d3b-a519-b492edb316ca
-- title:
--   Vertex-paired replay model of the one-edge family
-- statement:
--   With the same thresholds as the four-way model — old $(p,p)$, new $(p+s,p+s)$ under $H_0$ and $(p+s+d,p+s)$ under $H_1$ — a **vertex-paired round** at a vertex $x\in\{u,v\}$ draws one tape value $U\sim\mathrm{Unif}[0,1]$ and observes the ordered pair
--
--   $$
--   \bigl(P_0(x;U),\,P_1(x;U)\bigr).
--   $$
--
--   The model is the sequential-sampling environment with two actions: a round at $u$ (action $0$) and a round at $v$ (action $1$). Each action's observation law is the image of the uniform tape under $U\mapsto\mathrm{code}(P_0(x;U),P_1(x;U))$. Only the law at $u$ differs between the hypotheses. A tester may choose $u$ or $v$ in every round, adaptively.
--
--   **Formalization Note** The pair is passed through the injective code; round laws are pushforwards of the tape.
-- source:
--   Sah, Zhang, Lian, Testing Fairness of Evolving Software under Uncertainty, STOC 2027 submission (manuscript of 2026-11-03, sha256 e23940a0a0f5960aedaf6aba60adc41e966efc604b6379b3180b06590610d025), Theorem 10.4(ii), p.14 (PDF p.16); §2, pp.1–2; §10 'Observation primitives', p.11

import Mathlib
import Definitions.Def_BanditTrajectory
import Definitions.Def_FairReplay_thresholdOut
import Definitions.Def_FairReplay_uniformTape
import Definitions.Def_FairReplay_obsCode

open MeasureTheory

namespace FairReplay

/-- The two ordered raw outputs `(P0(x;U), P1(x;U))` of one vertex-paired replay round at a
vertex `x` with old threshold `θold` and new threshold `θnew`, on the tape value `U`. -/
noncomputable def pairObs (θold θnew U : ℝ) : Fin 2 → Bool :=
  ![thresholdOut θold U, thresholdOut θnew U]

lemma measurable_pairObs (θold θnew : ℝ) :
    Measurable (fun U : ℝ => pairObs θold θnew U) := by
  rw [measurable_pi_iff]
  intro i
  fin_cases i <;> simp [pairObs] <;> exact measurable_thresholdOut _

/-- The law of the coded observation of one vertex-paired round: the image of the uniform tape
under `U ↦ obsCode (pairObs θold θnew U)`. -/
noncomputable def pairLaw (θold θnew : ℝ) : Measure ℝ :=
  uniformTape.map (fun U => obsCode (pairObs θold θnew U))

instance pairLaw.instIsProbabilityMeasure (θold θnew : ℝ) :
    IsProbabilityMeasure (pairLaw θold θnew) :=
  Measure.isProbabilityMeasure_map
    (measurable_obsCode.comp (measurable_pairObs θold θnew)).aemeasurable

/-- **Vertex-paired replay model of the one-edge family** (Sah, Zhang, Lian, *Testing Fairness of
Evolving Software under Uncertainty*, STOC 2027 submission, manuscript of 2026-11-03,
sha256 e23940a0…, Theorem 10.4(ii), p.14 (PDF p.16), with §2, pp.1–2 and the observation primitives
of §10, p.11: "A raw vertex-pair replay reveals the ordered pair (P0(v; R), P1(v; R))").

`vertexModel p s d alt` is the sequential-sampling environment with two actions, a vertex-paired
round at `u` (action `0`) or at `v` (action `1`). A round at a vertex `x` observes the coded ordered
pair `(P0(x;U), P1(x;U))` on one uniform tape value `U`. The old thresholds are `(p, p)`; the new
thresholds are `(p + s, p + s)` under the null (`alt = false`) and `(p + s + d, p + s)` under the
alternative (`alt = true`), so only the law of action `0` changes.

**Formalization Note** `u` (action `0`) is the endpoint that may receive the differential effect;
the tester chooses `u` or `v` in every round, adaptively. Laws are images of the uniform tape on
`[0, 1]`; observations are passed through the injective code `obsCode`. -/
noncomputable def vertexModel (p s d : ℝ) (alt : Bool) : BanditAlgorithm.StochasticBandit 2 where
  P := ![pairLaw p (if alt then p + s + d else p + s), pairLaw p (p + s)]
  prob i := by
    fin_cases i <;> simp <;> infer_instance

end FairReplay


