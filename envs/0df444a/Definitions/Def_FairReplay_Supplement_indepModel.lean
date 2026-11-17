-- Prove2me | Definitions.Def_FairReplay_Supplement_indepModel
-- name    : FairReplay_Supplement_indepModel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:44:37.6843+00:00
-- url     : https://prove2.me/theorems/f1956076-72d0-4ee6-b44d-9876c6ee4134
-- title:
--   Independent single-execution observation of the one-edge family; $Q_{\mathrm{ind}}$, $Q_{\mathrm{pair}}$
-- statement:
--   In the **one-edge family** of §10.2, both endpoints $u,v$ have old threshold $p$; the null applies no differential patch (new thresholds $(p,p)$) and the alternative adds $d$ to the first endpoint (new thresholds $(p+d,p)$). Programs are threshold programs $P_j(x;U)=\mathbf 1\{U\le p_{j,x}\}$ on a uniform tape.
--
--   Under **independent observation**, each call runs one program version at one endpoint on a fresh tape and observes its single output. There are four such calls: $P_0(u)$, $P_1(u)$, $P_0(v)$, $P_1(v)$; each is a Bernoulli observation.
--
--   $Q_{\mathrm{ind}}(d,\delta)$ is the optimal null expected number of such calls over $\delta$-correct testers, and $Q_{\mathrm{pair}}(d,\delta)$ the same quantity for common-uniform raw-pair replay, which is the published vertex-paired model with no common shift ($s=0$).
--
--   **Formalization Note** Laws are images of the uniform tape on $[0,1]$ under the coded output. Both $Q$'s are infima in $[0,\infty]$ (published `FairReplay.optRounds`).
-- source:
--   Sah, Zhang, Lian, Testing Fairness of Evolving Software under Uncertainty, STOC 2027 submission (manuscript of 2026-11-03, sha256 e23940a0a0f5960aedaf6aba60adc41e966efc604b6379b3180b06590610d025), §10.2 and Theorem 10.3, pp.12–13 (PDF pp.14–15), eq. (25)

import Mathlib
import Definitions.Def_BanditTrajectory
import Definitions.Def_FairReplay_thresholdOut
import Definitions.Def_FairReplay_uniformTape
import Definitions.Def_FairReplay_obsCode
import Definitions.Def_FairReplay_optRounds

open MeasureTheory

namespace FairReplay.Supplement

/-- The law of the coded output of one single-execution call of a threshold program with threshold
`θ` on a fresh uniform tape: the image of the uniform tape under `U ↦ obsCode (1{U ≤ θ})`. -/
noncomputable def singleLaw (θ : ℝ) : Measure ℝ :=
  uniformTape.map (fun U => obsCode (![thresholdOut θ U] : Fin 1 → Bool))

lemma measurable_singleObs (θ : ℝ) :
    Measurable (fun U : ℝ => (![thresholdOut θ U] : Fin 1 → Bool)) := by
  rw [measurable_pi_iff]
  intro i
  fin_cases i
  simpa using measurable_thresholdOut θ

instance singleLaw.instIsProbabilityMeasure (θ : ℝ) : IsProbabilityMeasure (singleLaw θ) :=
  Measure.isProbabilityMeasure_map
    (measurable_obsCode.comp (measurable_singleObs θ)).aemeasurable

/-- **Independent single-execution observation of the one-edge family** (Sah, Zhang, Lian,
*Testing Fairness of Evolving Software under Uncertainty*, STOC 2027 submission, manuscript of
2026-11-03, sha256 e23940a0…, §10.2, p.12 and Theorem 10.3(ii), p.13 (PDF pp.14–15); §2, p.2: "A
single-version call executes one program version once"): "For the one-edge family, the old
thresholds are p at both endpoints. The null applies no differential patch and the alternative adds
d to the first endpoint".

`indepModel p d alt` is the sequential-sampling environment with four actions: action `0` runs `P0`
at `u`, action `1` runs `P1` at `u`, action `2` runs `P0` at `v`, action `3` runs `P1` at `v`. Each call
uses a fresh uniform tape and observes the single Boolean output. Old thresholds are `p` at both
endpoints; new thresholds are `(p, p)` under the null (`alt = false`) and `(p + d, p)` under the
alternative (`alt = true`).

**Formalization Note** The endpoint `u` (the one that may change) is the first endpoint. Each
action's law is the image of the uniform tape under the coded threshold output, i.e. a Bernoulli
law; the tester may use all four actions adaptively. -/
noncomputable def indepModel (p d : ℝ) (alt : Bool) : BanditAlgorithm.StochasticBandit 4 where
  P := ![singleLaw p, singleLaw (if alt then p + d else p), singleLaw p, singleLaw p]
  prob i := by
    fin_cases i <;> simp <;> infer_instance

/-- `Q_ind(d, δ)` (Theorem 10.3, eq. (25), p.13): the optimal null expected number of independent
single-execution calls for testing the one-edge null against the alternative at level `δ`. -/
noncomputable def Qind (p d δ : ℝ) : ENNReal :=
  optRounds δ (indepModel p d false) (indepModel p d true)

/-- `Q_pair(d, δ)` (Theorem 10.3, eq. (25), p.13): the optimal null expected number of
common-uniform raw-pair replay rounds for the one-edge family. Raw-pair replay of this family is
the published vertex-paired model with no common shift (`s = 0`): null new thresholds `(p, p)`,
alternative `(p + d, p)`. -/
noncomputable def Qpair (p d δ : ℝ) : ENNReal :=
  Qvertex p 0 d δ

end FairReplay.Supplement


