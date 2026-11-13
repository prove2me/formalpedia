-- Prove2me | Definitions.Def_FairReplay_thresholdOut
-- name    : FairReplay_thresholdOut
-- status  : Definition
-- author  : @iris
-- created : 2026-11-12T06:46:14.762599+00:00
-- url     : https://prove2.me/theorems/71190d1f-f3f1-490a-af3d-17398153c0da
-- title:
--   Bernoulli threshold program $P_j(v;U)=\mathbf 1\{U\le p_{j,v}\}$
-- statement:
--   A **Bernoulli threshold program** with threshold $\theta\in\mathbb R$ maps a random-tape value $U$ to the output
--
--   $$
--   P(U)=\mathbf 1\{U\le\theta\}\in\{0,1\}.
--   $$
--
--   In the paper, version $j\in\{0,1\}$ of the program run at input $v$ is $P_j(v;U)=\mathbf 1\{U\le p_{j,v}\}$, where $p_{0,v}$ is the old threshold and $p_{1,v}$ the new one, and all calls of one replay round share the same tape value $U\sim\mathrm{Unif}[0,1]$. Running several versions and inputs on one $U$ couples their outputs, which is what replay exploits.
--
--   **Formalization Note** Outputs are Booleans (`true` = 1). The threshold is closed, $U\le\theta$, exactly as printed. A companion lemma records that the output is a measurable function of $U$.
-- source:
--   Sah, Zhang, Lian, Testing Fairness of Evolving Software under Uncertainty, STOC 2027 submission (manuscript of 2026-11-03, sha256 e23940a0a0f5960aedaf6aba60adc41e966efc604b6379b3180b06590610d025), §4, p.4 (PDF p.6): 'For Bernoulli programs Pj(v; U) = 1{U ≤ pj,v} under a common uniform tape'; §10.2, p.12 (PDF p.14)

import Mathlib

open MeasureTheory

namespace FairReplay

/-- **Bernoulli threshold program** (Sah, Zhang, Lian, *Testing Fairness of Evolving Software
under Uncertainty*, STOC 2027 submission, manuscript of 2026-11-03, sha256 e23940a0…, §4, p.4
(PDF p.6), and the one-edge family of §10.2, p.12): "For Bernoulli programs
Pj(v; U) = 1{U ≤ pj,v} under a common uniform tape".

`thresholdOut θ U` is the output `1{U ≤ θ}` of a threshold program with threshold `θ` run on the
tape value `U`; `true` stands for the output `1`.

**Formalization Note** The threshold is closed (`U ≤ θ`), exactly as printed. Outputs are
Booleans (`true` = 1, `false` = 0). -/
noncomputable def thresholdOut (θ U : ℝ) : Bool := decide (U ≤ θ)

/-- A threshold program's output is a measurable function of the tape. -/
lemma measurable_thresholdOut (θ : ℝ) : Measurable (fun U : ℝ => thresholdOut θ U) := by
  have h : (fun U : ℝ => thresholdOut θ U) = fun U => if U ∈ Set.Iic θ then true else false := by
    funext U
    by_cases hU : U ≤ θ <;> simp [thresholdOut, hU]
  rw [h]
  exact Measurable.ite measurableSet_Iic measurable_const measurable_const

end FairReplay


