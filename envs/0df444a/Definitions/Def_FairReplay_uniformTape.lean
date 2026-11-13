-- Prove2me | Definitions.Def_FairReplay_uniformTape
-- name    : FairReplay_uniformTape
-- status  : Definition
-- author  : @iris
-- created : 2026-11-12T06:46:14.561194+00:00
-- url     : https://prove2.me/theorems/c5e94feb-24bc-40c9-93bd-be94e56204d8
-- title:
--   The uniform random tape $U\sim\mathrm{Unif}[0,1]$
-- statement:
--   Each replay round draws one **tape value** $U$ uniformly from $[0,1]$; every program call of the round is executed on this same $U$, and different rounds use independent tapes. The law of one tape value is Lebesgue measure restricted to $[0,1]$,
--
--   $$
--   \mathbb P(U\in A)=\lambda(A\cap[0,1]),
--   $$
--
--   which is a probability measure.
--
--   **Formalization Note** The tape is real-valued. Independence across rounds is supplied by the sequential-sampling model, which draws each round's observation afresh.
-- source:
--   Sah, Zhang, Lian, Testing Fairness of Evolving Software under Uncertainty, STOC 2027 submission (manuscript of 2026-11-03, sha256 e23940a0a0f5960aedaf6aba60adc41e966efc604b6379b3180b06590610d025), §2, pp.1–2 (PDF pp.3–4): 'Fresh rounds use independent tapes'; §4, p.4 (PDF p.6)

import Mathlib

open MeasureTheory

namespace FairReplay

/-- **The uniform random tape** (Sah, Zhang, Lian, *Testing Fairness of Evolving Software under
Uncertainty*, STOC 2027 submission, manuscript of 2026-11-03, sha256 e23940a0…, §2, pp.1–2 and
§4, p.4): each replay round draws one tape value `U ~ Unif[0, 1]`, shared by every program call
of that round; "Fresh rounds use independent tapes".

`uniformTape` is Lebesgue measure on `ℝ` restricted to `[0, 1]`, the law of one tape value.

**Formalization Note** The tape lives in `ℝ`; independence across rounds is supplied by the
sequential-sampling model (`BanditAlgorithm.banditTrajMeasure`), which draws every round's
observation afresh from its law. -/
noncomputable def uniformTape : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) 1)

instance uniformTape.instIsProbabilityMeasure : IsProbabilityMeasure uniformTape := by
  constructor
  simp [uniformTape]

end FairReplay


