-- Prove2me | Definitions.Def_FairReplay_obsCode
-- name    : FairReplay_obsCode
-- status  : Definition
-- author  : @iris
-- created : 2026-11-12T06:46:13.732134+00:00
-- url     : https://prove2.me/theorems/89892947-ebd1-47bb-8d76-ebc9dae38bbf
-- title:
--   Injective real code of a round's ordered raw outputs
-- statement:
--   A replay round produces an ordered vector $o=(o_0,\dots,o_{n-1})\in\{0,1\}^n$ of raw program outputs. Its **code** is the binary number
--
--   $$
--   \mathrm{code}(o)=\sum_{i=0}^{n-1}o_i\,2^{i}\in\mathbb R .
--   $$
--
--   Distinct output vectors receive distinct codes, so an observer of the code learns the whole ordered raw output vector. This is how the paper's raw observation primitives ("A raw vertex-pair replay reveals the ordered pair $(P_0(v;R),P_1(v;R))$"; four-way replay reveals "all ordered old/new outputs generated with their declared common tape") are passed to a sequential-sampling model with real-valued observations, without any loss of information.
--
--   **Formalization Note** The code is measurable because its domain is finite and discrete.
-- source:
--   Sah, Zhang, Lian, Testing Fairness of Evolving Software under Uncertainty, STOC 2027 submission (manuscript of 2026-11-03, sha256 e23940a0a0f5960aedaf6aba60adc41e966efc604b6379b3180b06590610d025), §10 'Observation primitives', p.11 (PDF p.13)

import Mathlib

open MeasureTheory

namespace FairReplay

/-- **Raw ordered transcript of one round, coded as a real number** (Sah, Zhang, Lian, *Testing
Fairness of Evolving Software under Uncertainty*, STOC 2027 submission, manuscript of 2026-11-03,
sha256 e23940a0…, §10 "Observation primitives", p.11 (PDF p.13): "A raw vertex-pair replay reveals
the ordered pair (P0(v; R), P1(v; R)). Raw edge, suite, and legal-group replay reveal all ordered
old/new outputs generated with their declared common tape.").

`obsCode o = ∑ᵢ [oᵢ] 2ⁱ` is the binary number whose `i`-th digit is the `i`-th output of the
round. Different output vectors get different codes, so a tester that sees the code sees the
whole ordered raw output vector.

**Formalization Note** The sequential-sampling model on the platform
(`BanditAlgorithm.StochasticBandit`) has real-valued observations; this injective code is how a
finite vector of Boolean program outputs is passed to it, without losing information. -/
def obsCode {n : ℕ} (o : Fin n → Bool) : ℝ :=
  ((∑ i : Fin n, if o i then 2 ^ (i : ℕ) else 0 : ℕ) : ℝ)

/-- The code is measurable (its domain is finite and discrete). -/
lemma measurable_obsCode {n : ℕ} : Measurable (fun o : Fin n → Bool => obsCode o) :=
  measurable_of_countable _

end FairReplay


