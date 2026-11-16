-- Prove2me | Definitions.Def_KTaxi_Competitive_Supplement_PrivatePolicy
-- name    : KTaxi_Competitive_Supplement_PrivatePolicy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T21:30:43.323219+00:00
-- url     : https://prove2.me/theorems/05338d87-db50-412a-9114-93bf97399733
-- title:
--   §2 — general causal policy with arbitrary private probability space
-- statement:
--   A general causal randomized policy has a private seed $\omega$ drawn from an arbitrary probability space $(\Omega,\mu)$, a visible-history input $h$, a current query $q$, and a response $a(\omega,h,q)$. For each fixed $h,q$, the response is measurable in $\omega$. The types of histories, queries and responses are parameters of the definition.
--
--   The seed can contain the whole private random tape, including continuous randomness and unbounded internal memory. No future query or comparator action is supplied. On the countable integer-line histories used here, this per-history measurability gives well-defined nonnegative finite-horizon expectations. This general policy interface is separated from the taxi model for reuse.
-- source:
--   Christian Coester, Yichen Huang, Tze-Yang Poon, STOC 2027 submission #96 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/96.pdf, §2, PDF p. 4 (printed p. 3); Appendix A, PDF p. 17 (printed p. 16)

import Mathlib

open MeasureTheory

namespace KTaxi.Competitive.Supplement

universe u

/-- A general causal randomized policy: draw a private seed from an arbitrary probability
space, then respond to the visible history h and current query q. All private memory,
including continuous randomness and the entire random tape, can be encoded in the seed.
Measurability is required only in the private seed for each fixed h,q. -/
structure PrivatePolicy (H Q R : Type*) [MeasurableSpace R] where
  Seed : Type u
  seedSpace : MeasurableSpace Seed
  law : @Measure Seed seedSpace
  probability : @IsProbabilityMeasure Seed seedSpace law
  act : Seed → H → Q → R
  measurable_act : ∀ h q, @Measurable Seed R seedSpace _ (fun ω => act ω h q)

end KTaxi.Competitive.Supplement


