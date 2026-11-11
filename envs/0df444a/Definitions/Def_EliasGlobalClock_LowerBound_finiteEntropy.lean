-- Prove2me | Definitions.Def_EliasGlobalClock_LowerBound_finiteEntropy
-- name    : EliasGlobalClock_LowerBound_finiteEntropy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:03:21.93401+00:00
-- url     : https://prove2.me/theorems/c4c48f4b-507c-4a88-aa4b-9a1afe956673
-- title:
--   Entropy in nats of an arbitrary finite probability law
-- statement:
--   For a probability mass function $\mu$ on any finite set $S$, define entropy using natural logarithms:
--
--   $$H(\mu)=-\sum_{z\in S}\mu(z)\ln\mu(z),\qquad 0\ln0=0.$$
--
--   Mathlib's probability mass function supplies nonnegative masses with total mass one; the masses may be irrational and may vanish. On a finite set every mass is finite, so conversion to real numbers loses no values. The logarithm at zero yields precisely the stated zero-mass convention.
--
--   This definition applies equally to a heterogeneous finite product and each coordinate marginal. It imposes no independence or uniform finite-source assumption and can be reused for finite-law entropy arguments beyond leader election.
-- source:
--   Kuowen Chen, Shengquan Du, Tsvi Kopelowitz, Seth Pettie, Ben Plosk, STOC 2027 submission #1311 (October 2026), printed pp.10, 36, PDF pp.11, 37, entropy convention, Fact D.2; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1311.pdf

import Mathlib

open scoped BigOperators

namespace EliasGlobalClock.LowerBound

/-- Entropy in nats for an arbitrary finite PMF; real masses need not be rational.
Real.log 0=0 gives precisely the source convention 0 ln 0=0. -/
noncomputable def finiteEntropy {α : Type*} [Fintype α] (μ : PMF α) : ℝ :=
  -∑ a, (μ a).toReal * Real.log (μ a).toReal

end EliasGlobalClock.LowerBound


