-- Prove2me | Definitions.Def_TTTSampling_tvDist
-- name    : TTTSampling_tvDist
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:36:13.706942+00:00
-- url     : https://prove2.me/theorems/057cffd1-3aa1-495f-9f03-29a309041ea6
-- title:
--   Total variation distance, probability of an event, expectation
-- statement:
--   For distributions $p,q$ on a finite set $B$, the **total variation distance** is
--
--   $$
--   D_{\mathrm{TV}}(p,q)=\frac12\sum_{b\in B}|p(b)-q(b)| \;=\;\max_{A\subseteq B}|p(A)-q(A)|.
--   $$
--
--   The module also fixes two pieces of notation used throughout: $\mathbb P_p(E)$, the probability of an event $E$ under $p$, and $\mathbb E_p[f]=\sum_b p(b)f(b)$, the expectation of a real function.
--
--   **Formalization Note** The expectation is a series; every expectation taken in this mission is of a function bounded on the support of a probability distribution, so the series converges absolutely.
-- source:
--   Golowich, Moitra, Rohatgi, The Power of Test-Time Training for Approximate Sampling, arXiv:2606.11437 (version of November 3, 2026), Theorem 3.2, p.18 (PDF p.20) and Lemma 3.14, p.29 (PDF p.31)

import Mathlib

namespace TTTSampling

/-- **Total variation distance** `D_TV(p, q) = ½ Σ_b |p(b) − q(b)|` of two distributions on a
finite type.

Golowich, Moitra, Rohatgi, arXiv:2606.11437 (version of November 3, 2026), used in Theorem 3.2,
printed p.18 (PDF p.20), and Lemma 3.14, p.29 (PDF p.31). On a finite type this equals
`max_A |p(A) − q(A)|`, the form used in the proof of Lemma 3.14. -/
noncomputable def tvDist {β : Type} [Fintype β] (p q : PMF β) : ℝ :=
  (1 / 2) * ∑ b : β, |(p b).toReal - (q b).toReal|

/-- The probability `ℙ_p(E)` of an event `E`, as a real number in `[0, 1]`. -/
noncomputable def prob {β : Type} (p : PMF β) (E : β → Prop) : ℝ :=
  (p.toOuterMeasure {b | E b}).toReal

/-- The expectation `𝔼_p[f] = Σ_b p(b)·f(b)` of a real function under a distribution.

**Formalization Note** Written as a `tsum`. Every expectation taken in this mission is of a
function that is bounded on the support of the distribution (counts of particles, of nodes, and
ratios bounded through Assumption 3.1), and `Σ_b p(b) = 1`, so the series converges absolutely and
the `tsum` is the true expectation, never a junk value. -/
noncomputable def expect {β : Type} (p : PMF β) (f : β → ℝ) : ℝ :=
  ∑' b : β, (p b).toReal * f b

end TTTSampling


