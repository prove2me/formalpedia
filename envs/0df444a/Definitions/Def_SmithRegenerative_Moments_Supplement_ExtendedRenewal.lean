-- Prove2me | Definitions.Def_SmithRegenerative_Moments_Supplement_ExtendedRenewal
-- name    : SmithRegenerative_Moments_Supplement_ExtendedRenewal
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T05:39:50.902056+00:00
-- url     : https://prove2.me/theorems/8d1b8229-783b-407c-9dd0-8e5f9d9c2e7e
-- title:
--   Improper delayed renewal intervals, finite laws, extended means and lattice spans
-- statement:
--   On a probability space with boundary parameter $z$, let $t_0,t_1,\ldots$ be independent random variables in $[0,\infty]$. The intervals after the first have a common law $F$ with $P(t_1=0)<1$; the first has law $K_z$. Infinite intervals represent an event that never occurs. Put
--   $$T_n=\sum_{i=0}^n t_i,\qquad n_t=\#\{n\ge0:T_n\le t\},\qquad \mu_1=\int u\,dF(u)\in[0,\infty].$$
--   The finite part of either law is a subprobability measure on the real line. Its missing mass is retained in the extended law and mean. A positive period is the greatest unshifted lattice span of its finite part. The last epoch is computed in the extended nonnegative reals and read as a real only at finite times. These objects extend the published proper-interval vocabulary without changing it.
--
--   **Formalization Note** Before the first event the last epoch is zero and unused; an infinite count is recorded as infinity on the renewal null event. The finite part of a law is restricted before applying `toReal`; an atom at infinity is never mapped to zero. The all-infinite law has no greatest span. The mean of the zero measure is zero; an infinite mean remains infinity.
-- source:
--   Smith, Regenerative stochastic processes, Proc. R. Soc. Lond. A 232(1188):6–31 (1955), DOI 10.1098/rspa.1955.0198, §2·1, p. 9; §3·2, pp. 12–13

import Mathlib
import Definitions.Def_SmithRegenerative_Equilibrium_Renewal

namespace SmithRegenerative.Moments.Supplement

open MeasureTheory ProbabilityTheory Filter Topology

/-- Smith (1955), §3·2, p. 13: intervals may be improper. Formalization Note:
`⊤` means that the next event never occurs. Its mass is retained in the mean and tail. -/
noncomputable def finiteLaw (D : Measure ENNReal) : Measure ℝ :=
  (D.restrict (Set.Iio ⊤)).map ENNReal.toReal

/-- Smith (1955), (2·1·1), p. 9, extended as allowed on p. 13.
Formalization Note: the mean includes the mass at infinity; no Bochner default is used. -/
noncomputable def extendedMean (D : Measure ENNReal) : ENNReal := ∫⁻ u, u ∂D

/-- Smith (1955), §2·2 and §3·3, pp. 10, 14. Formalization Note: this is
support of the finite part on the unshifted lattice; infinity is allowed separately. -/
def OnLattice (D : Measure ENNReal) (w : ℝ) : Prop :=
  ∀ᵐ u ∂D, u = ⊤ ∨ ∃ n : ℕ, u = ENNReal.ofReal ((n : ℝ) * w)

/-- Smith (1955), §2·2, p. 10: the greatest positive lattice span.
Formalization Note: the zero finite measure has no greatest span. -/
def HasPeriod (D : Measure ENNReal) (w : ℝ) : Prop :=
  0 < w ∧ OnLattice D w ∧ ∀ v : ℝ, 0 < v → OnLattice D v → v ≤ w

/-- Smith (1955), §3·3, p. 14: aperiodicity concerns the cycle law.
Formalization Note: it is distinct from failure of a joint cycle/delay period. -/
def Aperiodic (D : Measure ENNReal) : Prop := ¬ ∃ w : ℝ, HasPeriod D w

/-- Smith (1955), (2·1·3), p. 9. Formalization Note: sums are extended;
one infinite interval makes every later epoch infinite. -/
noncomputable def extEpoch {Ω : Type*} (τ : ℕ → Ω → ENNReal) (n : ℕ) (ω : Ω) : ENNReal :=
  ∑ i ∈ Finset.range (n + 1), τ i ω

/-- Smith (1955), (2·1·3), p. 9, count of events in [0,t].
Formalization Note: infinity is recorded on the null event of infinitely many renewals;
negative times have count zero. Infinite epochs never count. -/
noncomputable def extCount {Ω : Type*} (τ : ℕ → Ω → ENNReal) (t : ℝ) (ω : Ω) : ℕ∞ :=
  {n : ℕ | 0 ≤ t ∧ extEpoch τ n ω ≤ ENNReal.ofReal t}.encard

/-- Smith (1955), (3·4·1), p. 14, with the last-epoch index corrected.
Formalization Note: the supremum is in [0,∞], so it has no unbounded-set default;
it equals zero before the first event and is used only after that event. -/
noncomputable def extLast {Ω : Type*} (τ : ℕ → Ω → ENNReal) (t : ℝ) (ω : Ω) : ℝ :=
  (⨆ n : ℕ, if extEpoch τ n ω ≤ ENNReal.ofReal t then extEpoch τ n ω else 0).toReal

/-- Smith (1955), §2·1, p. 9 and §3·2, pp. 12–13: a delayed renewal process
allowing improper delays and cycles. Formalization Note: intervals live in [0,∞];
`F` and `K` are full probability laws, and their finite parts are subprobabilities.
`K(+∞)` in the paper means `K (Iio ⊤)`, not the mass of the whole extended space. -/
structure ExtendedRenewal (Ω Z : Type*) [MeasurableSpace Ω] where
  P : Z → Measure Ω
  probability : ∀ z, IsProbabilityMeasure (P z)
  F : Measure ENNReal
  cycle_probability : IsProbabilityMeasure F
  not_zero : F {0} < 1
  K : Z → Measure ENNReal
  τ : ℕ → Ω → ENNReal
  measurable : ∀ n, Measurable (τ n)
  independent : ∀ z, iIndepFun τ (P z)
  cycle_law : ∀ z n, (P z).map (τ (n + 1)) = F
  delay_law : ∀ z, (P z).map (τ 0) = K z

end SmithRegenerative.Moments.Supplement


