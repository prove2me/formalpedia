-- Prove2me | Definitions.Def_SmithRegenerative_Moments_Renewal
-- name    : SmithRegenerative_Moments_Renewal
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:26:51.023613+00:00
-- url     : https://prove2.me/theorems/17fff931-5d37-434f-b97b-9559860e1bfe
-- title:
--   Renewal process with zero initial delay and its renewal count
-- statement:
--   Let $(\Omega,P)$ be a probability space and let $t_1,t_2,\ldots$ be measurable, nonnegative, independent and identically distributed cycle lengths. Their common law is not concentrated at zero. Put $T_0=0$ and $T_n=\sum_{i=1}^n t_i$. The renewal count $n_t$ counts the epochs $T_k\leq t$, including $T_0=0$, and the renewal function is
--
--   $$
--   H_U(t)=\mathbb E[n_t],\qquad U=\delta_0.
--   $$
--
--   The cycle mean is allowed to be infinite. This model supplies the renewal time and count used by every cumulative-process statement in this mission.
--
--   **Formalization Note** The count is the first index $n$ with $T_n>t$. If no such index exists, it is set to zero; under the stated nondegeneracy and i.i.d. assumptions this occurs only on a null event.
-- source:
--   Smith, Regenerative stochastic processes, Proc. R. Soc. Lond. A 232(1188):6–31 (1955), DOI 10.1098/rspa.1955.0198, p. 9, §2·1, (2·1·1)–(2·1·5); zero initial delay p. 23, §5·2

import Mathlib

namespace SmithRegenerative.Moments

open MeasureTheory
open ProbabilityTheory

/-- Smith (1955), §2·1, p. 9, (2·1·1)–(2·1·5), specialized to the zero initial
delay stipulated in §5·2, p. 23. The index `1` is the first cycle; index `0` of
`cycleLength` is unused. All random variables live on the same probability space.
Formalization Note: a renewal law need not have finite mean. -/
structure Renewal (Ω : Type*) [MeasurableSpace Ω] where
  P : Measure Ω
  probability : IsProbabilityMeasure P
  cycleLength : ℕ → Ω → ℝ
  measurable_cycle : ∀ i : ℕ, Measurable (cycleLength (i + 1))
  nonnegative_cycle : ∀ i : ℕ, ∀ᵐ ω ∂P, 0 ≤ cycleLength (i + 1) ω
  independent_cycle : iIndepFun (fun i : ℕ => cycleLength (i + 1)) P
  identical_cycle : ∀ i : ℕ,
    Measure.map (cycleLength (i + 1)) P = Measure.map (cycleLength 1) P
  not_all_zero : P {ω | cycleLength 1 ω = 0} < 1

/-- Smith (1955), p. 9, (2·1·3): `T₀ = 0` and `Tₙ = t₁ + ⋯ + tₙ`. -/
def Renewal.epoch {Ω : Type*} [MeasurableSpace Ω] (R : Renewal Ω)
    (n : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.Icc 1 n, R.cycleLength i ω

/-- Smith (1955), p. 9, (2·1·3): the number of renewal epochs in `[0,t]`.
Formalization Note: `Nat.sInf` is the first index whose epoch is after `t`;
it is `0` if no such index exists, an event of probability zero for Smith's
nondegenerate i.i.d. renewal process. In particular the epoch at zero counts. -/
noncomputable def Renewal.count {Ω : Type*} [MeasurableSpace Ω]
    (R : Renewal Ω) (t : ℝ) (ω : Ω) : ℕ :=
  sInf {n : ℕ | t < R.epoch n ω}

/-- Smith (1955), p. 9, (2·1·5): the renewal function `H_U(t) = E n_t`
for the initial delay `U = δ₀`. -/
noncomputable def Renewal.function {Ω : Type*} [MeasurableSpace Ω]
    (R : Renewal Ω) (t : ℝ) : ℝ :=
  MeasureTheory.integral R.P (fun ω => (R.count t ω : ℝ))

end SmithRegenerative.Moments


