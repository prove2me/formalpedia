-- Prove2me | Definitions.Def_ReedGGN_RenewalRep_RenewalFunction
-- name    : ReedGGN_RenewalRep_RenewalFunction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T19:18:55.844645+00:00
-- url     : https://prove2.me/theorems/c75708ac-c28a-4460-a065-de105b3293f6
-- title:
--   The renewal measure dM = Σₙ≥₁ F^{∗n} and the renewal function M(t) (p. 29)
-- statement:
--   Let $\mu$ be a probability measure on $\mathbb R$ (the law of the interarrival times of a pure renewal process; in the paper, the service-time law $F$).
--
--   1. The **convolution powers** of $\mu$ are $\mu^{*0}=\delta_0$ and $\mu^{*(n+1)}=\mu^{*n}*\mu$. If $\eta_1,\eta_2,\dots$ are i.i.d. with law $\mu$, then $\mu^{*n}$ is the law of $S_n=\eta_1+\dots+\eta_n$.
--   2. The **renewal measure** is
--   $$dM=\sum_{n\ge 1}\mu^{*n},$$
--   a measure on $\mathbb R$ with values in $[0,\infty]$.
--   3. The **renewal function** is $M(t)=dM((-\infty,t])=\sum_{n\ge1}F^{*n}(t)$.
--
--   The paper defines $M(t)$ as "the expected number of renewals by time $t$", i.e. $\mathbb E\,\#\{n\ge1:S_n\le t\}=\sum_{n\ge 1}\mathbb P(S_n\le t)$, which is the formula above by Tonelli's theorem. The measure $dM$ is the integrator of the Stieltjes integrals $\int_0^t\cdots dM(u)$ in (5.41)–(5.45).
--
--   **Formalization Note** The renewal measure is defined directly as the sum of convolution powers, without constructing an i.i.d. sequence. $M(t)$ is the real number obtained from the extended value $dM((-\infty,t])$; when that value is $+\infty$ the real conversion gives $0$, so finiteness of $dM$ on bounded sets is stated separately where it is needed (milestone (5.39)). When $\mu(\{0\})>0$, $dM$ has an atom at $0$ of mass $\mu(\{0\})/(1-\mu(\{0\}))$, which is why every $dM$-integral of the mission is taken over the closed interval $[0,t]$.
-- source:
--   Reed, The G/GI/N Queue in the Halfin–Whitt Regime, arXiv:0912.2837v1, p. 29, §5.5 (renewal function M)

import Mathlib

namespace ReedGGN.RenewalRep

open MeasureTheory

/-- Convolution powers of a measure on `ℝ`: `μ^{∗0} = δ₀` and `μ^{∗(n+1)} = μ^{∗n} ∗ μ`
(additive convolution of measures). For the law `μ` of an i.i.d. sequence `η₁, η₂, …`,
`μ^{∗n}` is the law of `S_n = η₁ + ⋯ + η_n`. -/
noncomputable def convPow (μ : Measure ℝ) : ℕ → Measure ℝ
  | 0 => Measure.dirac 0
  | n + 1 => (convPow μ n).conv μ

/-- The renewal measure `dM = ∑_{n ≥ 1} μ^{∗n}` of the pure renewal process with interarrival
law `μ` (p. 29). Its value on `(-∞, t]` is `∑_{n≥1} P(S_n ≤ t)`, the expected number of renewals
by time `t` (Tonelli). It may be `∞` on a set; it is finite on bounded sets when `μ` is
carried by `[0, ∞)` with `μ {0} < 1`. An atom of `μ` at `0` gives `dM` an atom at `0`. -/
noncomputable def renewalMeasure (μ : Measure ℝ) : Measure ℝ :=
  Measure.sum (fun n : ℕ => convPow μ (n + 1))

/-- The renewal function `M(t) = dM((-∞, t])`, the expected number of renewals by time `t`
(p. 29), as a real number. `toReal` returns `0` if the value is `∞`; statements that need
finiteness state it separately. -/
noncomputable def renewalFn (μ : Measure ℝ) (t : ℝ) : ℝ :=
  (renewalMeasure μ (Set.Iic t)).toReal

end ReedGGN.RenewalRep


