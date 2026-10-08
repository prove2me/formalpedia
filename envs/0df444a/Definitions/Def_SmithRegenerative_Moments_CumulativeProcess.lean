-- Prove2me | Definitions.Def_SmithRegenerative_Moments_CumulativeProcess
-- name    : SmithRegenerative_Moments_CumulativeProcess
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:30:03.390994+00:00
-- url     : https://prove2.me/theorems/f7711109-be8f-4b28-9fd0-f2d232180ba4
-- title:
--   Cumulative process with joint cycle vectors and total variation
-- statement:
--   On the renewal process above, let $w_t$ be a real-valued measurable process with $w_0=0$. For cycle $n\geq1$, write $y_n=w_{T_n}-w_{T_{n-1}}$ and let $\tilde y_n$ be its total path variation on $[T_{n-1},T_n]$. A cumulative process has paths of bounded variation on every finite interval, almost surely. For the moment results, the vectors $(t_n,y_n,\tilde y_n)$ are independent and identically distributed across cycles; dependence among their three coordinates within a cycle is permitted. The overshoot reward is
--
--   $$
--   Y_t=\sum_{i=1}^{n_t+1}y_i.
--   $$
--
--   The mean cycle length and reward are $\mu_1=\mathbb E t_1$ and $\kappa_1=\mathbb E y_1$. This model provides the variation and covariance quantities needed for Smith's mean and variance limits.
--
--   **Formalization Note** The joint-vector reading records what Lemma 5's use of the common joint distribution of $(t_i,y_i)$ requires. Total variation is set to zero on the exceptional paths where it is infinite.
-- source:
--   Smith, Regenerative stochastic processes, Proc. R. Soc. Lond. A 232(1188):6–31 (1955), DOI 10.1098/rspa.1955.0198, pp. 22–24, §5·1–5·2, (C1)–(C2), (5·1·1), (5·2·1), and Lemma 5 proof

import Mathlib
import Definitions.Def_SmithRegenerative_Moments_Renewal

namespace SmithRegenerative.Moments

open MeasureTheory
open ProbabilityTheory

/-- Smith (1955), §5·1, pp. 22–23: the increment of `w` over cycle `n`.
The paper uses positive indices, so `n = 1` is the first cycle. -/
def cycleReward {Ω : Type*} [MeasurableSpace Ω] (R : Renewal Ω)
    (w : ℝ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  w (R.epoch n ω) ω - w (R.epoch (n - 1) ω) ω

/-- Smith (1955), p. 23, (5·1·1): variation over the nth cycle.
Formalization Note: `toReal` gives zero when variation is infinite; (C2) makes
that convention relevant only on a null set. -/
noncomputable def cycleVariation {Ω : Type*} [MeasurableSpace Ω]
    (R : Renewal Ω) (w : ℝ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  (eVariationOn (fun s => w s ω)
    (Set.Icc (R.epoch (n - 1) ω) (R.epoch n ω))).toReal

/-- Smith (1955), p. 23, (5·1·1): total variation of the path on `[0,t]`.
It is set to zero on paths with infinite variation, as permitted by the paper. -/
noncomputable def variationProcess {Ω : Type*} [MeasurableSpace Ω]
    (w : ℝ → Ω → ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  (eVariationOn (fun s => w s ω) (Set.Icc 0 t)).toReal

/-- Smith (1955), §5·1, pp. 22–23, (C1)–(C2), with the joint-cycle reading
used in Lemma 5 (p. 24). The vectors `(tₙ,yₙ,ỹₙ)` are i.i.d.; this does not
require reward and length within a cycle to be independent. -/
structure CumulativeProcess (Ω : Type*) [MeasurableSpace Ω] where
  renewal : Renewal Ω
  w : ℝ → Ω → ℝ
  measurable_w : ∀ s : ℝ, Measurable (w s)
  measurable_reward : ∀ i : ℕ,
    Measurable (cycleReward renewal w (i + 1))
  measurable_variation : ∀ i : ℕ,
    Measurable (cycleVariation renewal w (i + 1))
  zero_initial : ∀ᵐ ω ∂renewal.P, w 0 ω = 0
  bounded_variation : ∀ᵐ ω ∂renewal.P, ∀ s : ℝ,
    0 ≤ s → BoundedVariationOn (fun u => w u ω) (Set.Icc 0 s)
  independent_cycles : iIndepFun
    (fun i : ℕ => fun ω : Ω =>
      (renewal.cycleLength (i + 1) ω,
       cycleReward renewal w (i + 1) ω,
       cycleVariation renewal w (i + 1) ω)) renewal.P
  identical_cycles : ∀ i : ℕ,
    Measure.map (fun ω : Ω =>
      (renewal.cycleLength (i + 1) ω,
       cycleReward renewal w (i + 1) ω,
       cycleVariation renewal w (i + 1) ω)) renewal.P =
    Measure.map (fun ω : Ω =>
      (renewal.cycleLength 1 ω,
       cycleReward renewal w 1 ω,
       cycleVariation renewal w 1 ω)) renewal.P

/-- Smith (1955), p. 23, (5·2·1): `Y_t = ∑_{i=1}^{n_t+1} y_i`.
The upper limit deliberately remains `n_t+1` as printed. -/
noncomputable def CumulativeProcess.overshootReward {Ω : Type*}
    [MeasurableSpace Ω] (C : CumulativeProcess Ω) (t : ℝ) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.Icc 1 (C.renewal.count t ω + 1),
    cycleReward C.renewal C.w i ω

/-- Smith (1955), p. 23, (2·1·1), (5·1): first moments. -/
noncomputable def CumulativeProcess.meanLength {Ω : Type*}
    [MeasurableSpace Ω] (C : CumulativeProcess Ω) : ℝ :=
  ∫ ω, C.renewal.cycleLength 1 ω ∂C.renewal.P

noncomputable def CumulativeProcess.meanReward {Ω : Type*}
    [MeasurableSpace Ω] (C : CumulativeProcess Ω) : ℝ :=
  ∫ ω, cycleReward C.renewal C.w 1 ω ∂C.renewal.P

/-- Smith (1955), pp. 24, 28: `ρσ₁σ₂`, defined even if a variance vanishes. -/
noncomputable def CumulativeProcess.lengthRewardCovariance {Ω : Type*}
    [MeasurableSpace Ω] (C : CumulativeProcess Ω) : ℝ :=
  ProbabilityTheory.covariance (C.renewal.cycleLength 1)
    (cycleReward C.renewal C.w 1) C.renewal.P

end SmithRegenerative.Moments


