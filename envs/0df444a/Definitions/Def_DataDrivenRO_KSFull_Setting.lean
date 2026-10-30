-- Prove2me | Definitions.Def_DataDrivenRO_KSFull_Setting
-- name    : DataDrivenRO_KSFull_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T14:32:16.522922+00:00
-- url     : https://prove2.me/theorems/bbc979ba-61b5-476f-9c47-d989e0503583
-- title:
--   Raw samples and exact finite-sample KS calibration
-- statement:
--   This module constructs the data-dependent objects for the complete independent-marginal KS theorem (§§1.1 and 5.1).
--
--   For $d,N\ge1$, the sample $S=(\hat u^1,\ldots,\hat u^N)$ is indexed by $\mathrm{Fin}\,N$, and its law is the actual product $(P^*)^N$. Supported samples have every observation in the closed box $[lo,hi]$. The padded array uses the increasing coordinate order statistics, including ties, with $lo_i$ and $hi_i$ at ranks zero and $N+1$. It reuses the published ordinary sorting map, without using that other module's KS statistic or region.
--
--   Uniform$[0,1]$ is Lebesgue measure restricted to the unit interval. For its $N$-fold product, set
--   $$
--   T_N(s)=\max_{1\le j\le N}\max\{j/N-s_{(j)},\ s_{(j)}-(j-1)/N\},\qquad
--   \Gamma^{KS}(N,\beta)=\inf\{t:\Pr(T_N\le t)\ge1-\beta\}.
--   $$
--   The marginal level is $\beta=1-(1-\alpha)^{1/d}$. A scalar sample is accepted for a Borel probability law $Q$ exactly when
--   $$
--   Q(({-\infty},s_{(j)}])\ge j/N-\Gamma,\qquad
--   Q(({-\infty},s_{(j)}))\le(j-1)/N+\Gamma\quad(j=1,\ldots,N).
--   $$
--   The marginal of $P$ is its pushforward under coordinate evaluation. The joint confidence region and uncertainty set are the published product region and exact entropy set (18), evaluated at the constructed array and threshold. The good event consists of supported samples accepted in every marginal. It does not depend on $\epsilon$.
--
--   These definitions construct the objects, without supplying calibration or coverage as data. Their correctness obligations appear as conclusions of the goal. The mathematical domain is $d,N\ge1$ and $0<\alpha,\beta,\epsilon<1$ where used. At $N=0$ the statistic is $0$; a real infimum can return its default value on empty or unbounded sets outside the significance domain. The goal excludes those inputs. No observations are projected or conditioned.
--
--   The p. 15 phrase “jth largest” is read as increasing order, as required by the CDF ranks, endpoints, (17), and (EC.4). The tabulated threshold is made explicit as its exact uniform-statistic quantile. These are the only new modeling choices; all confidence-region and entropy conventions remain those of the published compatible definitions.
-- source:
--   Bertsimas, Gupta & Kallus, Data-Driven Robust Optimization, arXiv:1401.0212v2, https://arxiv.org/abs/1401.0212v2, §1.1 p. 6 (PDF 6); §5.1 pp. 15–16 (PDF 15–16), (17)–(18); §2.2 pp. 8–9; increasing-order reading also EC.1.4 p. ec3 (PDF 41).

import Mathlib
import Definitions.Def_DataDrivenRO_KS_Setting
import Definitions.Def_DataDrivenRO_Guarantee_Setting
import Definitions.Def_RobustSAA_Univariate_Setting

open MeasureTheory

namespace DataDrivenRO.KSFull

/-- The actual N-fold iid sampling law (§1.1, p. 6), with no conditioning. -/
noncomputable def sampleLaw {d : ℕ} (P : Measure (Fin d → ℝ)) (N : ℕ) :
    Measure (Fin N → Fin d → ℝ) :=
  Measure.pi (fun _ : Fin N => P)

/-- Samples whose observations all lie in the known closed box (§5.1, p. 15). -/
def supportedSamples {d N : ℕ} (lo hi : Fin d → ℝ) : Set (Fin N → Fin d → ℝ) :=
  {S | ∀ r, S r ∈ Set.Icc lo hi}

/-- Increasing coordinate order statistics, including multiplicities, padded by the box ends.
The phrase "jth largest" on p. 15 is read as smallest, as required by its CDF constraints,
(17), and the proof's interval decomposition (EC.4). No clipping or conditioning is applied. -/
noncomputable def paddedOrder {d N : ℕ} (lo hi : Fin d → ℝ)
    (S : Fin N → Fin d → ℝ) (i : Fin d) (j : Fin (N + 2)) : ℝ :=
  if hz : j.val = 0 then lo i
  else if hj : j.val ≤ N then
    RobustSAA.Univariate.ord (fun r => S r i) ⟨j.val - 1, by omega⟩
  else hi i

/-- Uniform[0,1], the probability law used to calibrate the tabulated exact KS threshold. -/
noncomputable def uniform01 : Measure ℝ :=
  volume.restrict (Set.Icc (0 : ℝ) 1)

/-- N independent Uniform[0,1] observations. -/
noncomputable def uniformSampleLaw (N : ℕ) : Measure (Fin N → ℝ) :=
  Measure.pi (fun _ : Fin N => uniform01)

/-- The two-sided finite-sample uniform KS statistic. `r : Fin N` is source rank r+1.
For N=0 the real supremum over the empty index type is 0; the goal excludes N=0. -/
noncomputable def uniformStatistic {N : ℕ} (s : Fin N → ℝ) : ℝ :=
  ⨆ r : Fin N, max (((r : ℝ) + 1) / N - RobustSAA.Univariate.ord s r)
    (RobustSAA.Univariate.ord s r - (r : ℝ) / N)

/-- The exact finite-sample tabulated critical value at significance β (§5.1, p. 15).
Its definition does not assert coverage or quantile attainment. The goal establishes these
for N>0, 0<β<1; outside that domain real sInf can have a default value. -/
noncomputable def criticalValue (N : ℕ) (β : ℝ) : ℝ :=
  sInf {t : ℝ | ENNReal.ofReal (1 - β) ≤
    uniformSampleLaw N {s | uniformStatistic s ≤ t}}

/-- Exact marginal significance α′=1−(1−α)^(1/d), p. 15. Used only for d>0, 0<α<1. -/
noncomputable def marginalLevel (d : ℕ) (α : ℝ) : ℝ :=
  1 - (1 - α) ^ (1 / (d : ℝ))

/-- Marginal acceptance at a fixed threshold, using BOTH the closed and the left CDF.
This is the source's test, including for atoms, not the continuous-CDF test of RobustSAA. -/
def marginalAcceptance {N : ℕ} (Q : Measure ℝ) (Γ : ℝ) : Set (Fin N → ℝ) :=
  {s | ∀ r : Fin N,
    ENNReal.ofReal (((r : ℝ) + 1) / N - Γ) ≤
      Q (Set.Iic (RobustSAA.Univariate.ord s r)) ∧
    Q (Set.Iio (RobustSAA.Univariate.ord s r)) ≤
      ENNReal.ofReal ((r : ℝ) / N + Γ)}

/-- The coordinate marginal. Evaluation on a finite real product is measurable. -/
noncomputable def marginal {d : ℕ} (P : Measure (Fin d → ℝ)) (i : Fin d) : Measure ℝ :=
  Measure.map (fun u => u i) P

/-- The actual sample-dependent product confidence region, §5.1, p. 15. -/
noncomputable def confidenceRegion {d N : ℕ} (lo hi : Fin d → ℝ) (α : ℝ)
    (S : Fin N → Fin d → ℝ) : Set (Measure (Fin d → ℝ)) :=
  KS.productRegion (paddedOrder lo hi S) (criticalValue N (marginalLevel d α))

/-- Exactly set (18), with the actual sample and calibrated threshold. The published UI
retains finite KL through AbsCont; missing base support therefore cannot produce finite entropy. -/
noncomputable def uncertaintySet {d N : ℕ} (lo hi : Fin d → ℝ) (α : ℝ)
    (S : Fin N → Fin d → ℝ) (ε : ℝ) : Set (Fin d → ℝ) :=
  KS.UI (paddedOrder lo hi S) (criticalValue N (marginalLevel d α)) ε

/-- The supported-sample, all-coordinate KS acceptance event, independent of ε. -/
noncomputable def goodEvent {d N : ℕ} (P : Measure (Fin d → ℝ))
    (lo hi : Fin d → ℝ) (α : ℝ) : Set (Fin N → Fin d → ℝ) :=
  {S | S ∈ supportedSamples lo hi ∧ ∀ i,
    (fun r => S r i) ∈ marginalAcceptance (marginal P i)
      (criticalValue N (marginalLevel d α))}

end DataDrivenRO.KSFull


