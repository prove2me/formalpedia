-- Prove2me | Definitions.Def_NondualStable_Optimization_Sampling
-- name    : NondualStable_Optimization_Sampling
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:44:29.989258+00:00
-- url     : https://prove2.me/theorems/d6ab4dd1-324c-4a9e-b9d7-b7198c5aab76
-- title:
--   Adaptive requests and feasible Gaussian Monte Carlo averages
-- statement:
--   For each requested body $K^t$, a fresh block of $N$ independent standard Gaussian vectors is read after that body is determined by the previous blocks. The exact sample is $Y^{t,j}=u_{K^t}(Z^{t,j})+v_{K^t}(Z^{t,j})$. Numerical samples are measurable functions of blocks already available and satisfy the source's deterministic feasible-solve requirement:
--   $$\hat Y^{t,j}\in K^t,\qquad \|\hat Y^{t,j}-Y^{t,j}\|_q\le E_{\rm sol}.$$
--   The exact empirical mean and the numerical selector are the averages of their respective $N$ samples. The request assumptions impose compact convex nonempty nesting and causal dependence on previous blocks. Joint measurability records the usual random-request convention. They do not assume a concentration, movement or running-time conclusion.
--
--   This representation permits adaptive requests, preserves fresh conditional Gaussian sampling, and distinguishes unconditional numerical feasibility from probabilistic sampling accuracy.
-- source:
--   David Martínez-Rubio, Cristóbal Guzmán, STOC 2027 submission #415 (October 2026), printed p. 11/PDF p. 12, Section 6 and (17)–(19); printed pp. 23–25/PDF pp. 24–26, (35)–(37)

import Definitions.Def_NondualStable_Optimization_GaussianCenter
import Definitions.Def_NondualStable_Optimization_RealMachine

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace NondualStable.Optimization

def sampleGaussian (d N t j : ℕ) (ω : Tape) : Vec d :=
  fun i => ω ((t * N + j) * d + i.val)

structure SampledRequests (d : ℕ) where
  request : ℕ → Tape → Set (Vec d)
  numerical : ℕ → ℕ → Tape → Vec d

noncomputable def empirical {d : ℕ} (p q : ℝ≥0∞) (R : ℝ) (H N : ℕ)
    (A : SampledRequests d) (t : ℕ) (ω : Tape) : Vec d :=
  (N : ℝ)⁻¹ • ∑ j ∈ Finset.range N,
    sample p q R H (A.request t ω) (sampleGaussian d N t j ω)

noncomputable def numericalAverage {d : ℕ} (N : ℕ) (A : SampledRequests d)
    (t : ℕ) (ω : Tape) : Vec d :=
  (N : ℝ)⁻¹ • ∑ j ∈ Finset.range N, A.numerical t j ω

/-- Requests depend only on earlier blocks of Gaussian samples. Joint
measurability is the usual random-request convention. Numerical error is a
deterministic feasible-solve specification, not a sampling success assumption. -/
def SamplingConditions {d : ℕ} (p q : ℝ≥0∞) (R Esol : ℝ) (H N : ℕ)
    (A : SampledRequests d) : Prop :=
  (∀ ω, Nested p R H (fun t => A.request t ω)) ∧
  (∀ t ≤ H, ∀ ω ω', (∀ i < t * N * d, ω i = ω' i) → A.request t ω = A.request t ω') ∧
  (∀ t ≤ H, Measurable (fun z : Tape × Vec d => optimizer p q R H (A.request t z.1) z.2)) ∧
  (∀ t ≤ H, ∀ j < N, Measurable (A.numerical t j)) ∧
  (∀ t ≤ H, ∀ j < N, ∀ ω ω', (∀ i < (t + 1) * N * d, ω i = ω' i) →
    A.numerical t j ω = A.numerical t j ω') ∧
  (∀ t ≤ H, ∀ j < N, ∀ ω,
    A.numerical t j ω ∈ A.request t ω ∧
    lpNorm q (A.numerical t j ω - sample p q R H (A.request t ω)
      (sampleGaussian d N t j ω)) ≤ Esol)

end NondualStable.Optimization


