-- Prove2me | Definitions.Def_ErlangA_Abandonment_Supplement_WaitingLaws
-- name    : ErlangA_Abandonment_Supplement_WaitingLaws
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T09:51:23.612451+00:00
-- url     : https://prove2.me/theorems/5b7dac4d-f072-4c13-ae00-bd4d2c87eae8
-- title:
--   Conditional waiting kernel and the two stationary-law candidates
-- statement:
--   For a system with $N\ge1$ agents, service rate $\mu>0$ and patience rate $\theta>0$, let $K_N(k)$ be the conditional potential-wait law given $k$ callers in the system. It is the point mass at zero when $k<N$. When $k=N+n$, it is the law of a sum of $n+1$ independent exponential variables:
--
--   $$K_N(N+n)=\mathcal L\!\left(\sum_{j=0}^{n} Z_j\right),\qquad Z_j\sim\operatorname{Exp}(N\mu+j\theta).$$
--
--   In particular, at $k=N$ there is one exponential interval, not a zero wait. Mix these laws against the published explicit stationary probabilities $\pi_k$ to define the candidate law $\eta_N=\sum_k\pi_kK_N(k)$ for $\upsilon_N(\infty)$. Define $r_\mu(x)=\max(x/\mu,0)$ and the candidate law $\eta=(r_\mu)_\#(f(x)\,dx)$ for $v(\infty)$, with $f$ the published `limitDensity`. Theorem 3 asserts normalization and actual long-time convergence for these candidates; they are not assumed to be invariant laws.
--
--   These measures encode the stationary part without constructing a random variable at an infinite time. Weak convergence is tested against every bounded continuous real function. The conditional kernel is used only for laws, while `Customers` defines the process through shared customer histories.
-- source:
--   Garnett, Mandelbaum & Reiman, Designing a Call Center with Impatient Customers, M&SOM 4(3), 2002, p. 222, Appendix B, conditional potential waiting law; pp. 217, 224–225, Theorem 3 and its proof

import Mathlib
import Definitions.Def_ErlangA_Abandonment_Model
import Definitions.Def_ErlangA_Staffing_Model

open MeasureTheory ProbabilityTheory Filter Topology

namespace ErlangA.Abandonment.Supplement

/-- Appendix B, p.222: zero if an agent is idle; otherwise the sum of `k-N+1`
independent exponential intervals, of rates `Nμ+jθ`, `j=0,…,k-N`. This is a law,
not a construction of joint waiting-time paths. The theorem excludes `N=0`. -/
noncomputable def waitKernel (N : ℕ) (μ θ : ℝ) (k : ℕ) : Measure ℝ :=
  if k < N then Measure.dirac 0 else
    (Measure.pi (fun j : Fin (k - N + 1) => expMeasure ((N : ℝ) * μ + (j : ℝ) * θ))).map
      (fun z => ∑ j : Fin (k - N + 1), z j)

/-- Explicit candidate for υ_N(∞), mixing the conditional kernel with the published π.
Probability and actual long-time convergence are conclusions of Theorem 3. -/
noncomputable def stationaryWaitLaw (N : ℕ) (lam μ θ : ℝ) : Measure ℝ :=
  Measure.sum (fun k => ENNReal.ofReal (ErlangA.Abandonment.stationaryDist N lam μ θ k) •
    waitKernel N μ θ k)

/-- Positive-part transformation v=[q/μ]⁺. -/
noncomputable def positiveWait (μ x : ℝ) : ℝ := max (x / μ) 0

/-- Explicit candidate for v(∞), the image of the published stationary diffusion density.
This definition does not assert normalization, invariance or convergence. -/
noncomputable def limitWaitLaw (β μ θ : ℝ) : Measure ℝ :=
  (volume.withDensity (fun x => ENNReal.ofReal (ErlangA.Staffing.limitDensity β μ θ x))).map
    (positiveWait μ)

/-- Weak convergence of finite real laws tested against every bounded continuous real
function. The theorem separately asserts that all candidate stationary laws are probabilities. -/
def WeakLawLimit {ι : Type*} (l : Filter ι) (laws : ι → Measure ℝ) (law : Measure ℝ) : Prop :=
  ∀ g : BoundedContinuousFunction ℝ ℝ,
    Tendsto (fun i => ∫ x, g x ∂(laws i)) l (𝓝 (∫ x, g x ∂law))

end ErlangA.Abandonment.Supplement


