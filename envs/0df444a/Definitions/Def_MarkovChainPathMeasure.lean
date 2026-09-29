-- Prove2me | Definitions.Def_MarkovChainPathMeasure
-- name    : MarkovChainPathMeasure
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-08-15T14:35:41.240077+00:00
-- url     : https://prove2.me/theorems/de76f828-bd49-4d0e-b9f0-0e93d65677c1
-- title:
--   Chain law from an initial distribution, sample averages, and the CLT property
-- statement:
--   Three notions used throughout the mission, for a transition kernel $P$ on a state space $\mathsf{X}$.
--
--   (i) The **law of the chain**: for an initial distribution $\lambda$, the probability measure on the path space $\mathsf{X}^{\mathbb{N}}$ under which the coordinate at time $0$ has law $\lambda$ and transitions are governed by $P$ (the Ionescu–Tulcea construction).
--
--   (ii) The **sample average** of a function $f : \mathsf{X} \to \mathbb{R}$ along the first $n$ steps of a path:
--
--   $$
--   \bar f_n \;=\; \frac{1}{n} \sum_{i=1}^{n} f(X_i),
--   $$
--
--   the initial state $X_0$ not included, matching the source.
--
--   (iii) The **central limit theorem property** of the chain $(P, \pi)$ and functional $f$: there exists an asymptotic variance $\sigma^2 \ge 0$ such that for every initial distribution $\lambda$,
--
--   $$
--   \sqrt{n}\,\bigl(\bar f_n - E_\pi f\bigr) \xrightarrow{d} N(0, \sigma^2) \qquad (n \to \infty).
--   $$
--
--   The CLT property is the shared conclusion of the drift-condition theorems, the five corollaries, and the goal theorem of the mission.
--
--   **Formalization Note** The chain law is built by composing the platform's existing Markov-chain trajectory kernel (from the Gittins mission's Ionescu–Tulcea infrastructure) with the initial distribution. Convergence in distribution is weak convergence of laws; $N(0,0)$ is read as the point mass at $0$. In the CLT property the existential quantifier over $\sigma^2$ comes first, so one variance is shared by all initial distributions.
-- source:
--   G. L. Jones, "On the Markov Chain Central Limit Theorem", Probability Surveys 1 (2004) 299-320, arXiv math/0409112v2, Section 1 (arXiv v2 pp. 1-2), eq. (1)

import Definitions.Def_MarkovChainKernel
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
The law of a time-homogeneous Markov chain started from an initial
distribution, sample averages of a functional along the chain, and the Markov
chain central limit theorem property.

Source: Galin L. Jones, *On the Markov Chain Central Limit Theorem*,
Probability Surveys 1 (2004) 299-320 (arXiv math/0409112v2), §1: the sample
average `f̄_n` (Section 1) and the CLT of eq. (1).

Builds on the platform's Ionescu-Tulcea infrastructure
(`BanditAlgorithm.markovChainKernel`, itself built on
`BanditAlgorithm.markovChainStep` and `ProbabilityTheory.Kernel.traj`).
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

namespace MarkovChainCLT

/-- The law of the trajectory `(X₀, X₁, X₂, …)` of the time-homogeneous Markov chain
with transition kernel `P` and **initial distribution** `lam` (coordinate `0` has law
`lam`), as a measure on the path space `ℕ → X`.  Built from the platform's
Ionescu-Tulcea infrastructure: `BanditAlgorithm.markovChainKernel P` is the kernel
sending a starting point to the law of the trajectory from that point. -/
noncomputable def chainMeasure {X : Type*} [MeasurableSpace X] (P : Kernel X X)
    [IsMarkovKernel P] (lam : Measure X) : Measure (ℕ → X) :=
  (BanditAlgorithm.markovChainKernel P) ∘ₘ lam

instance chainMeasure.instIsProbabilityMeasure {X : Type*} [MeasurableSpace X]
    (P : Kernel X X) [IsMarkovKernel P] (lam : Measure X) [IsProbabilityMeasure lam] :
    IsProbabilityMeasure (chainMeasure P lam) :=
  inferInstanceAs (IsProbabilityMeasure ((BanditAlgorithm.markovChainKernel P) ∘ₘ lam))

/-- The sample average `f̄_n = n⁻¹ ∑_{i=1}^n f(X_i)` of a functional `f` along the
first `n` steps of a trajectory `ω` (the initial point `ω 0` is not included,
matching Jones 2004, Section 1). -/
noncomputable def sampleAvg {X : Type*} (f : X → ℝ) (n : ℕ) (ω : ℕ → X) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, f (ω (i + 1))

/-- `SatisfiesCLT P π f` says: there is an asymptotic variance `v ≥ 0` such that for
**every** initial distribution `lam`, under the chain law started from `lam`,
`√n (f̄_n - E_π f)` converges in distribution to `N(0, v)` (Jones 2004 eq. (1); the
degenerate case `v = 0` means convergence to the point mass at `0`). -/
def SatisfiesCLT {X : Type*} [MeasurableSpace X] (P : Kernel X X) [IsMarkovKernel P]
    (π : Measure X) (f : X → ℝ) : Prop :=
  ∃ v : ℝ≥0, ∀ (lam : Measure X) [IsProbabilityMeasure lam],
    TendstoInDistribution
      (fun (n : ℕ) (ω : ℕ → X) => Real.sqrt n * (sampleAvg f n ω - ∫ x, f x ∂π))
      atTop (id : ℝ → ℝ) (fun _ => chainMeasure P lam) (gaussianReal 0 v)

end MarkovChainCLT


