-- Prove2me | Definitions.Def_GradDOvS_Submod_Supplement_SimCost
-- name    : GradDOvS_Submod_Supplement_SimCost
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T11:16:41.324233+00:00
-- url     : https://prove2.me/theorems/ce92f296-e001-4124-bd1b-48e436ccfad9
-- title:
--   §2, pp. 9–14 — simulation models on [N]^d, the classes MC and MC_c, simulation-optimization algorithms, PGS and PCS-IZ, and the expected simulation cost T(O, M) (Definition 2)
-- statement:
--   The simulation-optimization framework of §2 of Zhang, Zheng and Lavaei on the decision space $\mathcal X = [N]^d$.
--
--   1. **Simulation models.** A model $M$ specifies, for every point $x \in \mathcal X$, the law $\nu_x$ of the simulation output $F(x,\xi_x)$; the objective is $f(x) = \mathbb E[F(x,\xi_x)]$. A model is a stochastic bandit whose $N^d$ arms are the points of $\mathcal X$.
--   2. **Model classes** (Definition 3, p. 14; Assumption 1, p. 10). $\mathcal{MC}(d,N,\sigma)$ is the set of models whose outputs are integrable and sub-Gaussian with parameter $\sigma^2$ about their means, $\mathbb E\, e^{\lambda(F(x,\xi_x) - f(x))} \le e^{\sigma^2\lambda^2/2}$ for all $\lambda$, and whose objective $f$ is L♮-convex on $\mathcal X$. $\mathcal{MC}_c$ is the subset of models whose objective has a unique minimizer $x^*$ with $f(x) - f(x^*) \ge c$ for every $x \ne x^*$.
--   3. **Algorithms** (§2.1, p. 11). A simulation-optimization algorithm consists of a sampling rule (the next point to simulate, chosen from the history of observations, possibly with internal randomization), a stopping rule $\tau$ that is a stopping time of the filtration of observations ($\tau$ is the number of simulations; $\tau = \infty$ means never stopping), and a recommendation rule (the returned point $\hat x$), measurable with respect to the history up to $\tau$. $\mathbb P_M$ and $\mathbb E_M$ denote the law of the observation sequence when the algorithm runs on model $M$.
--   4. **Guarantees** (p. 10). The algorithm is $(\epsilon,\delta)$-PGS on $M$ if it stops almost surely and
--   $$\mathbb P_M\big(\tau < \infty \text{ and } f(\hat x) \le \min_{\mathcal X} f + \epsilon\big) \ge 1 - \delta .$$
--   It is $(c,\delta)$-PCS-IZ on $M$ if it stops almost surely and, whenever $x^*$ is the unique minimizer with indifference zone $c$, $\mathbb P_M(\tau < \infty \text{ and } \hat x = x^*) \ge 1 - \delta$.
--   5. **Expected simulation cost** (Definition 1, p. 11; Definition 2, p. 12). For a guarantee $O$ and a class $\mathcal M$, an $(O,\mathcal M)$-algorithm is one that satisfies $O$ on every model of $\mathcal M$, and
--   $$T(O, \mathcal M) = \inf_{\mathcal A \text{ is } (O,\mathcal M)}\ \sup_{M \in \mathcal M} \mathbb E_M[\tau] \in [0,\infty] .$$
--   In particular $T(\epsilon,\delta,\mathcal{MC}) = T((\epsilon,\delta)\text{-PGS}, \mathcal{MC})$ and $T(\delta,\mathcal{MC}_c) = T((c,\delta)\text{-PCS-IZ}, \mathcal{MC}_c)$.
--
--   These definitions are the setting of the lower bounds of Theorems 5 and 6.
--
--   **Formalization Note** Models reuse the platform's `BanditAlgorithm.StochasticBandit`, sub-Gaussianity reuses `BanditAlgorithm.IsSubgaussianBandit` (Mathlib's `HasSubgaussianMGF` with proxy $\sigma^2$), and the interaction law, filtration and stopping times reuse `BanditAlgorithm.banditTrajMeasure` and `IsBanditStoppingTime` (Lattimore–Szepesvári §4.6, §33.2). Arms are indexed by `Fin (N^d)`; arm $a$ simulates the point obtained from the bijection `Fin (N^d) ≃ (Fin d → Fin N)` shifted to $\{1,\dots,N\}^d$. The sampling rule is a Markov kernel of the history, so randomized rules are included. The cost takes values in $[0,\infty]$ and an infimum over no algorithm is $\infty$. Probabilities of events are measures of the stated sets (outer measure if a set were not measurable).
-- source:
--   Zhang, Zheng & Lavaei, arXiv:2010.16250v3, p. 9 (f(x) = E[F(x, ξx)]), p. 10 (PGS, PCS-IZ, Assumption 1), p. 11 (Definition 1, sampling/stopping/recommendation rules), p. 12 (Definition 2), p. 14 (Definition 3, MC, MC_c), p. 15 (Assumption 3)

import Mathlib
import Definitions.Def_BanditTrajectory
import Definitions.Def_GradDOvS_Submod_Supplement_ConvexExt

open MeasureTheory ProbabilityTheory NNReal ENNReal

namespace GradDOvS.Submod.Supplement

/-! Zhang, Zheng & Lavaei, arXiv:2010.16250v3, §2 (pp. 9–14): simulation models on `X = [N]^d`, the
model classes `MC` and `MC_c` (Definitions 1 and 3), simulation-optimization algorithms (§2.1,
p. 11), the guarantees (ε, δ)-PGS and (c, δ)-PCS-IZ (p. 10) and the expected simulation cost
`T(O, M)` (Definition 2, p. 12).

A simulation model is a stochastic bandit (`BanditAlgorithm.StochasticBandit`) whose arms are the
`N^d` points of `X`: arm `a` returns draws of `F(x, ξ_x)` at the point `x = ptOf a`, and
`f(x) = E[F(x, ξ_x)]` is the arm mean. The interaction of a sampling rule with a model is the
platform's canonical bandit trajectory measure. -/

/-- The point of `X = [N]^d` simulated by arm `a ∈ Fin (N^d)`: the bijection
`Fin (N^d) ≃ (Fin d → Fin N)` (`finFunctionFinEquiv`) followed by the shift `{0,…,N-1} → {1,…,N}`. -/
def ptOf {d N : ℕ} (a : Fin (N ^ d)) : Fin d → ℤ :=
  fun i => (((finFunctionFinEquiv.symm a i : Fin N) : ℕ) : ℤ) + 1

/-- The class `MC = MC(X)` of Definition 3 (p. 14) under Assumption 1 (p. 10): simulation models on
`X = [N]^d` whose outputs `F(x, ξ_x)` are integrable and sub-Gaussian with parameter `σ²` about their
means, and whose objective `f(x) = E[F(x, ξ_x)]` is L♮-convex on `X`. -/
def MC (d N : ℕ) (σ : ℝ≥0) : Set (BanditAlgorithm.StochasticBandit (N ^ d)) :=
  {ν | BanditAlgorithm.IsSubgaussianBandit σ ν ∧
    ∃ f : (Fin d → ℤ) → ℝ, LNatConvexOn d N f ∧ ∀ a, BanditAlgorithm.banditArmMean ν a = f (ptOf a)}

/-- The class `MC_c` (Definition 3, p. 14; indifference zone, p. 10): models of `MC` with a unique
optimal point whose objective value is at least `c` smaller than every other objective value. -/
def MCc (d N : ℕ) (σ : ℝ≥0) (c : ℝ) : Set (BanditAlgorithm.StochasticBandit (N ^ d)) :=
  {ν | ν ∈ MC d N σ ∧ ∃ a, ∀ b, b ≠ a →
    BanditAlgorithm.banditArmMean ν a + c ≤ BanditAlgorithm.banditArmMean ν b}

/-- A simulation-optimization algorithm (§2.1, p. 11): a sampling rule (which point to simulate next,
as a Markov kernel of the past observations, so internal randomization is allowed), a stopping rule
`τ` (the number of simulations; `⊤` means "never stops") and a recommendation rule (the returned
point), both functions of the trajectory of observations. -/
structure SimOptAlg (d N : ℕ) where
  /-- The sampling rule. -/
  sampling : BanditAlgorithm.BanditPolicy (N ^ d)
  /-- The stopping rule: the number of simulations before stopping. -/
  stopping : (ℕ → Fin (N ^ d) × ℝ) → ℕ∞
  /-- The recommendation rule. -/
  recommend : (ℕ → Fin (N ^ d) × ℝ) → Fin (N ^ d)

namespace SimOptAlg

variable {d N : ℕ}

/-- The rules of §2.1, p. 11, are well formed: the stopping rule is a stopping time of the filtration
of the observations, and the recommendation is measurable with respect to the history up to the
stopping time. -/
def IsAdmissible (A : SimOptAlg d N) : Prop :=
  ∃ h : BanditAlgorithm.IsBanditStoppingTime A.stopping, Measurable[h.measurableSpace] A.recommend

/-- The law `ℙ_M` of the trajectory of observations of `A` on the model `ν`. -/
noncomputable def law (A : SimOptAlg d N) (ν : BanditAlgorithm.StochasticBandit (N ^ d)) :
    Measure (ℕ → Fin (N ^ d) × ℝ) :=
  BanditAlgorithm.banditTrajMeasure ν A.sampling

/-- The expected number of simulations `𝔼_M[τ]` of `A` on the model `ν`, in `[0, ∞]`. -/
noncomputable def expCost (A : SimOptAlg d N) (ν : BanditAlgorithm.StochasticBandit (N ^ d)) : ℝ≥0∞ :=
  ∫⁻ ω, (A.stopping ω : ℝ≥0∞) ∂(A.law ν)

/-- The (ε, δ)-PGS guarantee (p. 10) of `A` on the model `ν`: `A` stops almost surely (p. 11) and,
with probability at least `1 - δ`, it stops and returns a point whose objective value is at most
`ε` larger than the optimal objective value. -/
def IsPGS (A : SimOptAlg d N) (ε δ : ℝ) (ν : BanditAlgorithm.StochasticBandit (N ^ d)) : Prop :=
  (∀ᵐ ω ∂(A.law ν), A.stopping ω < ⊤) ∧
    ENNReal.ofReal (1 - δ) ≤ A.law ν {ω | A.stopping ω < ⊤ ∧ ∀ b,
      BanditAlgorithm.banditArmMean ν (A.recommend ω) ≤ BanditAlgorithm.banditArmMean ν b + ε}

/-- The (c, δ)-PCS-IZ guarantee (p. 10) of `A` on the model `ν`: `A` stops almost surely (p. 11) and,
if `a` is the unique optimal point with indifference zone `c`, then with probability at least
`1 - δ` it stops and returns `a`. -/
def IsPCSIZ (A : SimOptAlg d N) (c δ : ℝ) (ν : BanditAlgorithm.StochasticBandit (N ^ d)) : Prop :=
  (∀ᵐ ω ∂(A.law ν), A.stopping ω < ⊤) ∧
    ∀ a, (∀ b, b ≠ a → BanditAlgorithm.banditArmMean ν a + c ≤ BanditAlgorithm.banditArmMean ν b) →
      ENNReal.ofReal (1 - δ) ≤ A.law ν {ω | A.stopping ω < ⊤ ∧ A.recommend ω = a}

end SimOptAlg

/-- Definition 2, p. 12: the expected simulation cost
`T(O, 𝓜) = inf_{A is (O, 𝓜)} sup_{M ∈ 𝓜} 𝔼_M[τ]`, the infimum over the admissible algorithms that
satisfy the guarantee `O` on every model of `𝓜` (Definition 1, p. 11), in `[0, ∞]` (an empty
infimum is `∞`). -/
noncomputable def simCost {d N : ℕ}
    (guar : SimOptAlg d N → BanditAlgorithm.StochasticBandit (N ^ d) → Prop)
    (C : Set (BanditAlgorithm.StochasticBandit (N ^ d))) : ℝ≥0∞ :=
  ⨅ (A : SimOptAlg d N) (_ : A.IsAdmissible ∧ ∀ ν ∈ C, guar A ν), ⨆ ν ∈ C, A.expCost ν

/-- `T(ε, δ, MC) = T((ε, δ)-PGS, MC)` (p. 12). -/
noncomputable def costPGS (d N : ℕ) (σ : ℝ≥0) (ε δ : ℝ) : ℝ≥0∞ :=
  simCost (fun A ν => A.IsPGS ε δ ν) (MC d N σ)

/-- `T(δ, MC_c) = T((c, δ)-PCS-IZ, MC_c)` (p. 12). -/
noncomputable def costPCSIZ (d N : ℕ) (σ : ℝ≥0) (c δ : ℝ) : ℝ≥0∞ :=
  simCost (fun A ν => A.IsPCSIZ c δ ν) (MCc d N σ c)

end GradDOvS.Submod.Supplement


