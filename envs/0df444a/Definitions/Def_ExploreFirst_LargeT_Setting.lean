-- Prove2me | Definitions.Def_ExploreFirst_LargeT_Setting
-- name    : ExploreFirst_LargeT_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T22:11:37.354551+00:00
-- url     : https://prove2.me/theorems/aea0f047-4a1a-4fe7-81c1-bf2651e72869
-- title:
--   §1.1–§4.1 — models, Bernoulli divergence, expected pulls, well-behavedness, super-fast convergence, and hardness
-- statement:
--   A stochastic bandit problem has finitely many arms, each with a probability law on the real rewards. A model $\mathcal D$ is a collection of probability laws with a finite first moment. A problem belongs to $\mathcal D$ when each arm law does. For a strategy $\psi$, $\mathbb E_{\underline\nu}[N_{\psi,a}(T)]$ is the expected number of pulls of arm $a$ in the first $T$ rounds. Optimal arms have mean $\mu^*$, and $H(\underline\nu)=\sum_{a:\Delta_a>0}\Delta_a^{-2}$, where $\Delta_a=\mu^*-\mu_a$.
--
--   The set $E(\mathcal D)$ is the interior of the set of means of laws in $\mathcal D$. A model is **well behaved** with witnesses $\varepsilon_{\mathcal D}$ and $\omega_{\mathcal D}$ when they are positive on their stated domains and, for $P\in\mathcal D$, $x\in E(\mathcal D)$ with $\mathrm E(P)<x$, and $0<\varepsilon<\varepsilon_{\mathcal D}(x)$,
--   $$
--   \mathcal K_{\inf}(P,x+\varepsilon,\mathcal D)\le\mathcal K_{\inf}(P,x,\mathcal D)+\varepsilon\omega_{\mathcal D}(P,x).
--   $$
--   A strategy is **uniformly super-fast convergent** with constant $C_{\psi,\mathcal D}$ when every problem in $\mathcal D$, every suboptimal arm, and every $T\ge2$ satisfy $\mathbb E[N_{\psi,a}(T)]\le C_{\psi,\mathcal D}\ln T/\Delta_a^2$. The same constant works for all problems, arms, and horizons. Bernoulli divergence $\mathrm{kl}$ is the Kullback–Leibler divergence between Bernoulli laws, including infinite boundary values.
--
--   These definitions give the shared data and domains of Theorem 5 and its intermediate bounds.
--
--   **Formalization Note** Arms are indexed from zero in Lean. Strategies are Markov kernels on observed histories. The witness functions are total, but their values are constrained only on $E(\mathcal D)$ and $\mathcal D\times E(\mathcal D)$. The paper's $\forall\varepsilon<\varepsilon_{\mathcal D}(x)$ is read as $0<\varepsilon<\varepsilon_{\mathcal D}(x)$.
-- source:
--   Garivier, Ménard, Stoltz, Explore First, Exploit Next, arXiv:1602.07182v3, pp. 2–4, 6, 15–17, §1.1, §1.2, (5), Definitions 5–6, (16)

import Mathlib
import Definitions.Def_BanditPolicy
import Definitions.Def_ConsistentBanditPolicy
import Definitions.Def_ExploreFirst_Asymptotic_Setting
import Definitions.Def_ExploreFirst_FundIneq_Setting

namespace ExploreFirst.LargeT

open MeasureTheory BanditAlgorithm
open scoped ENNReal

/-- Interior of the set of means attainable in the model, denoted `E(𝒟)`. -/
noncomputable def expectationInterior (𝒟 : Set (Measure ℝ)) : Set ℝ :=
  interior ((fun P : Measure ℝ => ∫ y, y ∂P) '' 𝒟)

/-- Definition 5 with its positive witnesses on their stated domains. -/
def IsWellBehaved (𝒟 : Set (Measure ℝ))
    (εD : ℝ → ℝ) (ωD : Measure ℝ → ℝ → ℝ) : Prop :=
  (∀ x ∈ expectationInterior 𝒟, 0 < εD x) ∧
  (∀ P ∈ 𝒟, ∀ x ∈ expectationInterior 𝒟, 0 < ωD P x) ∧
  (∀ P ∈ 𝒟, ∀ x ∈ expectationInterior 𝒟,
    (∫ y, y ∂P) < x → ∀ ε : ℝ, 0 < ε → ε < εD x →
      banditDInf 𝒟 P (x + ε) ≤
        banditDInf 𝒟 P x + ENNReal.ofReal (ε * ωD P x))

/-- Definition 6, with one constant uniform over problems, arms and horizons. -/
def IsUniformlySuperFast {K : ℕ} (𝒟 : Set (Measure ℝ))
    (π : BanditPolicy K) (C : ℝ) : Prop :=
  ∀ ν : StochasticBandit K, ExploreFirst.Asymptotic.InModel 𝒟 ν →
    ∀ a : Fin K, 0 < banditGap ν a →
      ∀ T : ℕ, 2 ≤ T →
        ExploreFirst.FundIneq.expPulls ν π T a ≤ C * Real.log T / (banditGap ν a) ^ 2

/-- The sum `H(ν)` of squared inverse gaps over suboptimal arms, (16). -/
noncomputable def hardness {K : ℕ} (ν : StochasticBandit K) : ℝ :=
  ∑ a ∈ (ExploreFirst.Asymptotic.optimalArms ν)ᶜ, 1 / (banditGap ν a) ^ 2

end ExploreFirst.LargeT


