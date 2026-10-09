-- Prove2me | Definitions.Def_ExploreFirst_Absolute_Setting
-- name    : ExploreFirst_Absolute_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T22:11:32.764746+00:00
-- url     : https://prove2.me/theorems/4a6ed2c7-b00c-4379-a495-065298a7012c
-- title:
--   Bandit model, Bernoulli divergence, expected pulls, and Definition 2
-- statement:
--   Fix a finite collection of arms, each with a probability law on the real line. A model $\mathcal D$ is a set of probability laws with finite expectations, and a bandit problem $\underline\nu$ belongs to it when every arm law $\nu_a$ lies in $\mathcal D$. Write $\mu_a$ for an arm's mean and $\mu^*=\max_a\mu_a$; the optimal arms are those with $\mu_a=\mu^*$.
--
--   The expected pull count $\mathbb E_{\underline\nu}[N_{\psi,a}(T)]$ is the expectation of the number of selections of arm $a$ in the first $T$ rounds under strategy $\psi$. Bernoulli $\mathrm{kl}(p,q)$ is the Kullback–Leibler divergence of Bernoulli laws with parameters $p$ and $q$, including its infinite boundary values.
--
--   Definition 2 calls $\psi$ smarter than uniform on $\mathcal D$ when, for every bandit problem in $\mathcal D$, every optimal arm $a^*$, and every integer $T\ge1$,
--   $$\mathbb E_{\underline\nu}[N_{\psi,a^*}(T)]\ge T/K.$$
--
--   These definitions set the admissible model and strategy class for the absolute lower bound.
--
--   **Formalization Note** Arms are indexed from zero in Lean. Strategies are stochastic kernels on observed histories; this gives the same arm and reward histories as the paper's auxiliary uniforms. Bernoulli divergence takes values in $[0,+\infty]$.
-- source:
--   Garivier, Ménard, Stoltz, Explore First, Exploit Next, arXiv:1602.07182v3, pp. 2–4, 6, 10, §1.1, §1.2, (5), Definition 2

import Mathlib
import Definitions.Def_BanditPolicy
import Definitions.Def_ConsistentBanditPolicy
import Definitions.Def_ExploreFirst_Asymptotic_Setting
import Definitions.Def_ExploreFirst_FundIneq_Setting

open MeasureTheory

namespace ExploreFirst.Absolute

/-- Garivier–Ménard–Stoltz, Definition 2: every optimal arm receives at least uniform expected allocation. -/
def IsSmarterThanUniform {K : ℕ} (𝒟 : Set (Measure ℝ))
    (π : BanditAlgorithm.BanditPolicy K) : Prop :=
  ∀ ν : BanditAlgorithm.StochasticBandit K, ExploreFirst.Asymptotic.InModel 𝒟 ν →
    ∀ a : Fin K, a ∈ ExploreFirst.Asymptotic.optimalArms ν → ∀ T : ℕ, 1 ≤ T →
      (T : ℝ) / K ≤ ExploreFirst.FundIneq.expPulls ν π T a

end ExploreFirst.Absolute


