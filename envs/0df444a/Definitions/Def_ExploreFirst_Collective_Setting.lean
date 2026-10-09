-- Prove2me | Definitions.Def_ExploreFirst_Collective_Setting
-- name    : ExploreFirst_Collective_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T23:03:08.532108+00:00
-- url     : https://prove2.me/theorems/ee6f1efb-468f-4893-91a3-cceaa8a75b38
-- title:
--   §1.1–§3.3, pp. 2–13 — models, kl (5), expected pull counts, optimal and worst arms, pairwise symmetry (Definition 3), the order ≼, monotonicity (Definition 4), and $\mathcal K^{\max}$
-- statement:
--   This file fixes the objects of the collective lower bound of Garivier, Ménard and Stoltz (Theorem 4, p. 13).
--
--   A **bandit problem** $\underline\nu=(\nu_a)_{a=1,\dots,K}$ is a family of $K$ probability distributions on $\mathbb R$, one per arm. Its means are $\mu_a=E(\nu_a)$ and $\mu^\star=\max_a\mu_a$. A **model** $\mathcal D$ is a set of distributions on $\mathbb R$; it is admissible when every member is a probability measure with an expectation, and $\underline\nu$ is **in** $\mathcal D$ when every $\nu_a\in\mathcal D$.
--
--   The file defines:
--
--   1. the **Bernoulli Kullback–Leibler divergence** of (5), $\mathrm{kl}(p,q)=p\ln\frac pq+(1-p)\ln\frac{1-p}{1-q}$, as the Kullback–Leibler divergence between the laws $p\,\delta_1+(1-p)\,\delta_0$ and $q\,\delta_1+(1-q)\,\delta_0$, with values in $[0,+\infty]$;
--   2. the **expected number of pulls** $\mathbb E_{\underline\nu}[N_{\psi,a}(T)]$ of arm $a$ in the first $T$ rounds, when the strategy $\psi$ interacts with $\underline\nu$;
--   3. the set $\mathcal A^\star(\underline\nu)=\{a:\mu_a=\mu^\star\}$ of **optimal arms**, with cardinality $A^\star_{\underline\nu}$, and the set $\mathcal W(\underline\nu)=\{w:\mu_w\le\mu_b\text{ for all }b\}$ of **worst arms**;
--   4. **pairwise symmetry for optimal arms on $\mathcal D$** (Definition 3, p. 11): for every $\underline\nu$ in $\mathcal D$ and every pair of optimal arms $a^\star,a_\star$ with $\nu_{a^\star}=\nu_{a_\star}$, for all $T\ge1$, the pairs $(N_{\psi,a^\star}(T),N_{\psi,a_\star}(T))$ and $(N_{\psi,a_\star}(T),N_{\psi,a^\star}(T))$ have the same distribution;
--   5. the **partial order** $\underline\nu'\preccurlyeq\underline\nu$ (p. 13): $\nu_a=\nu'_a$ for every $a\in\mathcal A^\star(\underline\nu)$ and $E(\nu'_a)\le E(\nu_a)$ for every $a\notin\mathcal A^\star(\underline\nu)$;
--   6. **monotonicity on $\mathcal D$** (Definition 4, p. 13): for all bandit problems $\underline\nu'\preccurlyeq\underline\nu$ in $\mathcal D$ and all $T\ge1$,
--   $$\sum_{a^\star\in\mathcal A^\star(\underline\nu')}\mathbb E_{\underline\nu'}\big[N_{\psi,a^\star}(T)\big]\ \ge\ \sum_{a^\star\in\mathcal A^\star(\underline\nu)}\mathbb E_{\underline\nu}\big[N_{\psi,a^\star}(T)\big];$$
--   7. the quantity of Theorem 4,
--   $$\mathcal K^{\max}_{\underline\nu}=\min_{w\in\mathcal W(\underline\nu)}\ \max_{a^\star\in\mathcal A^\star(\underline\nu)}\mathrm{KL}(\nu_w,\nu_{a^\star})\in[0,+\infty].$$
--
--   These are the hypotheses and the constant of the collective lower bound, which says that a symmetric, monotonic strategy must pull the suboptimal arms a linear number of times while $T$ is small compared with $K/(A^\star\mathcal K^{\max})$.
--
--   **Formalization Note** Arms are indexed by `Fin K`, so the paper's arm $a\in\{1,\dots,K\}$ is index $a-1$. Strategies are the published kernel policies `BanditPolicy`, which induce the same laws of arms and rewards as the paper's strategies with auxiliary uniform randomization. Definitions 3 and 4 leave $T$ implicit; both are read "for all $T\ge1$". $\mathrm{kl}$, $\mathrm{KL}$ and $\mathcal K^{\max}$ take values in $[0,+\infty]$. $\mathcal K^{\max}$ is computed with the lattice infimum and supremum over finite sets; when $K\ge1$ both sets are nonempty and these are the paper's min and max. The shared layer (`IsModel`, `InModel`, `bernoulliLaw`, `klBer`, `expPulls`, `optimalArms`) has the same names and bodies in every mission of this series, and `IsPairwiseSymmetric` is the same as in mission IV.
-- source:
--   Garivier, Ménard, Stoltz, Explore First, Exploit Next, arXiv:1602.07182v3, pp. 2–3 §1.1, p. 3 §1.2, p. 6 (5), p. 11 Definition 3, p. 13 §3.3 (𝒜⋆, 𝒲, ≼, Definition 4, 𝒦^max in Theorem 4)

import Mathlib
import Definitions.Def_BanditPolicy
import Definitions.Def_ExploreFirst_Asymptotic_Setting
import Definitions.Def_ExploreFirst_FundIneq_Setting
import Definitions.Def_ExploreFirst_Relative_Setting

namespace ExploreFirst.Collective

open MeasureTheory ProbabilityTheory BanditAlgorithm
open scoped ENNReal

/-- The set `𝒲(ν)` of worst arms (§3.3, p. 13): the arms with the smallest mean. -/
noncomputable def worstArms {K : ℕ} (ν : StochasticBandit K) : Finset (Fin K) :=
  Finset.univ.filter (fun a => ∀ b, banditArmMean ν a ≤ banditArmMean ν b)

/-- The partial order `ν' ≼ ν` of §3.3, p. 13: `ν'` has the same distributions as `ν` at the
optimal arms of `ν`, and means no larger than those of `ν` at the other arms. -/
def Precedes {K : ℕ} (ν' ν : StochasticBandit K) : Prop :=
  (∀ a ∈ ExploreFirst.Asymptotic.optimalArms ν, ν.P a = ν'.P a) ∧
    (∀ a ∉ ExploreFirst.Asymptotic.optimalArms ν, banditArmMean ν' a ≤ banditArmMean ν a)

/-- Definition 4, p. 13: `ψ` is monotonic on `𝒟` if for all bandit problems `ν' ≼ ν` in `𝒟` and
all `T ≥ 1`, `∑_{a ∈ 𝒜⋆(ν')} 𝔼_{ν'}[N_a(T)] ≥ ∑_{a ∈ 𝒜⋆(ν)} 𝔼_ν[N_a(T)]`. -/
def IsMonotonic {K : ℕ} (𝒟 : Set (Measure ℝ)) (π : BanditPolicy K) : Prop :=
  ∀ ν ν' : StochasticBandit K, ExploreFirst.Asymptotic.InModel 𝒟 ν → ExploreFirst.Asymptotic.InModel 𝒟 ν' → Precedes ν' ν → ∀ T : ℕ, 1 ≤ T →
    ∑ a ∈ ExploreFirst.Asymptotic.optimalArms ν, ExploreFirst.FundIneq.expPulls ν π T a ≤ ∑ a ∈ ExploreFirst.Asymptotic.optimalArms ν', ExploreFirst.FundIneq.expPulls ν' π T a

/-- `𝒦^max_ν = min_{w ∈ 𝒲(ν)} max_{a⋆ ∈ 𝒜⋆(ν)} KL(ν_w, ν_{a⋆})` (Theorem 4, p. 13), in `[0, ∞]`. -/
noncomputable def kMax {K : ℕ} (ν : StochasticBandit K) : ℝ≥0∞ :=
  (worstArms ν).inf (fun w => (ExploreFirst.Asymptotic.optimalArms ν).sup (fun a => InformationTheory.klDiv (ν.P w) (ν.P a)))

end ExploreFirst.Collective


