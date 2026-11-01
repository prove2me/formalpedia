-- Prove2me | Definitions.Def_MaxObjBandit_BanditInstance
-- name    : MaxObjBandit_BanditInstance
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:33:11.495287+00:00
-- url     : https://prove2.me/theorems/d8da2790-12b9-4d32-9930-4273028fa0d2
-- title:
--   Bandit instances $\boldsymbol\nu\in\mathcal V$, means, the reward table and $\log^+$
-- statement:
--   A **bandit instance** with $K$ arms is a $K$-tuple $\boldsymbol\nu=(\nu_1,\dots,\nu_K)$ of probability distributions on $\mathbb R$, each supported in $[0,1]$; $\mathcal V$ is the set of all of them. The **mean** of arm $i$ is $\mu_i=\int x\,d\nu_i(x)$.
--
--   The rewards are modelled by a **reward table** $(U^i_n)_{i\le K,\,n\ge1}$: $U^i_n$ is the reward of the $n$-th pull of arm $i$. Its law is the product measure under which all entries are independent and $U^i_n\sim\nu_i$. Finally, for $a>0$,
--   $$
--   \log^+(a)=\log\big(\max(a,1)\big).
--   $$
--
--   These are the primitives of the max-objective bandit model of §2.
--
--   **Formalization Note** Arms are `Fin K` (paper arm $i$ is index $i-1$). The reward table is a function `Fin K → ℕ → ℝ` with `ω i n` $=U^i_{n+1}$, and its law is `Measure.infinitePi` of `Measure.infinitePi` of the $\nu_i$. The arms are not assumed sorted by mean.
-- source:
--   Ozbay, Kamble, Maximal Objectives in the Multi-armed Bandit with Applications, arXiv:2006.06853v6, §2, p.15 (V, means), p.16 (U^i_n); footnote 2, p.22 (log⁺)

import Mathlib

open MeasureTheory ProbabilityTheory

namespace MaxObjBandit

/-- A `K`-armed bandit instance `ν = (ν₁, …, ν_K) ∈ 𝒱`: a `K`-tuple of probability distributions
on `ℝ`, each with support in `[0,1]` (Ozbay, Kamble, *Maximal Objectives in the Multi-armed Bandit
with Applications*, arXiv:2006.06853v6, §2, p.15: "We deﬁne V to be the set of all K-tuples of
distributions for the K arms having support in [0,1]").

**Formalization Note** Arms are `Fin K`; paper arm `i` is index `i − 1`. "Support in `[0,1]`" is
`ν i [0,1] = 1`; nothing else (no density, no atoms excluded) is assumed. The arms are not
assumed sorted by mean. -/
structure BanditInstance (K : ℕ) where
  /-- The reward distribution `νᵢ` of arm `i`. -/
  dist : Fin K → Measure ℝ
  /-- Each `νᵢ` is a probability measure. -/
  [isProb : ∀ i, IsProbabilityMeasure (dist i)]
  /-- Each `νᵢ` is supported in `[0,1]`. -/
  support : ∀ i, dist i (Set.Icc 0 1) = 1

attribute [instance] BanditInstance.isProb

/-- The mean `µᵢ = ∫ x dνᵢ(x)` of arm `i` (arXiv:2006.06853v6, §2, p.15). -/
noncomputable def BanditInstance.mean {K : ℕ} (ν : BanditInstance K) (i : Fin K) : ℝ :=
  ∫ x, x ∂(ν.dist i)

/-- The reward table `(Uⁱₙ)`: `ω i n` is the reward `Uⁱ_{n+1}` observed at the `(n+1)`-th pull of
arm `i` (arXiv:2006.06853v6, §2, p.16: "We also denote Uⁱₙ to be the reward observed from the nth
pull of arm i").

**Formalization Note** The table is indexed from `0`: `ω i n = Uⁱ_{n+1}`. -/
abbrev RewardTable (K : ℕ) := Fin K → ℕ → ℝ

/-- The law of the reward table: all `Uⁱₙ` independent, with `Uⁱₙ ∼ νᵢ` (arXiv:2006.06853v6, §2,
p.16: "(Uⁱₙ)_{n∈ℕ} is thus a sequence of i.i.d. random variables, each distributed as νᵢ"; the
arms' rewards are drawn independently, p.15).

**Formalization Note** The product measure `⊗ᵢ ⊗ₙ νᵢ` on `Fin K → ℕ → ℝ`
(`Measure.infinitePi`). -/
noncomputable def BanditInstance.tableMeasure {K : ℕ} (ν : BanditInstance K) :
    Measure (RewardTable K) :=
  Measure.infinitePi (fun i : Fin K => Measure.infinitePi (fun _ : ℕ => ν.dist i))

instance {K : ℕ} (ν : BanditInstance K) : IsProbabilityMeasure ν.tableMeasure := by
  unfold BanditInstance.tableMeasure; infer_instance

/-- `log⁺(a) = log(max(a, 1))` (arXiv:2006.06853v6, footnote 2, p.22: "We define
log⁺(a) = log(max(a,1)) for a > 0"). -/
noncomputable def logPlus (a : ℝ) : ℝ := Real.log (max a 1)

end MaxObjBandit


