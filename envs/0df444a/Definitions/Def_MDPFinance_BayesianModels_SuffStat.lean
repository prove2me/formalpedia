-- Prove2me | Definitions.Def_MDPFinance_BayesianModels_SuffStat
-- name    : MDPFinance_BayesianModels_SuffStat
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:23:05.345409+00:00
-- url     : https://prove2.me/theorems/ed3de51a-dcbd-4da6-bfbd-e576a74e8d0b
-- title:
--   Sufficient statistic and sequential sufficient statistic (Definitions 5.4.3, 5.4.5)
-- statement:
--   Two related definitions, bundled since the second only adds one property to the first.
--
--   **Definition 5.4.3 (sufficient statistic).** Computing $\mu_n(\cdot\mid\tilde h_n)$ may not
--   require the whole history $\tilde h_n$: a **sufficient statistic** for $(\mu_n)$ is a sequence of
--   measurable maps $t_n : \tilde H_n \to I$ (into some auxiliary "information state" space $I$) for
--   which there is a transition kernel $\hat\mu$ from $I$ to $\Theta$ with
--   $$
--   \mu_n(C \mid \tilde h_n) = \hat\mu(C \mid t_n(\tilde h_n))
--   $$
--   for every $n$, history, and $C \in \mathcal B(\Theta)$ — so $t_n(\tilde h_n)$ alone determines the
--   posterior.
--
--   **Definition 5.4.5 (sequential sufficient statistic).** $(t_n)$ is *sequential* if its value
--   updates recursively from only the current observable state, the current statistic, the action
--   taken, and the newly revealed disturbance:
--   $$
--   t_{n+1}(\tilde h_n,a_n,z_{n+1}) = \hat\Phi(x_n, t_n(\tilde h_n), a_n, z_{n+1})
--   $$
--   for a single measurable function $\hat\Phi : E_X \times I \times A \times Z \to I$ — so the
--   information state itself can be carried forward as part of an enlarged Markov state, instead of
--   recomputing $t_n$ from the whole history at every stage.
--
--   This is what makes the information-based Markov Decision Model of Definition 5.4.6 possible.
--
--   **Formalization Note.** `SuffStat` bundles `t`, its non-anticipation, and $\hat\mu$
--   (Definition 5.4.3); `SuffStat.IsSequential` is the extra predicate of Definition 5.4.5, taking
--   $\hat\Phi$ as a separate parameter so the same `SuffStat` can be asked whether *some* $\hat\Phi$
--   witnesses sequentiality.
--
--   **Moderation note.** `IsSequential` now includes the measurability of $\hat\Phi$, which Definition 5.4.5 requires ("for a measurable function $\hat\Phi$") and which makes $\hat T$ a measurable transition function in Definition 5.4.6.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 160-162, Definitions 5.4.3, 5.4.5

import Mathlib
import Definitions.Def_MDPFinance_BayesianModels_Model
import Definitions.Def_MDPFinance_BayesianModels_Posterior

open MeasureTheory ProbabilityTheory

namespace MDPFinance.BayesianModels

variable {EX Θ A Z : Type*} [MeasurableSpace EX] [MeasurableSpace Θ] [MeasurableSpace A]
  [MeasurableSpace Z]

/-- Definition 5.4.3 (Bäuerle–Rieder, p. 160-161, PDF 173-174): a **sufficient statistic** for
`(μ_n)` is a sequence `t = (t_n)` of measurable maps `t_n : H̃_n → I` (represented as functions of
the padded history triple `(xs,as,zs)`, non-anticipating exactly as a decision rule is) for which
there exists a transition kernel `μ̂` from `I` to `Θ` with `μ_n(C|h̃_n) = μ̂(C|t_n(h̃_n))` for all
`h̃_n`, `C ∈ B(Θ)`, `n`. -/
structure SuffStat (M : BayesModel EX Θ A Z) (Pf : M.Posterior) (I : Type*) [MeasurableSpace I]
    where
  t : (n : ℕ) → (ℕ → EX) → (ℕ → A) → (ℕ → Z) → I
  ht_meas : ∀ n, Measurable fun p : (ℕ → EX) × (ℕ → A) × (ℕ → Z) => t n p.1 p.2.1 p.2.2
  ht_dep : ∀ n xs xs' as as' zs zs', (∀ i ≤ n, xs i = xs' i) → (∀ i < n, as i = as' i) →
    (∀ i, 1 ≤ i → i ≤ n → zs i = zs' i) → t n xs as zs = t n xs' as' zs'
  muHat : Kernel I Θ
  hmuHat_prob : ∀ i, IsProbabilityMeasure (muHat i)
  ht_suff : ∀ n xs as zs (C : Set Θ), MeasurableSet C →
    (Pf.mu n xs as zs) C = muHat (t n xs as zs) C

variable {I : Type*} [MeasurableSpace I] {M : BayesModel EX Θ A Z} {Pf : M.Posterior}

/-- Definition 5.4.5 (Bäuerle–Rieder, p. 162, PDF 175): `(t_n)` is a **sequential sufficient
statistic** if its next value is a measurable function `Φ̂` of only the current observable state,
the current statistic, the action taken, and the newly revealed disturbance:
`t_{n+1}(h̃_n,a_n,z_{n+1}) = Φ̂(x_n,t_n(h̃_n),a_n,z_{n+1})`, with `Φ̂` measurable (Definition 5.4.5:
"for a measurable function `Φ̂`"). -/
def SuffStat.IsSequential (S : SuffStat M Pf I) (Phihat : EX → I → A → Z → I) : Prop :=
  Measurable (fun p : EX × I × A × Z => Phihat p.1 p.2.1 p.2.2.1 p.2.2.2) ∧
    ∀ n xs as zs, S.t (n + 1) xs as zs = Phihat (xs n) (S.t n xs as zs) (as n) (zs (n + 1))

end MDPFinance.BayesianModels


