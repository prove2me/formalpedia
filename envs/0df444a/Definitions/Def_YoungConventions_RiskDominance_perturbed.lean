-- Prove2me | Definitions.Def_YoungConventions_RiskDominance_perturbed
-- name    : YoungConventions_RiskDominance_perturbed
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:59:49.146468+00:00
-- url     : https://prove2.me/theorems/5bd2598f-e67f-4a5b-8db2-8d1bc9dc5487
-- title:
--   Adaptive play $P^\varepsilon$ with mistakes, display (2)
-- statement:
--   Let $p$ be a best-reply distribution and $(\lambda,q)$ an admissible experimentation. **Adaptive play with memory $m$, sample size $k$, experimentation probabilities $\varepsilon\lambda_i$ and experimentation distributions $q_i$** is the Markov chain on $H$ with transition matrix
--   $$P^\varepsilon_{hh'}=\Big(\prod_{i=1}^n(1-\varepsilon\lambda_i)\Big)P^0_{hh'}+\sum_{J\subseteq N,\,J\neq\emptyset}\varepsilon^{|J|}\Big(\prod_{j\in J}\lambda_j\Big)\Big(\prod_{j\notin J}(1-\varepsilon\lambda_j)\Big)Q^J_{hh'}.$$
--
--   The stochastically stable states are defined from the stationary distributions of this process as $\varepsilon\to0$.
--
--   **Formalization Note** The formula is defined for every real $\varepsilon$; it is a transition matrix for $0<\varepsilon$ with $\varepsilon\lambda_i\le1$, and only that range is used.
-- source:
--   Young (1993), The Evolution of Conventions, Econometrica 61:57–84, §5, p. 67, display (2)

import Mathlib
import Definitions.Def_YoungConventions_AdaptivePlay_History
import Definitions.Def_YoungConventions_RiskDominance_unperturbed
import Definitions.Def_YoungConventions_RiskDominance_experimentKernel

open Classical

namespace YoungConventions.RiskDominance

/-- **Adaptive play with mistakes `P^ε`**, display (2). Young (1993), The Evolution of Conventions, Econometrica 61:57–84, §5, p. 67 (PDF p. 12):
`P^ε_{hh′} = (∏_{i=1,n}(1 − ελᵢ)) P⁰_{hh′} + ∑_{J⊆N, J≠∅} ε^{|J|} (∏_{j∈J} λ_j)(∏_{j∉J}(1 − ελ_j)) Q^J_{hh′}`.
"The process `P^ε` will be called adaptive play with memory `m`, sample size `k`, experimentation
probabilities `ελᵢ` and experimentation distributions `qᵢ`."

**Formalization Note.** Defined for every real `ε`; it is a transition matrix when `0 < ε` and
`ελᵢ ≤ 1` for all `i`, and only that range (in fact only `ε → 0⁺`) is used by the theorems. -/
noncomputable def perturbed {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ι → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)] {m : ℕ} [NeZero m]
    (p q : (i : ι) → YoungConventions.AdaptivePlay.History S m → S i → ℝ) (lam : ι → ℝ) (ε : ℝ) :
    Matrix (YoungConventions.AdaptivePlay.History S m) (YoungConventions.AdaptivePlay.History S m) ℝ :=
  fun h h' => (∏ i, (1 - ε * lam i)) * unperturbed p h h' +
    ∑ J ∈ (Finset.univ : Finset (Finset ι)).filter (fun J => J.Nonempty),
      ε ^ J.card * (∏ j ∈ J, lam j) * (∏ j ∈ Jᶜ, (1 - ε * lam j)) * experimentKernel J p q h h'

end YoungConventions.RiskDominance


