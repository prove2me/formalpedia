-- Prove2me | Definitions.Def_YoungConventions_RiskDominance_IsGenericallyStable
-- name    : YoungConventions_RiskDominance_IsGenericallyStable
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T18:05:43.794173+00:00
-- url     : https://prove2.me/theorems/2713ea7b-8fb5-4f0a-8f50-699b8db61c52
-- title:
--   Generically stable equilibrium
-- statement:
--   A strict pure-strategy Nash equilibrium $s$ is **generically stable** if the associated convention $(s,\dots,s)$ is stochastically stable for all sufficiently large $k$ and $m$ such that $k\le m/(L_\Gamma+2)$. Precisely: there is $K$ such that for all $k\ge\max(K,1)$, all $m$ with $k(L_\Gamma+2)\le m$, every best-reply distribution $p$ for sample size $k$ and memory $m$, and every admissible experimentation $(\lambda,q)$, the convention $(s,\dots,s)$ is stochastically stable relative to $P^\varepsilon$.
--
--   This is the selection criterion of Theorem 3.
--
--   **Formalization Note** $k\le m/(L_\Gamma+2)$ is written $k(L_\Gamma+2)\le m$ in natural numbers. "Sufficiently large" is an eventual statement in $k$ (there is a threshold $K$), not "for some large $k$". The quantifier over $(p,\lambda,q)$ is universal; by Theorem 2 the stable states do not depend on $(\lambda,q)$ and depend on $p$ only through its support, which is fixed. The predicate includes the paper’s strict Nash equilibrium condition on $s$.
-- source:
--   Young (1993), The Evolution of Conventions, Econometrica 61:57–84, §7, p. 72, displayed definition (Generic Stability)

import Mathlib
import Definitions.Def_YoungConventions_AdaptivePlay_History
import Definitions.Def_YoungConventions_RiskDominance_convention
import Definitions.Def_YoungConventions_RiskDominance_IsBestReplyDistribution
import Definitions.Def_YoungConventions_RiskDominance_IsExperimentation
import Definitions.Def_YoungConventions_RiskDominance_IsStochasticallyStable
import Definitions.Def_YoungConventions_RiskDominance_bestReplyRadius
import Definitions.Def_YoungConventions_AdaptivePlay_IsStrictNash

namespace YoungConventions.RiskDominance

/-- **Generic stability.** Young (1993), The Evolution of Conventions, Econometrica 61:57–84, §7, p. 72 (PDF p. 17), displayed definition: "A strict pure
strategy Nash equilibrium is generically stable if the associated convention is stochastically
stable for all sufficiently large `k` and `m` such that `k ≤ m/(L_Γ + 2)`."

`s` is a strict pure Nash equilibrium and there is `K` such that for all `k ≥ K` (with `k ≥ 1`) and all `m` with
`k(L_Γ + 2) ≤ m`, for every best-reply distribution `p` (sample size `k`, memory `m`) and every
admissible experimentation `(λ, q)`, the convention `(s, …, s)` is stochastically stable relative to
`P^ε`.

**Formalization Note.** `k ≤ m/(L_Γ + 2)` is written in natural numbers as `k * (L_Γ + 2) ≤ m`
(no truncating division). "For all sufficiently large `k` and `m`" is `∃ K, ∀ k ≥ K, ∀ m` with the
side condition; it is not "for some large `k`" and not a limit. The quantifier over `(p, λ, q)` is
universal (the strong reading); by Theorem 2 the stochastically stable states do not depend on
`(λ, q)` and depend on `p` only through its support, which is fixed. `[NeZero m]` holds automatically
since `m ≥ k ≥ 1`. The strict Nash condition is part of the paper's displayed definition. -/
def IsGenericallyStable {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ι → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)] [∀ i, Nonempty (S i)]
    (u : ι → ((i : ι) → S i) → ℝ) (s : (i : ι) → S i) : Prop :=
  YoungConventions.AdaptivePlay.IsStrictNash u s ∧
  ∃ K : ℕ, ∀ k m : ℕ, K ≤ k → 1 ≤ k → k * (bestReplyRadius u + 2) ≤ m → ∀ [NeZero m],
    ∀ (p q : (i : ι) → YoungConventions.AdaptivePlay.History S m → S i → ℝ) (lam : ι → ℝ),
      IsBestReplyDistribution u k p → IsExperimentation lam q →
      IsStochasticallyStable p q lam (convention (m := m) s)

end YoungConventions.RiskDominance


