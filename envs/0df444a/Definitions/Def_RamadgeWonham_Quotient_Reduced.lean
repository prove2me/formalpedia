-- Prove2me | Definitions.Def_RamadgeWonham_Quotient_Reduced
-- name    : RamadgeWonham_Quotient_Reduced
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T21:39:49.600687+00:00
-- url     : https://prove2.me/theorems/1df859b8-bdc0-4a81-9dd9-1ac23c7a57bc
-- title:
--   K̄-equivalence, K̄-reduced and K̄-trim automata (§9, p. 222)
-- statement:
--   Let $K \subseteq \Sigma^*$ be a language with closure $\bar K$. Two strings are **$\bar K$-equivalent**, $s \equiv s' \pmod{\bar K}$, if
--   $$\forall t \in \Sigma^*:\quad st \in \bar K \iff s't \in \bar K.$$
--   An automaton $S = (X, \Sigma, \xi, x_0, X_m)$ is **$\bar K$-reduced** if $s, s' \in \bar K$ and $s \equiv s' \pmod{\bar K}$ imply $\xi(s, x_0) = \xi(s', x_0)$, and **$\bar K$-trim** if every state is visited by a word of $\bar K$: for every $x \in X$ there is $s \in \bar K$ with $\xi(s, x_0) = x$.
--
--   These two properties are the hypotheses on the supervisor's automaton in the quotient structure theorem (Theorem 10.1); the paper's efficient supervisor of §9 has both.
--
--   **Formalization Note** In the equation $\xi(s, x_0) = \xi(s', x_0)$ both sides are values of type `Option X`, so equality includes the case where both are undefined.
-- source:
--   Ramadge and Wonham, Supervisory Control of a Class of Discrete Event Processes, SIAM J. Control Optim. 25(1), 1987, p. 222, §9, definitions of K̄-equivalence, K̄-reduced, K̄-trim

import Mathlib
import Definitions.Def_RamadgeWonham_Shared_Generator

namespace RamadgeWonham.Quotient

variable {α : Type}

/-- `K̄`-equivalence on `Σ*` (§9, p. 222): `s ≡ s' (mod K̄)` iff for all `t ∈ Σ*`,
`st ∈ K̄ ⟺ s't ∈ K̄`. -/
def KEquiv (K : Set (List α)) (s s' : List α) : Prop :=
  ∀ t : List α, s ++ t ∈ Shared.pre K ↔ s' ++ t ∈ Shared.pre K

/-- An automaton `S = (X, Σ, ξ, x₀, X_m)` is `K̄`-reduced (§9, p. 222): if `s, s' ∈ K̄` and
`s ≡ s' (mod K̄)` then `ξ(s, x₀) = ξ(s', x₀)`. -/
def KReduced (S : Shared.Generator α) (K : Set (List α)) : Prop :=
  ∀ s s' : List α, s ∈ Shared.pre K → s' ∈ Shared.pre K → KEquiv K s s' → S.run s = S.run s'

/-- An automaton `S` is `K̄`-trim (§9, p. 222): every state of `S` is visited by a word of `K̄`,
i.e. for every `x ∈ X` there is `s ∈ K̄` with `ξ(s, x₀) = x`. -/
def KTrim (S : Shared.Generator α) (K : Set (List α)) : Prop :=
  ∀ x : S.Q, ∃ s ∈ Shared.pre K, S.run s = some x

end RamadgeWonham.Quotient


