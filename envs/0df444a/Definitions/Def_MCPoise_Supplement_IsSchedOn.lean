-- Prove2me | Definitions.Def_MCPoise_Supplement_IsSchedOn
-- name    : MCPoise_Supplement_IsSchedOn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:13:10.386529+00:00
-- url     : https://prove2.me/theorems/e0a738e2-3175-40bd-bcf5-9fd0f7f88d4f
-- title:
--   Schedules in the telephone model: every round a matching of the graph
-- statement:
--   Let $\Gamma$ be a graph on the vertices $\{0, \dots, n-1\}$. A **round** is a list of calls $(a, b)$. It is a **matching round of $\Gamma$** when every call is an edge $\{a, b\}$ of $\Gamma$ and no vertex lies in two calls of the round.
--
--   1. A **(finite) schedule on $\Gamma$** is a list of rounds $M_1, \dots, M_T$, each a matching round of $\Gamma$; its length is $T$.
--   2. An **infinite schedule on $\Gamma$** assigns to every round $\tau = 1, 2, \dots$ a matching round $M_\tau$ of $\Gamma$.
--
--   These are the feasible solutions of multicommodity multicast and of its vector-clock versions.
--
--   **Formalization Note** A round listing the same call twice is not a matching round; every matching is the call set of a duplicate-free list. Rounds of an infinite schedule are numbered from $1$, and the entry at index $0$ is unconstrained and never used.
-- source:
--   R. Jain, A. Niaparast, R. Ravi, Polylog Pairwise Poise: Approximating Multicommodity Multicast, STOC 2027 submission (manuscript sha256 2c6a7cc5…), §1, p.2 (Telephone Model: the exchanges of a round form a matching); §4.1.1, p.25 (infinite schedules)

import Mathlib
import Definitions.Def_MCPoise_Inst

namespace MCPoise.Supplement

/-- **A round of the telephone model is a matching of the communication graph.**
Jain, Niaparast, Ravi, *Polylog Pairwise Poise: Approximating Multicommodity Multicast*, STOC 2027 submission (manuscript sha256 2c6a7cc5…), §1, p.2: "The set of exchanges in each round forms a matching, modeling telephone calls"; §4.1.1, p.25: "at time t, a matching is selected".

A round is a list of calls `(a, b)` of vertex numbers. `IsMatchingRound Γ R` says that every call is an edge of
`Γ` (both endpoints are vertices `< n` and adjacent, hence distinct) and that distinct calls of the list share no
endpoint, so no vertex is in two calls.

**Formalization Note.** A round listing the same call twice is not a matching here; every matching is the set of
calls of a duplicate-free list, so no schedule is lost. -/
def IsMatchingRound {n : ℕ} (Γ : SimpleGraph (Fin n)) (R : List (ℕ × ℕ)) : Prop :=
  (∀ c ∈ R, ∃ (h₁ : c.1 < n) (h₂ : c.2 < n), Γ.Adj ⟨c.1, h₁⟩ ⟨c.2, h₂⟩) ∧
    R.Pairwise fun c d => c.1 ≠ d.1 ∧ c.1 ≠ d.2 ∧ c.2 ≠ d.1 ∧ c.2 ≠ d.2

/-- **A (finite) schedule on `Γ`**: a list of rounds `M₁, …, M_T`, each a matching of `Γ`.
Jain, Niaparast, Ravi, *Polylog Pairwise Poise: Approximating Multicommodity Multicast*, STOC 2027 submission (manuscript sha256 2c6a7cc5…), §1, p.2 (Telephone Model). Its length is `T = S.length`. -/
def IsSchedOn {n : ℕ} (Γ : SimpleGraph (Fin n)) (S : List (List (ℕ × ℕ))) : Prop :=
  ∀ R ∈ S, IsMatchingRound Γ R

/-- **An infinite schedule on `Γ`**: a matching `M τ` of `Γ` for every round `τ = 1, 2, …`.
Jain, Niaparast, Ravi, *Polylog Pairwise Poise: Approximating Multicommodity Multicast*, STOC 2027 submission (manuscript sha256 2c6a7cc5…), §4.1.1, p.25: "We refer to a sequence of matchings indexed by time as a schedule. … we will consider infinite
schedules, i.e. with an infinite time horizon."

**Formalization Note.** Rounds are numbered from `1`; the value `M 0` is never used by any definition and is
unconstrained. -/
def IsInfSchedOn {n : ℕ} (Γ : SimpleGraph (Fin n)) (M : ℕ → List (ℕ × ℕ)) : Prop :=
  ∀ τ : ℕ, 1 ≤ τ → IsMatchingRound Γ (M τ)

end MCPoise.Supplement


