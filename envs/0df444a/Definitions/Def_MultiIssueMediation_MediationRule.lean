-- Prove2me | Definitions.Def_MultiIssueMediation_MediationRule
-- name    : MultiIssueMediation_MediationRule
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:19:09.101568+00:00
-- url     : https://prove2.me/theorems/d7220873-43da-4c30-ba1c-42a307049f4d
-- title:
--   Definitions 2–4 — mediation rules; strategy-proof, individually rational and efficient
-- statement:
--   A mediation rule is an $m\times m$ matrix $f=[f_{\ell,j}]$ of bundles, with $\ell$ the row (the type of negotiator 1) and $j$ the column (the type of negotiator 2).
--
--   1. $f$ is **strategy-proof** if for all $i$ and $\theta_i$, $f(\theta_i,\theta_{-i})\,R_i\,f(\theta_i',\theta_{-i})$ for all $R_i\in\Lambda(\theta_i)$, $\theta_i'$ and $\theta_{-i}$.
--   2. $f$ is **individually rational** if for all $i$ and all profiles, $f(\theta_i,\theta_{-i})\,R_i\,(o_X,o_Y)$ for all $R_i\in\Lambda(\theta_i)$.
--   3. $f$ is **efficient** if there are no profile and no bundle $(x',y')\in X\times Y$ such that $(x',y')\,R_i\,f(\theta_i,\theta_{-i})$ for all $R_i\in\Lambda(\theta_i)$ and all $i$, and for at least one $i$, $(x',y')\,P_i\,f(\theta_i,\theta_{-i})$ for some $R_i\in\Lambda(\theta_i)$.
--
--   These are the three axioms of Theorem 1.
--
--   **Formalization Note** Strategy-proofness is written as one conjunct for each negotiator. In efficiency the quantifiers range over orderings, not over one chosen profile of orderings, and the candidate ranges over all of $X\times Y$.
-- source:
--   Kesten, Özyurt, Efficient and Incentive Compatible Mediation: An Ordinal Market Design Approach, working paper, 4 October 2018, pp.14–15, Definitions 2, 3, 4

import Mathlib
import Definitions.Def_MultiIssueMediation_ConsistentOrdering

namespace MultiIssueMediation

/-- A mediation rule `f : Θ → X × Y`, presented as the `m × m` matrix `[f_{ℓ,j}]` (working paper of
4 October 2018, pp.14–15).

**Formalization Note.** The first argument is the row, the type of negotiator 1, and the second is
the column, the type of negotiator 2. Row `ℓ` accepts `{x_k | k ≤ ℓ}` and column `j` accepts
`{x_k | k ≥ j}`. -/
abbrev MediationRule (m : ℕ) : Type := Fin m → Fin m → Bundle m

/-- The type of negotiator `i` at the type profile `(ℓ, j)`. -/
def typeAt {m : ℕ} : Negotiator → Fin m → Fin m → Fin m
  | .one, ℓ, _ => ℓ
  | .two, _, j => j

/-- Definition 2 (working paper of 4 October 2018, p.14): for all `i` and all `θ_i`,
`f(θ_i, θ_{−i}) R_i f(θ'_i, θ_{−i})` for all `R_i ∈ Λ(θ_i)`, `θ'_i` and `θ_{−i}`. The two
conjuncts are the cases `i = 1` and `i = 2`. -/
def StrategyProof {m : ℕ} (f : MediationRule m) : Prop :=
  (∀ ℓ ℓ' j : Fin m, ∀ R ∈ admissibleOrderings Negotiator.one ℓ, R (f ℓ j) (f ℓ' j)) ∧
    (∀ ℓ j j' : Fin m, ∀ R ∈ admissibleOrderings Negotiator.two j, R (f ℓ j) (f ℓ j'))

/-- Definition 3 (working paper of 4 October 2018, p.14): for all `i` and all `(θ_i, θ_{−i})`,
`f(θ_i, θ_{−i}) R_i (o_X, o_Y)` for all `R_i ∈ Λ(θ_i)`. -/
def IndividuallyRational {m : ℕ} (f : MediationRule m) : Prop :=
  ∀ (i : Negotiator) (ℓ j : Fin m), ∀ R ∈ admissibleOrderings i (typeAt i ℓ j),
    R (f ℓ j) (none, none)

/-- Definition 4 (working paper of 4 October 2018, p.15): there is no profile and no bundle
`(x', y') ∈ X × Y` such that `(x', y') R_i f(θ_i, θ_{−i})` for all `R_i ∈ Λ(θ_i)` and all `i`, and
for at least one `i`, `(x', y') P_i f(θ_i, θ_{−i})` for some `R_i ∈ Λ(θ_i)`. -/
def Efficient {m : ℕ} (f : MediationRule m) : Prop :=
  ¬ ∃ (ℓ j : Fin m) (c : Bundle m),
    (∀ (i : Negotiator), ∀ R ∈ admissibleOrderings i (typeAt i ℓ j), R c (f ℓ j)) ∧
      ∃ (i : Negotiator), ∃ R ∈ admissibleOrderings i (typeAt i ℓ j),
        StrictlyPrefers R c (f ℓ j)

end MultiIssueMediation


