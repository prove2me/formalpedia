-- Prove2me | Definitions.Def_YoungConventions_RiskDominance_IsExperimentation
-- name    : YoungConventions_RiskDominance_IsExperimentation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:57:46.161528+00:00
-- url     : https://prove2.me/theorems/847be1a9-0421-45b1-a768-f1605716aaf4
-- title:
--   Experimentation probabilities $\lambda_i$ and distributions $q_i$
-- statement:
--   In each period player $i$ experiments with probability $\varepsilon\lambda_i$, independently of the other players, and then chooses $s\in S_i$ with probability $q_i(s\mid h)$ instead of optimizing. The pair $(\lambda,q)$ is **admissible** if
--   1. $\lambda_i>0$ for every player $i$;
--   2. for every $i$ and $h$, $q_i(\cdot\mid h)$ is a probability distribution on $S_i$ with full support: $q_i(s\mid h)>0$ for all $s\in S_i$ and $\sum_{s\in S_i}q_i(s\mid h)=1$.
--
--   The noise level $\varepsilon$ is a separate parameter; the perturbed process is a transition matrix for $0<\varepsilon$ with $\varepsilon\lambda_i\le1$ for all $i$.
--
--   **Formalization Note** $\lambda$ is written `lam` in Lean.
-- source:
--   Young (1993), The Evolution of Conventions, Econometrica 61:57–84, §5, pp. 66–67

import Mathlib
import Definitions.Def_YoungConventions_AdaptivePlay_History

namespace YoungConventions.RiskDominance

/-- **Experimentation probabilities and distributions.** Young (1993), The Evolution of Conventions, Econometrica 61:57–84, §5, pp. 66–67 (PDF pp. 11–12):
"there is some small probability `ελᵢ > 0` that player `i` experiments by choosing a strategy
randomly from `Sᵢ` instead of optimizing"; "let `qᵢ(s|h)` be the conditional probability that `i`
chooses `s ∈ Sᵢ` given that `i` experiments and the process is in state `h`, where
`∑_{s∈Sᵢ} qᵢ(s|h) = 1` for every `i` and `h`. We shall assume that `qᵢ(s|h)` is independent of `t`,
and that `qᵢ(s|h) > 0` for all `s ∈ Sᵢ`."

`(λ, q)` is admissible iff every `λᵢ > 0` and every `qᵢ(·|h)` is a probability distribution on `Sᵢ`
with full support.

**Formalization Note.** `λ` is written `lam` (a Lean keyword clash). The noise level `ε` is a
separate argument; `ελᵢ ≤ 1` is imposed wherever `P^ε` is used. -/
def IsExperimentation {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ι → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)] {m : ℕ}
    (lam : ι → ℝ) (q : (i : ι) → YoungConventions.AdaptivePlay.History S m → S i → ℝ) : Prop :=
  (∀ i, 0 < lam i) ∧ ∀ (i : ι) (h : YoungConventions.AdaptivePlay.History S m), (∀ x, 0 < q i h x) ∧ ∑ x, q i h x = 1

end YoungConventions.RiskDominance


