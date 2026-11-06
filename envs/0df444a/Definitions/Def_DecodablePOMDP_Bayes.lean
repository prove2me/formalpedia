-- Prove2me | Definitions.Def_DecodablePOMDP_Bayes
-- name    : DecodablePOMDP_Bayes
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:23:53.759716+00:00
-- url     : https://prove2.me/theorems/bf5052c3-4cde-4840-a800-3d045df5b67b
-- title:
--   Next-observation probability $P(z\mid\beta,a)$ and the exact posterior
-- statement:
--   For a POMDP, a stage $h$, a belief $\beta$ on the states, an action $a$ and an observation $z$ at stage $h+1$,
--
--   $$P(z\mid\beta,a)=\sum_\xi\beta(\xi)\sum_{\xi'}T_h(\xi'\mid\xi,a)\,K_{h+1}(z\mid\xi'),\qquad \beta^+(\xi')=\frac{\sum_\xi\beta(\xi)\,T_h(\xi'\mid\xi,a)\,K_{h+1}(z\mid\xi')}{P(z\mid\beta,a)}.$$
--
--   $\beta^+$ is the exact one-step Bayes posterior. The planner of §4 is analysed through these two quantities in $\widetilde{\mathcal P}(L)$.
--
--   **Formalization Note** The stage is explicit. When $P(z\mid\beta,a)=0$ the formula gives the zero vector; every statement assumes positivity or multiplies by $P(z\mid\beta,a)$.
-- source:
--   Dobson, Jog, Shiu, Quasipolynomial-Time Planning for Decodable POMDPs (preprint, sha256 c1256cbe…3584b), §4.2, p.11; App. A.7, p.18

import Mathlib
import Definitions.Def_DecodablePOMDP_POMDP

namespace DecodablePOMDP

/-- **Next-observation probability** `P(z | β, a)` (§4.2, p.11): the probability of observing `z`
at stage `h + 1` when the hidden state at stage `h` has law `β` and action `a` is taken,
`Σ_ξ β(ξ) Σ_{ξ'} T_h(ξ' | ξ, a) K_{h+1}(z | ξ')`.

Dobson, Jog, Shiu (preprint, sha256 c1256cbe…3584b), §4.2, p.11: "Write P(z | β, a) for the
probability of the next observation z under the killed dynamics, given current belief β and action
a, with the stage implicit."

**Formalization Note.** Stated for any POMDP; the paper uses it for `P̃(L)`, with the stage `h`
explicit. -/
def POMDP.obsProb {S A O : Type} [Fintype S] (P : POMDP S A O) (h : ℕ) (β : S → ℝ) (a : A)
    (z : O) : ℝ :=
  ∑ ξ, β ξ * ∑ ξ', P.T h ξ a ξ' * P.K (h + 1) ξ' z

/-- **Exact posterior** `β⁺` (Lemma 5, p.10; A.7, p.18): the one-step Bayes update of the belief
`β` at stage `h` after action `a` and observation `z` at stage `h + 1`,
`β⁺(ξ') = Σ_ξ β(ξ) T_h(ξ' | ξ, a) K_{h+1}(z | ξ') / P(z | β, a)`.

Dobson, Jog, Shiu (preprint, sha256 c1256cbe…3584b), App. A.7, p.18: "β+_{m,a}(z) is the exact
posterior after taking action a and observing z".

**Formalization Note.** Lean's `x / 0 = 0` gives the zero vector when `P(z | β, a) = 0`; every
statement using it assumes `P(z | β, a) > 0` or multiplies it by `P(z | β, a)`. -/
noncomputable def POMDP.posterior {S A O : Type} [Fintype S] (P : POMDP S A O) (h : ℕ)
    (β : S → ℝ) (a : A) (z : O) (ξ' : S) : ℝ :=
  (∑ ξ, β ξ * P.T h ξ a ξ' * P.K (h + 1) ξ' z) / P.obsProb h β a z

end DecodablePOMDP


