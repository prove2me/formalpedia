-- Prove2me | Definitions.Def_AlgMechDesign_Randomized_WeightedVGC
-- name    : AlgMechDesign_Randomized_WeightedVGC
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T20:10:42.878845+00:00
-- url     : https://prove2.me/theorems/09866fed-aba8-4b67-b68a-9a120b37e402
-- title:
--   Weighted VGC mechanisms and truthfulness for a general mechanism design problem
-- statement:
--   This file fixes the general vocabulary of Nisan and Ronen's §2–§3.1 needed to state Roberts' theorem (Definitions 4, 8, 9).
--
--   There are $n$ agents $i \in \{1,\dots,n\}$, a set $O$ of possible outputs, and for each agent a set $T^i$ of possible types. Agent $i$ of type $t^i$ values the output $o$ at $v^i(t^i, o) \in \mathbb{R}$. A **direct revelation mechanism** $m = (o(t), p(t))$ maps each declared type profile $t = (t^1,\dots,t^n)$ to an output $o(t)$ and to payments $p^i(t)$ handed to the agents; agent $i$'s utility is $u^i = p^i + v^i(t^i, o)$.
--
--   1. The mechanism is **truthful** if for every agent $i$, every profile of declarations $t^{-i}$ of the others, every true type $t^i$ and every misreport $d^i$,
--   $$
--   v^i\big(t^i, o(t^{-i}, d^i)\big) + p^i(t^{-i}, d^i) \le v^i\big(t^i, o(t^{-i}, t^i)\big) + p^i(t^{-i}, t^i).
--   $$
--   2. Given weights $\beta^1,\dots,\beta^n$, the mechanism belongs to the **weighted VGC family** if its output maximizes the weighted utilitarian objective, $o(t) \in \arg\max_o \sum_i \beta^i v^i(t^i, o)$, and there are functions $h^i$ of $t^{-i}$ alone such that
--   $$
--   p^i(t) = \frac{1}{\beta^i} \sum_{j \ne i} \beta^j \, v^j\big(t^j, o(t)\big) + h^i(t^{-i}).
--   $$
--
--   With all weights equal to $1$ this is the Vickrey–Groves–Clarke family; the weighted version is what the biased min work mechanism reduces to on a single task.
--
--   **Formalization Note** Types live in a dependent product `∀ i, T i`; "$h^i$ depends only on $t^{-i}$" is stated as: $h^i(t) = h^i(t')$ whenever $t$ and $t'$ agree off coordinate $i$. The positivity $\beta^i > 0$ of Definition 8 is a hypothesis of the theorem that uses this definition, not part of the definition.
-- source:
--   Nisan, Ronen, Algorithmic Mechanism Design, Games Econ. Behav. 35, 2001, pp. 171–172, Definition 4; pp. 173–174, §3.1, Definitions 8 and 9

import Mathlib

namespace AlgMechDesign.Randomized

open Finset

/-- A general direct revelation mechanism design problem (Nisan–Ronen §2, pp. 170–172) with
agents `Fin n`, outputs `O`, and type sets `T i`; agent `i` with type `tᵢ` values output `o` at
`v i tᵢ o`. A direct mechanism is an output rule `o : (∀ i, T i) → O` and payments
`p : (∀ i, T i) → Fin n → ℝ` handed to the agents; utility is `p t i + v i (t i) (o t')`.

Truthfulness (Def. 4, general form): for every profile `t` (the others' declarations and agent
`i`'s true type `t i`) and every misreport `ti'` of agent `i`, telling the truth gives at least
the utility of the misreport. -/
def IsTruthfulGeneral {n : ℕ} {O : Type*} {T : Fin n → Type*} (v : ∀ i, T i → O → ℝ)
    (o : (∀ i, T i) → O) (p : (∀ i, T i) → Fin n → ℝ) : Prop :=
  ∀ (t : ∀ i, T i) (i : Fin n) (ti' : T i),
    v i (t i) (o (Function.update t i ti')) + p (Function.update t i ti') i ≤
      v i (t i) (o t) + p t i

/-- The weighted VGC family (Defs. 8–9, pp. 173–174) for weights `β`: the output maximizes the
weighted utilitarian objective `g(o, t) = ∑ⱼ βʲ vʲ(tʲ, o)` over all outputs, and the payment is
`pⁱ(t) = (1/βⁱ) ∑_{j ≠ i} βʲ vʲ(tʲ, o(t)) + hⁱ(t⁻ⁱ)` for some functions `hⁱ` that do not depend
on agent `i`'s own declaration. -/
def IsWeightedVGC {n : ℕ} {O : Type*} {T : Fin n → Type*} (v : ∀ i, T i → O → ℝ)
    (β : Fin n → ℝ) (o : (∀ i, T i) → O) (p : (∀ i, T i) → Fin n → ℝ) : Prop :=
  (∀ (t : ∀ i, T i) (o' : O), ∑ j, β j * v j (t j) o' ≤ ∑ j, β j * v j (t j) (o t)) ∧
    ∃ h : Fin n → (∀ i, T i) → ℝ,
      (∀ (i : Fin n) (t t' : ∀ i, T i), (∀ j, j ≠ i → t j = t' j) → h i t = h i t') ∧
      ∀ (t : ∀ i, T i) (i : Fin n),
        p t i = (1 / β i) * ∑ j ∈ univ.erase i, β j * v j (t j) (o t) + h i t

end AlgMechDesign.Randomized


