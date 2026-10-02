-- Prove2me | Definitions.Def_TheoryOfGames_CharFun_charFun
-- name    : TheoryOfGames_CharFun_charFun
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-01T03:37:21.591984+00:00
-- url     : https://prove2.me/theorems/9cdaf83e-673c-49f4-a0e9-1fcc532de8ab
-- title:
--   The characteristic function v(S) of a zero-sum n-person game (25.1.3)
-- statement:
--   Let $\Gamma$ be a zero-sum $n$-person game in normalized form with players $I = \{1, \dots, n\}$, strategy sets $\tau_k = 1, \dots, \beta_k$ and payoffs $\mathcal H_k(\tau_1, \dots, \tau_n)$. For a subset $S \subseteq I$ let $-S = I \setminus S$.
--
--   Consider the two-person game between the composite player $1'$ formed by all $k \in S$ and the composite player $2'$ formed by all $k \in -S$. The pure strategies of $1'$ are the aggregates $\tau^S$ of the variables $\tau_k$, $k \in S$, and those of $2'$ are the aggregates $\tau^{-S}$. Player $1'$ gets the amount (25:2)
--   $$\overline{\mathcal H}(\tau^S, \tau^{-S}) = \sum_{k \in S} \mathcal H_k(\tau_1, \dots, \tau_n),$$
--   and player $2'$ its negative. A mixed strategy of $1'$ is a probability vector $\xi = (\xi_{\tau^S})$ on the set of all aggregates $\tau^S$ (one joint distribution for the whole coalition, not one independent mixture per member), and a mixed strategy of $2'$ is a probability vector $\eta = (\eta_{\tau^{-S}})$ on the aggregates $\tau^{-S}$. With the bilinear form
--   $$K(\xi, \eta) = \sum_{\tau^S, \tau^{-S}} \overline{\mathcal H}(\tau^S, \tau^{-S})\, \xi_{\tau^S}\, \eta_{\tau^{-S}},$$
--   the **characteristic function** of $\Gamma$ is
--   $$v(S) = \operatorname{Max}_{\xi} \operatorname{Min}_{\eta} K(\xi, \eta).$$
--   It is defined for all subsets $S$ of $I$, including the empty set (which has exactly one, empty, aggregate) and $I$ itself.
--
--   The characteristic function is the numerical set function on which the book bases the whole theory of the zero-sum $n$-person game (25.2.1).
--
--   **Formalization Note** Players are `Fin n`, coalitions `Finset (Fin n)`, and $-S$ is the complement `Sᶜ`. An aggregate $\tau^S$ is a dependent function assigning to each $k \in S$ a strategy in `Fin (β k)`. Mixed strategies are elements of Mathlib's `stdSimplex`. The Max and Min are written as `⨆`/`⨅`; both simplices are nonempty (every $\beta_k \geqq 1$) and $K$ is bounded on them, so these are the book's attained maximum and minimum. By the minimax theorem (17:6) this number also equals $\operatorname{Min}_\eta \operatorname{Max}_\xi K(\xi,\eta)$; that equality is not part of the definition.
-- source:
--   von Neumann & Morgenstern, Theory of Games and Economic Behavior (60th-anniversary ed., Princeton 2007), pp. 239–240, 25.1.3, (25:2); p. 240, 25.2.1; p. 241, footnote 2

import Mathlib
import Definitions.Def_TheoryOfGames_CharFun_ZeroSumGame

namespace TheoryOfGames.CharFun

namespace ZeroSumGame

variable {n : ℕ} (Γ : ZeroSumGame n)

/-- The aggregate `τ^S` of the choices of the members of a coalition `S ⊆ I` (25.1.3): one
pure strategy for every `k ∈ S`. For `S = ∅` there is exactly one (empty) aggregate. -/
abbrev CoalStrat (S : Finset (Fin n)) : Type := (k : S) → Fin (Γ.β k)

/-- The full strategy profile `(τ₁, …, τₙ)` formed by the aggregates `τ^S` of `S` and
`τ^{-S}` of its complement `-S = Sᶜ` (footnote 2 on p. 239). -/
def joint (S : Finset (Fin n)) (τS : Γ.CoalStrat S) (τC : Γ.CoalStrat Sᶜ) :
    (k : Fin n) → Fin (Γ.β k) :=
  fun k => if h : k ∈ S then τS ⟨k, h⟩ else τC ⟨k, Finset.mem_compl.mpr h⟩

/-- (25:2): the amount `ℋ̄(τ^S, τ^{-S}) = ∑_{k ∈ S} ℋ_k(τ₁, …, τₙ)` the composite player `S`
(player 1') receives in the two-person game of `S` against `-S`. -/
def coalPayoff (S : Finset (Fin n)) (τS : Γ.CoalStrat S) (τC : Γ.CoalStrat Sᶜ) : ℝ :=
  ∑ k ∈ S, Γ.H (Γ.joint S τS τC) k

/-- The bilinear form `K(ξ, η) = ∑_{τ^S, τ^{-S}} ℋ̄(τ^S, τ^{-S}) ξ_{τ^S} η_{τ^{-S}}` (25.1.3,
p. 240). `ξ` is a weight on the aggregates `τ^S` (one joint distribution over all of `S`'s
strategy tuples) and `η` one on the aggregates `τ^{-S}`. -/
def bilin (S : Finset (Fin n)) (ξ : Γ.CoalStrat S → ℝ) (η : Γ.CoalStrat Sᶜ → ℝ) : ℝ :=
  ∑ τS, ∑ τC, Γ.coalPayoff S τS τC * ξ τS * η τC

/-- The characteristic function of the game (25.1.3, 25.2.1):
`v(S) = Max_ξ Min_η K(ξ, η)`, where `ξ` ranges over the probability vectors on the aggregates
`τ^S` (mixed strategies of the composite player `S`) and `η` over the probability vectors on
the aggregates `τ^{-S}`. It is defined for every subset `S` of `I`, including `∅` and `I`
(footnote 2 on p. 241). Both simplices are nonempty (every `β k ≥ 1`) and `K` is bounded on
them, so the supremum and infimum below are the book's attained Max and Min. -/
noncomputable def charFun (S : Finset (Fin n)) : ℝ :=
  ⨆ ξ : stdSimplex ℝ (Γ.CoalStrat S), ⨅ η : stdSimplex ℝ (Γ.CoalStrat Sᶜ),
    Γ.bilin S (ξ : Γ.CoalStrat S → ℝ) (η : Γ.CoalStrat Sᶜ → ℝ)

end ZeroSumGame

end TheoryOfGames.CharFun


