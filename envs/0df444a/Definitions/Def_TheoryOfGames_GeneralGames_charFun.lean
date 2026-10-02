-- Prove2me | Definitions.Def_TheoryOfGames_GeneralGames_charFun
-- name    : TheoryOfGames_GeneralGames_charFun
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-01T05:13:51.516333+00:00
-- url     : https://prove2.me/theorems/8a232d8f-6ea6-4e14-b65e-f4e4ba6dc62f
-- title:
--   Extended and restricted characteristic functions of a general n-person game (56.2.2, 57.1)
-- statement:
--   Let $\Gamma$ be a general $n$-person game with payoffs $\mathcal H_k(\tau_1, \dots, \tau_n)$, $k \in I = \{1, \dots, n\}$.
--
--   **Zero-sum extension.** The zero-sum extension $\overline\Gamma$ (56.2.2) is the zero-sum $(n+1)$-person game with players $\overline I = \{1, \dots, n, n+1\}$ in which the real players $1, \dots, n$ keep their variables and payoffs, and the *fictitious player* $n+1$, who has no influence on the course of the game, gets (56:2)
--   $$\mathcal H_{n+1}(\tau_1, \dots, \tau_n) \equiv -\sum_{k=1}^n \mathcal H_k(\tau_1, \dots, \tau_n).$$
--
--   **Extended characteristic function.** For $S \subseteq \overline I$ consider, as in 25.1.3, the two-person game between the composite player $S$ and the composite player $\overline I - S$. The pure strategies of $S$ are the aggregates $\tau^S$ of the variables of its real members, and those of $\overline I - S$ are the aggregates of the variables of the real members of $\overline I - S$. The composite player $S$ gets $\overline{\mathcal H}(\tau^S, \tau^{\overline I - S}) = \sum_{k \in S} \mathcal H_k$ (with $\mathcal H_{n+1}$ given by (56:2)), and $\overline I - S$ gets the negative. With mixed strategies $\xi$ (a probability vector on all aggregates $\tau^S$: one joint distribution for the whole coalition) and $\eta$ (a probability vector on the aggregates $\tau^{\overline I - S}$) and
--   $$K(\xi,\eta) = \sum_{\tau^S, \tau^{\overline I - S}} \overline{\mathcal H}(\tau^S, \tau^{\overline I - S})\,\xi_{\tau^S}\,\eta_{\tau^{\overline I - S}},$$
--   the **extended characteristic function** is
--   $$v(S) = \operatorname{Max}_\xi \operatorname{Min}_\eta K(\xi, \eta), \qquad S \subseteq \overline I .$$
--   This is the characteristic function of $\overline\Gamma$ in the sense of 25.1.3.
--
--   **Restricted characteristic function.** The same $v(S)$, considered only for $S \subseteq I = \{1, \dots, n\}$ (57.1). For a zero-sum game $\Gamma$ it coincides with the characteristic function of 25.1.3.
--
--   These are the two set functions whose complete characterization is the subject of §57.
--
--   **Formalization Note** $\overline I$ is `Fin (n + 1)`: real player $k$ is `Fin.castSucc k` and the fictitious player $n+1$ is `Fin.last n`. The fictitious player has a single strategy (footnote 2 on p. 506), so the aggregates of a coalition are those of its real members `realPart S`; this leaves the two-person game unchanged. The Max and Min are `⨆`/`⨅` over Mathlib's `stdSimplex`; both simplices are nonempty (every $\beta_k \geqq 1$) and $K$ is bounded on them, so these are the book's attained maximum and minimum. The restricted function is the extended one on `S.map Fin.castSuccEmb`.
-- source:
--   von Neumann & Morgenstern, Theory of Games and Economic Behavior (60th-anniversary ed., Princeton 2007), p. 506, 56.2.2, (56:2); pp. 527–528, 57.1; p. 528, 57.2.1; pp. 239–240, 25.1.3

import Mathlib
import Definitions.Def_TheoryOfGames_GeneralGames_GeneralGame

namespace TheoryOfGames.GeneralGames

namespace GeneralGame

variable {n : ℕ} (Γ : GeneralGame n)

/-- The payoffs of the zero-sum extension `Γ̄` (56.2.2, (56:2)): the players of `Γ̄` are
`Ī = Fin (n + 1)`, the real player `k` is `Fin.castSucc k` and the fictitious player `n + 1` is
`Fin.last n`. The real players get `ℋ_k(τ₁, …, τₙ)`; the fictitious player gets
`ℋ_{n+1}(τ₁, …, τₙ) ≡ -∑_{k=1}^n ℋ_k(τ₁, …, τₙ)`. The fictitious player has no variable of
his own (equivalently, a single strategy, footnote 2 on p. 506). -/
def extH (τ : (k : Fin n) → Fin (Γ.β k)) : Fin (n + 1) → ℝ :=
  Fin.lastCases (motive := fun _ => ℝ) (-(∑ k, Γ.H τ k)) (fun i => Γ.H τ i)

/-- The real members `S ∩ I` of a set `S ⊆ Ī = Fin (n + 1)`, as a subset of `I = Fin n`. -/
def realPart (S : Finset (Fin (n + 1))) : Finset (Fin n) :=
  Finset.univ.filter (fun i : Fin n => Fin.castSucc i ∈ S)

/-- The aggregate `τ^S` of the choices of the (real) members of a set `R ⊆ I` (25.1.3): one
pure strategy for every `k ∈ R`. For `R = ∅` there is exactly one (empty) aggregate. -/
abbrev CoalStrat (R : Finset (Fin n)) : Type := (k : R) → Fin (Γ.β k)

/-- The full profile `(τ₁, …, τₙ)` formed by the aggregates of `R` and of its complement `I - R`. -/
def joint (R : Finset (Fin n)) (τS : Γ.CoalStrat R) (τC : Γ.CoalStrat Rᶜ) :
    (k : Fin n) → Fin (Γ.β k) :=
  fun k => if h : k ∈ R then τS ⟨k, h⟩ else τC ⟨k, Finset.mem_compl.mpr h⟩

/-- (25:2) applied to `Γ̄`: the amount `∑_{k ∈ S} ℋ̄_k` that the composite player `S ⊆ Ī`
receives in the two-person game of `S` against `Ī - S`, when the real members of `S` play the
aggregate `τS` and the real members of `Ī - S` play `τC`. -/
def coalPayoff (S : Finset (Fin (n + 1))) (τS : Γ.CoalStrat (realPart S))
    (τC : Γ.CoalStrat (realPart S)ᶜ) : ℝ :=
  ∑ k ∈ S, Γ.extH (Γ.joint (realPart S) τS τC) k

/-- The bilinear form `K(ξ, η) = ∑_{τ^S, τ^{Ī-S}} ℋ̄(τ^S, τ^{Ī-S}) ξ_{τ^S} η_{τ^{Ī-S}}` (25.1.3
applied to `Γ̄`). `ξ` is one joint weight on all the strategy tuples of the members of `S`. -/
def bilin (S : Finset (Fin (n + 1))) (ξ : Γ.CoalStrat (realPart S) → ℝ)
    (η : Γ.CoalStrat (realPart S)ᶜ → ℝ) : ℝ :=
  ∑ τS, ∑ τC, Γ.coalPayoff S τS τC * ξ τS * η τC

/-- The *extended characteristic function* of `Γ` (57.1, 57.2.1): the characteristic function
(25.1.3) of the zero-sum extension `Γ̄`, defined for every `S ⊆ Ī = (1, …, n, n + 1)`:
`v(S) = Max_ξ Min_η K(ξ, η)`, with `ξ` ranging over the probability vectors on the aggregates of
`S` and `η` over those on the aggregates of `Ī - S`. The fictitious player's single strategy is
omitted from the aggregates (it does not change them). Both simplices are nonempty (every
`β k ≥ 1`) and `K` is bounded on them, so `⨆`/`⨅` are the book's attained Max/Min. -/
noncomputable def extCharFun (S : Finset (Fin (n + 1))) : ℝ :=
  ⨆ ξ : stdSimplex ℝ (Γ.CoalStrat (realPart S)),
    ⨅ η : stdSimplex ℝ (Γ.CoalStrat (realPart S)ᶜ),
      Γ.bilin S (ξ : Γ.CoalStrat (realPart S) → ℝ) (η : Γ.CoalStrat (realPart S)ᶜ → ℝ)

/-- The *restricted characteristic function* of `Γ` (57.1, 57.2.1): the extended one on the
sets `S ⊆ I = (1, …, n)` only (`S` viewed inside `Ī` via `Fin.castSucc`). For a zero-sum `Γ`
it is the characteristic function of 25.1.3 (57.1, p. 528). -/
noncomputable def restrictedCharFun (S : Finset (Fin n)) : ℝ :=
  Γ.extCharFun (S.map Fin.castSuccEmb)

end GeneralGame

end TheoryOfGames.GeneralGames


