-- Prove2me | Definitions.Def_Aumann1974_ZeroSum_Payoffs
-- name    : Aumann1974_ZeroSum_Payoffs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T11:04:02.365558+00:00
-- url     : https://prove2.me/theorems/c560a3e5-4a59-4c86-88e8-44adab61a18a
-- title:
--   Aumann (1974), Sects. 3 and 6: payoffs $H_i$, two-person zero-sum games and the value $v$
-- statement:
--   A **game** (Aumann 1974, p. 73) consists of a finite set $N$ of players, a finite set $S_i$ of pure strategies for each player, a finite set $X$ of outcomes and an outcome function $g : S=\times_{i}S_i \to X$ onto $X$; player $i$ has a utility function $u_i : X\to\mathbb R$ (Assumption I). This bundle defines:
--
--   1. **Pure payoffs.** $h_i(a) = u_i(g(a))$ for a pure strategy profile $a\in S$.
--   2. **Expected payoffs** (3.1). For a profile $s=(s_1,\dots,s_n)$ of randomized strategies $s_j:\Omega\to S_j$,
--   $$H_i(s) = E_i\big(h_i(s)\big) = \int_\Omega h_i\big(s(\omega)\big)\,dp_i(\omega),$$
--   the expectation being taken under player $i$'s **own** subjective probability $p_i$.
--   3. **Two-person zero-sum games** (p. 79). $N=\{1,2\}$ and the adopted utilities satisfy $u_1(x)+u_2(x)=0$ for all $x\in X$.
--   4. **The value** (p. 79). $v$ is the value of the game if $v = F_1(\sigma)$ for some Nash equilibrium $\sigma=(\sigma_1,\sigma_2)$ of the mixed extension, where $\sigma_i$ is a distribution on $S_i$ and $F_i(\sigma)=\sum_{a\in S} h_i(a)\,\sigma_1(a_1)\sigma_2(a_2)$ (p. 77); a Nash equilibrium is a pair against which neither player raises $F_i$ by switching to another distribution.
--
--   Because the two players evaluate $H_1$ and $H_2$ under different measures, $H_1(s)+H_2(s)$ need not vanish even in a zero-sum game; this is what the paper's Proposition 6.1 exploits.
--
--   **Formalization Note** The paper defines $v$ through an equilibrium point in objective mixed strategies, whose payoff is $(v,-v)$ by the minimax theorem; by the paper's Proposition 4.3 these payoffs are exactly the Nash equilibrium payoffs of the mixed extension, which is what is encoded here, using `AGT.IsMixedNash` and `AGT.expectedPayoff` from the published definition `agt_games`. By the minimax theorem (`AGT.zero_sum_minimax`), in a finite zero-sum game with nonempty strategy sets exactly one real number is the value. Players $1,2$ are `0, 1 : Fin 2`. $H_i$ is a Bochner integral; for strategies with finitely many values it is the finite sum $\sum_a p_i\{s=a\}\,h_i(a)$.
-- source:
--   R. J. Aumann, Subjectivity and Correlation in Randomized Strategies, J. Math. Econ. 1 (1974) 67–96, https://doi.org/10.1016/0304-4068(74)90037-8, Sect. 3, p. 73 (PDF p. 7): game (1)–(4); p. 76 (PDF p. 10): h_i and (3.1); Sect. 4, p. 77 (PDF p. 11): F_i and Nash equilibrium; Sect. 6, p. 79 (PDF p. 13): 2-person 0-sum game and its value

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_Aumann1974_ZeroSum_RandomizingStructure

/-!
# Aumann (1974), Sects. 3 and 6: payoffs, zero-sum games and the value

R. J. Aumann, *Subjectivity and Correlation in Randomized Strategies*, J. Math. Econ. 1 (1974),
Sect. 3, pp. 73–76 (PDF pp. 7–10), Sect. 4, p. 77 (PDF p. 11), and Sect. 6, p. 79 (PDF p. 13).

A game consists of a finite set of players, a finite set `Sᵢ` of pure strategies for each
player, a finite set `X` of outcomes and an outcome function `g : S → X` onto `X`, where
`S = ×ᵢ Sᵢ` (p. 73). Player `i` has a utility `uᵢ : X → ℝ` (Assumption I, p. 74). This bundle
defines the pure payoff `hᵢ = uᵢ ∘ g`, the expected payoff `Hᵢ(s)` of a profile of randomized
strategies (3.1), the zero-sum condition and the value of a two-person zero-sum game.

**Formalization Note.** The game is not bundled: the players are a type `ι`, the pure strategies a
family `S : ι → Type*`, the outcomes a type `X`, the outcome function `g : (∀ i, S i) → X` and the
utilities `u : ι → X → ℝ`. The finiteness of `Sᵢ`, `X` and the surjectivity of `g` are hypotheses
of the theorems. Players `1, 2` of a two-person game are `0, 1 : Fin 2`. Nash equilibria of the
mixed extension are those of the published definition `agt_games` (`AGT.IsMixedNash`).
-/

namespace Aumann1974.ZeroSum

open MeasureTheory

variable {ι : Type*} {Ω : Type*} {mΩ : MeasurableSpace Ω}
variable {S : ι → Type*} {X : Type*}

/-- **Pure payoff function** (Aumann 1974, Sect. 3, p. 76, PDF p. 10): for a pure strategy
`n`-tuple `a ∈ S`, `hᵢ(a) = uᵢ(g(a))`.

**Formalization Note.** The result has the shape `ι → (∀ i, S i) → ℝ` of the payoff argument of
`AGT.expectedPayoff` and `AGT.IsMixedNash`, so that `AGT.expectedPayoff (payoffFn u g) σ i` is the
paper's `Fᵢ(σ) = Σₐ hᵢ(a) Πⱼ σⱼ(aⱼ)` (p. 77). -/
def payoffFn (u : ι → X → ℝ) (g : (∀ i, S i) → X) : ι → (∀ i, S i) → ℝ :=
  fun i a => u i (g a)

/-- **Expected payoff** (Aumann 1974, Sect. 3, eq. (3.1), p. 76, PDF p. 10): for an `n`-tuple
`s` of randomized strategies,
`Hᵢ(s) = Eᵢ(hᵢ(s)) = ∫_Ω hᵢ(s(ω)) dpᵢ(ω)`,
the expectation being taken with respect to player `i`'s **own** subjective probability `pᵢ`.

**Formalization Note.** Bochner integral. When every `sⱼ` is a strategy (level sets in
`𝒥ⱼ ⊆ ℬ`) and the `Sⱼ` are finite, the integrand takes finitely many values and is
`ℬ`-measurable, hence bounded and `pᵢ`-integrable, so the integral is the paper's expectation
`Σₐ pᵢ{s = a} hᵢ(a)`; every theorem using `H` requires its profiles to be strategies. -/
noncomputable def H (R : RandomizingStructure ι Ω mΩ) (u : ι → X → ℝ) (g : (∀ i, S i) → X)
    (s : ∀ i, Ω → S i) (i : ι) : ℝ :=
  ∫ ω, payoffFn u g i (fun j => s j ω) ∂(R.p i)

/-- **Two-person zero-sum game** (Aumann 1974, Sect. 6, p. 79, PDF p. 13): a game with `n = 2`
whose (adopted) utility functions satisfy `u₁(x) + u₂(x) = 0` for all `x ∈ X`.

**Formalization Note.** `n = 2` is the choice of `Fin 2` as the player type; this predicate is
the utility condition for the adopted pair `u = (u₁, u₂)`. -/
def IsZeroSum (u : Fin 2 → X → ℝ) : Prop :=
  ∀ x, u 0 x + u 1 x = 0

/-- **Value of a two-person zero-sum game** (Aumann 1974, Sect. 6, p. 79, PDF p. 13): "one
defines the value of the game as usual. Specifically, Proposition 4.3 provides an equilibrium
point in objective mixed strategies; by the minimax theorem, all such equilibrium points must
have the same payoff, which is of the form `(v, −v)`. Then `v` is called the value of the game."

`IsValue u g v` says that `v` is player 1's payoff `F₁(σ)` at some Nash equilibrium `σ` of the
mixed extension (p. 77): a pair of distributions on `S₁`, `S₂` against which neither player can
raise his expected payoff `Fᵢ` by switching to another distribution.

**Formalization Note.** By Proposition 4.3 of the paper the Nash equilibrium payoffs are exactly
the objective mixed equilibrium payoffs of the model, so this is the paper's definition, stated
without the randomizing structure. By the minimax theorem (von Neumann; on the platform
`AGT.zero_sum_minimax`) a finite zero-sum game with nonempty strategy sets has a Nash equilibrium
and all its Nash equilibria give player 1 the same payoff, so for a zero-sum `u` exactly one `v`
satisfies `IsValue u g v`; player 2's payoff is then `−v`. -/
def IsValue {S : Fin 2 → Type*} [∀ i, Fintype (S i)] (u : Fin 2 → X → ℝ)
    (g : (∀ i, S i) → X) (v : ℝ) : Prop :=
  ∃ σ : ∀ i, S i → ℝ, AGT.IsMixedNash (payoffFn u g) σ ∧
    AGT.expectedPayoff (payoffFn u g) σ 0 = v

end Aumann1974.ZeroSum


