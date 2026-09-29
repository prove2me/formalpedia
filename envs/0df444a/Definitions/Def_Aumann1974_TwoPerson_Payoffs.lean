-- Prove2me | Definitions.Def_Aumann1974_TwoPerson_Payoffs
-- name    : Aumann1974_TwoPerson_Payoffs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T10:29:09.957591+00:00
-- url     : https://prove2.me/theorems/ce1093ef-797e-40cd-9673-787112e6bc21
-- title:
--   Aumann (1974), Sect. 3: pure payoffs $h_i = u_i\circ g$, expected payoffs $H_i(s)$, equilibrium points
-- statement:
--   A *game* (Aumann 1974, Sect. 3, p. 73) consists of a finite set $N$ of players, a finite set $S_i$ of pure strategies for each $i\in N$, a finite set $X$ of outcomes, and an outcome function $g$ from $S = \times_{i\in N} S_i$ onto $X$. Player $i$ has a utility function $u_i : X \to \mathbb R$ (Assumption I, p. 74). On a randomizing structure $(\Omega,\mathcal B,(\mathcal J_i),(p_i))$ this bundle defines:
--
--   1. **Pure payoffs.** For $a\in S$, $h_i(a) = u_i(g(a))$.
--   2. **Expected payoffs** (eq. (3.1), p. 76). For an $n$-tuple $s=(s_1,\dots,s_n)$ of strategies,
--   $$H_i(s) = E_i\big(h_i(s)\big) = \int_\Omega h_i\big(s(\omega)\big)\,dp_i(\omega),$$
--   the expectation being taken with respect to player $i$'s **own** subjective probability $p_i$.
--   3. **Equilibrium point** (p. 74). An $n$-tuple $s$ of strategies such that for every player $i$ and every strategy $t_i$ of $i$,
--   $$H_i(s) \ge H_i(s_1,\dots,s_{i-1},t_i,s_{i+1},\dots,s_n).$$
--
--   The payoff vector $H(s) = (H_1(s),\dots,H_n(s))$ of an equilibrium point is an *equilibrium payoff*; when all $s_i$ are objective and mixed it is an *objective mixed equilibrium payoff* (p. 76).
--
--   **Formalization Note** The paper defines equilibrium through the preference orders $\succsim_i$ on lotteries; by Assumption I, $x \succsim_i y$ iff $\int u_i(x)\,dp_i \ge \int u_i(y)\,dp_i$, which is the comparison of $H_i$ used here. Deviations $t_i$ range over **all** $\mathcal J_i$-measurable strategies, not only mixed or objective ones. The integral is a Bochner integral; for strategy profiles over finite $S_i$ the integrand is measurable with finitely many values, hence integrable. `payoffFn u g` has the shape of the payoff argument of `AGT.expectedPayoff` (definition `agt_games`), so the paper's $F_i(\sigma)$ of p. 77 is `AGT.expectedPayoff (payoffFn u g) σ i`.
-- source:
--   R. J. Aumann, Subjectivity and Correlation in Randomized Strategies, J. Math. Econ. 1 (1974) 67–96, https://doi.org/10.1016/0304-4068(74)90037-8, Sect. 3: game (1)–(4), p. 73 (PDF p. 7); equilibrium point and Assumption I, p. 74 (PDF p. 8); h_i, eq. (3.1), equilibrium and objective mixed equilibrium payoffs, p. 76 (PDF p. 10)

import Mathlib
import Definitions.Def_Aumann1974_TwoPerson_RandomizingStructure

/-!
# Aumann (1974), Sect. 3: payoffs and equilibrium points

R. J. Aumann, *Subjectivity and Correlation in Randomized Strategies*, J. Math. Econ. 1 (1974),
Sect. 3, pp. 73–76 (PDF pp. 7–10).

A game consists of a finite set of players, a finite set `Sᵢ` of pure strategies for each
player, a finite set `X` of outcomes and an outcome function `g : S → X` onto `X`, where
`S = ×ᵢ Sᵢ` (p. 73). Player `i` has a utility `uᵢ : X → ℝ` (Assumption I, p. 74). This bundle
defines the pure payoff `hᵢ = uᵢ ∘ g`, the expected payoff `Hᵢ(s)` of a profile of randomized
strategies (3.1), and equilibrium points.

**Formalization Note.** The game is not bundled: the players are a type `ι`, the pure strategies a
family `S : ι → Type*`, the outcomes a type `X`, the outcome function `g : (∀ i, S i) → X` and the
utilities `u : ι → X → ℝ`. The finiteness of `ι`, `Sᵢ`, `X` and the surjectivity of `g` are
hypotheses of the theorems that use these definitions. A profile of randomized strategies is a
function `s : ∀ i, Ω → S i`.
-/

namespace Aumann1974.TwoPerson

open MeasureTheory

variable {ι : Type*} {Ω : Type*} {mΩ : MeasurableSpace Ω}
variable {S : ι → Type*} {X : Type*}

/-- **Pure payoff function** (Aumann 1974, Sect. 3, p. 76, PDF p. 10): for a pure strategy
`n`-tuple `a ∈ S`, `hᵢ(a) = uᵢ(g(a))`.

**Formalization Note.** The result has the shape `ι → (∀ i, S i) → ℝ` of the payoff argument of
`AGT.expectedPayoff` and `AGT.IsMixedNash` (definition `agt_games`), so that `AGT.expectedPayoff
(payoffFn u g) σ i = ∑ₐ hᵢ(a) ∏ⱼ σⱼ(aⱼ)` is the paper's `Fᵢ(σ)` (p. 77). -/
def payoffFn (u : ι → X → ℝ) (g : (∀ i, S i) → X) : ι → (∀ i, S i) → ℝ :=
  fun i a => u i (g a)

/-- **Expected payoff** (Aumann 1974, Sect. 3, eq. (3.1), p. 76, PDF p. 10): for an `n`-tuple
`s` of randomized strategies,
`Hᵢ(s) = Eᵢ(hᵢ(s)) = ∫_Ω hᵢ(s(ω)) dpᵢ(ω)`,
the expectation being taken with respect to player `i`'s **own** subjective probability `pᵢ`.
The vector `H(s) = (H₁(s), …, Hₙ(s))` is `fun i => H R u g s i`.

**Formalization Note.** Bochner integral. When every `sⱼ` is a strategy (level sets in
`𝒥ⱼ ⊆ ℬ`) and the `Sⱼ` are finite, the integrand takes finitely many values and is
`ℬ`-measurable, hence bounded and `pᵢ`-integrable, so the integral is the paper's expectation
`∑ₐ pᵢ{s = a} hᵢ(a)`; every theorem using `H` assumes its profiles are strategies. -/
noncomputable def H (R : RandomizingStructure ι Ω mΩ) (u : ι → X → ℝ) (g : (∀ i, S i) → X)
    (s : ∀ i, Ω → S i) (i : ι) : ℝ :=
  ∫ ω, payoffFn u g i (fun j => s j ω) ∂(R.p i)

/-- **Equilibrium point** (Aumann 1974, Sect. 3, p. 74, PDF p. 8, with Assumption I and
p. 76): an `n`-tuple `s = (s₁, …, sₙ)` of strategies such that for all `i` and all strategies
`tᵢ` of `i`, `g(s) ≿ᵢ g(s₁, …, sᵢ₋₁, tᵢ, sᵢ₊₁, …, sₙ)`, i.e. (Assumption I)
`Hᵢ(s) ≥ Hᵢ(s₁, …, sᵢ₋₁, tᵢ, sᵢ₊₁, …, sₙ)`.

**Formalization Note.** Deviations `tᵢ` range over **all** strategies of `i` (all
`𝒥ᵢ`-measurable functions `Ω → Sᵢ`), not only mixed or objective ones. By Assumption I,
`x ≿ᵢ y` iff `∫ uᵢ(x) dpᵢ ≥ ∫ uᵢ(y) dpᵢ`, which is the comparison of `Hᵢ` used here. -/
def IsEquilibrium [DecidableEq ι] (R : RandomizingStructure ι Ω mΩ) (u : ι → X → ℝ)
    (g : (∀ i, S i) → X) (s : ∀ i, Ω → S i) : Prop :=
  (∀ i, IsStrategy R i (s i)) ∧
    ∀ (i : ι) (t : Ω → S i), IsStrategy R i t →
      H R u g (Function.update s i t) i ≤ H R u g s i

end Aumann1974.TwoPerson


