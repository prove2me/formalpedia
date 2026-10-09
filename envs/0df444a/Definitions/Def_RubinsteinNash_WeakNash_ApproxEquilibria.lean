-- Prove2me | Definitions.Def_RubinsteinNash_WeakNash_ApproxEquilibria
-- name    : RubinsteinNash_WeakNash_ApproxEquilibria
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T00:47:47.118057+00:00
-- url     : https://prove2.me/theorems/8af55084-e107-4bf9-a492-6249c57d59b4
-- title:
--   Defs. 2.5–2.8, p. 10, and §8.1, p. 50 — ε-best responses, (ε, δ)-WeakNash, (ε, δ)-Well-Supported WeakNash, the trimmed profile x̂
-- statement:
--   Let $\mathcal I$ be a finite set of players, $A_i$ the finite action set of player $i$, $u_i$ its utility, and $x=(x_i)_{i}$ a vector of mixed strategies, $x_i\in\Delta A_i$. For an action $s\in A_i$ write $U^i_s(x^{-i})=\mathbb E_{a_{-i}\sim x_{-i}}[u_i(s,a_{-i})]$, and $U^i_{\max}(x^{-i})=\max_{s\in A_i}U^i_s(x^{-i})$.
--
--   1. **$\epsilon$-best mixed response** (the per-player condition of Definitions 2.5 and 2.7): $x_i$ is an $\epsilon$-best response to $x_{-i}$ if
--   $$\mathbb E_{a\sim x}[u_i(a)]\ \ge\ \max_{x_i'\in\Delta A_i}\mathbb E_{a\sim(x_i';x_{-i})}[u_i(a)]-\epsilon .$$
--   2. **$\epsilon$-well-supported at $i$** (the per-player condition of Definitions 2.6 and 2.8): every $a_i$ in the support of $x_i$ satisfies $U^i_{a_i}(x^{-i})\ge\max_{a'\in A_i}U^i_{a'}(x^{-i})-\epsilon$.
--   3. **$(\epsilon,\delta)$-WeakNash** (Definition 2.7): for at least a $(1-\delta)$-fraction of the players $i$ (with $i$ uniform over all players), $x_i$ is an $\epsilon$-best mixed response to $x_{-i}$.
--   4. **$(\epsilon,\delta)$-Well-Supported WeakNash** (Definition 2.8): for at least a $(1-\delta)$-fraction of the players $i$, every action in the support of $x_i$ is an $\epsilon$-best response to $x_{-i}$.
--   5. **The trimmed profile** $\hat x$ (proof of Lemma 8.1): for $k>0$, let $z^v$ be the total probability that $x^v$ puts on actions $s$ with $U^v_s(x^{-v})<U^v_{\max}(x^{-v})-\epsilon k$. For every player $v$ who plays $\epsilon$-optimally in $x$,
--   $$\hat x^v_s=\begin{cases}\dfrac{x^v_s}{1-z^v}, & U^v_s(x^{-v})\ge U^v_{\max}(x^{-v})-\epsilon k,\\[4pt] 0, & \text{otherwise,}\end{cases}$$
--   and every other player keeps $\hat x^v=x^v$.
--
--   The relaxation from all players to most players is what makes WeakNash the target of the PPAD-hardness reductions in the paper; the trim converts the mixed-response notion into the support notion at a small loss.
--
--   **Formalization Note.** Mixed strategies, profiles and expected payoffs are those of the published `agt_games` bundle; $U^i_s$ is `DGPNash.NashMap.purePayoff`, and $z^v$, the trim formula and $U^v_{\max}$ are `trimMass`, `trim` and `maxPurePayoff` of `DGPNash_WellSupported_Equilibria`. The maxima are written as "for every lottery $y$" and "for every action $a'$". "A $(1-\delta)$-fraction of $i$'s" is the inequality $(1-\delta)\,|\mathcal I|\le\#\{i:\dots\}$, and both WeakNash notions include that $x$ is a mixed profile. The support of $x_i$ is $\{a: x_i(a)>0\}$. The page defines $\hat x^v$ only for the players who play $\epsilon$-optimally; the formalization lets every other player keep $x^v$ (for such a player $z^v$ may equal $1$, and the formula would not give a distribution).
-- source:
--   Rubinstein, arXiv:1606.04550 (version dated August 26, 2016), Definitions 2.5–2.8, p. 10, and proof of Lemma 8.1, §8.1, p. 50 (definition of x̂ and z^v)

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_DGPNash_NashMap_nashMap
import Definitions.Def_DGPNash_WellSupported_Equilibria

namespace RubinsteinNash.WeakNash

open Finset Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {S : ι → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]

/-- `x_i` is an **ε-best (mixed) response** to `x_{-i}` (the per-player condition of
Definitions 2.5 and 2.7, p. 10): no lottery `y` over `i`'s actions raises `i`'s expected payoff
by more than `ε`, i.e. `E_{a∼x}[u_i(a)] ≥ max_{x'_i ∈ ΔA_i} E_{a∼(x'_i; x_{-i})}[u_i(a)] − ε`. -/
def IsEpsBestResponse (u : ι → (∀ i, S i) → ℝ) (x : ∀ i, S i → ℝ) (ε : ℝ) (i : ι) : Prop :=
  ∀ y : S i → ℝ, AGT.IsLottery y →
    AGT.expectedPayoff u (Function.update x i y) i - ε ≤ AGT.expectedPayoff u x i

/-- Every action in the support of `x_i` is an **ε-best response** to `x_{-i}` (the per-player
condition of Definitions 2.6 and 2.8, p. 10): for all `a_i` with `x_i(a_i) > 0` and every
`a' ∈ A_i`, `E_{a_{-i}∼x_{-i}}[u_i(a_i, a_{-i})] ≥ E_{a_{-i}∼x_{-i}}[u_i(a', a_{-i})] − ε`. -/
def IsEpsWellSupportedAt (u : ι → (∀ i, S i) → ℝ) (x : ∀ i, S i → ℝ) (ε : ℝ) (i : ι) : Prop :=
  ∀ a : S i, 0 < x i a → ∀ a' : S i,
    DGPNash.NashMap.purePayoff u x i a' - ε ≤ DGPNash.NashMap.purePayoff u x i a

/-- **(ε, δ)-WeakNash** (Definition 2.7, p. 10): `x` is a mixed profile, and for at least a
`(1 − δ)`-fraction of all players `i` (`i` uniform over the player set), `x_i` is an ε-best
mixed response to `x_{-i}`. -/
def IsWeakNash (u : ι → (∀ i, S i) → ℝ) (x : ∀ i, S i → ℝ) (ε δ : ℝ) : Prop :=
  AGT.IsMixedProfile x ∧
    (1 - δ) * (Fintype.card ι : ℝ) ≤
      ((univ.filter (fun i => IsEpsBestResponse u x ε i)).card : ℝ)

/-- **(ε, δ)-Well-Supported WeakNash** (Definition 2.8, p. 10): `x` is a mixed profile, and for
at least a `(1 − δ)`-fraction of all players `i`, every action in the support of `x_i` is an
ε-best response to `x_{-i}`. -/
def IsWellSupportedWeakNash (u : ι → (∀ i, S i) → ℝ) (x : ∀ i, S i → ℝ) (ε δ : ℝ) : Prop :=
  AGT.IsMixedProfile x ∧
    (1 - δ) * (Fintype.card ι : ℝ) ≤
      ((univ.filter (fun i => IsEpsWellSupportedAt u x ε i)).card : ℝ)

/-- The trimmed profile `x̂` of the proof of Lemma 8.1 (p. 50): every player `v` who plays
ε-optimally in `x` keeps only the actions within `εk` of the best response,
`x̂^v_s = x^v_s / (1 − z^v)` if `U^v_s(x^{-v}) ≥ U^v_max(x^{-v}) − εk` and `0` otherwise
(`DGPNash.WellSupported.trim`); every other player keeps `x^v`. -/
noncomputable def weakTrim (u : ι → (∀ i, S i) → ℝ) (x : ∀ i, S i → ℝ) (ε k : ℝ) :
    ∀ i, S i → ℝ :=
  fun i => if IsEpsBestResponse u x ε i then DGPNash.WellSupported.trim u x ε k i else x i

end RubinsteinNash.WeakNash


