-- Prove2me | Definitions.Def_DGPNash_WellSupported_Equilibria
-- name    : DGPNash_WellSupported_Equilibria
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T18:27:34.829005+00:00
-- url     : https://prove2.me/theorems/c5e624cc-4d81-40b3-964f-3095d24ba39c
-- title:
--   Approximate and approximately well-supported Nash equilibria, and the trimmed profile (Eq. (2), Eq. (27), Claim 5)
-- statement:
--   Fix a game in normal form: a finite set of players $p$, for each player a finite set $S_p$ of pure strategies, and for each player $p$ and each pure strategy profile $s\in S=\prod_q S_q$ a payoff $u^p_s\in\mathbb R$. A **mixed profile** $x=\{x^p_j\}_{j\in S_p,\,p}$ consists of one probability distribution $x^p$ on $S_p$ per player, the players randomizing independently; for $s\in S_{-p}$ (a profile of the players other than $p$) write $x_s=\prod_{q\neq p}x^q_{s_q}$.
--
--   1. **Payoff of a pure strategy.** For $j\in S_p$,
--   $$\mathcal U^p_j=\sum_{s\in S_{-p}}u^p_{js}\,x_s$$
--   is the expected payoff of player $p$ for playing $j$ while the others play $x$; and $\mathcal U^p_{\max}=\max_{j\in S_p}\mathcal U^p_j$.
--   2. **Largest payoff entry.** $\max\{u\}$ is the maximum of $u^p_s$ over all players $p$ and all profiles $s\in S$.
--   3. **ε-approximate Nash equilibrium.** $x$ is a mixed profile and, for every player $p$ and every mixed strategy $\{y^p_j\}_{j\in S_p}$ of $p$,
--   $$\sum_{j\in S_p}\mathcal U^p_j\,x^p_j\ \ge\ \sum_{j\in S_p}\mathcal U^p_j\,y^p_j-\epsilon .$$
--   4. **ε-approximately well-supported Nash equilibrium** (ε-Nash equilibrium). $x$ is a mixed profile and, for every player $p$ and all $j,j'\in S_p$,
--   $$\mathcal U^p_j>\mathcal U^p_{j'}+\epsilon\ \Longrightarrow\ x^p_{j'}=0 .$$
--   5. **Trimmed mass and trimmed profile.** For reals $\epsilon,k$ and each player $p$,
--   $$z^p=\sum_{j\in S_p}x^p_j\cdot\mathcal X_{\{\mathcal U^p_j<\mathcal U^p_{\max}-\epsilon k\}},\qquad
--   \hat x^p_j=\begin{cases}\dfrac{x^p_j}{1-z^p}, & \mathcal U^p_j\ge\mathcal U^p_{\max}-\epsilon k,\\[4pt] 0, & \text{otherwise,}\end{cases}$$
--   where $\mathcal X_A$ is the indicator of $A$. The profile $\hat x$ removes the strategies whose payoff is more than $\epsilon k$ below the best response and renormalizes the rest.
--
--   An ε-approximately well-supported equilibrium is an ε-approximate one; the trimmed profile is the device by which an approximate equilibrium is turned into an approximately well-supported one (Lemma 4.28).
--
--   **Formalization Note.** Players form a finite type $\iota$, strategies finite types `S p`, payoffs `u : ι → (∀ i, S i) → ℝ`. Mixed profiles, lotteries and expected payoffs are `AGT.IsMixedProfile`, `AGT.IsLottery` and `AGT.expectedPayoff` from the published bundle `agt_games`. $\mathcal U^p_j$ is the expected payoff of $p$ after $p$ alone switches to the pure strategy $j$; the approximate-Nash inequality is stated as the expected payoff under $x$ versus the expected payoff after $p$ alone switches to $y$, which is the same quantity as in (27). $\mathcal U^p_{\max}$ and $\max\{u\}$ are suprema over finite types, hence maxima whenever the types are nonempty (a mixed profile forces each $S_p$ to be nonempty). Both equilibrium notions include the requirement that the profile be mixed. The trimmed profile is defined for arbitrary $\epsilon,k$; the theorems state the hypotheses under which $1-z^p>0$.
-- source:
--   Daskalakis, Goldberg & Papadimitriou, The Complexity of Computing a Nash Equilibrium, SIAM J. Comput. 39(1):195–259 (2009), p. 199, Sec. 2.1, Eq. (2) and the definition of ε-approximate Nash equilibrium; p. 243, Sec. 4.7, Eq. (27) and the definitions of U^p_j, U^p_max; pp. 243–244, Claim 5 (z^p) and the profile x̂

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_DGPNash_NashMap_nashMap

/-!
# Daskalakis–Goldberg–Papadimitriou (2009), §2.1 and §4.7: approximate equilibria and the trim

C. Daskalakis, P. W. Goldberg, C. H. Papadimitriou, *The Complexity of Computing a Nash
Equilibrium*, SIAM J. Comput. 39(1):195–259 (2009), §2.1 (p. 199, Eq. (2)) and §4.7
(pp. 243–244, Eq. (27), Claim 5, the profile `x̂`).

A game in normal form is given by a finite type `ι` of players, a finite strategy type `S p` for
each player `p`, and payoffs `u : ι → (∀ i, S i) → ℝ` (`u p s` is the paper's `u^p_s`). Mixed
profiles, lotteries and expected payoffs are those of the published bundle `agt_games`.

**Formalization Note.** `purePayoff u x p j` is the paper's `𝒰^p_j = Σ_{s ∈ S_{-p}} u^p_{js} x_s`,
written as the expected payoff of `p` when `p` switches to the pure strategy `j`.
`maxPurePayoff u x p` is `𝒰^p_max = max_j 𝒰^p_j` (a supremum over the finite type `S p`; it is
the maximum when `S p` is nonempty, which every mixed profile forces). `maxPayoff u` is `max{u}`,
the largest entry of all payoff tables (a supremum over the finite types `ι` and `∀ i, S i`).
-/

namespace DGPNash.WellSupported

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {S : ι → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]

/-- The pure strategy `j` of player `p`, as a lottery on `S p`. -/
def pureStrategy {p : ι} (j : S p) : S p → ℝ := fun k => if k = j then 1 else 0

/-- `𝒰^p_max = max_j 𝒰^p_j` (p. 243). -/
noncomputable def maxPurePayoff (u : ι → (∀ i, S i) → ℝ) (x : ∀ i, S i → ℝ) (p : ι) : ℝ :=
  ⨆ j : S p, DGPNash.NashMap.purePayoff u x p j

/-- `max{u}`: the maximum entry in the payoff tables of the game, over all players and all pure
strategy profiles (Lemma 4.28, p. 243). -/
noncomputable def maxPayoff (u : ι → (∀ i, S i) → ℝ) : ℝ :=
  ⨆ p : ι, ⨆ s : (∀ i, S i), u p s

/-- **ε-approximate Nash equilibrium** (p. 199; Eq. (27), p. 243): `x` is a mixed profile and, for
every player `p` and every mixed strategy `y` of `p`, the expected payoff of `p` under `x` is at
least the expected payoff of `p` when `p` alone switches to `y`, minus `ε`. -/
def IsEpsApproxNash (u : ι → (∀ i, S i) → ℝ) (x : ∀ i, S i → ℝ) (ε : ℝ) : Prop :=
  AGT.IsMixedProfile x ∧
    ∀ (p : ι) (y : S p → ℝ), AGT.IsLottery y →
      AGT.expectedPayoff u (Function.update x p y) p - ε ≤ AGT.expectedPayoff u x p

/-- **ε-approximately well-supported Nash equilibrium** (Eq. (2), p. 199): `x` is a mixed profile
and, for every player `p` and strategies `j, j'` of `p`, if `𝒰^p_j > 𝒰^p_{j'} + ε` then
`x^p_{j'} = 0`. -/
def IsEpsWellSupportedNash (u : ι → (∀ i, S i) → ℝ) (x : ∀ i, S i → ℝ) (ε : ℝ) : Prop :=
  AGT.IsMixedProfile x ∧
    ∀ (p : ι) (j j' : S p), DGPNash.NashMap.purePayoff u x p j > DGPNash.NashMap.purePayoff u x p j' + ε → x p j' = 0

/-- `z^p = Σ_{j ∈ S_p} x^p_j · 𝒳_{\{𝒰^p_j < 𝒰^p_max − εk\}}` (Claim 5, pp. 243–244): the mass `x`
puts on strategies of `p` whose payoff is more than `εk` below the best response. -/
noncomputable def trimMass (u : ι → (∀ i, S i) → ℝ) (x : ∀ i, S i → ℝ) (ε k : ℝ) (p : ι) : ℝ :=
  ∑ j : S p, if DGPNash.NashMap.purePayoff u x p j < maxPurePayoff u x p - ε * k then x p j else 0

/-- The trimmed profile `x̂` (proof of Lemma 4.28, p. 244):
`x̂^p_j = x^p_j / (1 − z^p)` if `𝒰^p_j ≥ 𝒰^p_max − εk`, and `x̂^p_j = 0` otherwise. -/
noncomputable def trim (u : ι → (∀ i, S i) → ℝ) (x : ∀ i, S i → ℝ) (ε k : ℝ) :
    ∀ i, S i → ℝ :=
  fun p j =>
    if DGPNash.NashMap.purePayoff u x p j ≥ maxPurePayoff u x p - ε * k then
      x p j / (1 - trimMass u x ε k p)
    else 0

end DGPNash.WellSupported


