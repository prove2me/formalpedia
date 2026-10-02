-- Prove2me | Definitions.Def_TheoryOfGames_SimpleGames_Majority
-- name    : TheoryOfGames_SimpleGames_Majority
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-01T04:45:06.322156+00:00
-- url     : https://prove2.me/theorems/f0cb2b6f-f429-4298-ae4e-d6a805d2e58b
-- title:
--   Weighted majorities (50:1), (50:B), the advantage a_S (50:6), homogeneity (50:E), the imputations α^S and the sets U*, U⁺, R(β)
-- statement:
--   Let $w_1, \dots, w_n$ be real numbers (weights) and $x_1, \dots, x_n$ real numbers.
--
--   1. (50:1) $W$ is the set of all $S \subseteq I$ which contain a majority of total weight: $\sum_{i \in S} w_i > \tfrac12 \sum_{i=1}^n w_i$.
--   2. (50:B) the conditions (50:B:a) $0 \leqq w_{i_0} < \tfrac12 \sum_{i=1}^n w_i$ for all $i_0$, and (50:B:b) $\sum_{i \in S} w_i \neq \tfrac12 \sum_{i=1}^n w_i$ for all $S \subseteq I$.
--   3. (50:6) the advantage of a coalition,
--   $$a_S = 2 \sum_{i \in S} w_i - \sum_{i=1}^n w_i = \sum_{i \in S} w_i - \sum_{i \in -S} w_i.$$
--   4. (50:E) the weights are **homogeneous** if the $a_S$ have a common value $a$ for all $S$ of $W^m$, the minimal elements of the $W$ of (50:1).
--   5. (50.1.3) $w$ are weights **for the game** $\Gamma$ (the game is the weighted majority game $[w_1, \dots, w_n]$) if they fulfil (50:B) and the $W$ of (50:1) is $W_\Gamma$.
--   6. (50.4.2, 50.5.1) for a set $S$, the vector $\vec\alpha^S$ with $\alpha^S_i = -1$ for $i$ not in $S$ and $\alpha^S_i = -1 + x_i$ for $i$ in $S$; and for a system $U$ of sets, the set $V$ of all $\vec\alpha^S$, $S$ in $U$.
--   7. (50:11) for a vector $\vec\beta$, $R(\vec\beta)$ is the set of all $i$ with $\beta_i \geqq -1 + x_i$.
--   8. (50:G) $U^*$ is the set of all $R \subseteq I$ which possess some subset belonging to $U$; $U^+$ is the set of all $R \subseteq I$ for which $-R$ does not belong to $U^*$.
--
--   These objects carry §50: the weighted majority games and the main simple solution built from the minimal winning coalitions.
--
--   **Formalization Note** `weightedW w` is (50:1); `advantage w S` is $a_S$; `IsHomogeneous w` is the existence of a common value of `advantage w S` over `minimalSets (weightedW w)`. `alphaS x S`, `mainSet U x`, `rSet x β`, `uStar U`, `uPlus U` are $\vec\alpha^S$, $V$, $R(\vec\beta)$, $U^*$, $U^+$. The values $-1$ in $\vec\alpha^S$ and $R(\vec\beta)$ are $v((i)) = -\gamma$ with $\gamma = 1$, the reduced normalization §50 assumes (50.4.1); the theorems using them assume $v((i)) = -1$. The numbers $x_i$ are given for every player, including players in no minimal winning coalition (for whom the book defines none, 50.4.2); they do not enter $\vec\alpha^S$ for minimal winning $S$.
-- source:
--   von Neumann & Morgenstern, Theory of Games and Economic Behavior (60th-anniversary ed., Princeton 2007), p. 432, (50:1); p. 433, (50:B); p. 434, (50:6); p. 435, (50:E); p. 437, 50.4.2 (α^S); p. 438, 50.5.1; p. 439, (50:11), (50:G)

import Mathlib
import Definitions.Def_TheoryOfGames_SimpleGames_WinningLosing

namespace TheoryOfGames.SimpleGames

/-- (50:1), 50.1.2: for numerical weights `w₁, …, wₙ`, `W` is the set of all those `S` which
contain a majority of total weight: `∑_{i in S} wᵢ > ½ ∑_{i=1}^n wᵢ`. -/
def weightedW {n : ℕ} (w : Fin n → ℝ) : Set (Finset (Fin n)) :=
  {S | (1 / 2 : ℝ) * ∑ i, w i < ∑ i ∈ S, w i}

/-- (50:B:a) and (50:B:b), 50.1.3: for all `i₀`, `0 ≦ w_{i₀} < ½ ∑_{i=1}^n wᵢ`; and for all
`S ⊆ I`, `∑_{i in S} wᵢ ≠ ½ ∑_{i=1}^n wᵢ`. -/
def SatisfiesB {n : ℕ} (w : Fin n → ℝ) : Prop :=
  (∀ i₀ : Fin n, 0 ≤ w i₀ ∧ w i₀ < (1 / 2 : ℝ) * ∑ i, w i) ∧
  (∀ S : Finset (Fin n), ∑ i ∈ S, w i ≠ (1 / 2 : ℝ) * ∑ i, w i)

/-- (50:6), 50.2.1: `a_S = 2 ∑_{i in S} wᵢ - ∑_{i=1}^n wᵢ = ∑_{i in S} wᵢ - ∑_{i in -S} wᵢ`. -/
def advantage {n : ℕ} (w : Fin n → ℝ) (S : Finset (Fin n)) : ℝ :=
  2 * ∑ i ∈ S, w i - ∑ i, w i

/-- (50:E), 50.2.2: the weights `w₁, …, wₙ` are *homogeneous* if the `a_S` of (50:6) have a
common value `a` for all `S` of `W^m` (the minimal elements of the `W` of (50:1)). -/
def IsHomogeneous {n : ℕ} (w : Fin n → ℝ) : Prop :=
  ∃ a : ℝ, ∀ S ∈ minimalSets (weightedW w), advantage w S = a

/-- 50.1.3: `w₁, …, wₙ` are weights for the game `v` — the game is the weighted majority game
`[w₁, …, wₙ]`: the weights fulfil (50:B) and the `W` they define by (50:1) is `W_Γ`. -/
def IsWeightsFor {n : ℕ} (v : Finset (Fin n) → ℝ) (w : Fin n → ℝ) : Prop :=
  SatisfiesB w ∧ winningSets v = weightedW w

/-- 50.4.2, 50.5.1: for numbers `x₁, …, xₙ` and a set `S`, the vector `α^S` with
`α^S_i = -1` for `i` not in `S` and `α^S_i = -1 + xᵢ` for `i` in `S`. -/
noncomputable def alphaS {n : ℕ} (x : Fin n → ℝ) (S : Finset (Fin n)) : Fin n → ℝ :=
  fun i => if i ∈ S then -1 + x i else -1

/-- 50.5.1: the set `V` of the `α^S`, `S` in `U`. -/
def mainSet {n : ℕ} (U : Set (Finset (Fin n))) (x : Fin n → ℝ) : Set (Fin n → ℝ) :=
  {α | ∃ S ∈ U, α = alphaS x S}

/-- (50:11), 50.5.2: `R(β)`, the set of all `i` with `βᵢ ≧ -1 + xᵢ`. -/
noncomputable def rSet {n : ℕ} (x : Fin n → ℝ) (β : Fin n → ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => -1 + x i ≤ β i)

/-- (50:G), 50.5.2: `U*` is the set of all `R (⊆ I)` which possess some subset belonging
to `U`. -/
def uStar {n : ℕ} (U : Set (Finset (Fin n))) : Set (Finset (Fin n)) :=
  {R | ∃ T ∈ U, T ⊆ R}

/-- (50:G), 50.5.2: `U⁺` is the set of all `R (⊆ I)` for which `-R` does not belong to `U*`. -/
def uPlus {n : ℕ} (U : Set (Finset (Fin n))) : Set (Finset (Fin n)) :=
  {R | Rᶜ ∉ uStar U}

end TheoryOfGames.SimpleGames


