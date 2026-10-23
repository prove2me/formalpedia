-- Prove2me | Definitions.Def_GoTBandit_Main_Assignment
-- name    : GoTBandit_Main_Assignment
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T07:14:02.60239+00:00
-- url     : https://prove2.me/theorems/1617c4c0-112f-418a-b0d3-d85f3bad6b93
-- title:
--   §II, Eqs. (1)–(4), Definition IV.1, Lemma IV.3 (19), pp. 2–7 — collision indicator, assignment objective, J0, J1, J2, ∆min, w
-- statement:
--   This file sets up the assignment problem underlying the multiplayer bandit of Bistritz and Leshem.
--
--   There are $N$ players and $M$ arms. A **strategy profile** is a map $a=(a_1,\dots,a_N)$ assigning an arm $a_n$ to every player $n$. The **non-collision indicator** of arm $i$ in profile $a$ (Eq. (1)) is
--
--   $$
--   \eta_i(a)=\begin{cases}0,& \text{if more than one player chose arm } i,\\ 1,& \text{otherwise.}\end{cases}
--   $$
--
--   Given a matrix of (true or estimated) mean rewards $\mu=(\mu_{n,i})$, the utility of player $n$ in profile $a$ is $g_n(a)=\mu_{n,a_n}\,\eta_{a_n}(a)$: she collects the mean of her arm unless she collides. The **assignment objective** is $\sum_{n=1}^N g_n(a)$, and $a$ is **optimal** when it maximizes this objective (Eq. (4)). The file also defines:
--
--   1. the optimal objective $J_1=\max_a\sum_n g_n(a)$;
--   2. $u_{n,\max}=\max_a g_n(a)$ and $J_0=\sum_n u_{n,\max}$ (§III-A);
--   3. the **second best objective** $J_2$, the largest value of $\sum_n g_n(a)$ over the profiles with $\sum_n g_n(a)<J_1$ (Definition IV.1);
--   4. the smallest utility gap $\Delta_{\min}=\min_n\min_{a_1,a_2:\,g_n(a_1)\ne g_n(a_2)}|g_n(a_1)-g_n(a_2)|$ (Lemma IV.3);
--   5. the exponent of Eq. (19),
--   $$
--   w=\frac{\Delta_{\min}^2}{80M\,(4\sigma_{\max}^2+b_{\max}\Delta_{\min})},
--   $$
--   as a function of $\mu$, $\sigma_{\max}$ and $b_{\max}$.
--
--   These objects are shared by every statement of the mission: the same functions serve the true means (Definition II.2) and the estimated means of an epoch (Definition V.1, Eq. (28)).
--
--   **Formalization Note** Players and arms are indexed from $0$ (`Fin N`, `Fin M`). The collision indicator, written $\eta$ in the paper, is named `noColl`, because $\eta$ is also the slack parameter of Theorem V.6 and Lemmas V.7–V.8. Maxima over the finite set of profiles are real suprema of finitely many values. Junk values: $J_2=0$ when no profile has objective below $J_1$ (`sSup ∅`), and $\Delta_{\min}=0$ when no player has two profiles of different utility (`sInf ∅`); statements that need $\Delta_{\min}$ assume it positive.
-- source:
--   Bistritz and Leshem, Game of Thrones: Fully Distributed Learning for Multiplayer Bandits, arXiv:1810.11162v7, pp. 2–7, Eqs. (1)–(4), §III-A, Definition IV.1, Lemma IV.3, Eq. (19)

import Mathlib

open Finset

namespace GoTBandit.Main

noncomputable section

variable {N M : ℕ}

/-- The non-collision indicator `η_i(a)` of Eq. (1): `0` if more than one player chose
arm `i` in the profile `a`, and `1` otherwise. -/
def noColl (a : Fin N → Fin M) (i : Fin M) : ℝ :=
  if 1 < (univ.filter (fun m => a m = i)).card then 0 else 1

/-- The utility `g_n(a) = μ_{n,a_n} η_{a_n}(a)` of player `n` in profile `a` for the
reward matrix `μ` (Definition II.2; also Eq. (28) with estimated means). -/
def gUtil (μ : Fin N → Fin M → ℝ) (a : Fin N → Fin M) (n : Fin N) : ℝ :=
  μ n (a n) * noColl a (a n)

/-- The assignment objective `∑_n g_n(a)` of Eq. (4). -/
def obj (μ : Fin N → Fin M → ℝ) (a : Fin N → Fin M) : ℝ :=
  ∑ n, gUtil μ a n

/-- `a ∈ arg max_a ∑_n g_n(a)`. -/
def IsOptimal (μ : Fin N → Fin M → ℝ) (a : Fin N → Fin M) : Prop :=
  ∀ a' : Fin N → Fin M, obj μ a' ≤ obj μ a

/-- The optimal objective `J1 = max_a ∑_n g_n(a)`. -/
def J1 (μ : Fin N → Fin M → ℝ) : ℝ :=
  ⨆ a : Fin N → Fin M, obj μ a

/-- `u_{n,max} = max_a g_n(a)`. -/
def uMax (μ : Fin N → Fin M → ℝ) (n : Fin N) : ℝ :=
  ⨆ a : Fin N → Fin M, gUtil μ a n

/-- `J0 = ∑_n u_{n,max}` (§III-A, p. 4). -/
def J0 (μ : Fin N → Fin M → ℝ) : ℝ :=
  ∑ n, uMax μ n

/-- The second best objective `J2` of Definition IV.1: the largest value of the objective
strictly below `J1`. Junk value `0` (`sSup ∅`) when every profile attains `J1`. -/
def J2 (μ : Fin N → Fin M → ℝ) : ℝ :=
  sSup (Set.range (obj μ) ∩ Set.Iio (J1 μ))

/-- `∆min = min_n min_{a1,a2 | g_n(a1) ≠ g_n(a2)} |g_n(a1) − g_n(a2)|` (Lemma IV.3).
Junk value `0` (`sInf ∅`) when no player has two profiles of different utility. -/
def Δmin (μ : Fin N → Fin M → ℝ) : ℝ :=
  sInf {d : ℝ | ∃ (n : Fin N) (a₁ a₂ : Fin N → Fin M),
    gUtil μ a₁ n ≠ gUtil μ a₂ n ∧ d = |gUtil μ a₁ n - gUtil μ a₂ n|}

/-- The exponent `w = ∆min² / (80 M (4 σmax² + bmax ∆min))` of Eq. (19). -/
def wConst (μ : Fin N → Fin M → ℝ) (σmax bmax : ℝ) : ℝ :=
  Δmin μ ^ 2 / (80 * (M : ℝ) * (4 * σmax ^ 2 + bmax * Δmin μ))

end

end GoTBandit.Main


