-- Prove2me | Definitions.Def_FixpNash_Bubelis_Gadget
-- name    : FixpNash_Bubelis_Gadget
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T06:44:31.796144+00:00
-- url     : https://prove2.me/theorems/535b6e49-1309-426f-a97f-594be9d743a5
-- title:
--   Lemma 7, p. 25 — the polynomial f, Bubelis's three-player gadget $G_f$, and fully mixed profiles
-- statement:
--   This file fixes the game $G_f$ that Etessami and Yannakakis build in the proof of Lemma 7 (after Bubelis), together with the polynomial $f$ it encodes.
--
--   **The polynomial.** Let $m \ge 0$ and let $c_0, \dots, c_m$ be real numbers. The polynomial is
--   $$
--   f(x) = c_0 x^m + c_1 x^{m-1} + \dots + c_m = \sum_{j=0}^{m} c_j\, x^{m-j},
--   $$
--   so $c_j$ is the coefficient of $x^{m-j}$. The leading coefficient $c_0$ may be $0$: the degree is at most $m$, not exactly $m$.
--
--   **The game.** $G_f$ has three players: the *primary* player $1$, with the two strategies $0, 1$, and the *auxiliary* players $2$ and $3$, each with the $m+1$ strategies $0, 1, \dots, m$. For a pure profile $s = (s_1, s_2, s_3)$ and a predicate $P$, write $\chi(P) \in \{0,1\}$ for its indicator. The payoffs are
--   $$
--   h^f_1(s) = \begin{cases} c_{s_2} & s_1 = 1,\\ 0 & s_1 = 0,\end{cases}\qquad
--   h^f_2(s) = \chi(s_2 = s_3),
--   $$
--   $$
--   h^f_3(s) = \chi\big(s_2 + 1 \equiv s_3 \bmod (m+1)\big) - \chi(s_1 = 0)\,\chi(s_2 = s_3) - \chi(s_1 = 1)\,\chi(s_3 = 0).
--   $$
--   In words: if $s_1 = 0$, player 3 receives $1$ if $s_2 + 1 \equiv s_3 \pmod{m+1}$, $-1$ if $s_2 = s_3$, and $0$ otherwise; if $s_1 = 1$, player 3 receives $1$ if $s_2 + 1 \equiv s_3 \pmod{m+1}$ and $s_3 \neq 0$, $-1$ if $s_3 = 0$ and $s_2 \ne m$, and $0$ otherwise. The payoffs of the auxiliary players do not depend on $f$ and take only the values $0$, $1$ and $-1$; the payoff of the primary player on $(s_1, s_2, s_3)$ is $c_{s_2}$ if $s_1 = 1$ and $0$ if $s_1 = 0$. These are the last two properties listed in Lemma 7, and they hold by this definition.
--
--   **Fully mixed profiles.** A mixed profile is *fully mixed* if every pure strategy of every player (here: both strategies of player 1 and all $m+1$ strategies of players 2 and 3) is played with positive probability.
--
--   Mixed strategies, expected payoffs and mixed Nash equilibria are those of the published vocabulary `agt_games`; this file adds only the gadget.
--
--   **Formalization Note** The players are a three-element type `primary | aux2 | aux3` (the paper's players 1, 2, 3); the strategy sets are `Fin 2` and `Fin (m+1)` with 0-based labels, as on the page. The coefficients are a function `c : Fin (m+1) → ℝ` and `poly c ξ` is the explicit sum $\sum_j c_j \xi^{m-j}$ with natural-number exponent $m - j$, exact since $j \le m$. The coefficients are real, a generalization of the paper's rational ones. The congruence $s_2 + 1 \equiv s_3 \pmod{m+1}$ is the equation $s_2 + 1 = s_3$ in `Fin (m+1)`, whose addition is modulo $m+1$.
-- source:
--   Etessami & Yannakakis, On the complexity of Nash equilibria and other fixed points, author manuscript (SIAM J. Comput. 39 (2010)), Lemma 7 and its proof, p. 25; fully mixed, p. 10

import Mathlib
import Definitions.Def_agt_games

namespace FixpNash.Bubelis

open Finset

/-- The three players of the gadget `G_f` of Lemma 7 (p. 25): the primary player 1 and the
auxiliary players 2 and 3. -/
inductive Player
  | primary
  | aux2
  | aux3
  deriving DecidableEq

instance Player.instFintype : Fintype Player :=
  ⟨{.primary, .aux2, .aux3}, by intro p; cases p <;> simp⟩

/-- The strategy sets of `G_f` (p. 25): the primary player has the strategies `0, 1`, each
auxiliary player has the `m + 1` strategies `0, 1, …, m`. Labels are 0-based, as on the page. -/
abbrev Strat (m : ℕ) : Player → Type
  | .primary => Fin 2
  | .aux2 => Fin (m + 1)
  | .aux3 => Fin (m + 1)

instance Strat.instFintype (m : ℕ) : ∀ p, Fintype (Strat m p) := by
  intro p; cases p <;> dsimp [Strat] <;> infer_instance

instance Strat.instDecidableEq (m : ℕ) : ∀ p, DecidableEq (Strat m p) := by
  intro p; cases p <;> dsimp [Strat] <;> infer_instance

/-- The polynomial `f(x) = c₀ xᵐ + … + c_m` of Lemma 7 (p. 25): the coefficient `c j` multiplies
`x ^ (m - j)`. The natural-number subtraction is exact because `j ≤ m`. -/
def poly {m : ℕ} (c : Fin (m + 1) → ℝ) (ξ : ℝ) : ℝ :=
  ∑ j : Fin (m + 1), c j * ξ ^ (m - (j : ℕ))

/-- The payoff functions `h^f_1, h^f_2, h^f_3` of the gadget `G_f` (p. 25), on a pure profile
`s = (s₁, s₂, s₃)`, with `χ` the indicator of a predicate:
* `h^f_1(s) = c_{s₂}` if `s₁ = 1`, and `0` otherwise;
* `h^f_2(s) = 1` if `s₂ = s₃`, and `0` otherwise;
* `h^f_3(s) = χ(s₂ + 1 ≡ s₃ mod (m + 1)) − χ(s₁ = 0) χ(s₂ = s₃) − χ(s₁ = 1) χ(s₃ = 0)`.
Addition in `Fin (m + 1)` is addition modulo `m + 1`, so `s₂ + 1 = s₃` in `Fin (m + 1)` is the
congruence `s₂ + 1 ≡ s₃ mod (m + 1)`. -/
def gadget {m : ℕ} (c : Fin (m + 1) → ℝ) : Player → (∀ p, Strat m p) → ℝ
  | .primary, s => if s .primary = 1 then c (s .aux2) else 0
  | .aux2, s => if s .aux2 = s .aux3 then 1 else 0
  | .aux3, s =>
      (if s .aux2 + 1 = s .aux3 then 1 else 0)
        - (if s .primary = 0 then 1 else 0) * (if s .aux2 = s .aux3 then 1 else 0)
        - (if s .primary = 1 then 1 else 0) * (if s .aux3 = 0 then 1 else 0)

/-- A mixed profile is **fully mixed** (p. 10) if every pure strategy of every player is played
with positive probability. -/
def IsFullyMixed {m : ℕ} (x : ∀ p, Strat m p → ℝ) : Prop :=
  ∀ p (s : Strat m p), 0 < x p s

end FixpNash.Bubelis


