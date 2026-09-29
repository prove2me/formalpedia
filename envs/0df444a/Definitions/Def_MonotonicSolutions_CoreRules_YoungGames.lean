-- Prove2me | Definitions.Def_MonotonicSolutions_CoreRules_YoungGames
-- name    : MonotonicSolutions_CoreRules_YoungGames
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T19:57:47.801464+00:00
-- url     : https://prove2.me/theorems/4fdba953-a603-409d-a6da-a6879d33272a
-- title:
--   The five-player games $w$ and $v$ of the proof of Theorem 1
-- statement:
--   Let $N = \{1, 2, 3, 4, 5\}$ and consider the five coalitions
--   $$S_1 = \{3,5\},\quad S_2 = \{1,2,3\},\quad S_3 = \{1,3,4\},\quad S_4 = \{2,4,5\},\quad S_5 = \{1,2,4,5\}.$$
--
--   The game $w$ is defined by
--   $$w(S_1) = w(S_2) = 3,\qquad w(S_3) = w(S_4) = w(S_5) = 9,\qquad w(N) = 11,$$
--   and for every other coalition $S$, $w(S) = \max_{S_k \subseteq S} w(S_k)$, or $w(S) = 0$ if $S$ contains no $S_k$. (The values are consistent: the only inclusion among the $S_k$ is $S_4 \subseteq S_5$, and $w(S_4) = w(S_5)$.)
--
--   The game $v$ is identical to $w$ except that
--   $$v(S_5) = v(N) = 12 .$$
--
--   These are the counterexample games of the proof of Theorem 1: $v$ is obtained from $w$ by raising the values of two coalitions, $S_5$ and $N$, both of which contain players 2 and 4.
--
--   **Formalization Note** Players $1,\dots,5$ are the Lean indices $0,\dots,4$, so `youngCoalition = ![{2,4}, {0,1,2}, {0,2,3}, {1,3,4}, {0,1,3,4}]`. The value function `youngMaxFun val top S` equals `top` on $S = N$ and otherwise the largest `val k` over the $k$ with $S_k \subseteq S$ (a supremum in $\mathbb{N}$, hence $0$ when no $S_k \subseteq S$), cast to $\mathbb{R}$. Then `youngW = youngMaxGame ![3,3,9,9,9] 11` and `youngV = youngMaxGame ![3,3,9,9,12] 12`. At $S = S_k$ the formula returns the listed value $w(S_k)$. The only coalitions containing $S_5$ are $S_5$ and $N$, so `youngV` agrees with `youngW` everywhere except at $S_5$ and $N$. The file contains the structural lemma `youngMaxFun_empty` (the value of $\emptyset$ is $0$), needed to form a `Game 5`.
-- source:
--   Young, Monotonic Solutions of Cooperative Games, Int. J. Game Theory 14 (1985), p. 69, proof of Theorem 1

import Mathlib
import Definitions.Def_MonotonicSolutions_CoreRules_Game

namespace MonotonicSolutions.CoreRules

/-- The five coalitions of the proof of Theorem 1 (Young 1985, p. 69), with the paper's
players `1, …, 5` renamed `0, …, 4`:
`S₁ = {3,5}`, `S₂ = {1,2,3}`, `S₃ = {1,3,4}`, `S₄ = {2,4,5}`, `S₅ = {1,2,4,5}`. -/
def youngCoalition : Fin 5 → Finset (Fin 5) :=
  ![{2, 4}, {0, 1, 2}, {0, 2, 3}, {1, 3, 4}, {0, 1, 3, 4}]

/-- The value function of the games of the proof of Theorem 1: `S ↦ top` on the grand
coalition, and otherwise the largest `val k` over the listed coalitions `S_k ⊆ S`
(`0` if `S` contains no `S_k`). -/
def youngMaxFun (val : Fin 5 → ℕ) (top : ℕ) (S : Finset (Fin 5)) : ℝ :=
  if S = Finset.univ then (top : ℝ)
  else (((Finset.univ.filter (fun k => youngCoalition k ⊆ S)).sup val : ℕ) : ℝ)

theorem youngMaxFun_empty (val : Fin 5 → ℕ) (top : ℕ) : youngMaxFun val top ∅ = 0 := by
  unfold youngMaxFun
  have h1 : (∅ : Finset (Fin 5)) ≠ Finset.univ := by decide
  have h2 : Finset.univ.filter (fun k => youngCoalition k ⊆ (∅ : Finset (Fin 5))) = ∅ := by
    decide
  rw [if_neg h1, h2]
  simp

/-- The game built from `youngMaxFun val top`. -/
def youngMaxGame (val : Fin 5 → ℕ) (top : ℕ) : Game 5 :=
  ⟨youngMaxFun val top, youngMaxFun_empty val top⟩

/-- The game `w` of the proof of Theorem 1 (Young 1985, p. 69):
`w(S₁) = w(S₂) = 3`, `w(S₃) = w(S₄) = w(S₅) = 9`, `w(N) = 11`, and otherwise
`w(S) = max_{S_k ⊆ S} w(S_k)` (or `0` if `S` contains no `S_k`). -/
def youngW : Game 5 := youngMaxGame ![3, 3, 9, 9, 9] 11

/-- The game `v` of the proof of Theorem 1 (Young 1985, p. 69): identical to `w` except that
`v(S₅) = v(N) = 12`. -/
def youngV : Game 5 := youngMaxGame ![3, 3, 9, 9, 12] 12

end MonotonicSolutions.CoreRules


