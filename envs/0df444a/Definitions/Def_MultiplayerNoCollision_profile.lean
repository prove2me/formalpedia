-- Prove2me | Definitions.Def_MultiplayerNoCollision_profile
-- name    : MultiplayerNoCollision_profile
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:23:02.61113+00:00
-- url     : https://prove2.me/theorems/9f807195-0534-4307-b231-8555403a7abc
-- title:
--   The play of the game, collision indicators, received rewards (1) and the regret (2)
-- statement:
--   Fix a policy rule $\pi$, rewards $Y$ and seeds $U$. All $m$ players use $\pi$.
--
--   1. The **collision indicator** of arm $i$ under an action profile $a$ is $C_i=1$ if there are distinct players $j\ne j'$ with $a_j=a_{j'}=i$, and $C_i=0$ otherwise.
--   2. The **received reward** of player $j$ in round $t$ is
--   $$r_j(t)=Y_{A_j(t),t}\,\bigl(1-C_{A_j(t)}(t)\bigr).\tag{1}$$
--   3. The **play** is defined by recursion on rounds: $A_j(t)=\pi_t\bigl(h_j(t),U_{j,t}\bigr)$, where $h_j(t)=\bigl((A_j(s),r_j(s))\bigr)_{s<t}$ is player $j$'s own history.
--   4. For a mean vector $\mu$ and horizon $T$ the **regret** is
--   $$\mathrm{Regret}=T\sum_{k=1}^{m}\mu_{(k)}-\sum_{t\in[T]}\sum_{j\in[m]}\mu_{A_j(t)}\bigl(1-C_{A_j(t)}(t)\bigr).\tag{2}$$
--
--   The regret compares the means actually collected (a colliding pull collects nothing) with the best possible assignment of the $m$ players to the $m$ best arms. It is a random variable; its expectation is the quantity bounded in Theorem 1.
--
--   **Formalization Note** Rounds are 0-based. $\mu_{(1)}\ge\dots\ge\mu_{(m)}$ are the $m$ largest means (`topSum`), since the means are not relabeled. The play is defined for any rule; measurability is required only of the policy in the goal.
-- source:
--   Lugosi, Mehrabian, Multiplayer bandits without observing collision information, arXiv:1808.08416v2, §1.1, (1) and (2), p.3

import Mathlib
import Definitions.Def_MultiplayerNoCollision_Policy
import Definitions.Def_MultiplayerNoCollision_kthLargest

namespace MultiplayerNoCollision

open Finset

/-- **The collision indicator** `C_i(t)` of arm `i` under the action profile `a` (Lugosi, Mehrabian,
arXiv:1808.08416v2, §1.1, p.3): "`C_i(t) = 1` if and only if there exist distinct `j, j′` with
`A_j(t) = A_{j′}(t) = i`". -/
noncomputable def collision {m K : ℕ} (a : Fin m → Fin K) (i : Fin K) : ℝ :=
  open Classical in if ∃ j j' : Fin m, j ≠ j' ∧ a j = i ∧ a j' = i then 1 else 0

/-- **The received reward (1)** `r_j(t) = Y_{A_j(t),t} (1 − C_{A_j(t)}(t))` of player `j` in round
`s` under the action profile `a` (Lugosi, Mehrabian, arXiv:1808.08416v2, §1.1, (1), p.3). -/
noncomputable def received {Ω : Type*} {m K : ℕ} (Y : Fin K → ℕ → Ω → ℝ) (a : Fin m → Fin K)
    (s : ℕ) (ω : Ω) (j : Fin m) : ℝ :=
  Y (a j) s ω * (1 - collision a (a j))

/-- **The play of the game.** Lugosi, Mehrabian, arXiv:1808.08416v2, §1.1, p.3: "in each round
`t = 1, …, T`, player `j` chooses an arm `A_j(t) ∈ [K]`".

When every player uses the rule `act` (see `Policy`), `profile act Y U ω t j` is the arm `A_j(t)`
pulled by player `j` in (0-based) round `t` at outcome `ω`: it is `act` applied to round `t`,
player `j`'s own history (her arms `A_j(s)` and received rewards `r_j(s)` for `s < t`) and her seed
`U j t ω`. It is defined by strong recursion on `t`.

**Formalization Note.** The rule `act` is the same for every player and receives only that player's
history and seed. `act` is a raw function here so that the definition applies to any rule;
measurability is required only of the `Policy` in the goal. -/
noncomputable def profile {Ω : Type*} {m K : ℕ} (act : (t : ℕ) → History K t → ℝ → Fin K)
    (Y : Fin K → ℕ → Ω → ℝ) (U : Fin m → ℕ → Ω → ℝ) (ω : Ω) : ℕ → Fin m → Fin K
  | t => fun j => act t
      (fun s => (profile act Y U ω (s : ℕ) j, received Y (profile act Y U ω (s : ℕ)) s ω j))
      (U j t ω)
termination_by t => t
decreasing_by all_goals exact s.isLt

/-- **Player `j`'s own history after `t` rounds**: her arms `A_j(s)` and rewards `r_j(s)` for
`s < t` (0-based), in the play `profile act Y U ω`. -/
noncomputable def history {Ω : Type*} {m K : ℕ} (act : (t : ℕ) → History K t → ℝ → Fin K)
    (Y : Fin K → ℕ → Ω → ℝ) (U : Fin m → ℕ → Ω → ℝ) (ω : Ω) (j : Fin m) (t : ℕ) : History K t :=
  fun s => (profile act Y U ω s j, received Y (profile act Y U ω s) s ω j)

/-- **The regret (2).** Lugosi, Mehrabian, arXiv:1808.08416v2, §1.1, (2), p.3:
`Regret = T ∑_{i∈[m]} µ_i − ∑_{t∈[T]} ∑_{j∈[m]} µ_{A_j(t)} (1 − C_{A_j(t)}(t))`.

`regret act Y U mu T ω` is this quantity for the play `profile act Y U ω`, rounds `0, …, T − 1`, and
mean vector `mu`, where `∑_{i∈[m]} µ_i` is the sum `topSum mu m` of the `m` largest means (the
paper's means are sorted, p.3). It uses the means, not the realized rewards.

**Formalization Note.** `mu` is not assumed sorted; the benchmark is computed from the sorted means.
The expected regret of the goal is the integral of this random variable. -/
noncomputable def regret {Ω : Type*} {m K : ℕ} (act : (t : ℕ) → History K t → ℝ → Fin K)
    (Y : Fin K → ℕ → Ω → ℝ) (U : Fin m → ℕ → Ω → ℝ) (mu : Fin K → ℝ) (T : ℕ) (ω : Ω) : ℝ :=
  (T : ℝ) * topSum mu m - ∑ t ∈ range T, ∑ j : Fin m,
    mu (profile act Y U ω t j) * (1 - collision (profile act Y U ω t) (profile act Y U ω t j))

end MultiplayerNoCollision


