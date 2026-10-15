-- Prove2me | Definitions.Def_SeqLoss_LiabilityGame_Game
-- name    : SeqLoss_LiabilityGame_Game
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T09:02:50.148917+00:00
-- url     : https://prove2.me/theorems/58264a25-4f39-4731-a493-a29f29a07468
-- title:
--   pp. 14–15, 24 — the liability game $v_\ell$ and the contributions $M_i(v)$ to the grand coalition
-- statement:
--   Fix a loss problem $\ell\in\mathcal L^n$ with $n\ge 1$ agents $N=\{1,\dots,n\}$. The **liability game** $v_\ell$ is the transferable-utility game on $N$ in which a coalition is liable for the direct losses of its members exactly when it contains the initiator:
--   $$v_\ell(S)=\begin{cases}\sum_{i\in S}\ell_i & \text{if } 1\in S,\\[2pt] 0 & \text{otherwise,}\end{cases}\qquad S\subseteq N.$$
--   In particular $v_\ell(\emptyset)=0$ and $v_\ell(N)=L$.
--
--   For any game $v$ on $N$, the **contribution of player $i$ to the grand coalition** is
--   $$M_i(v)=v(N)-v(N\setminus\{i\}).$$
--
--   The liability game is a "big boss" game in the sense of Muto, Nakayama, Potters and Tijs (1988), with the initiator as the big boss; Theorem 3 identifies its Shapley value and nucleolus.
--
--   **Formalization Note.** A game is a function `Finset (Fin n) → ℝ`, the type used by the platform's published `ShapleyValue` and `IsConvexGame`. The initiator is index `0`, which requires `n ≥ 1` (the instance `[NeZero n]`); the paper's $N=\{1,\dots,n\}$ contains agent 1, so it assumes this too. `marginalContribution` is defined for an arbitrary game.
-- source:
--   Gudmundsson, Hougaard & Ko, Sharing Sequentially Triggered Losses, accepted manuscript (2023), pp. 14–15, §4.2 (definition of v_ℓ); p. 24, proof of Theorem 3, second paragraph (M_i)

import Mathlib

namespace SeqLoss.LiabilityGame

/-- The liability game `v_ℓ` of a loss vector `ℓ` (§4.2, pp. 14–15): a coalition `S` containing
the initiator (agent 1, index `0`) is worth the total direct loss `∑_{i ∈ S} ℓ_i` of its members;
every other coalition is worth `0`. -/
def liabilityGame {n : ℕ} [NeZero n] (ℓ : Fin n → ℝ) : Finset (Fin n) → ℝ :=
  fun S => if (0 : Fin n) ∈ S then ∑ i ∈ S, ℓ i else 0

/-- The contribution of player `i` to the grand coalition, `M_i(v) = v(N) - v(N \ {i})` (p. 24). -/
def marginalContribution {n : ℕ} (v : Finset (Fin n) → ℝ) (i : Fin n) : ℝ :=
  v Finset.univ - v (Finset.univ.erase i)

end SeqLoss.LiabilityGame


