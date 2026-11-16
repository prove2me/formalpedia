-- Prove2me | Definitions.Def_OptHedgeGames_Supplement_MultiRun
-- name    : OptHedgeGames_Supplement_MultiRun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:19:59.428539+00:00
-- url     : https://prove2.me/theorems/bf1f512f-43ce-4abc-87f3-d00ea09fcfc7
-- title:
--   $m$-player games $\mathcal G(m,n)$, expected loss vectors (1), and the joint Optimistic Hedge run
-- statement:
--   An **$m$-player game with $n$ actions per player**, an element of the class $\mathcal G(m,n)$, is given by loss functions
--   $$
--   L_i:[n]^m\to[0,1],\qquad i\in[m],
--   $$
--   where $L_i(a)$ is player $i$'s loss at the pure action profile $a=(a_1,\dots,a_m)$.
--
--   For a profile $x=(x_1,\dots,x_m)$ of mixed strategies, player $i$'s **expected loss vector** is
--   $$
--   \ell_i(x)(b)=\sum_{a_{-i}}L_i(b,a_{-i})\prod_{j\ne i}x_j(a_j),\qquad b\in[n].
--   $$
--
--   In the **joint Optimistic Hedge run** with learning rate $\eta$, every player starts from the uniform strategy $x_i^1$ with $\ell_i^0=0$; in round $t\ge1$ every player receives $\ell_i^t=\ell_i(x^t)$, computed from the round-$t$ profile, and all players update simultaneously,
--   $$
--   x_i^{t+1}(a)\propto x_i^t(a)\,e^{-\eta(2\ell_i^t(a)-\ell_i^{t-1}(a))}.
--   $$
--   Player $i$'s regret $\mathrm{Reg}_i(T)=\sum_{t=1}^T\langle x_i^t,\ell_i^t\rangle-\min_a\sum_{t=1}^T\ell_i^t(a)$ is the mission's published regret applied to player $i$'s strategies and losses.
--
--   This is the setting of Theorems 3.3 and 3.6; the published two-player run is its case $m=2$ with matrix losses.
--
--   **Formalization Note** Players are `Fin m` and actions `Fin n` (0-based); every player has the same number $n$ of actions (footnote 1, p.4). The sum over $a_{-i}$ is the sum over the pure profiles $a$ with $a_i=b$. The strategy of round $t$ is `G.x η i t`, read for $t\ge1$; the value at $t=0$ is unused. The exponential tilt, the uniform strategy and the regret are imported from the published `OptHedgeGames.Notation` and `OptHedgeGames.OptimisticHedge`.
-- source:
--   Dagan, Eisen, Erez & Koren, Optimistic Hedge in General-Sum Games, STOC 2027 submission manuscript (sha256 383e3793…), §2, (1)–(3), p.4

import Mathlib
import Definitions.Def_OptHedgeGames_OptimisticHedge

namespace OptHedgeGames

namespace Supplement

/-- An **`m`-player game with `n` actions per player**, the class `G(m, n)`: player `i` has the loss
function `Lᵢ : [n]^m → [0, 1]`, and `Lᵢ(a)` is its loss at the pure action profile `a`
(Dagan, Eisen, Erez & Koren, *Optimistic Hedge in General-Sum Games*, STOC 2027 submission
manuscript (sha256 383e3793…), §2, (1), p.4).

**Formalization Note** Players are `Fin m` and actions `Fin n` (0-based). Every player has the same
number `n` of actions, as the paper assumes (footnote 1, p.4). -/
structure MGame (m n : ℕ) where
  /-- `L i a` is player `i`'s loss at the pure action profile `a`. -/
  L : Fin m → (Fin m → Fin n) → ℝ
  /-- Losses lie in `[0, 1]`. -/
  L_mem : ∀ i a, L i a ∈ Set.Icc (0 : ℝ) 1

/-- Player `i`'s **expected loss vector (1)** at a profile `x` of mixed strategies,
`ℓᵢ(x)(b) = Σ_{a₋ᵢ} Lᵢ(b, a₋ᵢ) Π_{j ≠ i} xⱼ(aⱼ)`
(manuscript sha256 383e3793…, (1), p.4).

**Formalization Note** The sum over `a₋ᵢ` is the sum over the pure profiles `a` with `aᵢ = b`. -/
noncomputable def MGame.lossVec {m n : ℕ} (G : MGame m n) (i : Fin m)
    (x : Fin m → Fin n → ℝ) : Fin n → ℝ :=
  fun b => ∑ a ∈ Finset.univ.filter (fun a : Fin m → Fin n => a i = b),
    G.L i a * ∏ j ∈ Finset.univ.erase i, x j (a j)

/-- One state of the joint run: every player's current strategy and previous loss vector. -/
structure MRunState (m n : ℕ) where
  /-- `x i` is player `i`'s strategy of the current round. -/
  x : Fin m → Fin n → ℝ
  /-- `prev i` is player `i`'s loss vector of the previous round. -/
  prev : Fin m → Fin n → ℝ

/-- The **joint run** of all `m` players under Optimistic Hedge (3) with the common learning rate
`η`: `G.state η t` is the state at round `t + 1`. Every player starts from the uniform strategy with
`ℓ⁰ᵢ = 0`; at every round all players simultaneously receive `ℓᵗᵢ = ℓᵢ(xᵗ)` (1) and update
`xᵗ⁺¹ᵢ = E_{xᵗᵢ}[−η(2ℓᵗᵢ − ℓᵗ⁻¹ᵢ)]` (manuscript sha256 383e3793…, (1)–(3), p.4). -/
noncomputable def MGame.state {m n : ℕ} (G : MGame m n) (η : ℝ) : ℕ → MRunState m n
  | 0 => ⟨fun _ => uniform n, fun _ => 0⟩
  | t + 1 =>
    let s := G.state η t
    let l := fun i => G.lossVec i s.x
    ⟨fun i => tilt (s.x i) (fun a => -η * (2 * l i a - s.prev i a)), l⟩

/-- Player `i`'s strategy `xᵗᵢ` of round `t ≥ 1` (manuscript sha256 383e3793…, (3), p.4).

**Formalization Note** `t - 1` is natural-number subtraction: `G.x η i 0` is an unused value, equal
to the uniform `G.x η i 1`. -/
noncomputable def MGame.x {m n : ℕ} (G : MGame m n) (η : ℝ) (i : Fin m) (t : ℕ) : Fin n → ℝ :=
  (G.state η (t - 1)).x i

/-- Player `i`'s loss vector `ℓᵗᵢ = ℓᵢ(xᵗ)` for `t ≥ 1`, and `ℓ⁰ᵢ = 0`
(manuscript sha256 383e3793…, (1), (3), p.4). -/
noncomputable def MGame.l {m n : ℕ} (G : MGame m n) (η : ℝ) (i : Fin m) : ℕ → Fin n → ℝ
  | 0 => 0
  | t + 1 => G.lossVec i (fun j => G.x η j (t + 1))

/-- Player `i`'s **regret** `Regᵢ(T)` (2) in the joint run with learning rate `η`: the published
`reg` applied to player `i`'s strategies and loss vectors
(manuscript sha256 383e3793…, (2), p.4). -/
noncomputable def MGame.Reg {m n : ℕ} (G : MGame m n) (η : ℝ) (i : Fin m) (T : ℕ) : ℝ :=
  reg (G.x η i) (G.l η i) T

end Supplement

end OptHedgeGames


