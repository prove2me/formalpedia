-- Prove2me | Definitions.Def_OptHedgeGames_TwoPlayerRun
-- name    : OptHedgeGames_TwoPlayerRun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:40:26.342862+00:00
-- url     : https://prove2.me/theorems/e795cf2b-ac17-495a-9659-4ce3543f3650
-- title:
--   Two-player games $\mathcal G(2,n)$ and the joint Optimistic Hedge run: $x_1^t,x_2^t,\ell_1^t,\ell_2^t,v^t$
-- statement:
--   A **two-player game** in $\mathcal G(2,n)$ consists of loss matrices $A,B\in[0,1]^{n\times n}$: when player 1 plays action $a$ and player 2 plays action $b$, their losses are $A_{ab}$ and $B_{ab}$.
--
--   Both players run Optimistic Hedge with a common learning rate $\eta$. The strategies $x_1^t,x_2^t$ and the loss vectors are given by
--   $$
--   \ell_1^t=Ax_2^t,\quad \ell_2^t=B^\top x_1^t,\quad x_1^{t+1}=E_{x_1^t}[-\eta(2\ell_1^t-\ell_1^{t-1})],\quad x_2^{t+1}=E_{x_2^t}[-\eta(2\ell_2^t-\ell_2^{t-1})],
--   $$
--   with $x_1^1=x_2^1$ uniform and $\ell_1^0=\ell_2^0=0$. Further, $v^t=\|\ell_1^t\|_{x_1^t}$, with $v^0=0$. Exchanging the players gives the game with loss matrices $(B^\top,A^\top)$.
--
--   These are the objects of Theorem 3.4 and of §5.
--
--   **Formalization Note** The run is a function of the game and $\eta$, computed by recursion on the state, so no statement assumes that a trajectory exists. The values at round $0$ of the two strategies are unused.
-- source:
--   Dagan, Eisen, Erez & Koren, Optimistic Hedge in General-Sum Games, STOC 2027 submission manuscript (sha256 383e3793…), (1), (3), p.4; Setup, p.7; Setting and notation of §5, p.18

import Mathlib
import Definitions.Def_OptHedgeGames_OptimisticHedge

open scoped Matrix

namespace OptHedgeGames

/-- A **two-player game with `n` actions per player**, the class `G(2, n)`: loss matrices
`A, B ∈ [0,1]^{n×n}`; when player 1 plays `a` and player 2 plays `b`, their losses are `A_ab` and
`B_ab` (Dagan, Eisen, Erez & Koren, *Optimistic Hedge in General-Sum Games*, STOC 2027 submission
manuscript (sha256 383e3793…), (1) at `m = 2`, p.4; Setup of §3.3, p.7).

**Formalization Note** Both players have the same `n`, as the paper assumes (footnote 1, p.4). -/
structure Game (n : ℕ) where
  /-- Player 1's loss matrix. -/
  A : Matrix (Fin n) (Fin n) ℝ
  /-- Player 2's loss matrix. -/
  B : Matrix (Fin n) (Fin n) ℝ
  A_mem : ∀ a b, A a b ∈ Set.Icc (0 : ℝ) 1
  B_mem : ∀ a b, B a b ∈ Set.Icc (0 : ℝ) 1

/-- One state of the joint run: the two current strategies and the two previous loss vectors. -/
structure RunState (n : ℕ) where
  /-- Player 1's strategy of the current round. -/
  x1 : Fin n → ℝ
  /-- Player 2's strategy of the current round. -/
  x2 : Fin n → ℝ
  /-- Player 1's loss vector of the previous round. -/
  prev1 : Fin n → ℝ
  /-- Player 2's loss vector of the previous round. -/
  prev2 : Fin n → ℝ

/-- The **joint run** of both players under Optimistic Hedge (3): `G.state η t` is the state at round
`t + 1`. It starts from uniform strategies and zero previous losses (`ℓ⁰₁ = ℓ⁰₂ = 0`), and each player
updates by `xᵗ⁺¹ = E_{xᵗ}[−η(2ℓᵗ − ℓᵗ⁻¹)]`, with `ℓᵗ₁ = Axᵗ₂` and `ℓᵗ₂ = B⊤xᵗ₁`
(manuscript sha256 383e3793…, (3), p.4; Setup, p.7; Setting and notation of §5, p.18). -/
noncomputable def Game.state {n : ℕ} (G : Game n) (η : ℝ) : ℕ → RunState n
  | 0 => ⟨uniform n, uniform n, 0, 0⟩
  | t + 1 =>
    let s := G.state η t
    let l1 := G.A *ᵥ s.x2
    let l2 := G.Bᵀ *ᵥ s.x1
    ⟨tilt s.x1 (fun a => -η * (2 * l1 a - s.prev1 a)),
      tilt s.x2 (fun b => -η * (2 * l2 b - s.prev2 b)), l1, l2⟩

/-- Player 1's strategy `xᵗ₁` of round `t ≥ 1` (manuscript sha256 383e3793…, Setup, p.7).

**Formalization Note** `t - 1` is natural-number subtraction: `G.x1 η 0` is an unused value, equal to
the uniform `G.x1 η 1`. -/
noncomputable def Game.x1 {n : ℕ} (G : Game n) (η : ℝ) (t : ℕ) : Fin n → ℝ :=
  (G.state η (t - 1)).x1

/-- Player 2's strategy `xᵗ₂` of round `t ≥ 1` (manuscript sha256 383e3793…, Setup, p.7). -/
noncomputable def Game.x2 {n : ℕ} (G : Game n) (η : ℝ) (t : ℕ) : Fin n → ℝ :=
  (G.state η (t - 1)).x2

/-- Player 1's loss vector: `ℓᵗ₁ = Axᵗ₂` for `t ≥ 1`, and `ℓ⁰₁ = 0`
(manuscript sha256 383e3793…, Setup, p.7; (3), p.4). -/
noncomputable def Game.l1 {n : ℕ} (G : Game n) (η : ℝ) : ℕ → Fin n → ℝ
  | 0 => 0
  | t + 1 => G.A *ᵥ G.x2 η (t + 1)

/-- Player 2's loss vector: `ℓᵗ₂ = B⊤xᵗ₁` for `t ≥ 1`, and `ℓ⁰₂ = 0`
(manuscript sha256 383e3793…, Setup, p.7; (3), p.4). -/
noncomputable def Game.l2 {n : ℕ} (G : Game n) (η : ℝ) : ℕ → Fin n → ℝ
  | 0 => 0
  | t + 1 => G.Bᵀ *ᵥ G.x1 η (t + 1)

/-- `vᵗ = ∥ℓᵗ₁∥_{xᵗ₁} = √Var_{xᵗ₁}(ℓᵗ₁)`, with `v⁰ = 0`
(manuscript sha256 383e3793…, Setting and notation of §5, p.18).

**Formalization Note** The value `v⁰ = 0` is built into the definition; `t + 1` reads round `t + 1`. -/
noncomputable def Game.v {n : ℕ} (G : Game n) (η : ℝ) : ℕ → ℝ
  | 0 => 0
  | t + 1 => vnorm (G.x1 η (t + 1)) (G.l1 η (t + 1))

/-- The **exchange of the two players**: player 1 of `G.swap` has loss matrix `B⊤` and player 2 has
`A⊤`, so that `G.swap` is `G` seen with the roles exchanged. The paper uses this as "the same
argument with the roles of the players exchanged" (manuscript sha256 383e3793…, p.21). -/
def Game.swap {n : ℕ} (G : Game n) : Game n where
  A := G.Bᵀ
  B := G.Aᵀ
  A_mem := fun a b => G.B_mem b a
  B_mem := fun a b => G.A_mem b a

end OptHedgeGames


