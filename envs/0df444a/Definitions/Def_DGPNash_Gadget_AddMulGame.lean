-- Prove2me | Definitions.Def_DGPNash_Gadget_AddMulGame
-- name    : DGPNash_Gadget_AddMulGame
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T18:08:33.052085+00:00
-- url     : https://prove2.me/theorems/b32d7b1f-19e8-40e3-9e73-f9a5f292a94c
-- title:
--   The addition/multiplication game $\mathcal G_{+,*}$ (Fig. 11, proof of Proposition 4.18)
-- statement:
--   Fix nonnegative integers $\alpha, \beta, \gamma$. The graphical game $\mathcal G_{+,*}$ has ten players: two input players $v_1, v_2$, one output player $v_3$, and intermediate players $w_1, v_1', w_2, v_2', w_3, w, u$. Every player has strategy set $\{0, 1\}$ except $v_2'$, whose strategy set is $\{0, 1, *\}$. Writing $[A]$ for $1$ if $A$ holds and $0$ otherwise, the payoffs are:
--
--   | player | payoff when it plays 0 | payoff when it plays 1 | payoff when it plays $*$ |
--   |---|---|---|---|
--   | $v_1'$ | $[w_1 = 1]$ | $[w_1 = 0]$ | |
--   | $w_1$ | $\tfrac18 [v_1 = 1]$ | $[v_1' = 1]$ | |
--   | $v_3$ | $[w_3 = 1]$ | $[w_3 = 0]$ | |
--   | $w_3$ | $8 [v_2' = *]$ | $[v_3 = 1]$ | |
--   | $w_2$ | $\tfrac18 [v_2 = 1]$ | $[v_2' = 1]$ | |
--   | $v_2'$ | $[u = 0]\,[w_2 = 1]$ | $[w_2 = 0]$ | $[u = 1]\,[w_2 = 1]$ |
--   | $w$ | see below | $[v_2' = 1] + [v_2' = *]$ | |
--   | $u$ | $[w = 1]$ | $[w = 0]$ | |
--
--   When $w$ plays $0$ its payoff is $0$ if $(v_2', v_1') = (0, 0)$ or $(*, 0)$; $\alpha$ if $(v_2', v_1') = (0, 1)$ or $(*, 1)$; $1 + \beta$ if $(v_2', v_1') = (1, 0)$; and $1 + \alpha + \beta + 8\gamma$ if $(v_2', v_1') = (1, 1)$.
--
--   The payoffs of the input players $v_1, v_2$ are unconstrained in the paper; here they are $0$, so that every mixed strategy of the inputs is compatible with equilibrium (see the note). This gadget computes $\min\{1, \alpha p[v_1] + \beta p[v_2] + \gamma p[v_1]p[v_2]\}$ at the output with error amplification $81$ (Proposition 4.18), where $p[v]$ is the probability that a binary player $v$ plays $1$.
--
--   **Formalization Note** Players are the inductive type `AddMulRole`; $v_2'$'s strategies $\{0, 1, *\}$ are the inductive type `Tri` (`zero`, `one`, `star`), every other player's are `Fin 2` with the paper's labels $0, 1$. Since every payoff of an intermediate or output player depends only on players of the gadget, giving the inputs payoff $0$ (which makes the $\epsilon$-well-supported condition at $v_1, v_2$ hold for every profile) means that "$\sigma$ is an $\epsilon$-Nash equilibrium of this game" is exactly "$\sigma$ is a mixed profile, the input strategies are arbitrary, and the eight non-input players satisfy the $\epsilon$-condition", which is the paper's meaning when $\mathcal G_{+,*}$ sits inside a larger game.
-- source:
--   Daskalakis, Goldberg & Papadimitriou, The Complexity of Computing a Nash Equilibrium, SIAM J. Comput. 39(1):195–259 (2009), pp. 230–231, Fig. 11 and payoff tables in the proof of Proposition 4.18

import Mathlib

namespace DGPNash.Gadget

/-- The ten players of the addition/multiplication game `G_{+,∗}` (Fig. 11, p. 230):
inputs `v₁, v₂`, output `v₃`, and intermediate players `w₁, v₁', w₂, v₂', w₃, w, u`. -/
inductive AddMulRole
  | v1 | v2 | v3 | w1 | v1' | w2 | v2' | w3 | w | u
  deriving DecidableEq

instance AddMulRole.instFintype : Fintype AddMulRole :=
  Fintype.ofList [.v1, .v2, .v3, .w1, .v1', .w2, .v2', .w3, .w, .u]
    (by intro x; cases x <;> simp)

/-- The three strategies `{0, 1, ∗}` of player `v₂'`. -/
inductive Tri
  | zero | one | star
  deriving DecidableEq

instance Tri.instFintype : Fintype Tri :=
  Fintype.ofList [.zero, .one, .star] (by intro x; cases x <;> simp)

/-- Strategy sets of `G_{+,∗}`: `{0, 1, ∗}` (as `Tri`) for `v₂'`, and `{0, 1}` (as `Fin 2`) for
every other player. -/
def AddMulStrat : AddMulRole → Type
  | .v2' => Tri
  | _ => Fin 2

instance AddMulStrat.instFintype : ∀ r, Fintype (AddMulStrat r) := by
  intro r; cases r <;> dsimp [AddMulStrat] <;> infer_instance

instance AddMulStrat.instDecidableEq : ∀ r, DecidableEq (AddMulStrat r) := by
  intro r; cases r <;> dsimp [AddMulStrat] <;> infer_instance

/-- `[P]`: `1` if `P` holds, `0` otherwise. -/
def ind (P : Prop) [Decidable P] : ℝ := if P then 1 else 0

/-- The payoff tables of `G_{+,∗}` from the proof of Proposition 4.18 (pp. 230–231), for the
parameters `α, β, γ`. `pay r s` is the payoff of player `r` at the pure profile `s`; the input
players `v₁, v₂` receive payoff `0` (their payoffs are unconstrained in the paper). -/
noncomputable def addMulPayoff (α β γ : ℕ) : AddMulRole → (∀ r, AddMulStrat r) → ℝ :=
  fun r s =>
    let sv1 : Fin 2 := s .v1
    let sv2 : Fin 2 := s .v2
    let sv3 : Fin 2 := s .v3
    let sw1 : Fin 2 := s .w1
    let sv1' : Fin 2 := s .v1'
    let sw2 : Fin 2 := s .w2
    let sv2' : Tri := s .v2'
    let sw3 : Fin 2 := s .w3
    let sw : Fin 2 := s .w
    let su : Fin 2 := s .u
    match r with
    | .v1 => 0
    | .v2 => 0
    | .v1' => if sv1' = 0 then ind (sw1 = 1) else ind (sw1 = 0)
    | .w1 => if sw1 = 0 then (1 / 8 : ℝ) * ind (sv1 = 1) else ind (sv1' = 1)
    | .v3 => if sv3 = 0 then ind (sw3 = 1) else ind (sw3 = 0)
    | .w3 => if sw3 = 0 then 8 * ind (sv2' = .star) else ind (sv3 = 1)
    | .w2 => if sw2 = 0 then (1 / 8 : ℝ) * ind (sv2 = 1) else ind (sv2' = .one)
    | .v2' =>
        match sv2' with
        | .zero => ind (su = 0) * ind (sw2 = 1)
        | .one => ind (sw2 = 0)
        | .star => ind (su = 1) * ind (sw2 = 1)
    | .w =>
        if sw = 0 then
          (match sv2' with
            | .zero => if sv1' = 0 then 0 else (α : ℝ)
            | .one => if sv1' = 0 then 1 + (β : ℝ) else 1 + α + β + 8 * γ
            | .star => if sv1' = 0 then 0 else (α : ℝ))
        else ind (sv2' = .one) + ind (sv2' = .star)
    | .u => if su = 0 then ind (sw = 1) else ind (sw = 0)

end DGPNash.Gadget


