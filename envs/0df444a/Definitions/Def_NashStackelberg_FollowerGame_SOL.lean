-- Prove2me | Definitions.Def_NashStackelberg_FollowerGame_SOL
-- name    : NashStackelberg_FollowerGame_SOL
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:14:46.498934+00:00
-- url     : https://prove2.me/theorems/4895785f-c819-4a2b-9873-0140a5eba580
-- title:
--   The followers' solution set $\mathrm{SOL}(P(w))$
-- statement:
--   For leader variables $w$, $\mathrm{SOL}(P(w))$ is the set of pure Nash equilibria of the followers' game $P(w)$: the follower profiles $y=(y_1,\dots,y_K)$ such that, for every follower $k$, $y_k$ satisfies $A_k w+B_k y_k\le b_k$ and minimizes
--   $$
--   \tfrac12\,y_k^\top Q_k y_k + c_k^\top y_k + \Big(\sum_{k'\ne k} C_{kk'}\,y_{k'}\Big)^{\!\top} y_k + (H_k w)^\top y_k
--   $$
--   over all $y_k'$ with $A_k w+B_k y_k'\le b_k$, the other followers' variables being fixed.
--
--   $\mathrm{SOL}(P(w))$ is the lower-level constraint of every Stackelberg player of a NASP: the leader may choose any equilibrium of its followers, which is the optimistic convention of the paper.
--
--   **Formalization Note** No selection among several follower equilibria is made: any $y\in\mathrm{SOL}(P(w))$ is admissible for the leader (optimistic selection, Definition 3 and Remark 2).
-- source:
--   Carvalho, Dragotto, Feijoo, Lodi & Sankaranarayanan, When Nash Meets Stackelberg, arXiv:1910.06452v6, Definition 3, p.7, and §5, p.10

import Mathlib
import Definitions.Def_NashStackelberg_IsPNE
import Definitions.Def_NashStackelberg_FollowerGame

open Matrix

namespace NashStackelberg

/-- **The followers' solution set `SOL(P(w))`** (Carvalho, Dragotto, Feijoo, Lodi &
Sankaranarayanan, *When Nash Meets Stackelberg*, arXiv:1910.06452v6, Definition 3, p.7, and §5,
p.10: "SOL(P(wⁱ)) is the set of points satisfying all the KKT conditions associated with the
followers' optimization problems").

For leader variables `w`, `SOL(P(w))` is the set of (pure) Nash equilibria of the followers' game
`P(w)`: profiles `y = (y₁, …, y_K)` such that every `yₖ` satisfies `Aₖ w + Bₖ yₖ ≤ bₖ` and minimizes
`½ yₖᵀ Qₖ yₖ + cₖᵀ yₖ + (Σ_{k' ≠ k} Cₖₖ' yₖ')ᵀ yₖ + (Hₖ w)ᵀ yₖ` over the feasible `yₖ`, the other
followers' `y₋ₖ` being fixed.

**Formalization Note.** No selection among several equilibria is made: a leader may pick any
`y ∈ SOL(P(w))`, which is the optimistic convention of Definition 3 and Remark 2. -/
def FollowerGame.SOL {nl : ℕ} (G : FollowerGame nl) (w : Fin nl → ℝ) :
    Set ((k : Fin G.K) → Fin (G.d k) → ℝ) :=
  {y | IsPNE (fun k => {v | G.A k *ᵥ w + G.B k *ᵥ v ≤ G.b k})
    (fun k y => (1 / 2 : ℝ) * (y k ⬝ᵥ (G.Q k *ᵥ y k)) + G.c k ⬝ᵥ y k
      + (∑ k' ∈ Finset.univ.erase k, G.C k k' *ᵥ y k') ⬝ᵥ y k + (G.H k *ᵥ w) ⬝ᵥ y k) y}

end NashStackelberg


