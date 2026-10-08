-- Prove2me | Definitions.Def_HartSchmeidler_Finite_Game
-- name    : HartSchmeidler_Finite_Game
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T11:33:24.265991+00:00
-- url     : https://prove2.me/theorems/4e70f656-a288-4aa2-9ff8-3aa268545dc9
-- title:
--   §2, condition (1) — correlated equilibrium and auxiliary game
-- statement:
--   Let $N$ be a finite set of players. Each player $i$ has a finite set $S^i$ of pure strategies, and $h^i(s)$ is that player's real payoff at the strategy profile $s\in S=\prod_{j\in N}S^j$. A **lottery** $p$ on $S$ has nonnegative weights summing to one. It is a **correlated equilibrium** when, for every player $i$ and every recommended strategy $r^i$ and possible deviation $t^i$,
--
--   $$
--   \sum_{s^{-i}\in S^{-i}}p(s^{-i},r^i)\bigl[h^i(s^{-i},r^i)-h^i(s^{-i},t^i)\bigr]\ge 0.
--   $$
--
--   The auxiliary two-person zero-sum game has pure strategies $s\in S$ for player I and triples $(i,r^i,t^i)$ for player II. Its payment to player I is $h^i(s)-h^i(s^{-i},t^i)$ if $s^i=r^i$, and zero otherwise. These definitions express the paper's condition (1) and the game used in its proof of Theorem 1.
--
--   **Formalization Note** A profile with coordinate $i$ replaced by $t^i$ represents $(s^{-i},t^i)$; the sum above is over profiles whose $i$th coordinate equals $r^i$. The lottery predicate is the published `AGT.IsLottery`. Equality decisions and finite enumeration are Lean implementation instances.
-- source:
--   Hart and Schmeidler, Existence of Correlated Equilibria, Math. Oper. Res. 14 (1989), pp. 18–19, §2, condition (1) and proof of Theorem 1; https://doi.org/10.1287/moor.14.1.18

import Mathlib
import Definitions.Def_agt_games

namespace HartSchmeidler.Finite

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {S : ι → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]

/-- The paper's condition (1): a lottery on pure strategy profiles obeying every
recommendation-to-deviation inequality. -/
def IsCorrelatedEq (h : ι → (∀ i, S i) → ℝ) (p : (∀ i, S i) → ℝ) : Prop :=
  AGT.IsLottery p ∧
    ∀ (i : ι) (r t : S i),
      0 ≤ ∑ s ∈ Finset.univ.filter (fun s : ∀ j, S j => s i = r),
        p s * (h i s - h i (Function.update s i t))

/-- Player II's pure strategy in the auxiliary two-person zero-sum game. -/
def Deviation (S : ι → Type*) := Σ i : ι, S i × S i

instance instFintypeDeviation (S : ι → Type*) [∀ i, Fintype (S i)] :
    Fintype (Deviation S) := by
  dsimp [Deviation]
  infer_instance

/-- The payment from player II to player I for pure profile `s` and a triple
`(i,r,t)`. -/
def auxPayoff (h : ι → (∀ i, S i) → ℝ) (s : ∀ i, S i)
    (c : Deviation S) : ℝ :=
  if s c.1 = c.2.1 then h c.1 s - h c.1 (Function.update s c.1 c.2.2) else 0

end HartSchmeidler.Finite


