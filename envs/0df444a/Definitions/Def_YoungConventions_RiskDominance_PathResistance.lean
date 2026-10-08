-- Prove2me | Definitions.Def_YoungConventions_RiskDominance_PathResistance
-- name    : YoungConventions_RiskDominance_PathResistance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T18:01:18.18579+00:00
-- url     : https://prove2.me/theorems/b2803354-f13b-4259-9d8b-3cb8f91806f9
-- title:
--   Paths of successor steps and their total resistance
-- statement:
--   View $H$ as the vertices of a directed graph with an edge $h\to h'$ whenever $r(h,h')$ is finite, i.e. whenever $h'$ is a successor of $h$, weighted by $r(h,h')$. A **path** from $h$ to $h'$ is a sequence $h=h^0\to h^1\to\cdots\to h^L=h'$ ($L\ge0$) of such edges; its **total resistance** is
--   $$\sum_{l=0}^{L-1}r(h^l,h^{l+1}).$$
--   The predicate says that there is a path from $h$ to $h'$ with total resistance $r$.
--
--   **Formalization Note** The empty path from $h$ to itself has resistance $0$.
-- source:
--   Young (1993), The Evolution of Conventions, Econometrica 61:57–84, §6, pp. 68–69

import Mathlib
import Definitions.Def_YoungConventions_AdaptivePlay_History
import Definitions.Def_YoungConventions_AdaptivePlay_IsSuccessor
import Definitions.Def_YoungConventions_RiskDominance_numMistakes

namespace YoungConventions.RiskDominance

/-- **Directed paths of successor steps and their total resistance.** Young (1993), The Evolution of Conventions, Econometrica 61:57–84, §6, pp. 68–69
(PDF pp. 13–14): "view the state space `H` as the vertices of a directed graph. For every pair of
states `h, h′` insert a directed edge `h → h′` if `r(h, h′)` is finite, and let `r(h, h′)` be its
weight or resistance."

`PathResistance u k h h' r` holds iff there is a directed path `h = h⁰ → h¹ → ⋯ → hᴸ = h′`
(`L ≥ 0`) in which every step is a successor step, with total resistance
`r = ∑ₗ r(hˡ, hˡ⁺¹)`.

**Formalization Note.** Edges are exactly the successor pairs (the pairs of finite resistance);
the empty path from `h` to itself has resistance `0`. -/
inductive PathResistance {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ι → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)] {m : ℕ} [NeZero m]
    (u : ι → ((i : ι) → S i) → ℝ) (k : ℕ) : YoungConventions.AdaptivePlay.History S m → YoungConventions.AdaptivePlay.History S m → ℕ → Prop
  | refl (h : YoungConventions.AdaptivePlay.History S m) : PathResistance u k h h 0
  | step {h h₁ h₂ : YoungConventions.AdaptivePlay.History S m} {r : ℕ} :
      PathResistance u k h h₁ r → YoungConventions.AdaptivePlay.IsSuccessor h₁ h₂ →
      PathResistance u k h h₂ (r + numMistakes u k h₁ h₂)

end YoungConventions.RiskDominance


