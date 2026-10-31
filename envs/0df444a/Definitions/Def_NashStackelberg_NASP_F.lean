-- Prove2me | Definitions.Def_NashStackelberg_NASP_F
-- name    : NashStackelberg_NASP_F
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:16:25.531993+00:00
-- url     : https://prove2.me/theorems/5acbb206-89e2-4299-a7b7-33452e3cb484
-- title:
--   The player feasible region $\mathcal F^i$ of a NASP
-- statement:
--   For a NASP $N$ and a player $i$, the **player feasible region** is
--   $$
--   \mathcal F^i=\{x^i=(w^i,y^i):\ x^i\in\mathcal S^i,\ y^i\in\mathrm{SOL}(P^i(w^i))\}:
--   $$
--   the joint vectors lying in the polyhedron $\mathcal S^i$ whose follower part is a Nash equilibrium of the followers' game at the leader part. Its elements are player $i$'s pure strategies. $\mathcal F^i$ is in general not convex.
--
--   **Formalization Note** The leader part of $x$ is $a\mapsto x(\mathrm{inl}\,a)$ and follower $k$'s part is $l\mapsto x(\mathrm{inr}\,(k,l))$. Any follower equilibrium is admissible (optimistic selection).
-- source:
--   Carvalho, Dragotto, Feijoo, Lodi & Sankaranarayanan, When Nash Meets Stackelberg, arXiv:1910.06452v6, Definition 4, p.8

import Mathlib
import Definitions.Def_NashStackelberg_FollowerGame_SOL
import Definitions.Def_NashStackelberg_NASP_Var

open Matrix

namespace NashStackelberg

/-- **The player feasible region `𝓕ⁱ`** (Carvalho, Dragotto, Feijoo, Lodi & Sankaranarayanan,
*When Nash Meets Stackelberg*, arXiv:1910.06452v6, Definition 4, p.8):
`𝓕ⁱ := {xⁱ = (wⁱ, yⁱ) : xⁱ ∈ 𝓢ⁱ, yⁱ ∈ SOL(P(wⁱ))}`.

A joint vector `x` of player `i` is feasible when it lies in the polyhedron
`𝓢ⁱ = {x : AS i x ≤ bS i}` and its follower part `yⁱ` is a Nash equilibrium of the followers' game
at the leader part `wⁱ`. These are the pure strategies of player `i` (Definition 1, p.7).

**Formalization Note.** The leader part of `x` is `fun a => x (Sum.inl a)` and follower `k`'s part
is `fun l => x (Sum.inr ⟨k, l⟩)`. Any `y ∈ SOL(P(w))` is admissible (optimistic selection, Remark 2,
p.8). -/
def NASP.F {n : ℕ} (N : NASP n) (i : Fin n) : Set (N.Var i → ℝ) :=
  {x | N.AS i *ᵥ x ≤ N.bS i ∧
    (fun k l => x (Sum.inr ⟨k, l⟩)) ∈ (N.P i).SOL (fun a => x (Sum.inl a))}

end NashStackelberg


