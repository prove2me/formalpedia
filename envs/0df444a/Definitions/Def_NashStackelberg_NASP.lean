-- Prove2me | Definitions.Def_NashStackelberg_NASP
-- name    : NashStackelberg_NASP
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:14:52.24088+00:00
-- url     : https://prove2.me/theorems/a695c0fb-90be-4724-86b3-2c3de92daddf
-- title:
--   NASP — a Nash game among Stackelberg players
-- statement:
--   A **NASP** $N=(S^1,\dots,S^n)$ is a complete-information simultaneous game among $n$ players, each of which is a simple Stackelberg game. Player $i$ is a leader with variables $w^i$ and followers playing the game $P^i(w^i)$ (a `FollowerGame`). Its joint vector is $x^i=(w^i,y^i)$, where $y^i$ stacks the followers' variables, and it solves
--   $$
--   S^i(x^i,x^{-i})=\min_{x^i}\ (c^i)^\top x^i+(C^i x^{-i})^\top x^i\quad\text{s.t.}\quad x^i\in\mathcal F^i,
--   $$
--   $$
--   \mathcal F^i=\{x^i=(w^i,y^i):\ x^i\in\mathcal S^i,\ y^i\in\mathrm{SOL}(P^i(w^i))\},
--   $$
--   where $\mathcal S^i=\{x^i: A_S^i x^i\le b_S^i\}$ is a polyhedron.
--
--   The data of the structure are, for every player $i$: the number of leader variables, the followers' game, the polyhedron $\mathcal S^i$, the cost vector $c^i$, and the blocks $C^{ij}$ of $C^i$ acting on the other players' vectors $x^j$.
--
--   **Formalization Note** Player $i$'s joint vector is indexed by the disjoint union of its leader coordinates and its followers' coordinates. Different players may have different numbers of leader and follower variables. The block $C^{ii}$ is never used.
-- source:
--   Carvalho, Dragotto, Feijoo, Lodi & Sankaranarayanan, When Nash Meets Stackelberg, arXiv:1910.06452v6, Definition 4, p.8, with Definition 3, p.7

import Mathlib
import Definitions.Def_NashStackelberg_FollowerGame

namespace NashStackelberg

/-- **NASP: a Nash game among Stackelberg players** (Carvalho, Dragotto, Feijoo, Lodi &
Sankaranarayanan, *When Nash Meets Stackelberg*, arXiv:1910.06452v6, Definition 4, p.8, with
Definition 3, p.7).

A NASP `N = (S¹, …, Sⁿ)` is a complete-information simultaneous game among `n` players. Player
`i` is a leader with variables `wⁱ ∈ ℝ^{nℓ i}` and followers playing the game `P i` (a simple,
facile game with a simple parameterization in `wⁱ`). The player's joint vector is
`xⁱ = (wⁱ, yⁱ)`, where `yⁱ` stacks all followers' variables. Player `i` solves the simple
Stackelberg game
`Sⁱ(xⁱ, x⁻ⁱ) = min_{xⁱ} (cⁱ)ᵀ xⁱ + (Cⁱ x⁻ⁱ)ᵀ xⁱ  s.t.  xⁱ ∈ 𝓕ⁱ`,
`𝓕ⁱ = {xⁱ = (wⁱ, yⁱ) : xⁱ ∈ 𝓢ⁱ, yⁱ ∈ SOL(P(wⁱ))}`, with `𝓢ⁱ = {xⁱ : AS i xⁱ ≤ bS i}` a polyhedron.

**Formalization Note.** Player `i`'s joint vector is indexed by
`Fin (nℓ i) ⊕ Σ k, Fin (d k)`: `Sum.inl a` is the leader's `a`-th variable and `Sum.inr ⟨k, l⟩`
follower `k`'s `l`-th variable. Leader and follower dimensions may differ between players. The
matrix `Cⁱ` acting on `x⁻ⁱ` is given by its blocks `C i j` (`j ≠ i`); `C i i` is never used. -/
structure NASP (n : ℕ) where
  /-- The number of leader variables of player `i`. -/
  nl : Fin n → ℕ
  /-- The followers' game of player `i`, parameterized by its leader's variables. -/
  P : (i : Fin n) → FollowerGame (nl i)
  /-- The number of rows describing the polyhedron `𝓢ⁱ`. -/
  rS : Fin n → ℕ
  /-- The constraint matrix of `𝓢ⁱ = {x : AS i x ≤ bS i}`. -/
  AS : (i : Fin n) → Matrix (Fin (rS i)) (Fin (nl i) ⊕ (Σ k : Fin (P i).K, Fin ((P i).d k))) ℝ
  /-- The right-hand side of `𝓢ⁱ`. -/
  bS : (i : Fin n) → Fin (rS i) → ℝ
  /-- The linear cost vector `cⁱ`. -/
  c : (i : Fin n) → (Fin (nl i) ⊕ (Σ k : Fin (P i).K, Fin ((P i).d k))) → ℝ
  /-- The block of `Cⁱ` acting on player `j`'s variables. -/
  C : (i j : Fin n) → Matrix (Fin (nl i) ⊕ (Σ k : Fin (P i).K, Fin ((P i).d k)))
    (Fin (nl j) ⊕ (Σ k : Fin (P j).K, Fin ((P j).d k))) ℝ

end NashStackelberg


