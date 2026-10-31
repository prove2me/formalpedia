-- Prove2me | Definitions.Def_NashStackelberg_NASP_Var
-- name    : NashStackelberg_NASP_Var
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:15:38.61455+00:00
-- url     : https://prove2.me/theorems/649f2980-219f-4907-bb6b-50bc55a786b3
-- title:
--   The index set of a NASP player's joint leader–follower vector
-- statement:
--   For a NASP $N$ and a player $i$, the coordinates of the joint vector $x^i=(w^i,y^i)$ are the leader's coordinates $1,\dots,n_\ell^i$ together with the pairs $(k,l)$, where $k$ is a follower of player $i$ and $l$ indexes follower $k$'s variables. Player $i$'s strategies are the real vectors indexed by this set.
--
--   **Formalization Note** The index type is `Fin nℓ ⊕ Σ k, Fin (d k)`: `Sum.inl a` is the leader's $a$-th variable and `Sum.inr ⟨k, l⟩` is follower $k$'s $l$-th variable.
-- source:
--   Carvalho, Dragotto, Feijoo, Lodi & Sankaranarayanan, When Nash Meets Stackelberg, arXiv:1910.06452v6, Definition 4 and the paragraph after it, p.8

import Mathlib
import Definitions.Def_NashStackelberg_NASP

namespace NashStackelberg

/-- **The index type of a NASP player's joint vector `xⁱ = (wⁱ, yⁱ)`** (Carvalho, Dragotto, Feijoo,
Lodi & Sankaranarayanan, *When Nash Meets Stackelberg*, arXiv:1910.06452v6, Definition 4, p.8:
"we let xⁱ ∈ ℝ^{nℓ+nf} be a joint representation of the leader's and the followers' variables").

`Sum.inl a` indexes the leader's `a`-th variable; `Sum.inr ⟨k, l⟩` indexes follower `k`'s `l`-th
variable. Player `i`'s strategies are vectors `N.Var i → ℝ`. -/
abbrev NASP.Var {n : ℕ} (N : NASP n) (i : Fin n) : Type :=
  Fin (N.nl i) ⊕ (Σ k : Fin (N.P i).K, Fin ((N.P i).d k))

end NashStackelberg


