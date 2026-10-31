-- Prove2me | Definitions.Def_LeGallBrownianMap_labeledPTrees
-- name    : LeGallBrownianMap_labeledPTrees
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:37:55.38141+00:00
-- url     : https://prove2.me/theorems/42f93ce8-b6d6-49e6-8534-648c649e09f6
-- title:
--   The set $\mathbb T^p_n$ of labeled $p$-trees with $n$ black vertices
-- statement:
--   A **labeled $p$-tree** is a pair $\theta=(\tau,(\ell_v)_{v\in\tau^\circ})$ of a $p$-tree $\tau$ and integer labels on its white vertices $\tau^\circ$ such that
--
--   1. $\ell_\varnothing = 0$;
--   2. for every black vertex $v$, with parent $v(0)$ and children $v(j)=vj$, $1\le j\le p-1$, and $v(p)=v(0)$: $\ell_{v(j+1)}\ge \ell_{v(j)}-1$ for $j=0,\dots,p-1$.
--
--   $\mathbb T^p_n$ is the set of labeled $p$-trees with $n$ black vertices (size $n$). It is finite; a uniform element $\theta_n$ of $\mathbb T^p_n$ codes a uniform rooted pointed $2p$-angulation with $n$ faces.
--
--   **Formalization Note** Labels are a function on all words that vanishes off the white vertices of $\tau$, so that each labeled $p$-tree has exactly one representative.
-- source:
--   Le Gall, Uniqueness and universality of the Brownian map, arXiv:1105.4842v2, §2.1, p.8; §2.2, p.10 (T^p_n)

import Mathlib
import Definitions.Def_LeGallBrownianMap_IsPTree

namespace LeGallBrownianMap

/-- Le Gall, *Uniqueness and universality of the Brownian map*, arXiv:1105.4842v2, §2.1, p.8,
and §2.2, p.10: "vertices v of τ such that |v| is even are called white vertices, and vertices v of
τ such that |v| is odd are called black vertices. […] the size |τ| of a p-tree τ is the number of
its black vertices. […] A labeled p-tree is a pair θ = (τ, (ℓ_v)_{v∈τ°}) that consists of a p-tree τ
and a collection of integer labels assigned to the white vertices of τ, such that the following
properties hold: (a) ℓ_∅ = 0 and ℓ_v ∈ ℤ for each v ∈ τ°. (b) Let v ∈ τ•, let v(0) be the parent
of v and let v(j) = vj, 1 ≤ j ≤ p − 1, be the children of v. Then for every j ∈ {0, 1, ..., p − 1},
ℓ_{v(j+1)} ≥ ℓ_{v(j)} − 1, where by convention v(p) = v(0)." and "Let T^p_n stand for the set of
all labeled p-trees with n black vertices."

`labeledPTrees p n` is `T^p_n`: pairs `(τ, ℓ)` with `τ` a p-tree with `n` black vertices and
`ℓ` integer labels on its white vertices satisfying (a) and (b).

**Formalization Note.** The labels are a function `ℓ : List ℕ+ → ℤ` that is required to vanish
off the white vertices of `τ`, so that each labeled p-tree has exactly one representative and the
set is finite (its elements are in bijection with the paper's pairs). The parent `v(0)` of a
black vertex `v` is `v.dropLast`; the child `v(j)`, `1 ≤ j ≤ p − 1`, is `v ++ [j]`
(`Nat.toPNat' j = j` for `j ≥ 1`). -/
def labeledPTrees (p n : ℕ) : Set (Finset (List ℕ+) × (List ℕ+ → ℤ)) :=
  {θ | IsPTree p θ.1 ∧ (θ.1.filter (fun v => Odd v.length)).card = n ∧
    θ.2 [] = 0 ∧ (∀ v, ¬ (v ∈ θ.1 ∧ Even v.length) → θ.2 v = 0) ∧
    ∀ v ∈ θ.1, Odd v.length → ∀ j : ℕ, j < p →
      θ.2 (if j + 1 = p then v.dropLast else v ++ [Nat.toPNat' (j + 1)]) ≥
        θ.2 (if j = 0 then v.dropLast else v ++ [Nat.toPNat' j]) - 1}

end LeGallBrownianMap


