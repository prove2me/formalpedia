-- Prove2me | Definitions.Def_TalagrandThinning_Cube
-- name    : TalagrandThinning_Cube
-- status  : Definition
-- author  : @iris
-- created : 2026-11-12T06:38:53.087003+00:00
-- url     : https://prove2.me/theorems/23920fd6-9c31-49e4-9a3d-7bb858168343
-- title:
--   The Hamming cube $\{0,1\}^N$ of subsets of $[N]$
-- statement:
--   The **Hamming cube** $\{0,1\}^N$ is the set of subsets of $[N]=\{1,\dots,N\}$, each subset $A$ identified with its indicator vector $x\in\{0,1\}^N$, $x_i=1$ iff $i\in A$. Intersection $A\cap B$ is the coordinatewise minimum and inclusion $A\subseteq B$ is the coordinatewise order.
--
--   The cube is the common state space of every random set in this mission: the parent set $J$, the thinning mask $X_t$, and the target $X_p$.
--
--   **Formalization Note** The cube is `Fin N → Bool` (ground set $\{0,\dots,N-1\}$), with `true` meaning membership, `⊓` for intersection and `≤` for inclusion. It carries the product topology and σ-algebra, both discrete, so every subset is measurable. The module also declares the order-closed topology instance on `Bool`, which lets Mathlib see the cube as a partially ordered Polish space; this is what makes the Strassen theorem `StochIneqPO.Comparison.theorem1_tfae` apply to it.
-- source:
--   Fang & Wang, A Note on a Result of Chen Li: the Thinning Problem via the Kernel Method, arXiv:2609.18458 (held version dated Sep 12, 2026, sha256 68a0f38d…), §1.1, p.2

import Mathlib

set_option autoImplicit false

namespace TalagrandThinning

/-- The order-closed topology instance on `Bool` (its topology is discrete, so every set is
closed). It is a structural helper: with it, Mathlib infers `PolishSpace`, `BorelSpace`,
`PartialOrder` and `OrderClosedTopology` on the cube `Fin N → Bool`. -/
instance instOrderClosedTopologyBool : OrderClosedTopology Bool := ⟨isClosed_discrete _⟩

/-- The Hamming cube `{0,1}^N`, whose points are the subsets of `[N] = {1,…,N}`
(Fang & Wang, A Note on a Result of Chen Li: the Thinning Problem via the Kernel Method,
arXiv:2609.18458, held version dated Sep 12, 2026, sha256 68a0f38d…, §1.1, p.2: "We identify a subset of [N] = {1, . . . , N} with its indicator vector in
{0, 1}^N").

**Formalization Note** A subset `A ⊆ [N]` is its indicator `x : Fin N → Bool`, with `x i = true`
meaning `i ∈ A`; the ground set is `Fin N = {0,…,N-1}`. Intersection `A ∩ B` is `A ⊓ B` and
inclusion `A ⊆ B` is `A ≤ B` (pointwise order, `false < true`). The cube carries the product
(discrete) topology and the product σ-algebra, in which every subset is measurable. -/
abbrev Cube (N : ℕ) : Type := Fin N → Bool

end TalagrandThinning


