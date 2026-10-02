-- Prove2me | Definitions.Def_ChebotarevDensity_Aux
-- name    : ChebotarevDensity_Aux
-- status  : Definition
-- author  : @vebis
-- created : 2026-10-01T14:21:44.741221+00:00
-- url     : https://prove2.me/theorems/32a0c86a-231d-4a46-8e25-61b8b0b3a7f2
-- title:
--   Root counts modulo p and fixed-point counts on coset spaces
-- statement:
--   Two counting functions used to relate the factorization of a polynomial modulo a prime to the action of a Galois group.
--
--   1. For an integer polynomial $g\in\mathbb Z[X]$ and a natural number $p$ (in practice a prime), $\operatorname{rootCount}(g,p)$ is the number of roots of the reduction $\bar g=g \bmod p$ in the field $\mathbb F_p$, that is, $\#\{x\in\mathbb Z/p\mathbb Z:\ \bar g(x)=0\}$.
--
--   2. For a group $G$, a subgroup $H\le G$ and $\sigma\in G$, $\operatorname{fixCount}_H(\sigma)$ is the number of fixed points of $\sigma$ acting by left multiplication on the coset space $G/H$:
--   $$\operatorname{fixCount}_H(\sigma)=\#\{xH\in G/H:\ \sigma xH=xH\}.$$
--   This is the value at $\sigma$ of the permutation character of $G$ on $G/H$.
--
--   **Formalization Note** Both quantities are defined with `Nat.card`, so they take the junk value $0$ when the underlying set is infinite; this does not occur in the intended applications ($p$ prime, $G$ finite).
-- source:
--   Stevenhagen–Lenstra, Chebotarëv and his density theorem, Math. Intelligencer 18 (1996), no. 2, pp. 32–34 (decomposition type and Frobenius's theorem); permutation characters as in any text on finite group actions

import Mathlib

open Polynomial

namespace ChebotarevDensity

/-- The number of roots of the reduction modulo `p` of an integer polynomial `g` in `𝔽_p`. -/
noncomputable def rootCount (g : ℤ[X]) (p : ℕ) : ℕ :=
  Nat.card {x : ZMod p // (g.map (Int.castRingHom (ZMod p))).IsRoot x}

/-- The number of fixed points of `g` acting on the coset space `G / H`. -/
noncomputable def fixCount {G : Type*} [Group G] (H : Subgroup G) (g : G) : ℕ :=
  Nat.card {x : G ⧸ H // g • x = x}

end ChebotarevDensity


