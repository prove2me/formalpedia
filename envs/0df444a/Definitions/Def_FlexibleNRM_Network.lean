-- Prove2me | Definitions.Def_FlexibleNRM_Network
-- name    : FlexibleNRM_Network
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:23:57.708736+00:00
-- url     : https://prove2.me/theorems/98694760-5a13-4f69-8f27-6e90670e3059
-- title:
--   Network revenue management instance with flexible products
-- statement:
--   An instance consists of a finite set of $n$ products $\mathcal J$, a finite set of $m$ resources $\mathcal L$ and a finite set of $r$ routes, together with the following data.
--
--   1. Resource $i$ has capacity $c_i\ge 1$.
--   2. Product $j$ has revenue $f_j$.
--   3. The selling horizon has periods $t=1,\dots,T$, with one customer arrival per period.
--   4. For each period $t$ there is a choice model: if the assortment $S\subseteq\mathcal J$ is offered, the customer buys $j$ with probability $\phi_{jt}(S)$, and leaves with probability $1-\sum_{j}\phi_{jt}(S)$. These probabilities are nonnegative, sum to at most one, and vanish for $j\notin S$.
--   5. Each product $j$ has a nonempty set $\mathcal R_j$ of routes that can serve it, and each route $p$ uses a nonempty set $A_p$ of resources. The incidence is $a_{ip}=1$ if $i\in A_p$ and $a_{ip}=0$ otherwise.
--
--   This is the data every other object of the mission is built on. A product with $|\mathcal R_j|=1$ is inflexible, and two products may share a route.
--
--   **Formalization Note** The periods are `Finset.Icc 1 T`, 1-based like the paper. The conditions $c_i\ge1$, $\mathcal R_j\ne\emptyset$ and $A_p\ne\emptyset$ exclude only expressions the paper leaves undefined. The revenue $f_j$ carries no sign.
-- source:
--   Zhu, Topaloglu, Performance Guarantees for Network Revenue Management with Flexible Products, manuscript of November 16, 2022, §2, p.7; §3, p.9 (A_p)

import Mathlib
import Definitions.Def_PersonalizedAssortment_IB_ChoiceModel

namespace FlexibleNRM

/-- An instance of **network revenue management with flexible products**.

Zhu, Topaloglu, *Performance Guarantees for Network Revenue Management with Flexible Products*,
manuscript of November 16, 2022, §2, p.7, and the definition of `A_p`, §3, p.9.

`n` products `J = Fin n`, `m` resources `L = Fin m`, `r` routes `Fin r`. Resource `i` has `c i`
units, product `j` has revenue `f j`, the selling horizon has the periods `1, …, T`, and
`(φ t).prob S j` is `φ_jt(S)`, the probability that the customer of period `t` buys `j` when `S` is
offered. `R j` is the set `R_j` of routes that can serve a purchase of product `j`, and `A p` is
the set `A_p` of resources used by route `p`.

**Formalization Note** Products, resources and routes are `Fin n`, `Fin m`, `Fin r`. Routes form one
type with `R : Fin n → Finset (Fin r)`, so two products may share a route (p.19 writes
`R = ∪_j R_j`). The periods stay 1-based like the paper: they are `Finset.Icc 1 T`, and the values
of `φ` outside it are never read. The hypotheses `0 < c i`, `(R j).Nonempty`, `(A p).Nonempty` only
exclude undefined expressions of the paper: it divides by `c_i`, and takes an `arg max` over `R_j`
and a `min` over `A_p`. `f` has no sign. The published `ChoiceModel` carries exactly the implicit
conditions of p.7 and p.2: probabilities are nonnegative, sum to at most one, and vanish off the
offered assortment. -/
structure Network (n m r : ℕ) where
  /-- The capacity `c_i` of resource `i`. -/
  c : Fin m → ℕ
  /-- Capacities are positive (the paper divides by `c_i`). -/
  c_pos : ∀ i, 0 < c i
  /-- The revenue `f_j` of product `j`. -/
  f : Fin n → ℝ
  /-- The number of periods `T`. -/
  T : ℕ
  /-- The choice model of period `t`: `(φ t).prob S j = φ_jt(S)`. -/
  φ : ℕ → PersonalizedAssortment.IB.ChoiceModel n
  /-- The set `R_j` of routes that can serve product `j`. -/
  R : Fin n → Finset (Fin r)
  /-- Every product has a route. -/
  R_nonempty : ∀ j, (R j).Nonempty
  /-- The set `A_p` of resources used by route `p`. -/
  A : Fin r → Finset (Fin m)
  /-- Every route uses a resource. -/
  A_nonempty : ∀ p, (A p).Nonempty

/-- The incidence `a_ip`: `1` if route `p` uses resource `i`, and `0` otherwise (p.7). -/
def Network.a {n m r : ℕ} (N : Network n m r) (i : Fin m) (p : Fin r) : ℕ :=
  if i ∈ N.A p then 1 else 0

end FlexibleNRM


