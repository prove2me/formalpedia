-- Prove2me | Definitions.Def_PredAdvice_H
-- name    : PredAdvice_H
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:33:58.258173+00:00
-- url     : https://prove2.me/theorems/87317950-7289-4d28-a36f-e71a83390bdf
-- title:
--   Shortest-path vertices $H_{u,v}$, $H^\circ_{u,v}$ and large/small pairs
-- statement:
--   Let $G=(V,E)$ be a finite directed graph. For a reachable ordered pair $(u,v)$ the set of **shortest-path vertices** is
--   $$
--   H_{u,v}=\{h\in V : \mathrm{dist}(u,h)+\mathrm{dist}(h,v)=\mathrm{dist}(u,v)\},
--   $$
--   and $H^\circ_{u,v}=H_{u,v}\setminus\{u,v\}$. For an integer $D$, a reachable pair is **large** if $|H_{u,v}|\ge D$ and **small** if $|H_{u,v}|<D$.
--
--   These sets drive the whole construction: large pairs are hit by a random sample, small pairs are handled by colourings and induced matchings.
--
--   **Formalization Note** For an unreachable pair the identity holds at $+\infty=+\infty$ for many $h$, so $H_{u,v}$ is defined to be empty there, and large and small pairs are reachable by definition. $H^\circ_{u,u}=\emptyset$.
-- source:
--   Kopelowitz, Korin, Roditty, Using Small Advice to Compress the Predecessor Matrix, STOC 2027 submission (manuscript sha256 0ae8a68d…), §3, p.11; §3.2, p.12

import Mathlib
import Definitions.Def_PredAdvice_dist

set_option autoImplicit false

namespace PredAdvice

open Classical in
/-- The **shortest-path vertices** of a pair (Kopelowitz, Korin, Roditty, *Using Small Advice to
Compress the Predecessor Matrix*, STOC 2027 submission (manuscript sha256 0ae8a68d…), §3, p.11):
for a reachable ordered pair `(u, v)`,
`H_{u,v} := {h ∈ V : dist(u, h) + dist(h, v) = dist(u, v)}`.

**Formalization Note** The paper defines `H_{u,v}` only for reachable pairs. In `ℕ∞` the identity
`⊤ + dist(h, v) = ⊤` would put many vertices into `H_{u,v}` of an unreachable pair, so the set is
defined to be empty when `v` is unreachable from `u`; every statement of the mission uses
`H_{u,v}` only on reachable pairs. -/
noncomputable def H {V : Type*} [Fintype V] (G : Digraph V) (u v : V) : Finset V :=
  Finset.univ.filter fun h => Reachable G u v ∧ dist G u h + dist G h v = dist G u v

/-- `H°_{u,v} := H_{u,v} \ {u, v}` (§3.2, p.12), the interior shortest-path vertices.

**Formalization Note** The paper writes it for nontrivial pairs `u ≠ v`; the formula is used for
every pair, and for `u = v` it is empty. -/
noncomputable def Hcirc {V : Type*} [Fintype V] [DecidableEq V] (G : Digraph V) (u v : V) :
    Finset V :=
  (H G u v \ {u}) \ {v}

/-- A reachable pair `(u, v)` is **large** if `|H_{u,v}| ≥ D` (§3, p.11). -/
def IsLarge {V : Type*} [Fintype V] (G : Digraph V) (D : ℕ) (u v : V) : Prop :=
  Reachable G u v ∧ D ≤ (H G u v).card

/-- A reachable pair `(u, v)` is **small** if `|H_{u,v}| < D` (§3, p.11). Trivial pairs `(u, u)`
are small for `D ≥ 2`, since `H_{u,u} = {u}`. -/
def IsSmall {V : Type*} [Fintype V] (G : Digraph V) (D : ℕ) (u v : V) : Prop :=
  Reachable G u v ∧ (H G u v).card < D

end PredAdvice


