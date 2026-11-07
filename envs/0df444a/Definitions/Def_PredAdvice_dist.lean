-- Prove2me | Definitions.Def_PredAdvice_dist
-- name    : PredAdvice_dist
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:33:16.274565+00:00
-- url     : https://prove2.me/theorems/d569df29-7461-435c-99af-189c390def44
-- title:
--   Directed distance $\mathrm{dist}_G(u,v)\in\mathbb N\cup\{+\infty\}$
-- statement:
--   Let $G=(V,E)$ be a directed graph. The **directed distance** $\mathrm{dist}_G(u,v)$ is the minimum number of edges of a directed walk from $u$ to $v$, and $\mathrm{dist}_G(u,v)=+\infty$ when $v$ is unreachable from $u$:
--   $$
--   \mathrm{dist}_G(u,v)=\min\{k\in\mathbb N : \text{there are } u=p_0,p_1,\dots,p_k=v \text{ with } (p_{i-1},p_i)\in E\}.
--   $$
--   A pair $(u,v)$ is **reachable** when $\mathrm{dist}_G(u,v)<\infty$. The module also defines the **reversed graph** $G^{\mathrm{rev}}$, in which every edge $(a,b)$ becomes $(b,a)$, and a **shortest $u$–$v$ path** as a vertex list $(p_0=u,\dots,p_d=v)$ of consecutive edges with $d=\mathrm{dist}_G(u,v)$.
--
--   All statements of the mission measure lengths with this distance.
--
--   **Formalization Note** The value lives in $\mathbb N_\infty$ (`ℕ∞`), the infimum of the empty set being $+\infty$. Graphs are Mathlib's `Digraph`, which allows loops; a loop never lies on a shortest walk.
-- source:
--   Kopelowitz, Korin, Roditty, Using Small Advice to Compress the Predecessor Matrix, STOC 2027 submission (manuscript sha256 0ae8a68d…), §2 Conventions, p.10

import Mathlib

set_option autoImplicit false

namespace PredAdvice

/-- A directed walk with exactly `k` edges from `u` to `v` in the digraph `G`
(Kopelowitz, Korin, Roditty, *Using Small Advice to Compress the Predecessor Matrix*,
STOC 2027 submission (manuscript sha256 0ae8a68d…), §2 Conventions, p.10): `WalkLen G k u v`
holds when there are vertices `u = p₀, p₁, …, p_k = v` with an edge `p_{i−1} → p_i` for every
`i`. Helper for `dist`. -/
inductive WalkLen {V : Type*} (G : Digraph V) : ℕ → V → V → Prop
  | refl (u : V) : WalkLen G 0 u u
  | tail {k : ℕ} {u x y : V} : WalkLen G k u x → G.Adj x y → WalkLen G (k + 1) u y

/-- The directed distance `dist_G(u, v)` (Kopelowitz, Korin, Roditty, *Using Small Advice to
Compress the Predecessor Matrix*, STOC 2027 submission (manuscript sha256 0ae8a68d…),
§2 Conventions, p.10): "the minimum number of edges in a directed u–v path", and `+∞` when `v` is
unreachable from `u`.

**Formalization Note** The value lies in `ℕ∞`: it is the infimum of the lengths of all directed
walks from `u` to `v` (a shortest walk is a path), and the infimum of the empty set is `⊤ = +∞`,
which is the paper's convention for unreachable pairs. Mathlib's `Digraph` allows loops; a loop
never lies on a shortest walk, so distances are those of the loopless graph. -/
noncomputable def dist {V : Type*} (G : Digraph V) (u v : V) : ℕ∞ :=
  ⨅ (k : ℕ) (_ : WalkLen G k u v), (k : ℕ∞)

/-- `v` is reachable from `u`: `dist_G(u, v) < +∞`. -/
def Reachable {V : Type*} (G : Digraph V) (u v : V) : Prop :=
  dist G u v ≠ ⊤

/-- The reversed graph `G^rev` of p.7: every edge `(a, b)` of `G` becomes `(b, a)`. -/
def rev {V : Type*} (G : Digraph V) : Digraph V where
  Adj a b := G.Adj b a

/-- A shortest `u–v` path, given as its list of vertices `[p₀ = u, p₁, …, p_d = v]`: consecutive
vertices are joined by edges of `G` and the number of edges `d` equals `dist_G(u, v)`. -/
def IsShortestPath {V : Type*} (G : Digraph V) (p : List V) (u v : V) : Prop :=
  p.head? = some u ∧ p.getLast? = some v ∧ p.IsChain G.Adj ∧
    ((p.length - 1 : ℕ) : ℕ∞) = dist G u v

end PredAdvice


