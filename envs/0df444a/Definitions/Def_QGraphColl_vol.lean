-- Prove2me | Definitions.Def_QGraphColl_vol
-- name    : QGraphColl_vol
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:10:15.589416+00:00
-- url     : https://prove2.me/theorems/873c2b07-815b-406f-9ef4-7e3a3f72c384
-- title:
--   Marked volume $\mathrm{vol}(G,S,x)$, counts $\ell_u(S)$, common-neighbour counts $c_{vw}$ and the objective $\psi_z(S)$
-- statement:
--   Let $G$ be a graph on the finite vertex set $V$, $x$ an input with marked set $M$, and $S\subseteq V$.
--
--   1. **Marked volume (Definition 2.1).**
--   $$\mathrm{vol}(G,S,x)=\sum_{v\in S\cap M}\deg_G(v),\qquad \mathrm{vol}(G,x)=\mathrm{vol}(G,V(G),x).$$
--   It counts incidences between edges and marked vertices of $S$.
--   2. **Neighbourhood counts.** $\ell_u(S)=|N_G(u)\cap S|$; in particular $\ell_u(M)$ is the number of marked neighbours of $u$.
--   3. **Common-neighbour counts.** $c_{vw}=|N_G(v)\cap N_G(w)|$ (so $c_{vv}=\deg_G(v)$).
--   4. **Least-squares objective.** For a real vector $z$ indexed by $V$,
--   $$\psi_z(S)=\sum_{u}\ell_u(S)^2-2\sum_{v\in S}z_v.$$
--
--   The marked volume is the quantity the algorithm repeatedly halves; $\ell$, $c$ and $\psi_z$ are the estimation and comparison quantities of §§3–4.
--
--   **Formalization Note.** Degrees in `vol G S x` are taken in `G` itself, so the volume of an edge set uses degrees in that edge set. Volumes and counts are natural numbers; `psi` is real.
-- source:
--   Cornelissen, Gilani, Kintali, Le Gall, Patro, Zhou, Breaking the quantum barriers for Graph Collision, arXiv:2611.05356 (version of October 2026, sha256 21da7ff0…), Definition 2.1, p.12; §3 Part 1, p.15 (ℓ_u(S)); §3 Part 2, p.16 (c_vw, ψ_z(S))

import Mathlib
import Definitions.Def_QGraphColl_gc

namespace QGraphColl

/-!
# Marked volume, neighbourhood counts, common-neighbour counts and the objective `ψ_z`

A. Cornelissen, A. S. Gilani, S. Kintali, F. Le Gall, S. Patro, X. Zhou, *Breaking the quantum
barriers for Graph Collision*, arXiv:2611.05356 (version of October 2026, sha256 21da7ff0…),
Definition 2.1, p.12 (marked volume); §3 Part 1, p.15 (`ℓ_u(S)`); §3 Part 2, p.16 (`c_vw`, `ψ_z`).

**Formalization Note.**
* `vol G S x = ∑_{v ∈ S ∩ M} deg_G(v)`, with degrees taken in `G` itself; the paper's
  `vol(G, x)` is `vol G Finset.univ x`. Volumes are natural numbers.
* `ell G S u = |N_G(u) ∩ S|`, `cn G v w = |N_G(v) ∩ N_G(w)|` (so `cn G v v = deg_G(v)`), and
  `psi G z S = ∑_u ℓ_u(S)² − 2 ∑_{v ∈ S} z_v` for a real vector `z` indexed by the vertices.
-/

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Definition 2.1, p.12: the marked volume `vol(G, S, x) = ∑_{v ∈ S ∩ M} deg_G(v)`. -/
noncomputable def vol (G : SimpleGraph V) (S : Finset V) (x : V → Bool) : ℕ :=
  ∑ v ∈ S ∩ marked x, deg G v

/-- §3 Part 1, p.15: `ℓ_u(S) = |N_G(u) ∩ S|`, the number of neighbours of `u` in `S`. -/
noncomputable def ell (G : SimpleGraph V) (S : Finset V) (u : V) : ℕ :=
  (nbr G u ∩ S).card

/-- §3 Part 2, p.16: the common-neighbour count `c_vw = |N_G(v) ∩ N_G(w)|`. -/
noncomputable def cn (G : SimpleGraph V) (v w : V) : ℕ :=
  (nbr G v ∩ nbr G w).card

/-- §3 Part 2, p.16: the least-squares objective `ψ_z(S) = ∑_u ℓ_u(S)² − 2 ∑_{v ∈ S} z_v`. -/
noncomputable def psi (G : SimpleGraph V) (z : V → ℝ) (S : Finset V) : ℝ :=
  ∑ u, ((ell G S u : ℝ)) ^ 2 - 2 * ∑ v ∈ S, z v

end QGraphColl


