-- Prove2me | Definitions.Def_ConeL2G_avail
-- name    : ConeL2G_avail
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:39:38.321261+00:00
-- url     : https://prove2.me/theorems/97165be3-451c-46fb-98ae-78e70f08f56d
-- title:
--   Available colors $L_i^{-x_{N_H(i)}}$
-- statement:
--   For a vertex $i$ of $H$ and an assignment $x$, the **available colors** of $i$ are
--   $$L_i^{-x_{N_H(i)}}=L_i\setminus\{x_j: j\in N_H(i)\},$$
--   the colors of the list of $i$ not used by its neighbours. Its size is written $\ell_i^{-x_{N_H(i)}}$; it does not depend on $x_i$. Conditioned on the colors of all other vertices, the color of $i$ under $\mu_H$ is uniform on this set.
-- source:
--   Li–Oveis Gharan, Local-to-Global Theorems Based on Cones with Applications to Graph Coloring, arXiv:2610.37721, Section 2, p.7

import Mathlib

namespace ConeL2G

open Finset

/-- **The available colors** `L_i^{−x_{N_H(i)}} = Lᵢ ∖ x_{N_H(i)}` of a vertex `i` given the colors
`x` of its neighbours. Li–Oveis Gharan, arXiv:2610.37721, Section 2, p.7: "for a vector x we write
`L_i^{−x_{N(i)}}` to denote `Lᵢ ∖ x_{N(i)}`. Analogously, we write `ℓᵢ` or `ℓ_i^{−C}` to denote the
sizes of `Lᵢ`, `L_i^{−C}`".

Its cardinality is `ℓ_i^{−x_{N_H(i)}}`. It does not depend on `x i`. -/
def avail {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    {K : ℕ} (L : V → Finset (Fin K)) (i : V) (x : V → Fin K) : Finset (Fin K) :=
  L i \ (H.neighborFinset i).image x

end ConeL2G


