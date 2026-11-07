-- Prove2me | Definitions.Def_EulerSparsify_DiGraph_effRes
-- name    : EulerSparsify_DiGraph_effRes
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:34:17.164754+00:00
-- url     : https://prove2.me/theorems/7903e1d2-61be-43fc-8af2-b00e278e47f6
-- title:
--   Effective resistance $\mathrm{ER}_G(u,v)$
-- statement:
--   For an undirected weighted graph $G$ and vertices $u,v$, the **effective resistance** is
--
--   $$\mathrm{ER}_G(u,v)=b_{(u,v)}^\top L_G^\dagger\, b_{(u,v)},\qquad b_{(u,v)}=e_u-e_v .$$
--
--   When $u$ and $v$ lie in the same connected component this is the energy of a unit electrical flow from $u$ to $v$.
--
--   **Formalization Note** Across two connected components the true resistance is $+\infty$, while the pseudoinverse formula gives a finite number; every ER diameter bound in the mission therefore also requires connectivity (`DiamERLe`).
-- source:
--   Peng, Sachdeva, Zhang, Zhao, Nested Effective Resistance Partitions and Eulerian Sparsification, STOC 2027 submission (manuscript sha256 0cdf0d3973c1d2c682db79c667cac6e49bab79e8912a5fc379a98fe0aece077d), §3, Effective resistance, p.10 (PDF p.12)

import Mathlib
import Definitions.Def_EulerSparsify_DiGraph_lap
import Definitions.Def_EulerSparsify_sqrtPinv

namespace EulerSparsify

/-- **Effective resistance** `ER_G(u, v) = b_{(u,v)}ᵀ L_G† b_{(u,v)}` (§3, p.10, PDF p.12).
Peng, Sachdeva, Zhang, Zhao, *Nested Effective Resistance Partitions and Eulerian
Sparsification*, STOC 2027 submission (manuscript sha256 0cdf0d39…), §3, p.10: "For an undirected graph G, recall that the effective resistance (ER) of u, v ∈ V
is ER_G(u, v) := b_{(u,v)}ᵀ L_G† b_{(u,v)}", with `b_{(u,v)} = e_u − e_v` (p.9).

**Formalization Note.** `L_G†` is `pinvMat G.lap`. Between two vertices in different connected
components this is a finite value and not the resistance `+∞`; the ER diameter
`DiGraph.DiamERLe` therefore also requires connectivity. -/
noncomputable def DiGraph.effRes {V E : Type} [Fintype V] [DecidableEq V] [Fintype E]
    [DecidableEq E] (G : DiGraph V E) (u v : V) : ℝ :=
  let b : V → ℝ := Pi.single u 1 - Pi.single v 1
  b ⬝ᵥ (pinvMat G.lap).mulVec b

end EulerSparsify


