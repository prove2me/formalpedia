-- Prove2me | Definitions.Def_EulerSparsify_IsEulerianApprox
-- name    : EulerSparsify_IsEulerianApprox
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:35:41.207172+00:00
-- url     : https://prove2.me/theorems/167118cd-99a2-4e4e-802d-741d831265d3
-- title:
--   Definition 1.1 — $\varepsilon$-Eulerian spectral approximation
-- statement:
--   Let $\vec G=(V,E,w)$ and $\vec H$ be directed graphs with nonnegative weights on the same vertex set $V$, and let $G=\mathrm{und}(\vec G)$. Then $\vec H$ is an **$\varepsilon$-Eulerian spectral approximation** of $\vec G$ if $\vec G$ and $\vec H$ are both Eulerian and
--
--   $$\bigl\|L_G^{\dagger/2}\,(\vec L_{\vec G}-\vec L_{\vec H})\,L_G^{\dagger/2}\bigr\|_{\mathrm{op}}\le\varepsilon .$$
--
--   The error is measured against the undirected Laplacian of $\vec G$ only. This is the notion of Cohen et al. used throughout the mission.
--
--   **Formalization Note** $\vec H$ may have its own edge type. Nonnegative weights are the paper's standing convention for graphs (p.8).
-- source:
--   Peng, Sachdeva, Zhang, Zhao, Nested Effective Resistance Partitions and Eulerian Sparsification, STOC 2027 submission (manuscript sha256 0cdf0d3973c1d2c682db79c667cac6e49bab79e8912a5fc379a98fe0aece077d), Definition 1.1, p.1 (PDF p.3)

import Mathlib
import Definitions.Def_EulerSparsify_DiGraph_dirLap
import Definitions.Def_EulerSparsify_DiGraph_IsEulerian
import Definitions.Def_EulerSparsify_sqrtPinv
import Definitions.Def_LiqPremiaEq_opNorm

namespace EulerSparsify

/-- **Definition 1.1 (Eulerian spectral approximation)**, p.1, PDF p.3.
Peng, Sachdeva, Zhang, Zhao, *Nested Effective Resistance Partitions and Eulerian
Sparsification*, STOC 2027 submission (manuscript sha256 0cdf0d39…), Definition 1.1: "A directed graph ⃗H is an ε-Eulerian spectral approximation of
⃗G = (V, E, w) if ⃗H and ⃗G are both Eulerian, V(⃗H) = V, and for G := und(⃗G),
‖L_G^{†/2} (⃗L_⃗G − ⃗L_⃗H) L_G^{†/2}‖_op ≤ ε."

`IsEulerianApprox G H ε`: both graphs have nonnegative weights and are Eulerian, they share the
vertex type `V`, and `LiqPremiaEq.opNorm (L_G^{†/2} (⃗L_G − ⃗L_H) L_G^{†/2}) ≤ ε`, where `L_G = G.lap` is the
Laplacian of `und(⃗G)`.

**Formalization Note.** `H` may have its own edge type `F`. Only the undirected Laplacian of
`⃗G` (not of `⃗H`) enters the norm, as in the definition. Nonnegative weights are the paper's
standing convention for graphs (p.8: "w ∈ ℝ^E_{≥0}"). `L^{†/2}` is `sqrtPinv` and the norm is the
spectral norm `LiqPremiaEq.opNorm`. -/
def IsEulerianApprox {V E F : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    [Fintype F] [DecidableEq F] (G : DiGraph V E) (H : DiGraph V F) (ε : ℝ) : Prop :=
  (∀ e, 0 ≤ G.w e) ∧ (∀ f, 0 ≤ H.w f) ∧ G.IsEulerian ∧ H.IsEulerian ∧
    LiqPremiaEq.opNorm (sqrtPinv G.lap * (G.dirLap - H.dirLap) * sqrtPinv G.lap) ≤ ε

end EulerSparsify


