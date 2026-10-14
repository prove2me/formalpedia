-- Prove2me | Definitions.Def_LNTopology_Hermetic_Model
-- name    : LNTopology_Hermetic_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T08:31:53.013861+00:00
-- url     : https://prove2.me/theorems/5a8f76f4-7171-46db-82da-d3bb61d57cd3
-- title:
--   (SA+), p. 5 — the strengthened subadditivity of a channel cost with growth function $g_+$
-- statement:
--   Let $c:\mathbb R\to\mathbb R_+$ be a channel cost, that is, a cost satisfying (MO), (SY), (CI) and (SA) of §2.2 (the module `LNTopology.Local.Model`, which this one imports). The hermetization results of the paper (Theorems 3.8 and 3.9) need a property stronger than subadditivity: if the flow in a channel grows $k$-fold, the relative savings also grow.
--
--   Let $g_+:\mathbb R\to\mathbb R$ be nonnegative and strictly increasing on $[0,\infty)$. The cost $c$ satisfies **(SA+)** with $g_+$ if
--
--   $$c(kx)<\frac{k}{g_+(k)}\,c(x)\qquad\text{for all }k>1\text{ and }x>0 .$$
--
--   Since $g_+(k)>g_+(0)\ge 0$ for $k>1$, the quotient is well defined. The function $g_+$ measures how fast the per-unit cost of a channel falls as its flow grows; it enters the paper's degree thresholds through $g_+^{-1}$.
--
--   **Formalization Note** The page writes (SA+) as "for some strictly increasing $g_+:\mathbb R_+\to\mathbb R_+$, $c(kx)<\frac{k}{g_+(k)}c(x)$, $k\in\mathbb R_+$". Taken for all $x$ and all $k\ge0$ it is unsatisfiable (at $x=0$ it reads $0<0$) and false for the paper's own Appendix D cost when $k\le1$; it is stated here for $k>1$ and $x>0$, matching "if the flow in a channel grows $n$-fold". The case $x<0$ follows from (SY). $g_+$ is a function on $\mathbb R$ whose monotonicity and nonnegativity are required on $[0,\infty)$ only. The definition does not itself require $c$ to be a channel cost; every statement that uses it also assumes `IsChannelCost c`.
-- source:
--   Guasoni, Huberman & Shikhelman, Lightning Network Economics: Topology, SSRN 4439190 (version of Feb. 3, 2023), p. 5 (PDF 6), §2.2, (SA+)

import Mathlib
import Definitions.Def_LNTopology_Local_Model

namespace LNTopology.Hermetic

/-- Property (SA+) of §2.2 for the function `g` (the paper's `g₊`), in the corrected form:
`g` is strictly increasing and nonnegative on `[0, ∞)`, and `c (k x) < k / g k * c x`
for every `k > 1` and `x > 0`. -/
def SAPlus (c g : ℝ → ℝ) : Prop :=
  StrictMonoOn g (Set.Ici 0) ∧ (∀ k, 0 ≤ k → 0 ≤ g k) ∧
    ∀ k x, 1 < k → 0 < x → c (k * x) < k / g k * c x

end LNTopology.Hermetic


