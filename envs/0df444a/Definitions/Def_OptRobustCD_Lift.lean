-- Prove2me | Definitions.Def_OptRobustCD_Lift
-- name    : OptRobustCD_Lift
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:50:42.605208+00:00
-- url     : https://prove2.me/theorems/7ea93049-f643-481d-835b-f7e6449791db
-- title:
--   The lift $(R_Qx)_{u\to v}=x_v-x_u/(d\lambda)$ and the degree cutoff $Q_J$
-- statement:
--   For a graph $Q$ on $[n]$ and $x\in\mathbb R^n$, the lift $R_Qx\in\mathbb R^{\vec E(Q)}$ is
--   $$(R_Qx)_{u\to v}=x_v-\frac{x_u}{d\lambda}.$$
--   For $J\ge1$, $Q_J$ is obtained from $Q$ by deleting every edge with an endpoint of degree more than $J$ in $Q$ (all vertices are kept). The degree cutoff $F_k$ of §7 is the same operation.
--
--   The postprocessing of Lemma 5.3 outputs $R_{F_J}y/\|R_{F_J}y\|$.
--
--   **Formalization Note** Only $x_u$ is divided by $d\lambda$ (checked on the rendered page).
-- source:
--   Hopkins, Hua, Mohanty, Rajaraman, Steurer, Optimal Robust Community Detection, STOC 2027 submission (manuscript of November 3, 2026, sha256 3d287d5422db7c4a43e74333bda1dbed204af51a25fd9f2c6e875ae03a4dafa1), §9 p.43 (pdf p.45); §7 p.34 (pdf p.36)

import Mathlib
import Definitions.Def_OptRobustCD_DirEdges

namespace OptRobustCD

/-!
# The lift `R_Q` and the degree cutoff `Q_J`

Hopkins, Hua, Mohanty, Rajaraman, Steurer, *Optimal Robust Community Detection*, STOC 2027
submission (manuscript of November 3, 2026, sha256 3d287d54…), §9, p.43 (pdf p.45): "For a graph `Q`
on `[n]` and `x ∈ R^n`, let `R_Q x ∈ R^{E⃗(Q)}` lift to a vector on directed edges:
`(R_Q x)_{u→v} = x_v − x_u/(dλ)`. For `J ⩾ 1` let `Q_J` be the graph obtained from `Q` by deleting
every edge with an endpoint of degree more than `J` in `Q`."

**Formalization Note.**
* Only `x_u` is divided by `dλ` (checked on the rendered page). `R_Q x` vanishes off `E⃗(Q)`.
* `Q_J` keeps all vertices; an edge survives iff both endpoints have degree at most `J` in `Q`.
  §7's degree cutoff `F_k` (p.34) is the same operation.
-/

open scoped Classical

/-- `(R_Q x)_{u→v} = x_v − x_u/(dλ)` on `E⃗(Q)`, `0` elsewhere. -/
noncomputable def liftR {n : ℕ} (d lam : ℝ) (Q : SimpleGraph (Fin n)) (x : Fin n → ℝ) : EVec n :=
  fun p => if Q.Adj p.1 p.2 then x p.2 - x p.1 / (d * lam) else 0

/-- `Q_J`: delete every edge with an endpoint of degree more than `J` in `Q`. -/
noncomputable def degCut {n : ℕ} (Q : SimpleGraph (Fin n)) (J : ℕ) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel fun u v => Q.Adj u v ∧ Q.degree u ≤ J ∧ Q.degree v ≤ J

end OptRobustCD


