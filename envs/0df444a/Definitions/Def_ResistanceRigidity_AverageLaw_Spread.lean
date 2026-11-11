-- Prove2me | Definitions.Def_ResistanceRigidity_AverageLaw_Spread
-- name    : ResistanceRigidity_AverageLaw_Spread
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T23:05:40.759188+00:00
-- url     : https://prove2.me/theorems/55faa80b-6aae-4b24-9b40-fb39cac95863
-- title:
--   Edge count $m$, average support degree $d = 2m/N$ and resistance spread $\varepsilon$ of a weighted graph (§2)
-- statement:
--   Let $c$ be the conductance function of a weighted graph on a finite vertex set $V$ with $N$ vertices, and let $R_{uv}$ be its effective resistances (the published `IncrementalER.reff`).
--
--   - $m$ (`edgeCount`) is the number of edges with positive conductance: the number of unordered pairs $\{u,v\}$, $u \ne v$, with $c(u,v) > 0$.
--   - $d = 2m/N$ (`avgDeg`) is the average support degree, a real number.
--   - For a graph with at least two vertices, the **spread** (`spread`) is
--   $$\varepsilon = \frac{\max_{u \ne v} R_{uv}}{\min_{u \ne v} R_{uv}} - 1,$$
--   where the maximum (`maxRes`) and the minimum (`minRes`) range over all ordered pairs of distinct vertices.
--
--   The spread measures how far the effective resistances are from being all equal: $\varepsilon = 0$ exactly when all resistances between distinct vertices coincide. It does not change when all conductances are multiplied by the same positive constant.
--
--   **Formalization Note.** When $V$ has fewer than two vertices there is no pair $u \ne v$, and `maxRes` and `minRes` are set to $0$; every statement of this mission assumes $N \ge 2$, so this value is never used. $\varepsilon$ is not normalized: the paper's normalization $\min_{u\ne v} R_{uv} = 1$ is a device of its proof, not part of the definition.
-- source:
--   Tianlang Chen, A Sharp Rigidity Law for Effective Resistance, STOC 2027 submission (manuscript, sha256 3846da8c…1e8b), p. 5, §2

import Mathlib
import Definitions.Def_IncrementalER_lap

namespace ResistanceRigidity.AverageLaw

/-!
# Edge count, average support degree and resistance spread

Tianlang Chen, *A Sharp Rigidity Law for Effective Resistance*, STOC 2027 submission
(manuscript, sha256 3846da8c…1e8b), §2, p. 5.

`m` is the number of edges with positive conductance (unordered pairs `{u, v}`, `u ≠ v`,
`c u v > 0`), `d = 2m/N`, and for a graph with at least two vertices the spread is
`ε = max_{u ≠ v} R_uv / min_{u ≠ v} R_uv − 1`, max and min over ordered pairs of distinct
vertices. On fewer than two vertices there are no such pairs, and `maxRes`, `minRes` take the
value `0` (never used: every statement assumes at least two vertices).
-/

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `m`: the number of edges of positive conductance, i.e. of the simple graph
`IncrementalER.adj c`. -/
noncomputable def edgeCount (c : V → V → ℝ) : ℕ := by
  classical
  exact (IncrementalER.adj c).edgeFinset.card

/-- `d = 2m/N`, the average support degree (a real number). -/
noncomputable def avgDeg (c : V → V → ℝ) : ℝ :=
  2 * (edgeCount c : ℝ) / (Fintype.card V : ℝ)

/-- `max_{u ≠ v} R_uv` over ordered pairs of distinct vertices (`0` if there is none). -/
noncomputable def maxRes (c : V → V → ℝ) : ℝ :=
  if h : (Finset.univ.offDiag : Finset (V × V)).Nonempty then
    Finset.univ.offDiag.sup' h (fun p => IncrementalER.reff c p.1 p.2)
  else 0

/-- `min_{u ≠ v} R_uv` over ordered pairs of distinct vertices (`0` if there is none). -/
noncomputable def minRes (c : V → V → ℝ) : ℝ :=
  if h : (Finset.univ.offDiag : Finset (V × V)).Nonempty then
    Finset.univ.offDiag.inf' h (fun p => IncrementalER.reff c p.1 p.2)
  else 0

/-- The spread `ε = max_{u ≠ v} R_uv / min_{u ≠ v} R_uv − 1`. -/
noncomputable def spread (c : V → V → ℝ) : ℝ :=
  maxRes c / minRes c - 1

end ResistanceRigidity.AverageLaw


