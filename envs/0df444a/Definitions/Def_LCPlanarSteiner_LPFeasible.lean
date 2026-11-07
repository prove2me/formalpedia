-- Prove2me | Definitions.Def_LCPlanarSteiner_LPFeasible
-- name    : LCPlanarSteiner_LPFeasible
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T17:06:05.48184+00:00
-- url     : https://prove2.me/theorems/658a8892-373b-41b0-8da5-10561b72ce72
-- title:
--   Feasible points of the total-budget density LP (15)
-- statement:
--   For pairs $(s_i, t_i)$, $i \in [r]$, and a root $v$, a **feasible point** consists of purchases $x_e \ge 0$, demands $y_i \ge 0$ and flows $f^i \ge 0$ on the staged arcs of each pair such that
--   1. $\sum_i y_i = 1$;
--   2. (conservation) at every state of pair $i$ the outflow minus the inflow is $y_i$ at the source $(s_i, 0, -)$ and $0$ elsewhere, so the sink receives $y_i$;
--   3. (15) for every original arc $e$, pair $i$ and phase $d$,
--   $$
--   \sum_{j} f^{i,d}_{e,j} \le x_e ,
--   $$
--   the sum across levels, not across pairs or phases.
--
--   The objective is $X = \sum_e c_e x_e$.
--
--   **Formalization Note** Points are rational; the root must be a vertex.
-- source:
--   Mahboub, Rahgoshay, Nearly Exact Length Bounds for Directed Steiner Tree and Forest in Planar Graphs, STOC 2027 submission (manuscript sha256 5af18346c1fe696ca8ed57aa7736510e10e27188695bb15edcbe662315790dda), §4.4, display (15), p.14

import Mathlib
import Definitions.Def_LCPlanarSteiner_stagedArcs

namespace LCPlanarSteiner

open Classical in
/-- **Feasible points of the total-budget density LP (15) at root `v`.**
Mahboub, Rahgoshay, *Nearly Exact Length Bounds for Directed Steiner Tree and Forest in Planar
Graphs*, STOC 2027 submission (manuscript sha256 5af18346…), §4.4, p.14: "Use one purchase x_e ≥ 0, demands y_i ≥ 0, and staged flows of value y_i.
Minimize X = Σ_e c_e x_e under conservation and Σ_i y_i = 1, Σ_{copies in phase d} f^{i,d}_{e,j} ≤ x_e
(e, i, d). (15) The sum is across levels, not across pairs or phases."

`LPFeasible G dem v ε h x y f` for the pairs `dem` (`r` of them), the root `v < n`, purchases `x`,
demands `y` and flows `f i a` on the staged arcs `a` of pair `i`:
1. `x_e ≥ 0` (`e < m`), `y_i ≥ 0` and `f_i ≥ 0` on staged arcs (`i < r`), and `Σ_i y_i = 1`;
2. conservation: at every state `(u, j, d)` with `u < n`, `j ≤ Q`, the outflow minus the inflow of
   pair `i` is `y_i` at the source `(s_i, 0, −)` and `0` elsewhere (so the private sink receives
   `y_i`);
3. (15): for every arc `e`, pair `i` and phase `d`, `Σ_j f^{i,d}_{e,j} ≤ x_e`.

`lpValue G x = Σ_e c_e x_e` is the objective `X`.

**Formalization Note.** Flows are rational (an LP with rational data has rational optimal points).
Values of `f` off the staged arcs, of `x` off the arcs and of `y` off `[r]` are not used. -/
def LPFeasible (G : Net) (dem : List (ℕ × ℕ)) (v : ℕ) (ε h : ℚ) (x y : ℕ → ℚ)
    (f : ℕ → ℕ × ℕ × ℕ → ℚ) : Prop :=
  v < G.n ∧
  (∀ e < G.arcs.length, 0 ≤ x e) ∧ (∀ i < dem.length, 0 ≤ y i) ∧
  (∀ i < dem.length, ∀ a ∈ stagedArcs G ε h, 0 ≤ f i a) ∧
  (∑ i ∈ Finset.range dem.length, y i) = 1 ∧
  (∀ i < dem.length, ∀ st : ℕ × ℕ × Bool, st.1 < G.n → st.2.1 ≤ lpQ G ε h →
    (∑ a ∈ (stagedArcs G ε h).filter (fun a => stSrc G v (dem.getD i (0, 0)).2 a = some st),
        f i a) -
      (∑ a ∈ (stagedArcs G ε h).filter (fun a => stDst G ε h v a = some st), f i a) =
      if st = ((dem.getD i (0, 0)).1, 0, false) then y i else 0) ∧
  ∀ e < G.arcs.length, ∀ i < dem.length, ∀ d < 2,
    (∑ a ∈ (stagedArcs G ε h).filter (fun a => a.1 = d ∧ a.2.1 = e), f i a) ≤ x e

/-- The LP objective `X = Σ_e c_e x_e`. -/
def lpValue (G : Net) (x : ℕ → ℚ) : ℚ := ∑ e ∈ Finset.range G.arcs.length, G.cst e * x e

end LCPlanarSteiner


