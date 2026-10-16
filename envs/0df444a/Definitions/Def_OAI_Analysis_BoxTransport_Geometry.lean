-- Prove2me | Definitions.Def_OAI_Analysis_BoxTransport_Geometry
-- name    : OAI_Analysis_BoxTransport_Geometry
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T13:05:51.955055+00:00
-- url     : https://prove2.me/theorems/d86235da-e100-4e49-9604-48292a013313
-- title:
--   Coordinate gap between two rational boxes and $\varepsilon$-enlarged open boxes in $\mathbb{R}^3$
-- statement:
--   This file introduces two elementary notions about axis-parallel boxes in three-dimensional space and records one simplification rule for iterated derivatives. Points of $\mathbb{R}^3$ and of $\mathbb{Q}^3$ have coordinates indexed by $j\in\{0,1,2\}$.
--
--   1. **Coordinate gap.** For rational vectors $a,b,h,k\in\mathbb{Q}^3$, thought of as the centers $a,b$ and half-widths $h,k$ of the closed boxes $\{x:|x_j-a_j|\le h_j\ \text{for all } j\}$ and $\{x:|x_j-b_j|\le k_j\ \text{for all } j\}$, the coordinate gap is the rational number
--   $$\operatorname{gap}(a,b,h,k)=\max_{j\in\{0,1,2\}}\bigl(|a_j-b_j|-h_j-k_j\bigr)\in\mathbb{Q}.$$
--   It is positive exactly when some coordinate $j$ satisfies $|a_j-b_j|>h_j+k_j$; for nonnegative half-widths this says that the projections of the two boxes onto the $j$-th axis are disjoint intervals at distance $|a_j-b_j|-h_j-k_j$.
--
--   2. **Enlarged open box.** For $c,h\in\mathbb{R}^3$ and $\varepsilon\in\mathbb{R}$,
--   $$O_\varepsilon(c,h)=\bigl\{x\in\mathbb{R}^3:\ |x_j-c_j|<h_j+\varepsilon\ \text{for } j=0,1,2\bigr\}.$$
--   This is an open (possibly empty) box with center $c$ and half-widths $h_j+\varepsilon$; when $\varepsilon>0$ it contains the closed box with center $c$ and half-widths $h$.
--
--   3. **Mixed derivatives of the zero field.** Consider vector fields $U:\mathbb{R}\times\mathbb{R}^3\to\mathbb{R}^3$ on space-time, whose points are written $p=(t,x)$. An axis is either the time direction $(1,0)$ or a spatial direction $(0,e_j)$, where $e_j$ is the $j$-th standard basis vector of $\mathbb{R}^3$. For a finite list of axes $(\delta_1,\dots,\delta_m)$ the mixed derivative is defined recursively by $\partial_{()}U=U$ and $\partial_{(\delta_1,\dots,\delta_m)}U(p)=D\bigl(\partial_{(\delta_2,\dots,\delta_m)}U\bigr)(p)\,\delta_1$, the derivative at $p$ applied to the vector $\delta_1$. Every mixed derivative of the zero field vanishes:
--   $$\partial_{(\delta_1,\dots,\delta_m)}0=0\qquad\text{for every finite list of axes}.$$
--
--   The coordinate gap is an exactly computable rational measure of how well two rational boxes are separated, and the enlarged open boxes supply open neighbourhoods of closed boxes, as needed for smooth cutoffs that are identically one near a box and for open sets on which a flow is required to coincide with an affine map.
--
--   **Formalization Note** Points are functions `Fin 3 → ℝ` (resp. `Fin 3 → ℚ`). `coordinateGap a b h k` takes the maximum with `Finset.sup'` over `Fin 3`, and `openBox c h ε` is the enlarged open box. `mixedDerivative_zero` is a simp lemma about the mission's `mixedDerivative`, which is built from `fderiv` (the Fréchet derivative, which Lean takes to be $0$ at points where the function is not differentiable).
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/BoxTransport/Geometry.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/BoxTransport/Geometry.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the BalancedBoxRouting mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_BalancedBoxRouting

namespace OAI

/-! Quantitative box separation, affine images and positive diagonal shape estimates. -/

noncomputable section
open scoped Topology
open scoped BigOperators ContDiff

namespace BoxTransport.Routing
@[simp] theorem mixedDerivative_zero (ds : List Axis) :
    mixedDerivative ds (fun _ => (0 : Space)) = fun _ => 0 := by
  induction ds with
  | nil => rfl
  | cons j js ih => simp [mixedDerivative, ih]

def coordinateGap (a b h k : RationalSpace) : ℚ :=
  (Finset.univ : Finset (Fin 3)).sup' Finset.univ_nonempty
    (fun j => |a j - b j| - h j - k j)

def openBox (c h : Space) (ε : ℝ) : Set Space :=
  {x | ∀ j, |x j - c j| < h j + ε}

end BoxTransport.Routing

end

end OAI


