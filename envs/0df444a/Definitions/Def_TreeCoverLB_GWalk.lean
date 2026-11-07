-- Prove2me | Definitions.Def_TreeCoverLB_GWalk
-- name    : TreeCoverLB_GWalk
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:24:07.066122+00:00
-- url     : https://prove2.me/theorems/a6cb76ab-c604-4df6-805c-ce898dd4935f
-- title:
--   Walks in the graph $\widetilde G_r$: weighted length and winding number
-- statement:
--   Given a triangulation $\Gamma$ of the scaled cone $C_r$ over $E_d\mathbb Z_p$, the graph $\widetilde G_r$ has vertex set $\Lambda_r=V(\Gamma)$ and two kinds of edges:
--
--   1. **ordinary edges**: the edges $\{x,y\}$ of $\Gamma$, with weight $\|x-y\|_2$;
--   2. **special edges**: for every boundary vertex $x\in\partial\Lambda_r=\Lambda_r\cap r|K|$, a zero-weight edge between $x$ and $\gamma x$ ($\gamma$ the action of $1\in\mathbb Z_p$), oriented $x\to\gamma x$.
--
--   A walk is a sequence of traversals of these edges. Its **length** is the sum of the weights of the traversed edges, and its **winding number** is
--   $$
--   \operatorname{wind}=\#\{\text{positive special traversals}\}-\#\{\text{negative special traversals}\}\pmod p .
--   $$
--
--   **Formalization Note** A walk is built step by step: the trivial walk, an ordinary step, a special step along the orientation ($x\to\gamma x$), or against it ($\gamma x\to x$).
-- source:
--   Chen, Huang, Tan, Xu, Improved Lower Bounds on Tree Covers, arXiv:2607.27264 (version of October 31, 2026), §4.1, p.13 (PDF p.15) (the graph G̃_r) and §4.2, p.14 (PDF p.16) (winding number)

import Mathlib
import Definitions.Def_TreeCoverLB_EJoin
import Definitions.Def_TreeCoverLB_scaledCone
import Definitions.Def_TreeCoverLB_IsTriangulation

open Classical

namespace TreeCoverLB

/-- A **walk in the graph `G̃_r`** (Chen, Huang, Tan, Xu, *Improved Lower Bounds on Tree Covers*, arXiv:2607.27264 (version of October 31, 2026), §4.1, p.13 (PDF p.15), and §4.2, p.14 (PDF p.16)), from
`x` to `z`. The vertices of `G̃_r` are the vertices `Λ_r = V(Γ)` of the triangulation `Γ` of the
scaled cone `C_r` over `E_dℤ_p`; it has
* **ordinary edges**: the edges `{x, y}` (`x ≠ y`) of `Γ`;
* **special edges**: for every boundary vertex `x ∈ ∂Λ_r = Λ_r ∩ r|K|`, an edge between `x` and
  `γx` (`γ` the action of `1 ∈ ℤ_p`), oriented `x → γx`.

A walk is a sequence of steps: `nil x` is the trivial walk at `x`; `ordinary` traverses an
ordinary edge `x — y`; `fwd` traverses a special edge along its orientation `x → γx`; `bwd`
traverses it against its orientation `γx → x`. -/
inductive GWalk {p d : ℕ} [NeZero p] (r : ℝ) (Γ : Finset (Finset (Fin (d + 1) × ZMod p → ℝ))) :
    (Fin (d + 1) × ZMod p → ℝ) → (Fin (d + 1) × ZMod p → ℝ) → Type
  /-- the trivial walk at `x` -/
  | nil (x : Fin (d + 1) × ZMod p → ℝ) : GWalk r Γ x x
  /-- an ordinary edge `x — y` of `Γ`, followed by a walk from `y` -/
  | ordinary {x y z : Fin (d + 1) × ZMod p → ℝ} (hne : x ≠ y) (hedge : ({x, y} : Finset _) ∈ Γ)
      (w : GWalk r Γ y z) : GWalk r Γ x z
  /-- the special edge `x → γx` traversed positively, followed by a walk from `γx` -/
  | fwd {x z : Fin (d + 1) × ZMod p → ℝ} (hx : x ∈ vertexSet Γ)
      (hb : x ∈ coneBase (EJoin d (ZMod p)) r) (w : GWalk r Γ (ejoinAct (1 : ZMod p) x) z) :
      GWalk r Γ x z
  /-- the special edge `x → γx` traversed negatively (from `γx` to `x`), followed by a walk
  from `x` -/
  | bwd {x z : Fin (d + 1) × ZMod p → ℝ} (hx : x ∈ vertexSet Γ)
      (hb : x ∈ coneBase (EJoin d (ZMod p)) r) (w : GWalk r Γ x z) :
      GWalk r Γ (ejoinAct (1 : ZMod p) x) z

namespace GWalk

variable {p d : ℕ} [NeZero p] {r : ℝ} {Γ : Finset (Finset (Fin (d + 1) × ZMod p → ℝ))}

/-- The **weighted length** of a walk in `G̃_r` (Chen, Huang, Tan, Xu, *Improved Lower Bounds on Tree Covers*, arXiv:2607.27264 (version of October 31, 2026), §3, p.8, `len(P)`; §4.1, p.13): an ordinary
edge `(x, y)` has weight `‖x − y‖₂`, a special edge has weight `0`. -/
noncomputable def length : {x z : Fin (d + 1) × ZMod p → ℝ} → GWalk r Γ x z → ℝ
  | _, _, nil _ => 0
  | x, _, ordinary (y := y) _ _ w => euclid x y + length w
  | _, _, fwd _ _ w => length w
  | _, _, bwd _ _ w => length w

/-- The **winding number** of a walk in `G̃_r` (Chen, Huang, Tan, Xu, *Improved Lower Bounds on Tree Covers*, arXiv:2607.27264 (version of October 31, 2026), §4.2, p.14 (PDF p.16)): the number of
positive special traversals minus the number of negative special traversals, mod `p`. -/
def winding : {x z : Fin (d + 1) × ZMod p → ℝ} → GWalk r Γ x z → ZMod p
  | _, _, nil _ => 0
  | _, _, ordinary _ _ w => winding w
  | _, _, fwd _ _ w => 1 + winding w
  | _, _, bwd _ _ w => -1 + winding w

end GWalk

end TreeCoverLB


