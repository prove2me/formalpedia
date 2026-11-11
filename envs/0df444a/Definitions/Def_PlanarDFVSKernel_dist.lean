-- Prove2me | Definitions.Def_PlanarDFVSKernel_dist
-- name    : PlanarDFVSKernel_dist
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:35:02.581234+00:00
-- url     : https://prove2.me/theorems/704eee5f-a25e-475a-89a6-53892fc73cf2
-- title:
--   Directed shortest-path distance with nonnegative lengths
-- statement:
--   For a digraph with nonnegative real arc lengths $\ell$, $d(u,v)\in[0,\infty]$ is the infimum of $\sum_{e}\ell(e)$ over directed walks from $u$ to $v$; it is $\infty$ if $v$ is unreachable from $u$. The **incoming ball** of radius $r\ge0$ centred at $v$ is $B^-(v,r)=\{u: d(u,v)\le r\}$.
-- source:
--   Sheng, Xiao, A Polynomial Kernel for Planar Directed Feedback Vertex Set, arXiv:2609.23669 (held version, sha256 75cfca8f…), §5.1, p.18 (PDF 19)

import Mathlib
import Definitions.Def_PlanarDFVS_SingleExp_Graphs

set_option autoImplicit false

namespace PlanarDFVSKernel

open PlanarDFVS.SingleExp
open scoped NNReal ENNReal

/-- **The directed shortest-path distance `d(u, v)`** (Sheng, Xiao, *A Polynomial Kernel for
Planar Directed Feedback Vertex Set*, arXiv:2609.23669 (held version, sha256 75cfca8f…), §5.1,
p.18 (PDF 19)): "For a digraph with nonnegative arc lengths, let d(u, v) be the directed
shortest-path distance, with value ∞ if v is unreachable from u."

The infimum, over directed walks `es` from `u` to `v` (published `Walk`), of the total length
`∑ ℓ(e)`, computed in `[0, ∞]`; it is `∞` when no walk exists and `0` for `u = v`.

**Formalization Note** Lengths are nonnegative reals; an infimum over walks equals the minimum over
paths since lengths are nonnegative. The incoming ball of the paper is
`B⁻(v, r) = {u : dist G ℓ u v ≤ r}` for a real `r ≥ 0`. -/
noncomputable def dist {n m : ℕ} (G : Graph n m) (ℓ : Fin m → ℝ≥0) (u v : Fin n) : ℝ≥0∞ :=
  ⨅ (es : List (Fin m)) (_ : Walk G u v es), ((es.map fun e => (ℓ e : ℝ≥0∞)).sum)

end PlanarDFVSKernel


