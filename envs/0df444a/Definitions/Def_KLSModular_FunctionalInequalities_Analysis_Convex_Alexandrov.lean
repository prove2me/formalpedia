-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Alexandrov
-- name    : KLSModular_FunctionalInequalities_Analysis_Convex_Alexandrov
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T16:52:45.899365+00:00
-- url     : https://prove2.me/theorems/3d12d62d-28ee-413a-8964-1771fdfa5905
-- title:
--   Quadratic test function at a point
-- statement:
--   For $A\in\mathbb{R}^{n\times n}$, $x_0,b,x\in\operatorname{EuclideanSpace}(\mathbb{R},\operatorname{Fin} n)$, and $c\in\mathbb{R}$, `quadraticAt A x₀ b c x` is $c+\langle b,x-x_0\rangle+\frac12\langle x-x_0,A(x-x_0)\rangle$. It is the quadratic test used in the weak Alexandrov and viscosity development, which also contains push-forward and geometric auxiliary results.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.Analysis.Convex.Subgradient
--   import Mathlib
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   def quadraticAt {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (x₀ b : EuclideanSpace ℝ (Fin n)) (c : ℝ)
--       (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
--     c + ⟪b, x - x₀⟫ + (1 / 2) * ⟪x - x₀, Matrix.toEuclideanLin A (x - x₀)⟫
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`Analysis/Convex/Subgradient`](https://prove2.me/theorems/67a77afb-a546-4173-875a-237133f9cad7).
--
--   Theorems in source order:
--
--   - [`lintegral_subgradientImage_eq_of_map_gradient`](https://prove2.me/theorems/72af9bcf-0597-4b8f-9f71-0ba93a4e8609)
--   - [`mem_subgradientImage_of_affine_le_of_nonneg_frontier`](https://prove2.me/theorems/f79e9028-f752-4900-ae74-36d3b8229978)
--   - [`exists_unit_inner_le_infDist_frontier`](https://prove2.me/theorems/f4f9ef6d-abf7-4073-89c1-856846d679e9)
--   - [`exists_pos_volume_convexHull_closedBall_union_singleton_ge`](https://prove2.me/theorems/04941f10-f990-4b5d-a225-77ccc909d39f)
--   - [`exists_pos_alexandrov_maximum_principle`](https://prove2.me/theorems/fb6f8a3c-985d-4638-9d88-5993fe585328)
--   - [`quadraticAt_subgradient_iff`](https://prove2.me/theorems/30c05a45-559f-4ce4-9d75-9148915945b6)
--   - [`convexOn_quadraticAt`](https://prove2.me/theorems/cc6c84fa-e5eb-4068-927b-9d626453be97)
--   - [`volume_subgradientImage_quadraticAt_aux`](https://prove2.me/theorems/af304715-487f-4a7a-bf76-4a29343dc231)
--   - [`infDist_frontier_le_of_forall_inner_le`](https://prove2.me/theorems/bd9c0578-bb14-4e91-95ff-70001c4a6fce)
--   - [`subgradientImage_comp_affineEquiv_symm`](https://prove2.me/theorems/3ad116ee-9145-4587-a1b0-81a8f51d65df)
--   - [`volume_subgradientImage_comp_affineEquiv_symm`](https://prove2.me/theorems/17cd1bb9-8c78-49af-a2a8-52c8ebcc13dc)
--   - [`subgradientImage_sub_inner_add_const`](https://prove2.me/theorems/8b64958d-7cd7-4f0c-96e8-9c9b1e0139d2)
--   - [`volume_subgradientImage_eq_lintegral_of_isOpen`](https://prove2.me/theorems/a875c8d6-d13c-4184-b1ba-d8541c085171)
--   - [`exists_inverse_subgradient_volume_bounds`](https://prove2.me/theorems/d2723f7d-8cba-4654-bce4-6f99044af824)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Convex/Alexandrov.lean) · `FunctionalInequalities.Analysis.Convex.Alexandrov` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Alexandrov.lean#L1414-L1418 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Alexandrov`, definition bundle `KLSModular_FunctionalInequalities_Analysis_Convex_Alexandrov`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Subgradient
import Mathlib

noncomputable section
open MeasureTheory Set
open scoped RealInnerProductSpace ENNReal
section LT12C1QuadraticSubgradientImage
open MeasureTheory Set Matrix
open scoped RealInnerProductSpace ENNReal
namespace FunctionalInequalities
namespace Analysis
/-- The quadratic function with constant `c`, slope `b` and Hessian matrix `A` centred at `x₀`:
`Q x = c + ⟪b, x − x₀⟫ + ½ ⟪x − x₀, A (x − x₀)⟫` (weak Letwin route, viscosity tests). -/
def quadraticAt {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (x₀ b : EuclideanSpace ℝ (Fin n)) (c : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  c + ⟪b, x - x₀⟫ + (1 / 2) * ⟪x - x₀, Matrix.toEuclideanLin A (x - x₀)⟫
end Analysis
end FunctionalInequalities
end LT12C1QuadraticSubgradientImage


