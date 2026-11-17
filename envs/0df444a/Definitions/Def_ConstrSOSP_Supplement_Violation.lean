-- Prove2me | Definitions.Def_ConstrSOSP_Supplement_Violation
-- name    : ConstrSOSP_Supplement_Violation
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:22:51.941798+00:00
-- url     : https://prove2.me/theorems/e85ba0d5-df2a-4284-931d-e0dfe8a6bfc9
-- title:
--   A regularity violation at a pair of points (five strict inequalities)
-- statement:
--   Let $x,y\in\mathbb R^d$ carry data $(f(x),\nabla f(x),\nabla^2 f(x))$ and $(f(y),\nabla f(y),\nabla^2 f(y))$, and let $L,L_1,L_2$ be constants. The pair is a **regularity violation** if at least one of the following holds:
--
--   1. $|f(x)-f(y)|>L\|x-y\|$;
--   2. $\|\nabla f(x)-\nabla f(y)\|>L_1\|x-y\|$;
--   3. $\|\nabla^2 f(x)-\nabla^2 f(y)\|>L_2\|x-y\|$;
--   4. $|f(y)-f(x)-\langle\nabla f(x),y-x\rangle|>\frac{L_1}{2}\|x-y\|^2$ (first-order Taylor);
--   5. $\left|f(y)-f(x)-\langle\nabla f(x),y-x\rangle-\frac12(y-x)^\top\nabla^2 f(x)(y-x)\right|>\frac{L_2}{6}\|x-y\|^3$ (second-order Taylor).
--
--   These are the "violations" that Definitions 4.6 and 4.8 accept as solutions, which make the white-box problems total.
--
--   **Formalization Note** The paper's norm is the Euclidean norm $\|\cdot\|_2$ (p.18); on matrices this is the induced operator (spectral) norm, `HighDimProb.QuadraticForms.opNorm`. All inequalities are strict as printed.
-- source:
--   Kontogiannis, Panageas & Pollatos, The Computational Complexity of Avoiding Strict Saddle Points in Constrained Optimization, arXiv:2604.02285 (2 Nov 2026), Definition 4.6, p.20; Definition 4.8, p.21; norm convention p.18

import Mathlib
import Definitions.Def_ApproxVI_euclNorm
import Definitions.Def_HighDimProb_QuadraticForms_OperatorNorm

namespace ConstrSOSP.Supplement

/-- **A regularity violation at a pair of points** (Kontogiannis, Panageas & Pollatos,
arXiv:2604.02285, 2 Nov 2026, the violation outputs of Definition 4.6, p.20, repeated in
Definition 4.8, p.21): for the data `(f(x), ∇f(x), ∇²f(x)) = (fx, gx, Hx)` and
`(f(y), ∇f(y), ∇²f(y)) = (fy, gy, Hy)`, at least one of
1. `|f(x) − f(y)| > L ‖x − y‖`,
2. `‖∇f(x) − ∇f(y)‖ > L₁ ‖x − y‖`,
3. `‖∇²f(x) − ∇²f(y)‖ > L₂ ‖x − y‖` ("f or ∇f or ∇²f is not Lipschitz"),
4. `|f(y) − f(x) − ⟨∇f(x), y − x⟩| > (L₁/2) ‖x − y‖²` ("∇f is not the gradient"),
5. `|f(y) − f(x) − ⟨∇f(x), y − x⟩ − ½ (y − x)ᵀ∇²f(x)(y − x)| > (L₂/6) ‖x − y‖³` ("∇²f is not the
   Hessian").

**Formalization Note** "Throughout this paper, we denote ‖·‖ by the Euclidean norm ‖·‖₂" (p.18):
vector norms are Euclidean (`ApproxVI.euclNorm`) and the matrix norm in (3) is the norm induced by
it, the operator (spectral) norm (`HighDimProb.QuadraticForms.opNorm`). All five inequalities are
strict, as printed. The base mission's `ConstrSOSP.NoViolation` uses the Frobenius norm in (3), so
it is not the negation of this predicate and is not reused. -/
def Violation {d : ℕ} (L L1 L2 : ℝ) (x : Fin d → ℝ) (fx : ℝ) (gx : Fin d → ℝ)
    (Hx : Matrix (Fin d) (Fin d) ℝ) (y : Fin d → ℝ) (fy : ℝ) (gy : Fin d → ℝ)
    (Hy : Matrix (Fin d) (Fin d) ℝ) : Prop :=
  L * ApproxVI.euclNorm (x - y) < |fx - fy| ∨
    L1 * ApproxVI.euclNorm (x - y) < ApproxVI.euclNorm (gx - gy) ∨
    L2 * ApproxVI.euclNorm (x - y) < HighDimProb.QuadraticForms.opNorm (Hx - Hy) ∨
    L1 / 2 * ApproxVI.euclNorm (x - y) ^ 2 < |fy - fx - gx ⬝ᵥ (y - x)| ∨
    L2 / 6 * ApproxVI.euclNorm (x - y) ^ 3 <
      |fy - fx - gx ⬝ᵥ (y - x) - 1 / 2 * ((y - x) ⬝ᵥ (Matrix.mulVec Hx (y - x)))|

end ConstrSOSP.Supplement


