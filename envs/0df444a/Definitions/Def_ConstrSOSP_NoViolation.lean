-- Prove2me | Definitions.Def_ConstrSOSP_NoViolation
-- name    : ConstrSOSP_NoViolation
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:57:50.86946+00:00
-- url     : https://prove2.me/theorems/fbb74c27-eb44-4e60-8b42-7f2f9720acb6
-- title:
--   No regularity violation at a pair of points
-- statement:
--   For data $(f(x),\nabla f(x),\nabla^2f(x))$ and $(f(y),\nabla f(y),\nabla^2f(y))$ at two points and constants $L,L_1,L_2$, **no violation** occurs when
--
--   1. $|f(x)-f(y)|\le L\|x-y\|$;
--   2. $\|\nabla f(x)-\nabla f(y)\|\le L_1\|x-y\|$;
--   3. $\|\nabla^2f(x)-\nabla^2f(y)\|_F\le L_2\|x-y\|$;
--   4. $|f(y)-f(x)-\langle\nabla f(x),y-x\rangle|\le\frac{L_1}2\|x-y\|^2$;
--   5. $\big|f(y)-f(x)-\langle\nabla f(x),y-x\rangle-\frac12(y-x)^\top\nabla^2f(x)(y-x)\big|\le\frac{L_2}6\|x-y\|^3$.
--
--   These are the negations of the five violation outputs of the paper's total problems.
--
--   **Formalization Note** The Hessian difference is measured in the Frobenius norm, the stronger reading (the norm of the proof of Lemma 5.4).
-- source:
--   Kontogiannis, Panageas & Pollatos, The Computational Complexity of Avoiding Strict Saddle Points in Constrained Optimization, arXiv:2604.02285 (2 Nov 2026), Assumption 4.3, p.18; Definitions 4.6, 4.8, 4.10, pp.20–22

import Mathlib
import Definitions.Def_ApproxVI_euclNorm
import Definitions.Def_ParamSDPTraj_frob

namespace ConstrSOSP

/-- **No regularity violation at a pair of points** (arXiv:2604.02285, 2 Nov 2026, the violation
outputs of Definitions 4.6, 4.8 and 4.10, pp.20–22, and Assumption 4.3, p.18): for the data
`(f(x), ∇f(x), ∇²f(x)) = (fx, gx, Hx)` and `(f(y), ∇f(y), ∇²f(y)) = (fy, gy, Hy)`,
1. `|f(x) − f(y)| ≤ L ‖x − y‖`,
2. `‖∇f(x) − ∇f(y)‖ ≤ L₁ ‖x − y‖`,
3. `‖∇²f(x) − ∇²f(y)‖ ≤ L₂ ‖x − y‖`,
4. `|f(y) − f(x) − ⟨∇f(x), y − x⟩| ≤ (L₁/2) ‖x − y‖²` (first-order Taylor),
5. `|f(y) − f(x) − ⟨∇f(x), y − x⟩ − ½ (y − x)ᵀ∇²f(x)(y − x)| ≤ (L₂/6) ‖x − y‖³` (second-order
   Taylor).

These are the negations of the five violation inequalities.

**Formalization Note** Vector norms are Euclidean; the matrix norm in (3) is the Frobenius norm,
the stronger of the two usual readings (the norm of the proof of Lemma 5.4, p.49). -/
def NoViolation {d : ℕ} (L L1 L2 : ℝ) (x : Fin d → ℝ) (fx : ℝ) (gx : Fin d → ℝ)
    (Hx : Matrix (Fin d) (Fin d) ℝ) (y : Fin d → ℝ) (fy : ℝ) (gy : Fin d → ℝ)
    (Hy : Matrix (Fin d) (Fin d) ℝ) : Prop :=
  |fx - fy| ≤ L * ApproxVI.euclNorm (x - y) ∧
    ApproxVI.euclNorm (gx - gy) ≤ L1 * ApproxVI.euclNorm (x - y) ∧
    ParamSDPTraj.frob (Hx - Hy) ≤ L2 * ApproxVI.euclNorm (x - y) ∧
    |fy - fx - gx ⬝ᵥ (y - x)| ≤ L1 / 2 * ApproxVI.euclNorm (x - y) ^ 2 ∧
    |fy - fx - gx ⬝ᵥ (y - x) - 1 / 2 * ((y - x) ⬝ᵥ (Matrix.mulVec Hx (y - x)))| ≤ L2 / 6 * ApproxVI.euclNorm (x - y) ^ 3

end ConstrSOSP


