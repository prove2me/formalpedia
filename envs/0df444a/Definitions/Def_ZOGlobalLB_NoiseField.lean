-- Prove2me | Definitions.Def_ZOGlobalLB_NoiseField
-- name    : ZOGlobalLB_NoiseField
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:49:24.65706+00:00
-- url     : https://prove2.me/theorems/ba65089f-8efd-41f5-af00-c9467134d608
-- title:
--   The multistage noise field $N_j$
-- statement:
--   For one sample label $j$, let $Q_{j,i}$ be the one-stage field built from the stage-$i$ tensors of $j$, all stage and degree tensors being independent. The combined noise is
--   $$N_j(w,x)=\sum_{i=1}^T\tau(\|g_{>i}(w)\|)\,Q_{j,i}(x-a_{<i}(w),g_i(w)),$$
--   considered as a function of $(w,x)\in\mathbb R^T\times\mathbb R^m$, and composed with the soft coordinate map as $(z,x)\mapsto N_j(U^\top y(z),x)$.
--
--   **Formalization Note.** Both versions are functions on Euclidean products (`WithLp 2`), so their global Lipschitz constants are for the Euclidean norm on pairs.
-- source:
--   Xia, Yuan, On Global Joint Lower Bounds in Zeroth-Order Nonconvex Optimization, arXiv:2610.19652, (34), p.19; Appendix D, p.56

import Mathlib
import Definitions.Def_ZOGlobalLB_Fnew
import Definitions.Def_ZOGlobalLB_Field

namespace ZOGlobalLB

/-- **The multistage noise field** (34), p.19 (and p.56):
`N_j(w, x) = Σ_{i=1}^T τ(‖g_{>i}(w)‖) Q_{j,i}(x - a_{<i}(w), g_i(w))`, where `Q_{j,i}` is the
one-stage field (85) built from the stage-`i` tensors of label `j`.

**Formalization Note.** `G : Fin T × Idx m → ℝ` holds all stage tensors of one label `j`:
`G (i, ·)` is the array of stage `i` (0-based). Under `gaussArr (Fin T × Idx m)` all
stage/degree entries are independent standard Gaussians, as in (34). -/
noncomputable def noiseN {m T : ℕ} (σ : ℝ) (V : Fin T → E m) (G : Fin T × Idx m → ℝ)
    (w : E T) (x : E m) : ℝ :=
  ∑ i, tauC (sufGt w i) * Qfield σ (fun k => G (i, k)) (x - aBefore V w i) (gAct w i)

/-- The field (34) as a function of `(w, x)` in `WithLp 2 (E T × E m)` (Euclidean norm), whose
global Lipschitz constant is `Lip_{(w,x)}(N_j)` of Theorem D.1. -/
noncomputable def noiseNP {m T : ℕ} (σ : ℝ) (V : Fin T → E m) (G : Fin T × Idx m → ℝ)
    (p : WithLp 2 (E T × E m)) : ℝ :=
  noiseN σ V G p.ofLp.1 p.ofLp.2

/-- The field composed with the soft coordinate map, `(z, x) ↦ N_j(Uᵀ y(z), x)` (Theorem D.1,
p.56; p.65), on `WithLp 2 (E r × E m)`. -/
noncomputable def noiseNZ {r m T : ℕ} (σ : ℝ) (U : Fin T → E r) (V : Fin T → E m)
    (G : Fin T × Idx m → ℝ) (p : WithLp 2 (E r × E m)) : ℝ :=
  noiseN σ V G (wcoord U p.ofLp.1) p.ofLp.2

end ZOGlobalLB


