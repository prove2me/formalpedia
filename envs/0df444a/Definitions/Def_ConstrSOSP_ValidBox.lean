-- Prove2me | Definitions.Def_ConstrSOSP_ValidBox
-- name    : ConstrSOSP_ValidBox
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T21:03:02.36048+00:00
-- url     : https://prove2.me/theorems/1d27184b-21e9-42a5-840e-36ac4af4be2e
-- title:
--   Valid instances under the restrictions of Theorem 5.1
-- statement:
--   A white-box instance $(\epsilon_G,\epsilon_H,T,C_f,C_{\nabla f},C_{\nabla^2f})$ on $\mathcal X=[0,1]^2$ is **valid** (for the clock exponent $K$) when
--
--   1. $\epsilon_G>0$, $\epsilon_H>0$ and $\epsilon_H^2=\epsilon_G$, i.e. the accuracy is $(\epsilon,\sqrt\epsilon)$;
--   2. at every rational $x\in[0,1]^2$ the machines return $f(x)$, $\nabla f(x)$, $\nabla^2f(x)$ within the clock;
--   3. all regularity promises hold with $L=L_1=L_2=1$: no Lipschitz, smoothness, Hessian-Lipschitz or Taylor violation at any pair of rational points of $[0,1]^2$;
--   4. every $\epsilon_G$-approximate KKT point (proximal gradient with smoothness constant $1$) lies in $[1/12,11/12]^2$.
--
--   **Formalization Note** The white-box maps are the machines' rational outputs at rational inputs (p.17), so all promises are over rational points. The Hessian-Lipschitz promise uses the Frobenius norm.
-- source:
--   Kontogiannis, Panageas & Pollatos, The Computational Complexity of Avoiding Strict Saddle Points in Constrained Optimization, arXiv:2604.02285 (2 Nov 2026), Theorem 5.1, p.22; §4.1, p.17

import Mathlib
import Definitions.Def_ConstrSOSP_Poly
import Definitions.Def_ConstrSOSP_boxA
import Definitions.Def_ConstrSOSP_boxB
import Definitions.Def_ConstrSOSP_IsApproxKKT
import Definitions.Def_ConstrSOSP_Evals
import Definitions.Def_ConstrSOSP_NoViolation
import Definitions.Def_ConstrSOSP_encInst

namespace ConstrSOSP

/-- **Valid white-box instances on `[0, 1]²` under the restrictions of Theorem 5.1**
(arXiv:2604.02285, 2 Nov 2026, Theorem 5.1, p.22: "even when the domain is fixed to [0, 1]^2 and
all regularity promises hold. Hardness holds for finding an (ϵ, √ϵ)-SOSP with L = L1 = L2 = 1,
even when every ϵ-approximate KKT point belongs to [1/12, 11/12]^2").

`ValidBox K s` holds iff `s = encInst ϵG ϵH T cf cg cH` with
1. `ϵG > 0`, `ϵH > 0` and `ϵH² = ϵG` (the accuracy `(ϵ, √ϵ)`);
2. at every rational `x ∈ [0, 1]²` the three machines, run with the clock `T · (|w| + 1)^K`,
   return values `f(x)`, `∇f(x)`, `∇²f(x)` (`Evals`);
3. all regularity promises hold with `L = L₁ = L₂ = 1`: for all rational `x, y ∈ [0, 1]²` and
   all returned data, none of the five violation inequalities holds (`NoViolation`);
4. every `ϵG`-approximate KKT point lies in `[1/12, 11/12]²`: every rational `x ∈ [0, 1]²` with
   `‖g_π(x)‖ ≤ ϵG` (proximal gradient with smoothness constant 1 on `[0, 1]²`) has both
   coordinates in `[1/12, 11/12]`.

**Formalization Note** The white-box maps are the machines' rational outputs at rational inputs
(p.17), so every promise is quantified over rational points. `[0, 1]²` is `Poly boxA boxB`.
The Hessian-Lipschitz promise uses the Frobenius norm. -/
def ValidBox (K : ℕ) (s : List Bool) : Prop :=
  ∃ (ϵG ϵH : ℚ) (T : ℕ) (cf cg cH : List Bool), s = encInst ϵG ϵH T cf cg cH ∧
    0 < ϵG ∧ 0 < ϵH ∧ ϵH ^ 2 = ϵG ∧
    (∀ x : Fin 2 → ℚ, (fun i => (x i : ℝ)) ∈ Poly boxA boxB →
      ∃ (v : ℚ) (g : Fin 2 → ℚ) (H : Fin 2 → Fin 2 → ℚ), Evals K T cf cg cH x v g H) ∧
    (∀ x y : Fin 2 → ℚ, (fun i => (x i : ℝ)) ∈ Poly boxA boxB →
      (fun i => (y i : ℝ)) ∈ Poly boxA boxB →
      ∀ (vx : ℚ) (gx : Fin 2 → ℚ) (Hx : Fin 2 → Fin 2 → ℚ) (vy : ℚ) (gy : Fin 2 → ℚ)
        (Hy : Fin 2 → Fin 2 → ℚ),
        Evals K T cf cg cH x vx gx Hx → Evals K T cf cg cH y vy gy Hy →
        NoViolation 1 1 1 (fun i => (x i : ℝ)) (vx : ℝ) (fun i => (gx i : ℝ))
          (Matrix.of fun i j => (Hx i j : ℝ)) (fun i => (y i : ℝ)) (vy : ℝ)
          (fun i => (gy i : ℝ)) (Matrix.of fun i j => (Hy i j : ℝ))) ∧
    (∀ x : Fin 2 → ℚ, (fun i => (x i : ℝ)) ∈ Poly boxA boxB →
      ∀ (v : ℚ) (g : Fin 2 → ℚ) (H : Fin 2 → Fin 2 → ℚ), Evals K T cf cg cH x v g H →
        IsApproxKKT boxA boxB 1 (ϵG : ℝ) (fun i => (x i : ℝ)) (fun i => (g i : ℝ)) →
        ∀ i, (1 / 12 : ℝ) ≤ (x i : ℝ) ∧ (x i : ℝ) ≤ 11 / 12)

end ConstrSOSP


