-- Prove2me | Definitions.Def_AnchoredEP_Supplement_newtonAbar
-- name    : AnchoredEP_Supplement_newtonAbar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:05:20.50018+00:00
-- url     : https://prove2.me/theorems/948f42c3-9c69-4e21-8d66-040a2a66eb84
-- title:
--   Upper trial step $\bar a_k$ of AEP Newton, Eq. (24)
-- statement:
--   At an outer iteration $k$ of the AEP Newton method with state $(z_k,v_k,A_k)$, target accuracy $\varepsilon>0$ and Jacobian Lipschitz constant $L_2>0$, the line search first evaluates the **upper trial step**
--   $$
--   \bar a_k:=\max\Big\{\frac{2A_k\|F(z_k)+v_k\|}{\varepsilon},\ \sqrt{\frac{2(1+\sqrt2)}{L_2\varepsilon}}\Big\}.
--   $$
--   If $\varphi_k(\bar a_k)\le\sqrt2$, the corresponding trial point already has tangent residual at most $\varepsilon$ (Lemma 4.2); otherwise $[0,\bar a_k]$ is the initial bisection interval.
-- source:
--   Jiang–Yoon, Anchored Extra-Proximal Methods: Optimal Higher-Order Methods for Monotone Inclusion Problems, arXiv:2609.30212, Eq. (24), p.9

import Mathlib
import Definitions.Def_AnchoredEP_IterState

namespace AnchoredEP.Supplement

/-- **The upper trial step size `ā_k` of AEP Newton.** Jiang–Yoon, arXiv:2609.30212, Eq. (24),
p.9:
`ā_k := max { 2A_k‖F(z_k) + v_k‖/ε , √(2(1 + √2)/(L₂ε)) }`. -/
noncomputable def newtonAbar {d : ℕ} (F : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (L ε : ℝ)
    (s : IterState d) : ℝ :=
  max (2 * s.A * ‖F s.z + s.v‖ / ε) (Real.sqrt (2 * (1 + Real.sqrt 2) / (L * ε)))

end AnchoredEP.Supplement


